import V185TrunkScan23Chunk0357

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2117480 : List Nat := [2, 1, 4, 2, 1, 1, 3, 2, 3, 2, 2]
def baseStart_2117480 : Nat := 118140960795 + 2117480 * 2 ^ 59
def prefixEnd_2117480 : Nat := 4983230072969 + 3 ^ 40 * 2117480 * 2
def baseEnd_2117480 : Nat := 1087285016282480583461893

theorem tailTrace_2117480 : CollatzResearch.WordTrace tailWord_2117480 prefixEnd_2117480 1087285016282480583461893 := by
  unfold tailWord_2117480
  simp only [CollatzResearch.WordTrace]
  refine ⟨38615420184369535818866947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51487226912492714425155929 38615420184369535818866947)
  ·
    refine ⟨57923130276554303728300421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38615420184369535818866947 57923130276554303728300421)
    ·
      refine ⟨10860586926853931949056329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57923130276554303728300421 10860586926853931949056329)
      ·
        refine ⟨8145440195140448961792247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10860586926853931949056329 8145440195140448961792247)
        ·
          refine ⟨12218160292710673442688371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8145440195140448961792247 12218160292710673442688371)
          ·
            refine ⟨18327240439066010164032557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12218160292710673442688371 18327240439066010164032557)
            ·
              refine ⟨6872715164649753811512209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18327240439066010164032557 6872715164649753811512209)
              ·
                refine ⟨5154536373487315358634157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6872715164649753811512209 5154536373487315358634157)
                ·
                  refine ⟨1932951140057743259487809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5154536373487315358634157 1932951140057743259487809)
                  ·
                    refine ⟨1449713355043307444615857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1932951140057743259487809 1449713355043307444615857)
                    ·
                      refine ⟨1087285016282480583461893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1449713355043307444615857 1087285016282480583461893)
                      ·
                        rfl

theorem cell23_2117480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 2, 3, 2, 2].length) (baseStart_2117480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2117480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2117480 prefixEnd_2117480 := by exact prefixLift 2117480
  have htrace : WordTrace (prefixWord ++ tailWord_2117480) baseStart_2117480 baseEnd_2117480 := by
    simpa [prefixWord, tailWord_2117480, baseEnd_2117480] using wordTrace_append hprefix tailTrace_2117480
  have hstable : (prefixWord ++ tailWord_2117480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117480).length < 2 ^ (prefixWord ++ tailWord_2117480).sum := by decide
  have hdescent : baseEnd_2117480 < baseStart_2117480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117494 : List Nat := [5, 1, 1, 3, 3, 1, 2, 1, 1, 5]
def baseStart_2117494 : Nat := 118140960795 + 2117494 * 2 ^ 59
def prefixEnd_2117494 : Nat := 4983230072969 + 3 ^ 40 * 2117494 * 2
def baseEnd_2117494 : Nat := 362430735003881176228943

theorem tailTrace_2117494 : CollatzResearch.WordTrace tailWord_2117494 prefixEnd_2117494 362430735003881176228943 := by
  unfold tailWord_2117494
  simp only [CollatzResearch.WordTrace]
  refine ⟨4826959436918022001796471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 51487567327125568019162357 4826959436918022001796471)
  ·
    refine ⟨7240439155377033002694707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4826959436918022001796471 7240439155377033002694707)
    ·
      refine ⟨10860658733065549504042061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7240439155377033002694707 10860658733065549504042061)
      ·
        refine ⟨4072747024899581064015773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10860658733065549504042061 4072747024899581064015773)
        ·
          refine ⟨1527280134337342899005915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4072747024899581064015773 1527280134337342899005915)
          ·
            refine ⟨2290920201506014348508873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1527280134337342899005915 2290920201506014348508873)
            ·
              refine ⟨1718190151129510761381655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2290920201506014348508873 1718190151129510761381655)
              ·
                refine ⟨2577285226694266142072483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1718190151129510761381655 2577285226694266142072483)
                ·
                  refine ⟨3865927840041399213108725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2577285226694266142072483 3865927840041399213108725)
                  ·
                    refine ⟨362430735003881176228943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3865927840041399213108725 362430735003881176228943)
                    ·
                      rfl

theorem cell23_2117494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 2, 1, 1, 5].length) (baseStart_2117494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2117494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2117494 prefixEnd_2117494 := by exact prefixLift 2117494
  have htrace : WordTrace (prefixWord ++ tailWord_2117494) baseStart_2117494 baseEnd_2117494 := by
    simpa [prefixWord, tailWord_2117494, baseEnd_2117494] using wordTrace_append hprefix tailTrace_2117494
  have hstable : (prefixWord ++ tailWord_2117494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117494).length < 2 ^ (prefixWord ++ tailWord_2117494).sum := by decide
  have hdescent : baseEnd_2117494 < baseStart_2117494 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117497 : List Nat := [1, 2, 1, 3, 2, 2, 4, 3, 1, 2, 2]
def baseStart_2117497 : Nat := 118140960795 + 2117497 * 2 ^ 59
def prefixEnd_2117497 : Nat := 4983230072969 + 3 ^ 40 * 2117497 * 2
def baseEnd_2117497 : Nat := 1087293745453607016949315

theorem tailTrace_2117497 : CollatzResearch.WordTrace tailWord_2117497 prefixEnd_2117497 1087293745453607016949315 := by
  unfold tailWord_2117497
  simp only [CollatzResearch.WordTrace]
  refine ⟨77231460409677483541102745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51487640273118322360735163 77231460409677483541102745)
  ·
    refine ⟨57923595307258112655827059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77231460409677483541102745 57923595307258112655827059)
    ·
      refine ⟨86885392960887168983740589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57923595307258112655827059 86885392960887168983740589)
      ·
        refine ⟨32582022360332688368902721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86885392960887168983740589 32582022360332688368902721)
        ·
          refine ⟨24436516770249516276677041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32582022360332688368902721 24436516770249516276677041)
          ·
            refine ⟨18327387577687137207507781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24436516770249516276677041 18327387577687137207507781)
            ·
              refine ⟨3436385170816338226407709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18327387577687137207507781 3436385170816338226407709)
              ·
                refine ⟨1288644439056126834902891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3436385170816338226407709 1288644439056126834902891)
                ·
                  refine ⟨1932966658584190252354337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1288644439056126834902891 1932966658584190252354337)
                  ·
                    refine ⟨1449724993938142689265753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1932966658584190252354337 1449724993938142689265753)
                    ·
                      refine ⟨1087293745453607016949315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1449724993938142689265753 1087293745453607016949315)
                      ·
                        rfl

theorem cell23_2117497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 3, 1, 2, 2].length) (baseStart_2117497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2117497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2117497 prefixEnd_2117497 := by exact prefixLift 2117497
  have htrace : WordTrace (prefixWord ++ tailWord_2117497) baseStart_2117497 baseEnd_2117497 := by
    simpa [prefixWord, tailWord_2117497, baseEnd_2117497] using wordTrace_append hprefix tailTrace_2117497
  have hstable : (prefixWord ++ tailWord_2117497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117497).length < 2 ^ (prefixWord ++ tailWord_2117497).sum := by decide
  have hdescent : baseEnd_2117497 < baseStart_2117497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117513 : List Nat := [1, 2, 1, 1, 5, 1, 3, 1, 4, 1, 3]
def baseStart_2117513 : Nat := 118140960795 + 2117513 * 2 ^ 59
def prefixEnd_2117513 : Nat := 4983230072969 + 3 ^ 40 * 2117513 * 2
def baseEnd_2117513 : Nat := 1087301961144078954349241

theorem tailTrace_2117513 : CollatzResearch.WordTrace tailWord_2117513 prefixEnd_2117513 1087301961144078954349241 := by
  unfold tailWord_2117513
  simp only [CollatzResearch.WordTrace]
  refine ⟨77232043977619518273685193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51488029318413012182456795 77232043977619518273685193)
  ·
    refine ⟨57924032983214638705263895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77232043977619518273685193 57924032983214638705263895)
    ·
      refine ⟨86886049474821958057895843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57924032983214638705263895 86886049474821958057895843)
      ·
        refine ⟨130329074212232937086843765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86886049474821958057895843 130329074212232937086843765)
        ·
          refine ⟨12218350707396837851891603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 130329074212232937086843765 12218350707396837851891603)
          ·
            refine ⟨18327526061095256777837405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12218350707396837851891603 18327526061095256777837405)
            ·
              refine ⟨6872822272910721291689027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18327526061095256777837405 6872822272910721291689027)
              ·
                refine ⟨10309233409366081937533541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6872822272910721291689027 10309233409366081937533541)
                ·
                  refine ⟨1932981264256140363287539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10309233409366081937533541 1932981264256140363287539)
                  ·
                    refine ⟨2899471896384210544931309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1932981264256140363287539 2899471896384210544931309)
                    ·
                      refine ⟨1087301961144078954349241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2899471896384210544931309 1087301961144078954349241)
                      ·
                        rfl

theorem cell23_2117513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 1, 4, 1, 3].length) (baseStart_2117513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2117513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2117513 prefixEnd_2117513 := by exact prefixLift 2117513
  have htrace : WordTrace (prefixWord ++ tailWord_2117513) baseStart_2117513 baseEnd_2117513 := by
    simpa [prefixWord, tailWord_2117513, baseEnd_2117513] using wordTrace_append hprefix tailTrace_2117513
  have hstable : (prefixWord ++ tailWord_2117513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117513).length < 2 ^ (prefixWord ++ tailWord_2117513).sum := by decide
  have hdescent : baseEnd_2117513 < baseStart_2117513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117530 : List Nat := [3, 1, 1, 4, 2, 3, 1, 1, 1, 3, 3]
def baseStart_2117530 : Nat := 118140960795 + 2117530 * 2 ^ 59
def prefixEnd_2117530 : Nat := 4983230072969 + 3 ^ 40 * 2117530 * 2
def baseEnd_2117530 : Nat := 1087310690315205387836663

theorem tailTrace_2117530 : CollatzResearch.WordTrace tailWord_2117530 prefixEnd_2117530 1087310690315205387836663 := by
  unfold tailWord_2117530
  simp only [CollatzResearch.WordTrace]
  refine ⟨19308166004639482544263511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51488442679038620118036029 19308166004639482544263511)
  ·
    refine ⟨28962249006959223816395267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19308166004639482544263511 28962249006959223816395267)
    ·
      refine ⟨43443373510438835724592901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28962249006959223816395267 43443373510438835724592901)
      ·
        refine ⟨8145632533207281698361169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43443373510438835724592901 8145632533207281698361169)
        ·
          refine ⟨6109224399905461273770877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8145632533207281698361169 6109224399905461273770877)
          ·
            refine ⟨2290959149964547977664079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6109224399905461273770877 2290959149964547977664079)
            ·
              refine ⟨3436438724946821966496119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2290959149964547977664079 3436438724946821966496119)
              ·
                refine ⟨5154658087420232949744179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3436438724946821966496119 5154658087420232949744179)
                ·
                  refine ⟨7731987131130349424616269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5154658087420232949744179 7731987131130349424616269)
                  ·
                    refine ⟨2899495174173881034231101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7731987131130349424616269 2899495174173881034231101)
                    ·
                      refine ⟨1087310690315205387836663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2899495174173881034231101 1087310690315205387836663)
                      ·
                        rfl

theorem cell23_2117530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_2117530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2117530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2117530 prefixEnd_2117530 := by exact prefixLift 2117530
  have htrace : WordTrace (prefixWord ++ tailWord_2117530) baseStart_2117530 baseEnd_2117530 := by
    simpa [prefixWord, tailWord_2117530, baseEnd_2117530] using wordTrace_append hprefix tailTrace_2117530
  have hstable : (prefixWord ++ tailWord_2117530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117530).length < 2 ^ (prefixWord ++ tailWord_2117530).sum := by decide
  have hdescent : baseEnd_2117530 < baseStart_2117530 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117534 : List Nat := [4, 3, 1, 3, 1, 1, 2, 2, 1, 2, 3]
def baseStart_2117534 : Nat := 118140960795 + 2117534 * 2 ^ 59
def prefixEnd_2117534 : Nat := 4983230072969 + 3 ^ 40 * 2117534 * 2
def baseEnd_2117534 : Nat := 1087312744237823372186645

theorem tailTrace_2117534 : CollatzResearch.WordTrace tailWord_2117534 prefixEnd_2117534 1087312744237823372186645 := by
  unfold tailWord_2117534
  simp only [CollatzResearch.WordTrace]
  refine ⟨9654101238817929857524957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51488539940362292573466437 9654101238817929857524957)
  ·
    refine ⟨3620287964556723696571859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9654101238817929857524957 3620287964556723696571859)
    ·
      refine ⟨5430431946835085544857789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3620287964556723696571859 5430431946835085544857789)
      ·
        refine ⟨2036411980063157079321671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5430431946835085544857789 2036411980063157079321671)
        ·
          refine ⟨3054617970094735618982507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2036411980063157079321671 3054617970094735618982507)
          ·
            refine ⟨4581926955142103428473761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3054617970094735618982507 4581926955142103428473761)
            ·
              refine ⟨3436445216356577571355321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4581926955142103428473761 3436445216356577571355321)
              ·
                refine ⟨2577333912267433178516491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3436445216356577571355321 2577333912267433178516491)
                ·
                  refine ⟨3866000868401149767774737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2577333912267433178516491 3866000868401149767774737)
                  ·
                    refine ⟨2899500651300862325831053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3866000868401149767774737 2899500651300862325831053)
                    ·
                      refine ⟨1087312744237823372186645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2899500651300862325831053 1087312744237823372186645)
                      ·
                        rfl

theorem cell23_2117534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_2117534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2117534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2117534 prefixEnd_2117534 := by exact prefixLift 2117534
  have htrace : WordTrace (prefixWord ++ tailWord_2117534) baseStart_2117534 baseEnd_2117534 := by
    simpa [prefixWord, tailWord_2117534, baseEnd_2117534] using wordTrace_append hprefix tailTrace_2117534
  have hstable : (prefixWord ++ tailWord_2117534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117534).length < 2 ^ (prefixWord ++ tailWord_2117534).sum := by decide
  have hdescent : baseEnd_2117534 < baseStart_2117534 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117540 : List Nat := [2, 3, 1, 2, 1, 3, 1, 4, 1, 3, 2]
def baseStart_2117540 : Nat := 118140960795 + 2117540 * 2 ^ 59
def prefixEnd_2117540 : Nat := 4983230072969 + 3 ^ 40 * 2117540 * 2
def baseEnd_2117540 : Nat := 1087315825121750348711617

theorem tailTrace_2117540 : CollatzResearch.WordTrace tailWord_2117540 prefixEnd_2117540 1087315825121750348711617 := by
  unfold tailWord_2117540
  simp only [CollatzResearch.WordTrace]
  refine ⟨38616514374260850942459037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51488685832347801256612049 38616514374260850942459037)
  ·
    refine ⟨14481192890347819103422139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38616514374260850942459037 14481192890347819103422139)
    ·
      refine ⟨21721789335521728655133209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14481192890347819103422139 21721789335521728655133209)
      ·
        refine ⟨16291342001641296491349907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21721789335521728655133209 16291342001641296491349907)
        ·
          refine ⟨24437013002461944737024861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16291342001641296491349907 24437013002461944737024861)
          ·
            refine ⟨9163879875923229276384323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24437013002461944737024861 9163879875923229276384323)
            ·
              refine ⟨13745819813884843914576485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9163879875923229276384323 13745819813884843914576485)
              ·
                refine ⟨2577341215103408233983091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13745819813884843914576485 2577341215103408233983091)
                ·
                  refine ⟨3866011822655112350974637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2577341215103408233983091 3866011822655112350974637)
                  ·
                    refine ⟨1449754433495667131615489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3866011822655112350974637 1449754433495667131615489)
                    ·
                      refine ⟨1087315825121750348711617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1449754433495667131615489 1087315825121750348711617)
                      ·
                        rfl

theorem cell23_2117540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 4, 1, 3, 2].length) (baseStart_2117540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2117540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2117540 prefixEnd_2117540 := by exact prefixLift 2117540
  have htrace : WordTrace (prefixWord ++ tailWord_2117540) baseStart_2117540 baseEnd_2117540 := by
    simpa [prefixWord, tailWord_2117540, baseEnd_2117540] using wordTrace_append hprefix tailTrace_2117540
  have hstable : (prefixWord ++ tailWord_2117540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117540).length < 2 ^ (prefixWord ++ tailWord_2117540).sum := by decide
  have hdescent : baseEnd_2117540 < baseStart_2117540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117616 : List Nat := [2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 5]
def baseStart_2117616 : Nat := 118140960795 + 2117616 * 2 ^ 59
def prefixEnd_2117616 : Nat := 4983230072969 + 3 ^ 40 * 2117616 * 2
def baseEnd_2117616 : Nat := 1087354849651492051361267

theorem tailTrace_2117616 : CollatzResearch.WordTrace tailWord_2117616 prefixEnd_2117616 1087354849651492051361267 := by
  unfold tailWord_2117616
  simp only [CollatzResearch.WordTrace]
  refine ⟨38617900348123183432342351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51490533797497577909789801 38617900348123183432342351)
  ·
    refine ⟨57926850522184775148513527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38617900348123183432342351 57926850522184775148513527)
    ·
      refine ⟨86890275783277162722770291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57926850522184775148513527 86890275783277162722770291)
      ·
        refine ⟨130335413674915744084155437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86890275783277162722770291 130335413674915744084155437)
        ·
          refine ⟨48875780128093404031558289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 130335413674915744084155437 48875780128093404031558289)
          ·
            refine ⟨36656835096070053023668717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48875780128093404031558289 36656835096070053023668717)
            ·
              refine ⟨13746313161026269883875769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36656835096070053023668717 13746313161026269883875769)
              ·
                refine ⟨10309734870769702412906827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13746313161026269883875769 10309734870769702412906827)
                ·
                  refine ⟨15464602306154553619360241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10309734870769702412906827 15464602306154553619360241)
                  ·
                    refine ⟨11598451729615915214520181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15464602306154553619360241 11598451729615915214520181)
                    ·
                      refine ⟨1087354849651492051361267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11598451729615915214520181 1087354849651492051361267)
                      ·
                        rfl

theorem cell23_2117616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 5].length) (baseStart_2117616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2117616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2117616 prefixEnd_2117616 := by exact prefixLift 2117616
  have htrace : WordTrace (prefixWord ++ tailWord_2117616) baseStart_2117616 baseEnd_2117616 := by
    simpa [prefixWord, tailWord_2117616, baseEnd_2117616] using wordTrace_append hprefix tailTrace_2117616
  have hstable : (prefixWord ++ tailWord_2117616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117616).length < 2 ^ (prefixWord ++ tailWord_2117616).sum := by decide
  have hdescent : baseEnd_2117616 < baseStart_2117616 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117626 : List Nat := [3, 1, 1, 1, 1, 2, 1, 1, 5, 3, 4]
def baseStart_2117626 : Nat := 118140960795 + 2117626 * 2 ^ 59
def prefixEnd_2117626 : Nat := 4983230072969 + 3 ^ 40 * 2117626 * 2
def baseEnd_2117626 : Nat := 1087359984458037012236221

theorem tailTrace_2117626 : CollatzResearch.WordTrace tailWord_2117626 prefixEnd_2117626 1087359984458037012236221 := by
  unfold tailWord_2117626
  simp only [CollatzResearch.WordTrace]
  refine ⟨19309041356552534643137183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51490776950806759048365821 19309041356552534643137183)
  ·
    refine ⟨28963562034828801964705775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19309041356552534643137183 28963562034828801964705775)
    ·
      refine ⟨43445343052243202947058663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28963562034828801964705775 43445343052243202947058663)
      ·
        refine ⟨65168014578364804420587995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43445343052243202947058663 65168014578364804420587995)
        ·
          refine ⟨97752021867547206630881993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65168014578364804420587995 97752021867547206630881993)
          ·
            refine ⟨73314016400660404973161495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97752021867547206630881993 73314016400660404973161495)
            ·
              refine ⟨109971024600990607459742243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73314016400660404973161495 109971024600990607459742243)
              ·
                refine ⟨164956536901485911189613365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109971024600990607459742243 164956536901485911189613365)
                ·
                  refine ⟨15464675334514304174026253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 164956536901485911189613365 15464675334514304174026253)
                  ·
                    refine ⟨5799253250442864065259845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15464675334514304174026253 5799253250442864065259845)
                    ·
                      refine ⟨1087359984458037012236221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5799253250442864065259845 1087359984458037012236221)
                      ·
                        rfl

theorem cell23_2117626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 5, 3, 4].length) (baseStart_2117626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2117626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2117626 prefixEnd_2117626 := by exact prefixLift 2117626
  have htrace : WordTrace (prefixWord ++ tailWord_2117626) baseStart_2117626 baseEnd_2117626 := by
    simpa [prefixWord, tailWord_2117626, baseEnd_2117626] using wordTrace_append hprefix tailTrace_2117626
  have hstable : (prefixWord ++ tailWord_2117626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117626).length < 2 ^ (prefixWord ++ tailWord_2117626).sum := by decide
  have hdescent : baseEnd_2117626 < baseStart_2117626 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117638 : List Nat := [6, 2, 1, 2, 1, 1, 2, 1, 1, 4, 2]
def baseStart_2117638 : Nat := 118140960795 + 2117638 * 2 ^ 59
def prefixEnd_2117638 : Nat := 4983230072969 + 3 ^ 40 * 2117638 * 2
def baseEnd_2117638 : Nat := 1087366146225890965286167

theorem tailTrace_2117638 : CollatzResearch.WordTrace tailWord_2117638 prefixEnd_2117638 1087366146225890965286167 := by
  unfold tailWord_2117638
  simp only [CollatzResearch.WordTrace]
  refine ⟨2413643846942708269437049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 51491068734777776414657045 2413643846942708269437049)
  ·
    refine ⟨1810232885207031202077787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2413643846942708269437049 1810232885207031202077787)
    ·
      refine ⟨2715349327810546803116681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1810232885207031202077787 2715349327810546803116681)
      ·
        refine ⟨2036511995857910102337511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2715349327810546803116681 2036511995857910102337511)
        ·
          refine ⟨3054767993786865153506267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2036511995857910102337511 3054767993786865153506267)
          ·
            refine ⟨4582151990680297730259401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3054767993786865153506267 4582151990680297730259401)
            ·
              refine ⟨3436613993010223297694551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4582151990680297730259401 3436613993010223297694551)
              ·
                refine ⟨5154920989515334946541827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3436613993010223297694551 5154920989515334946541827)
                ·
                  refine ⟨7732381484273002419812741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5154920989515334946541827 7732381484273002419812741)
                  ·
                    refine ⟨1449821528301187953714889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7732381484273002419812741 1449821528301187953714889)
                    ·
                      refine ⟨1087366146225890965286167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1449821528301187953714889 1087366146225890965286167)
                      ·
                        rfl

theorem cell23_2117638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_2117638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2117638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2117638 prefixEnd_2117638 := by exact prefixLift 2117638
  have htrace : WordTrace (prefixWord ++ tailWord_2117638) baseStart_2117638 baseEnd_2117638 := by
    simpa [prefixWord, tailWord_2117638, baseEnd_2117638] using wordTrace_append hprefix tailTrace_2117638
  have hstable : (prefixWord ++ tailWord_2117638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117638).length < 2 ^ (prefixWord ++ tailWord_2117638).sum := by decide
  have hdescent : baseEnd_2117638 < baseStart_2117638 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117660 : List Nat := [2, 2, 3, 1, 3, 1, 3, 1, 2, 1, 4]
def baseStart_2117660 : Nat := 118140960795 + 2117660 * 2 ^ 59
def prefixEnd_2117660 : Nat := 4983230072969 + 3 ^ 40 * 2117660 * 2
def baseEnd_2117660 : Nat := 1087377442800289879211065

theorem tailTrace_2117660 : CollatzResearch.WordTrace tailWord_2117660 prefixEnd_2117660 1087377442800289879211065 := by
  unfold tailWord_2117660
  simp only [CollatzResearch.WordTrace]
  refine ⟨38618702754043481189643217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51491603672057974919524289 38618702754043481189643217)
  ·
    refine ⟨28964027065532610892232413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38618702754043481189643217 28964027065532610892232413)
    ·
      refine ⟨10861510149574729084587155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28964027065532610892232413 10861510149574729084587155)
      ·
        refine ⟨16292265224362093626880733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10861510149574729084587155 16292265224362093626880733)
        ·
          refine ⟨6109599459135785110080275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16292265224362093626880733 6109599459135785110080275)
          ·
            refine ⟨9164399188703677665120413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6109599459135785110080275 9164399188703677665120413)
            ·
              refine ⟨3436649695763879124420155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9164399188703677665120413 3436649695763879124420155)
              ·
                refine ⟨5154974543645818686630233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3436649695763879124420155 5154974543645818686630233)
                ·
                  refine ⟨3866230907734364014972675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5154974543645818686630233 3866230907734364014972675)
                  ·
                    refine ⟨5799346361601546022459013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3866230907734364014972675 5799346361601546022459013)
                    ·
                      refine ⟨1087377442800289879211065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5799346361601546022459013 1087377442800289879211065)
                      ·
                        rfl

theorem cell23_2117660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 1, 2, 1, 4].length) (baseStart_2117660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2117660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2117660 prefixEnd_2117660 := by exact prefixLift 2117660
  have htrace : WordTrace (prefixWord ++ tailWord_2117660) baseStart_2117660 baseEnd_2117660 := by
    simpa [prefixWord, tailWord_2117660, baseEnd_2117660] using wordTrace_append hprefix tailTrace_2117660
  have hstable : (prefixWord ++ tailWord_2117660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117660).length < 2 ^ (prefixWord ++ tailWord_2117660).sum := by decide
  have hdescent : baseEnd_2117660 < baseStart_2117660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117663 : List Nat := [1, 1, 2, 4, 1, 2, 3, 1, 1, 4, 3]
def baseStart_2117663 : Nat := 118140960795 + 2117663 * 2 ^ 59
def prefixEnd_2117663 : Nat := 4983230072969 + 3 ^ 40 * 2117663 * 2
def baseEnd_2117663 : Nat := 1087378983242253367473551

theorem tailTrace_2117663 : CollatzResearch.WordTrace tailWord_2117663 prefixEnd_2117663 1087378983242253367473551 := by
  unfold tailWord_2117663
  simp only [CollatzResearch.WordTrace]
  refine ⟨77237514927076093891645643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51491676618050729261097095 77237514927076093891645643)
  ·
    refine ⟨115856272390614140837468465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77237514927076093891645643 115856272390614140837468465)
    ·
      refine ⟨86892204292960605628101349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115856272390614140837468465 86892204292960605628101349)
      ·
        refine ⟨16292288304930113555269003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 86892204292960605628101349 16292288304930113555269003)
        ·
          refine ⟨24438432457395170332903505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16292288304930113555269003 24438432457395170332903505)
          ·
            refine ⟨18328824343046377749677629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24438432457395170332903505 18328824343046377749677629)
            ·
              refine ⟨6873309128642391656129111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18328824343046377749677629 6873309128642391656129111)
              ·
                refine ⟨10309963692963587484193667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6873309128642391656129111 10309963692963587484193667)
                ·
                  refine ⟨15464945539445381226290501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10309963692963587484193667 15464945539445381226290501)
                  ·
                    refine ⟨2899677288646008979929469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15464945539445381226290501 2899677288646008979929469)
                    ·
                      refine ⟨1087378983242253367473551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2899677288646008979929469 1087378983242253367473551)
                      ·
                        rfl

theorem cell23_2117663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 1, 1, 4, 3].length) (baseStart_2117663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2117663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2117663 prefixEnd_2117663 := by exact prefixLift 2117663
  have htrace : WordTrace (prefixWord ++ tailWord_2117663) baseStart_2117663 baseEnd_2117663 := by
    simpa [prefixWord, tailWord_2117663, baseEnd_2117663] using wordTrace_append hprefix tailTrace_2117663
  have hstable : (prefixWord ++ tailWord_2117663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117663).length < 2 ^ (prefixWord ++ tailWord_2117663).sum := by decide
  have hdescent : baseEnd_2117663 < baseStart_2117663 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117683 : List Nat := [1, 1, 1, 2, 4, 1, 5, 2, 6]
def baseStart_2117683 : Nat := 118140960795 + 2117683 * 2 ^ 59
def prefixEnd_2117683 : Nat := 4983230072969 + 3 ^ 40 * 2117683 * 2
def baseEnd_2117683 : Nat := 120821028095038143247051

theorem tailTrace_2117683 : CollatzResearch.WordTrace tailWord_2117683 prefixEnd_2117683 120821028095038143247051 := by
  unfold tailWord_2117683
  simp only [CollatzResearch.WordTrace]
  refine ⟨77238244387003637307373703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51492162924669091538249135 77238244387003637307373703)
  ·
    refine ⟨115857366580505455961060555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77238244387003637307373703 115857366580505455961060555)
    ·
      refine ⟨173786049870758183941590833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115857366580505455961060555 173786049870758183941590833)
      ·
        refine ⟨130339537403068637956193125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173786049870758183941590833 130339537403068637956193125)
        ·
          refine ⟨24438663263075369616786211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 130339537403068637956193125 24438663263075369616786211)
          ·
            refine ⟨36657994894613054425179317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24438663263075369616786211 36657994894613054425179317)
            ·
              refine ⟨3436687021369973852360561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36657994894613054425179317 3436687021369973852360561)
              ·
                refine ⟨2577515266027480389270421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3436687021369973852360561 2577515266027480389270421)
                ·
                  refine ⟨120821028095038143247051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2577515266027480389270421 120821028095038143247051)
                  ·
                    rfl

theorem cell23_2117683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 2, 6].length) (baseStart_2117683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2117683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2117683 prefixEnd_2117683 := by exact prefixLift 2117683
  have htrace : WordTrace (prefixWord ++ tailWord_2117683) baseStart_2117683 baseEnd_2117683 := by
    simpa [prefixWord, tailWord_2117683, baseEnd_2117683] using wordTrace_append hprefix tailTrace_2117683
  have hstable : (prefixWord ++ tailWord_2117683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117683).length < 2 ^ (prefixWord ++ tailWord_2117683).sum := by decide
  have hdescent : baseEnd_2117683 < baseStart_2117683 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117720 : List Nat := [2, 1, 2, 2, 1, 4, 2, 1, 1, 5, 2]
def baseStart_2117720 : Nat := 118140960795 + 2117720 * 2 ^ 59
def prefixEnd_2117720 : Nat := 4983230072969 + 3 ^ 40 * 2117720 * 2
def baseEnd_2117720 : Nat := 1087408251639559644460789

theorem tailTrace_2117720 : CollatzResearch.WordTrace tailWord_2117720 prefixEnd_2117720 1087408251639559644460789 := by
  unfold tailWord_2117720
  simp only [CollatzResearch.WordTrace]
  refine ⟨38619796943934796313235307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51493062591913061750980409 38619796943934796313235307)
  ·
    refine ⟨57929695415902194469852961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38619796943934796313235307 57929695415902194469852961)
    ·
      refine ⟨43447271561926645852389721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57929695415902194469852961 43447271561926645852389721)
      ·
        refine ⟨32585453671444984389292291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43447271561926645852389721 32585453671444984389292291)
        ·
          refine ⟨48878180507167476583938437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32585453671444984389292291 48878180507167476583938437)
          ·
            refine ⟨9164658845093901859488457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48878180507167476583938437 9164658845093901859488457)
            ·
              refine ⟨6873494133820426394616343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9164658845093901859488457 6873494133820426394616343)
              ·
                refine ⟨10310241200730639591924515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6873494133820426394616343 10310241200730639591924515)
                ·
                  refine ⟨15465361801095959387886773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10310241200730639591924515 15465361801095959387886773)
                  ·
                    refine ⟨1449877668852746192614385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15465361801095959387886773 1449877668852746192614385)
                    ·
                      refine ⟨1087408251639559644460789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1449877668852746192614385 1087408251639559644460789)
                      ·
                        rfl

theorem cell23_2117720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 1, 1, 5, 2].length) (baseStart_2117720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2117720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2117720 prefixEnd_2117720 := by exact prefixLift 2117720
  have htrace : WordTrace (prefixWord ++ tailWord_2117720) baseStart_2117720 baseEnd_2117720 := by
    simpa [prefixWord, tailWord_2117720, baseEnd_2117720] using wordTrace_append hprefix tailTrace_2117720
  have hstable : (prefixWord ++ tailWord_2117720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117720).length < 2 ^ (prefixWord ++ tailWord_2117720).sum := by decide
  have hdescent : baseEnd_2117720 < baseStart_2117720 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117727 : List Nat := [1, 1, 2, 3, 1, 1, 2, 7, 1, 1, 3]
def baseStart_2117727 : Nat := 118140960795 + 2117727 * 2 ^ 59
def prefixEnd_2117727 : Nat := 4983230072969 + 3 ^ 40 * 2117727 * 2
def baseEnd_2117727 : Nat := 1087411846004141117073257

theorem tailTrace_2117727 : CollatzResearch.WordTrace tailWord_2117727 prefixEnd_2117727 1087411846004141117073257 := by
  unfold tailWord_2117727
  simp only [CollatzResearch.WordTrace]
  refine ⟨77239849198844232821975435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51493232799229488547983623 77239849198844232821975435)
  ·
    refine ⟨115859773798266349232963153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77239849198844232821975435 115859773798266349232963153)
    ·
      refine ⟨86894830348699761924722365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115859773798266349232963153 86894830348699761924722365)
      ·
        refine ⟨32585561380762410721770887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86894830348699761924722365 32585561380762410721770887)
        ·
          refine ⟨48878342071143616082656331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32585561380762410721770887 48878342071143616082656331)
          ·
            refine ⟨73317513106715424123984497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48878342071143616082656331 73317513106715424123984497)
            ·
              refine ⟨54988134830036568092988373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73317513106715424123984497 54988134830036568092988373)
              ·
                refine ⟨1288784410078982064679415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 54988134830036568092988373 1288784410078982064679415)
                ·
                  refine ⟨1933176615118473097019123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1288784410078982064679415 1933176615118473097019123)
                  ·
                    refine ⟨2899764922677709645528685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1933176615118473097019123 2899764922677709645528685)
                    ·
                      refine ⟨1087411846004141117073257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2899764922677709645528685 1087411846004141117073257)
                      ·
                        rfl

theorem cell23_2117727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 7, 1, 1, 3].length) (baseStart_2117727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2117727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2117727 prefixEnd_2117727 := by exact prefixLift 2117727
  have htrace : WordTrace (prefixWord ++ tailWord_2117727) baseStart_2117727 baseEnd_2117727 := by
    simpa [prefixWord, tailWord_2117727, baseEnd_2117727] using wordTrace_append hprefix tailTrace_2117727
  have hstable : (prefixWord ++ tailWord_2117727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117727).length < 2 ^ (prefixWord ++ tailWord_2117727).sum := by decide
  have hdescent : baseEnd_2117727 < baseStart_2117727 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117763 : List Nat := [1, 1, 1, 3, 3, 3, 2, 1, 1, 1, 6]
def baseStart_2117763 : Nat := 118140960795 + 2117763 * 2 ^ 59
def prefixEnd_2117763 : Nat := 4983230072969 + 3 ^ 40 * 2117763 * 2
def baseEnd_2117763 : Nat := 1087430331307702976223091

theorem tailTrace_2117763 : CollatzResearch.WordTrace tailWord_2117763 prefixEnd_2117763 1087430331307702976223091 := by
  unfold tailWord_2117763
  simp only [CollatzResearch.WordTrace]
  refine ⟨77241162226713810970285943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51494108151142540646857295 77241162226713810970285943)
  ·
    refine ⟨115861743340070716455428915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77241162226713810970285943 115861743340070716455428915)
    ·
      refine ⟨173792615010106074683143373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115861743340070716455428915 173792615010106074683143373)
      ·
        refine ⟨65172230628789778006178765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 173792615010106074683143373 65172230628789778006178765)
        ·
          refine ⟨24439586485796166752317037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65172230628789778006178765 24439586485796166752317037)
          ·
            refine ⟨9164844932173562532118889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24439586485796166752317037 9164844932173562532118889)
            ·
              refine ⟨6873633699130171899089167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9164844932173562532118889 6873633699130171899089167)
              ·
                refine ⟨10310450548695257848633751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6873633699130171899089167 10310450548695257848633751)
                ·
                  refine ⟨15465675823042886772950627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10310450548695257848633751 15465675823042886772950627)
                  ·
                    refine ⟨23198513734564330159425941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15465675823042886772950627 23198513734564330159425941)
                    ·
                      refine ⟨1087430331307702976223091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23198513734564330159425941 1087430331307702976223091)
                      ·
                        rfl

theorem cell23_2117763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 1, 1, 1, 6].length) (baseStart_2117763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2117763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2117763 prefixEnd_2117763 := by exact prefixLift 2117763
  have htrace : WordTrace (prefixWord ++ tailWord_2117763) baseStart_2117763 baseEnd_2117763 := by
    simpa [prefixWord, tailWord_2117763, baseEnd_2117763] using wordTrace_append hprefix tailTrace_2117763
  have hstable : (prefixWord ++ tailWord_2117763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117763).length < 2 ^ (prefixWord ++ tailWord_2117763).sum := by decide
  have hdescent : baseEnd_2117763 < baseStart_2117763 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117767 : List Nat := [1, 1, 4, 2, 1, 1, 2, 4, 3, 2, 2]
def baseStart_2117767 : Nat := 118140960795 + 2117767 * 2 ^ 59
def prefixEnd_2117767 : Nat := 4983230072969 + 3 ^ 40 * 2117767 * 2
def baseEnd_2117767 : Nat := 1087432385230320960573073

theorem tailTrace_2117767 : CollatzResearch.WordTrace tailWord_2117767 prefixEnd_2117767 1087432385230320960573073 := by
  unfold tailWord_2117767
  simp only [CollatzResearch.WordTrace]
  refine ⟨77241308118699319653431555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51494205412466213102287703 77241308118699319653431555)
  ·
    refine ⟨115861962178048979480147333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77241308118699319653431555 115861962178048979480147333)
    ·
      refine ⟨21724117908384183652527625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 115861962178048979480147333 21724117908384183652527625)
      ·
        refine ⟨16293088431288137739395719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21724117908384183652527625 16293088431288137739395719)
        ·
          refine ⟨24439632646932206609093579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16293088431288137739395719 24439632646932206609093579)
          ·
            refine ⟨36659448970398309913640369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24439632646932206609093579 36659448970398309913640369)
            ·
              refine ⟨27494586727798732435230277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36659448970398309913640369 27494586727798732435230277)
              ·
                refine ⟨5155235011462262331605677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27494586727798732435230277 5155235011462262331605677)
                ·
                  refine ⟨1933213129298348374352129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5155235011462262331605677 1933213129298348374352129)
                  ·
                    refine ⟨1449909846973761280764097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1933213129298348374352129 1449909846973761280764097)
                    ·
                      refine ⟨1087432385230320960573073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1449909846973761280764097 1087432385230320960573073)
                      ·
                        rfl

theorem cell23_2117767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 4, 3, 2, 2].length) (baseStart_2117767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2117767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2117767 prefixEnd_2117767 := by exact prefixLift 2117767
  have htrace : WordTrace (prefixWord ++ tailWord_2117767) baseStart_2117767 baseEnd_2117767 := by
    simpa [prefixWord, tailWord_2117767, baseEnd_2117767] using wordTrace_append hprefix tailTrace_2117767
  have hstable : (prefixWord ++ tailWord_2117767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117767).length < 2 ^ (prefixWord ++ tailWord_2117767).sum := by decide
  have hdescent : baseEnd_2117767 < baseStart_2117767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117784 : List Nat := [2, 1, 2, 4, 3, 1, 3, 1, 1, 1, 4]
def baseStart_2117784 : Nat := 118140960795 + 2117784 * 2 ^ 59
def prefixEnd_2117784 : Nat := 4983230072969 + 3 ^ 40 * 2117784 * 2
def baseEnd_2117784 : Nat := 1087441114401447394060495

theorem tailTrace_2117784 : CollatzResearch.WordTrace tailWord_2117784 prefixEnd_2117784 1087441114401447394060495 := by
  unfold tailWord_2117784
  simp only [CollatzResearch.WordTrace]
  refine ⟨38620964079818865778400203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51494618773091821037866937 38620964079818865778400203)
  ·
    refine ⟨57931446119728298667600305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38620964079818865778400203 57931446119728298667600305)
    ·
      refine ⟨43448584589796224000700229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57931446119728298667600305 43448584589796224000700229)
      ·
        refine ⟨8146609610586792000131293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43448584589796224000700229 8146609610586792000131293)
        ·
          refine ⟨3054978603970047000049235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8146609610586792000131293 3054978603970047000049235)
          ·
            refine ⟨4582467905955070500073853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3054978603970047000049235 4582467905955070500073853)
            ·
              refine ⟨1718425464733151437527695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4582467905955070500073853 1718425464733151437527695)
              ·
                refine ⟨2577638197099727156291543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1718425464733151437527695 2577638197099727156291543)
                ·
                  refine ⟨3866457295649590734437315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2577638197099727156291543 3866457295649590734437315)
                  ·
                    refine ⟨5799685943474386101655973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3866457295649590734437315 5799685943474386101655973)
                    ·
                      refine ⟨1087441114401447394060495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5799685943474386101655973 1087441114401447394060495)
                      ·
                        rfl

theorem cell23_2117784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 3, 1, 1, 1, 4].length) (baseStart_2117784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2117784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2117784 prefixEnd_2117784 := by exact prefixLift 2117784
  have htrace : WordTrace (prefixWord ++ tailWord_2117784) baseStart_2117784 baseEnd_2117784 := by
    simpa [prefixWord, tailWord_2117784, baseEnd_2117784] using wordTrace_append hprefix tailTrace_2117784
  have hstable : (prefixWord ++ tailWord_2117784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117784).length < 2 ^ (prefixWord ++ tailWord_2117784).sum := by decide
  have hdescent : baseEnd_2117784 < baseStart_2117784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117790 : List Nat := [4, 3, 1, 1, 3, 11]
def baseStart_2117790 : Nat := 118140960795 + 2117790 * 2 ^ 59
def prefixEnd_2117790 : Nat := 4983230072969 + 3 ^ 40 * 2117790 * 2
def baseEnd_2117790 : Nat := 4475078992943927450969

theorem tailTrace_2117790 : CollatzResearch.WordTrace tailWord_2117790 prefixEnd_2117790 4475078992943927450969 := by
  unfold tailWord_2117790
  simp only [CollatzResearch.WordTrace]
  refine ⟨9655268374701999322689853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51494764665077329721012549 9655268374701999322689853)
  ·
    refine ⟨3620725640513249746008695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9655268374701999322689853 3620725640513249746008695)
    ·
      refine ⟨5431088460769874619013043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3620725640513249746008695 5431088460769874619013043)
      ·
        refine ⟨8146632691154811928519565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5431088460769874619013043 8146632691154811928519565)
        ·
          refine ⟨3054987259183054473194837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8146632691154811928519565 3054987259183054473194837)
          ·
            refine ⟨4475078992943927450969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 3054987259183054473194837 4475078992943927450969)
            ·
              rfl

theorem cell23_2117790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 11].length) (baseStart_2117790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2117790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2117790 prefixEnd_2117790 := by exact prefixLift 2117790
  have htrace : WordTrace (prefixWord ++ tailWord_2117790) baseStart_2117790 baseEnd_2117790 := by
    simpa [prefixWord, tailWord_2117790, baseEnd_2117790] using wordTrace_append hprefix tailTrace_2117790
  have hstable : (prefixWord ++ tailWord_2117790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117790).length < 2 ^ (prefixWord ++ tailWord_2117790).sum := by decide
  have hdescent : baseEnd_2117790 < baseStart_2117790 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117794 : List Nat := [3, 3, 1, 3, 1, 2, 2, 2, 2, 4]
def baseStart_2117794 : Nat := 118140960795 + 2117794 * 2 ^ 59
def prefixEnd_2117794 : Nat := 4983230072969 + 3 ^ 40 * 2117794 * 2
def baseEnd_2117794 : Nat := 362482083069330784978483

theorem tailTrace_2117794 : CollatzResearch.WordTrace tailWord_2117794 prefixEnd_2117794 362482083069330784978483 := by
  unfold tailWord_2117794
  simp only [CollatzResearch.WordTrace]
  refine ⟨19310573222400375816166109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51494861926401002176442957 19310573222400375816166109)
  ·
    refine ⟨7241464958400140931062291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19310573222400375816166109 7241464958400140931062291)
    ·
      refine ⟨10862197437600211396593437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7241464958400140931062291 10862197437600211396593437)
      ·
        refine ⟨4073324039100079273722539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10862197437600211396593437 4073324039100079273722539)
        ·
          refine ⟨6109986058650118910583809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4073324039100079273722539 6109986058650118910583809)
          ·
            refine ⟨4582489543987589182937857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6109986058650118910583809 4582489543987589182937857)
            ·
              refine ⟨3436867157990691887203393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4582489543987589182937857 3436867157990691887203393)
              ·
                refine ⟨2577650368493018915402545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3436867157990691887203393 2577650368493018915402545)
                ·
                  refine ⟨1933237776369764186551909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2577650368493018915402545 1933237776369764186551909)
                  ·
                    refine ⟨362482083069330784978483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1933237776369764186551909 362482083069330784978483)
                    ·
                      rfl

theorem cell23_2117794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 2, 2, 4].length) (baseStart_2117794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2117794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2117794 prefixEnd_2117794 := by exact prefixLift 2117794
  have htrace : WordTrace (prefixWord ++ tailWord_2117794) baseStart_2117794 baseEnd_2117794 := by
    simpa [prefixWord, tailWord_2117794, baseEnd_2117794] using wordTrace_append hprefix tailTrace_2117794
  have hstable : (prefixWord ++ tailWord_2117794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117794).length < 2 ^ (prefixWord ++ tailWord_2117794).sum := by decide
  have hdescent : baseEnd_2117794 < baseStart_2117794 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117817 : List Nat := [1, 2, 1, 4, 1, 2, 1, 5, 2, 1, 3]
def baseStart_2117817 : Nat := 118140960795 + 2117817 * 2 ^ 59
def prefixEnd_2117817 : Nat := 4983230072969 + 3 ^ 40 * 2117817 * 2
def baseEnd_2117817 : Nat := 1087458059263045764947843

theorem tailTrace_2117817 : CollatzResearch.WordTrace tailWord_2117817 prefixEnd_2117817 1087458059263045764947843 := by
  unfold tailWord_2117817
  simp only [CollatzResearch.WordTrace]
  refine ⟨77243131768518178192751705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51495421179012118795167803 77243131768518178192751705)
  ·
    refine ⟨57932348826388633644563779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77243131768518178192751705 57932348826388633644563779)
    ·
      refine ⟨86898523239582950466845669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57932348826388633644563779 86898523239582950466845669)
      ·
        refine ⟨16293473107421803212533563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 86898523239582950466845669 16293473107421803212533563)
        ·
          refine ⟨24440209661132704818800345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16293473107421803212533563 24440209661132704818800345)
          ·
            refine ⟨18330157245849528614100259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24440209661132704818800345 18330157245849528614100259)
            ·
              refine ⟨27495235868774292921150389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18330157245849528614100259 27495235868774292921150389)
              ·
                refine ⟨2577678362697589961357849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27495235868774292921150389 2577678362697589961357849)
                ·
                  refine ⟨1933258772023192471018387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2577678362697589961357849 1933258772023192471018387)
                  ·
                    refine ⟨2899888158034788706527581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1933258772023192471018387 2899888158034788706527581)
                    ·
                      refine ⟨1087458059263045764947843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2899888158034788706527581 1087458059263045764947843)
                      ·
                        rfl

theorem cell23_2117817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 5, 2, 1, 3].length) (baseStart_2117817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2117817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2117817 prefixEnd_2117817 := by exact prefixLift 2117817
  have htrace : WordTrace (prefixWord ++ tailWord_2117817) baseStart_2117817 baseEnd_2117817 := by
    simpa [prefixWord, tailWord_2117817, baseEnd_2117817] using wordTrace_append hprefix tailTrace_2117817
  have hstable : (prefixWord ++ tailWord_2117817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117817).length < 2 ^ (prefixWord ++ tailWord_2117817).sum := by decide
  have hdescent : baseEnd_2117817 < baseStart_2117817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117823 : List Nat := [1, 1, 2, 2, 2, 2, 1, 1, 4, 3, 4]
def baseStart_2117823 : Nat := 118140960795 + 2117823 * 2 ^ 59
def prefixEnd_2117823 : Nat := 4983230072969 + 3 ^ 40 * 2117823 * 2
def baseEnd_2117823 : Nat := 1087461140146972741472815

theorem tailTrace_2117823 : CollatzResearch.WordTrace tailWord_2117823 prefixEnd_2117823 1087461140146972741472815 := by
  unfold tailWord_2117823
  simp only [CollatzResearch.WordTrace]
  refine ⟨77243350606496441217470123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51495567070997627478313415 77243350606496441217470123)
  ·
    refine ⟨115865025909744661826205185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77243350606496441217470123 115865025909744661826205185)
    ·
      refine ⟨86898769432308496369653889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115865025909744661826205185 86898769432308496369653889)
      ·
        refine ⟨65174077074231372277240417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86898769432308496369653889 65174077074231372277240417)
        ·
          refine ⟨48880557805673529207930313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65174077074231372277240417 48880557805673529207930313)
          ·
            refine ⟨36660418354255146905947735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48880557805673529207930313 36660418354255146905947735)
            ·
              refine ⟨54990627531382720358921603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36660418354255146905947735 54990627531382720358921603)
              ·
                refine ⟨82485941297074080538382405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54990627531382720358921603 82485941297074080538382405)
                ·
                  refine ⟨15466113993201390100946701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 82485941297074080538382405 15466113993201390100946701)
                  ·
                    refine ⟨5799792747450521287855013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15466113993201390100946701 5799792747450521287855013)
                    ·
                      refine ⟨1087461140146972741472815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5799792747450521287855013 1087461140146972741472815)
                      ·
                        rfl

theorem cell23_2117823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 4, 3, 4].length) (baseStart_2117823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2117823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2117823 prefixEnd_2117823 := by exact prefixLift 2117823
  have htrace : WordTrace (prefixWord ++ tailWord_2117823) baseStart_2117823 baseEnd_2117823 := by
    simpa [prefixWord, tailWord_2117823, baseEnd_2117823] using wordTrace_append hprefix tailTrace_2117823
  have hstable : (prefixWord ++ tailWord_2117823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117823).length < 2 ^ (prefixWord ++ tailWord_2117823).sum := by decide
  have hdescent : baseEnd_2117823 < baseStart_2117823 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117874 : List Nat := [3, 2, 1, 3, 2, 1, 3, 1, 1, 4, 2]
def baseStart_2117874 : Nat := 118140960795 + 2117874 * 2 ^ 59
def prefixEnd_2117874 : Nat := 4983230072969 + 3 ^ 40 * 2117874 * 2
def baseEnd_2117874 : Nat := 1087487327660352041935081

theorem tailTrace_2117874 : CollatzResearch.WordTrace tailWord_2117874 prefixEnd_2117874 1087487327660352041935081 := by
  unfold tailWord_2117874
  simp only [CollatzResearch.WordTrace]
  refine ⟨19311302682327919231894169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51496807152874451285051117 19311302682327919231894169)
  ·
    refine ⟨14483477011745939423920627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19311302682327919231894169 14483477011745939423920627)
    ·
      refine ⟨21725215517618909135880941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14483477011745939423920627 21725215517618909135880941)
      ·
        refine ⟨8146955819107090925955353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21725215517618909135880941 8146955819107090925955353)
        ·
          refine ⟨6110216864330318194466515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8146955819107090925955353 6110216864330318194466515)
          ·
            refine ⟨9165325296495477291699773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6110216864330318194466515 9165325296495477291699773)
            ·
              refine ⟨3436996986185803984387415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9165325296495477291699773 3436996986185803984387415)
              ·
                refine ⟨5155495479278705976581123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3436996986185803984387415 5155495479278705976581123)
                ·
                  refine ⟨7733243218918058964871685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5155495479278705976581123 7733243218918058964871685)
                  ·
                    refine ⟨1449983103547136055913441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7733243218918058964871685 1449983103547136055913441)
                    ·
                      refine ⟨1087487327660352041935081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1449983103547136055913441 1087487327660352041935081)
                      ·
                        rfl

theorem cell23_2117874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 1, 1, 4, 2].length) (baseStart_2117874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2117874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2117874 prefixEnd_2117874 := by exact prefixLift 2117874
  have htrace : WordTrace (prefixWord ++ tailWord_2117874) baseStart_2117874 baseEnd_2117874 := by
    simpa [prefixWord, tailWord_2117874, baseEnd_2117874] using wordTrace_append hprefix tailTrace_2117874
  have hstable : (prefixWord ++ tailWord_2117874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117874).length < 2 ^ (prefixWord ++ tailWord_2117874).sum := by decide
  have hdescent : baseEnd_2117874 < baseStart_2117874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117897 : List Nat := [1, 2, 1, 1, 3, 4, 3, 3, 5]
def baseStart_2117897 : Nat := 118140960795 + 2117897 * 2 ^ 59
def prefixEnd_2117897 : Nat := 4983230072969 + 3 ^ 40 * 2117897 * 2
def baseEnd_2117897 : Nat := 120833237523933939105275

theorem tailTrace_2117897 : CollatzResearch.WordTrace tailWord_2117897 prefixEnd_2117897 120833237523933939105275 := by
  unfold tailWord_2117897
  simp only [CollatzResearch.WordTrace]
  refine ⟨77246049608228351855663945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51497366405485567903775963 77246049608228351855663945)
  ·
    refine ⟨57934537206171263891747959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77246049608228351855663945 57934537206171263891747959)
    ·
      refine ⟨86901805809256895837621939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57934537206171263891747959 86901805809256895837621939)
      ·
        refine ⟨130352708713885343756432909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86901805809256895837621939 130352708713885343756432909)
        ·
          refine ⟨48882265767707003908662341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 130352708713885343756432909 48882265767707003908662341)
          ·
            refine ⟨9165424831445063232874189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48882265767707003908662341 9165424831445063232874189)
            ·
              refine ⟨3437034311791898712327821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9165424831445063232874189 3437034311791898712327821)
              ·
                refine ⟨1288887866921962017122933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3437034311791898712327821 1288887866921962017122933)
                ·
                  refine ⟨120833237523933939105275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1288887866921962017122933 120833237523933939105275)
                  ·
                    rfl

theorem cell23_2117897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 3, 5].length) (baseStart_2117897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2117897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2117897 prefixEnd_2117897 := by exact prefixLift 2117897
  have htrace : WordTrace (prefixWord ++ tailWord_2117897) baseStart_2117897 baseEnd_2117897 := by
    simpa [prefixWord, tailWord_2117897, baseEnd_2117897] using wordTrace_append hprefix tailTrace_2117897
  have hstable : (prefixWord ++ tailWord_2117897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117897).length < 2 ^ (prefixWord ++ tailWord_2117897).sum := by decide
  have hdescent : baseEnd_2117897 < baseStart_2117897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117903 : List Nat := [1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 7]
def baseStart_2117903 : Nat := 118140960795 + 2117903 * 2 ^ 59
def prefixEnd_2117903 : Nat := 4983230072969 + 3 ^ 40 * 2117903 * 2
def baseEnd_2117903 : Nat := 1087502218599332428472447

theorem tailTrace_2117903 : CollatzResearch.WordTrace tailWord_2117903 prefixEnd_2117903 1087502218599332428472447 := by
  unfold tailWord_2117903
  simp only [CollatzResearch.WordTrace]
  refine ⟨77246268446206614880382363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51497512297471076586921575 77246268446206614880382363)
  ·
    refine ⟨115869402669309922320573545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77246268446206614880382363 115869402669309922320573545)
    ·
      refine ⟨86902052001982441740430159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115869402669309922320573545 86902052001982441740430159)
      ·
        refine ⟨130353078002973662610645239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86902052001982441740430159 130353078002973662610645239)
        ·
          refine ⟨195529617004460493915967859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130353078002973662610645239 195529617004460493915967859)
          ·
            refine ⟨293294425506690740873951789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 195529617004460493915967859 293294425506690740873951789)
            ·
              refine ⟨109985409565009027827731921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 293294425506690740873951789 109985409565009027827731921)
              ·
                refine ⟨82489057173756770870798941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 109985409565009027827731921 82489057173756770870798941)
                ·
                  refine ⟨30933396440158789076549603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 82489057173756770870798941 30933396440158789076549603)
                  ·
                    refine ⟨46400094660238183614824405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30933396440158789076549603 46400094660238183614824405)
                    ·
                      refine ⟨1087502218599332428472447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 46400094660238183614824405 1087502218599332428472447)
                      ·
                        rfl

theorem cell23_2117903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 7].length) (baseStart_2117903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2117903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2117903 prefixEnd_2117903 := by exact prefixLift 2117903
  have htrace : WordTrace (prefixWord ++ tailWord_2117903) baseStart_2117903 baseEnd_2117903 := by
    simpa [prefixWord, tailWord_2117903, baseEnd_2117903] using wordTrace_append hprefix tailTrace_2117903
  have hstable : (prefixWord ++ tailWord_2117903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117903).length < 2 ^ (prefixWord ++ tailWord_2117903).sum := by decide
  have hdescent : baseEnd_2117903 < baseStart_2117903 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117913 : List Nat := [1, 2, 1, 2, 1, 1, 1, 1, 1, 4, 8]
def baseStart_2117913 : Nat := 118140960795 + 2117913 * 2 ^ 59
def prefixEnd_2117913 : Nat := 4983230072969 + 3 ^ 40 * 2117913 * 2
def baseEnd_2117913 : Nat := 1087507353405877389347401

theorem tailTrace_2117913 : CollatzResearch.WordTrace tailWord_2117913 prefixEnd_2117913 1087507353405877389347401 := by
  unfold tailWord_2117913
  simp only [CollatzResearch.WordTrace]
  refine ⟨77246633176170386588246393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51497755450780257725497595 77246633176170386588246393)
  ·
    refine ⟨57934974882127789941184795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77246633176170386588246393 57934974882127789941184795)
    ·
      refine ⟨86902462323191684911777193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57934974882127789941184795 86902462323191684911777193)
      ·
        refine ⟨65176846742393763683832895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86902462323191684911777193 65176846742393763683832895)
        ·
          refine ⟨97765270113590645525749343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65176846742393763683832895 97765270113590645525749343)
          ·
            refine ⟨146647905170385968288624015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97765270113590645525749343 146647905170385968288624015)
            ·
              refine ⟨219971857755578952432936023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146647905170385968288624015 219971857755578952432936023)
              ·
                refine ⟨329957786633368428649404035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 219971857755578952432936023 329957786633368428649404035)
                ·
                  refine ⟨494936679950052642974106053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 329957786633368428649404035 494936679950052642974106053)
                  ·
                    refine ⟨92800627490634870557644885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 494936679950052642974106053 92800627490634870557644885)
                    ·
                      refine ⟨1087507353405877389347401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 92800627490634870557644885 1087507353405877389347401)
                      ·
                        rfl

theorem cell23_2117913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 4, 8].length) (baseStart_2117913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2117913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2117913 prefixEnd_2117913 := by exact prefixLift 2117913
  have htrace : WordTrace (prefixWord ++ tailWord_2117913) baseStart_2117913 baseEnd_2117913 := by
    simpa [prefixWord, tailWord_2117913, baseEnd_2117913] using wordTrace_append hprefix tailTrace_2117913
  have hstable : (prefixWord ++ tailWord_2117913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117913).length < 2 ^ (prefixWord ++ tailWord_2117913).sum := by decide
  have hdescent : baseEnd_2117913 < baseStart_2117913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117914 : List Nat := [3, 1, 1, 3, 5, 1, 1, 1, 7]
def baseStart_2117914 : Nat := 118140960795 + 2117914 * 2 ^ 59
def prefixEnd_2117914 : Nat := 4983230072969 + 3 ^ 40 * 2117914 * 2
def baseEnd_2117914 : Nat := 120834207431836876159433

theorem tailTrace_2117914 : CollatzResearch.WordTrace tailWord_2117914 prefixEnd_2117914 120834207431836876159433 := by
  unfold tailWord_2117914
  simp only [CollatzResearch.WordTrace]
  refine ⟨19311667412291690939758199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51497779766111175839355197 19311667412291690939758199)
  ·
    refine ⟨28967501118437536409637299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19311667412291690939758199 28967501118437536409637299)
    ·
      refine ⟨43451251677656304614455949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28967501118437536409637299 43451251677656304614455949)
      ·
        refine ⟨16294219379121114230420981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43451251677656304614455949 16294219379121114230420981)
        ·
          refine ⟨1527583066792604459101967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16294219379121114230420981 1527583066792604459101967)
          ·
            refine ⟨2291374600188906688652951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1527583066792604459101967 2291374600188906688652951)
            ·
              refine ⟨3437061900283360032979427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2291374600188906688652951 3437061900283360032979427)
              ·
                refine ⟨5155592850425040049469141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3437061900283360032979427 5155592850425040049469141)
                ·
                  refine ⟨120834207431836876159433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5155592850425040049469141 120834207431836876159433)
                  ·
                    rfl

theorem cell23_2117914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 1, 7].length) (baseStart_2117914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2117914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2117914 prefixEnd_2117914 := by exact prefixLift 2117914
  have htrace : WordTrace (prefixWord ++ tailWord_2117914) baseStart_2117914 baseEnd_2117914 := by
    simpa [prefixWord, tailWord_2117914, baseEnd_2117914] using wordTrace_append hprefix tailTrace_2117914
  have hstable : (prefixWord ++ tailWord_2117914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117914).length < 2 ^ (prefixWord ++ tailWord_2117914).sum := by decide
  have hdescent : baseEnd_2117914 < baseStart_2117914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117920 : List Nat := [2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 7]
def baseStart_2117920 : Nat := 118140960795 + 2117920 * 2 ^ 59
def prefixEnd_2117920 : Nat := 4983230072969 + 3 ^ 40 * 2117920 * 2
def baseEnd_2117920 : Nat := 1087510947770458861959869

theorem tailTrace_2117920 : CollatzResearch.WordTrace tailWord_2117920 prefixEnd_2117920 1087510947770458861959869 := by
  unfold tailWord_2117920
  simp only [CollatzResearch.WordTrace]
  refine ⟨38623444243572513391875607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51497925658096684522500809 38623444243572513391875607)
  ·
    refine ⟨57935166365358770087813411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38623444243572513391875607 57935166365358770087813411)
    ·
      refine ⟨86902749548038155131720117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57935166365358770087813411 86902749548038155131720117)
      ·
        refine ⟨8147132770128577043598761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 86902749548038155131720117 8147132770128577043598761)
        ·
          refine ⟨6110349577596432782699071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8147132770128577043598761 6110349577596432782699071)
          ·
            refine ⟨9165524366394649174048607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6110349577596432782699071 9165524366394649174048607)
            ·
              refine ⟨13748286549591973761072911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9165524366394649174048607 13748286549591973761072911)
              ·
                refine ⟨20622429824387960641609367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13748286549591973761072911 20622429824387960641609367)
                ·
                  refine ⟨30933644736581940962414051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20622429824387960641609367 30933644736581940962414051)
                  ·
                    refine ⟨46400467104872911443621077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30933644736581940962414051 46400467104872911443621077)
                    ·
                      refine ⟨1087510947770458861959869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 46400467104872911443621077 1087510947770458861959869)
                      ·
                        rfl

theorem cell23_2117920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_2117920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2117920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2117920 prefixEnd_2117920 := by exact prefixLift 2117920
  have htrace : WordTrace (prefixWord ++ tailWord_2117920) baseStart_2117920 baseEnd_2117920 := by
    simpa [prefixWord, tailWord_2117920, baseEnd_2117920] using wordTrace_append hprefix tailTrace_2117920
  have hstable : (prefixWord ++ tailWord_2117920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117920).length < 2 ^ (prefixWord ++ tailWord_2117920).sum := by decide
  have hdescent : baseEnd_2117920 < baseStart_2117920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117925 : List Nat := [1, 3, 1, 2, 6, 1, 2, 1, 2, 2, 2]
def baseStart_2117925 : Nat := 118140960795 + 2117925 * 2 ^ 59
def prefixEnd_2117925 : Nat := 4983230072969 + 3 ^ 40 * 2117925 * 2
def baseEnd_2117925 : Nat := 1087513515173731342397347

theorem tailTrace_2117925 : CollatzResearch.WordTrace tailWord_2117925 prefixEnd_2117925 1087513515173731342397347 := by
  unfold tailWord_2117925
  simp only [CollatzResearch.WordTrace]
  refine ⟨77247070852126912637683229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51498047234751275091788819 77247070852126912637683229)
  ·
    refine ⟨28967651569547592239131211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77247070852126912637683229 28967651569547592239131211)
    ·
      refine ⟨43451477354321388358696817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28967651569547592239131211 43451477354321388358696817)
      ·
        refine ⟨32588608015741041269022613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43451477354321388358696817 32588608015741041269022613)
        ·
          refine ⟨1527591000737861309485435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 32588608015741041269022613 1527591000737861309485435)
          ·
            refine ⟨2291386501106791964228153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1527591000737861309485435 2291386501106791964228153)
            ·
              refine ⟨1718539875830093973171115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2291386501106791964228153 1718539875830093973171115)
              ·
                refine ⟨2577809813745140959756673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1718539875830093973171115 2577809813745140959756673)
                ·
                  refine ⟨1933357360308855719817505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2577809813745140959756673 1933357360308855719817505)
                  ·
                    refine ⟨1450018020231641789863129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1933357360308855719817505 1450018020231641789863129)
                    ·
                      refine ⟨1087513515173731342397347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1450018020231641789863129 1087513515173731342397347)
                      ·
                        rfl

theorem cell23_2117925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 2, 1, 2, 2, 2].length) (baseStart_2117925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2117925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2117925 prefixEnd_2117925 := by exact prefixLift 2117925
  have htrace : WordTrace (prefixWord ++ tailWord_2117925) baseStart_2117925 baseEnd_2117925 := by
    simpa [prefixWord, tailWord_2117925, baseEnd_2117925] using wordTrace_append hprefix tailTrace_2117925
  have hstable : (prefixWord ++ tailWord_2117925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117925).length < 2 ^ (prefixWord ++ tailWord_2117925).sum := by decide
  have hdescent : baseEnd_2117925 < baseStart_2117925 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117970 : List Nat := [3, 2, 2, 1, 1, 1, 2, 3, 8]
def baseStart_2117970 : Nat := 118140960795 + 2117970 * 2 ^ 59
def prefixEnd_2117970 : Nat := 4983230072969 + 3 ^ 40 * 2117970 * 2
def baseEnd_2117970 : Nat := 120837402422575962926071

theorem tailTrace_2117970 : CollatzResearch.WordTrace tailWord_2117970 prefixEnd_2117970 120837402422575962926071 := by
  unfold tailWord_2117970
  simp only [CollatzResearch.WordTrace]
  refine ⟨19312178034240971330767841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51499141424642590215380909 19312178034240971330767841)
  ·
    refine ⟨14484133525680728498075881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19312178034240971330767841 14484133525680728498075881)
    ·
      refine ⟨10863100144260546373556911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14484133525680728498075881 10863100144260546373556911)
      ·
        refine ⟨16294650216390819560335367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10863100144260546373556911 16294650216390819560335367)
        ·
          refine ⟨24441975324586229340503051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16294650216390819560335367 24441975324586229340503051)
          ·
            refine ⟨36662962986879344010754577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24441975324586229340503051 36662962986879344010754577)
            ·
              refine ⟨27497222240159508008065933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36662962986879344010754577 27497222240159508008065933)
              ·
                refine ⟨10311458340059815503024725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27497222240159508008065933 10311458340059815503024725)
                ·
                  refine ⟨120837402422575962926071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10311458340059815503024725 120837402422575962926071)
                  ·
                    rfl

theorem cell23_2117970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 3, 8].length) (baseStart_2117970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2117970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2117970 prefixEnd_2117970 := by exact prefixLift 2117970
  have htrace : WordTrace (prefixWord ++ tailWord_2117970) baseStart_2117970 baseEnd_2117970 := by
    simpa [prefixWord, tailWord_2117970, baseEnd_2117970] using wordTrace_append hprefix tailTrace_2117970
  have hstable : (prefixWord ++ tailWord_2117970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117970).length < 2 ^ (prefixWord ++ tailWord_2117970).sum := by decide
  have hdescent : baseEnd_2117970 < baseStart_2117970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2118024 : List Nat := [2, 1, 3, 3, 1, 1, 2, 1, 4, 3, 2]
def baseStart_2118024 : Nat := 118140960795 + 2118024 * 2 ^ 59
def prefixEnd_2118024 : Nat := 4983230072969 + 3 ^ 40 * 2118024 * 2
def baseEnd_2118024 : Nat := 1087564349758526455059391

theorem tailTrace_2118024 : CollatzResearch.WordTrace tailWord_2118024 prefixEnd_2118024 1087564349758526455059391 := by
  unfold tailWord_2118024
  simp only [CollatzResearch.WordTrace]
  refine ⟨38625340839384126272768563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51500454452512168363691417 38625340839384126272768563)
  ·
    refine ⟨57938011259076189409152845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38625340839384126272768563 57938011259076189409152845)
    ·
      refine ⟨21726754222153571028432317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57938011259076189409152845 21726754222153571028432317)
      ·
        refine ⟨8147532833307589135662119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21726754222153571028432317 8147532833307589135662119)
        ·
          refine ⟨12221299249961383703493179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8147532833307589135662119 12221299249961383703493179)
          ·
            refine ⟨18331948874942075555239769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12221299249961383703493179 18331948874942075555239769)
            ·
              refine ⟨13748961656206556666429827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18331948874942075555239769 13748961656206556666429827)
              ·
                refine ⟨20623442484309834999644741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13748961656206556666429827 20623442484309834999644741)
                ·
                  refine ⟨3866895465808094062433389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20623442484309834999644741 3866895465808094062433389)
                  ·
                    refine ⟨1450085799678035273412521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3866895465808094062433389 1450085799678035273412521)
                    ·
                      refine ⟨1087564349758526455059391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1450085799678035273412521 1087564349758526455059391)
                      ·
                        rfl

theorem cell23_2118024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 4, 3, 2].length) (baseStart_2118024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2118024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2118024 prefixEnd_2118024 := by exact prefixLift 2118024
  have htrace : WordTrace (prefixWord ++ tailWord_2118024) baseStart_2118024 baseEnd_2118024 := by
    simpa [prefixWord, tailWord_2118024, baseEnd_2118024] using wordTrace_append hprefix tailTrace_2118024
  have hstable : (prefixWord ++ tailWord_2118024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2118024).length < 2 ^ (prefixWord ++ tailWord_2118024).sum := by decide
  have hdescent : baseEnd_2118024 < baseStart_2118024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2118024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2118057 : List Nat := [1, 2, 1, 1, 1, 1, 3, 5, 3, 2, 3]
def baseStart_2118057 : Nat := 118140960795 + 2118057 * 2 ^ 59
def prefixEnd_2118057 : Nat := 4983230072969 + 3 ^ 40 * 2118057 * 2
def baseEnd_2118057 : Nat := 1087581294620124825946739

theorem tailTrace_2118057 : CollatzResearch.WordTrace tailWord_2118057 prefixEnd_2118057 1087581294620124825946739 := by
  unfold tailWord_2118057
  simp only [CollatzResearch.WordTrace]
  refine ⟨77251885287648699181488425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51501256858432466120992283 77251885287648699181488425)
  ·
    refine ⟨57938913965736524386116319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77251885287648699181488425 57938913965736524386116319)
    ·
      refine ⟨86908370948604786579174479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57938913965736524386116319 86908370948604786579174479)
      ·
        refine ⟨130362556422907179868761719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86908370948604786579174479 130362556422907179868761719)
        ·
          refine ⟨195543834634360769803142579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130362556422907179868761719 195543834634360769803142579)
          ·
            refine ⟨293315751951541154704713869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 195543834634360769803142579 293315751951541154704713869)
            ·
              refine ⟨109993406981827933014267701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 293315751951541154704713869 109993406981827933014267701)
              ·
                refine ⟨10311881904546368720087597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 109993406981827933014267701 10311881904546368720087597)
                ·
                  refine ⟨3866955714204888270032849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10311881904546368720087597 3866955714204888270032849)
                  ·
                    refine ⟨2900216785653666202524637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3866955714204888270032849 2900216785653666202524637)
                    ·
                      refine ⟨1087581294620124825946739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2900216785653666202524637 1087581294620124825946739)
                      ·
                        rfl

theorem cell23_2118057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 5, 3, 2, 3].length) (baseStart_2118057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2118057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2118057 prefixEnd_2118057 := by exact prefixLift 2118057
  have htrace : WordTrace (prefixWord ++ tailWord_2118057) baseStart_2118057 baseEnd_2118057 := by
    simpa [prefixWord, tailWord_2118057, baseEnd_2118057] using wordTrace_append hprefix tailTrace_2118057
  have hstable : (prefixWord ++ tailWord_2118057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2118057).length < 2 ^ (prefixWord ++ tailWord_2118057).sum := by decide
  have hdescent : baseEnd_2118057 < baseStart_2118057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2118057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2118077 : List Nat := [1, 4, 1, 2, 2, 4, 9]
def baseStart_2118077 : Nat := 118140960795 + 2118077 * 2 ^ 59
def prefixEnd_2118077 : Nat := 4983230072969 + 3 ^ 40 * 2118077 * 2
def baseEnd_2118077 : Nat := 13427056348558206761687

theorem tailTrace_2118077 : CollatzResearch.WordTrace tailWord_2118077 prefixEnd_2118077 13427056348558206761687 := by
  unfold tailWord_2118077
  simp only [CollatzResearch.WordTrace]
  refine ⟨77252614747576242597216485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51501743165050828398144323 77252614747576242597216485)
  ·
    refine ⟨14484865265170545486978091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77252614747576242597216485 14484865265170545486978091)
    ·
      refine ⟨21727297897755818230467137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14484865265170545486978091 21727297897755818230467137)
      ·
        refine ⟨16295473423316863672850353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21727297897755818230467137 16295473423316863672850353)
        ·
          refine ⟨12221605067487647754637765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16295473423316863672850353 12221605067487647754637765)
          ·
            refine ⟨2291550950153933953994581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12221605067487647754637765 2291550950153933953994581)
            ·
              refine ⟨13427056348558206761687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2291550950153933953994581 13427056348558206761687)
              ·
                rfl

theorem cell23_2118077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 9].length) (baseStart_2118077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2118077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2118077 prefixEnd_2118077 := by exact prefixLift 2118077
  have htrace : WordTrace (prefixWord ++ tailWord_2118077) baseStart_2118077 baseEnd_2118077 := by
    simpa [prefixWord, tailWord_2118077, baseEnd_2118077] using wordTrace_append hprefix tailTrace_2118077
  have hstable : (prefixWord ++ tailWord_2118077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2118077).length < 2 ^ (prefixWord ++ tailWord_2118077).sum := by decide
  have hdescent : baseEnd_2118077 < baseStart_2118077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2118077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2118088 : List Nat := [2, 1, 3, 1, 3, 4, 1, 1, 3, 2, 2]
def baseStart_2118088 : Nat := 118140960795 + 2118088 * 2 ^ 59
def prefixEnd_2118088 : Nat := 4983230072969 + 3 ^ 40 * 2118088 * 2
def baseEnd_2118088 : Nat := 1087597212520414204659097

theorem tailTrace_2118088 : CollatzResearch.WordTrace tailWord_2118088 prefixEnd_2118088 1087597212520414204659097 := by
  unfold tailWord_2118088
  simp only [CollatzResearch.WordTrace]
  refine ⟨38626507975268195737933459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51502010633690927650577945 38626507975268195737933459)
  ·
    refine ⟨57939761962902293606900189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38626507975268195737933459 57939761962902293606900189)
    ·
      refine ⟨21727410736088360102587571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57939761962902293606900189 21727410736088360102587571)
      ·
        refine ⟨32591116104132540153881357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21727410736088360102587571 32591116104132540153881357)
        ·
          refine ⟨12221668539049702557705509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32591116104132540153881357 12221668539049702557705509)
          ·
            refine ⟨2291562851071819229569783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12221668539049702557705509 2291562851071819229569783)
            ·
              refine ⟨3437344276607728844354675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2291562851071819229569783 3437344276607728844354675)
              ·
                refine ⟨5156016414911593266532013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3437344276607728844354675 5156016414911593266532013)
                ·
                  refine ⟨1933506155591847474949505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5156016414911593266532013 1933506155591847474949505)
                  ·
                    refine ⟨1450129616693885606212129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1933506155591847474949505 1450129616693885606212129)
                    ·
                      refine ⟨1087597212520414204659097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1450129616693885606212129 1087597212520414204659097)
                      ·
                        rfl

theorem cell23_2118088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 1, 3, 2, 2].length) (baseStart_2118088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2118088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2118088 prefixEnd_2118088 := by exact prefixLift 2118088
  have htrace : WordTrace (prefixWord ++ tailWord_2118088) baseStart_2118088 baseEnd_2118088 := by
    simpa [prefixWord, tailWord_2118088, baseEnd_2118088] using wordTrace_append hprefix tailTrace_2118088
  have hstable : (prefixWord ++ tailWord_2118088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2118088).length < 2 ^ (prefixWord ++ tailWord_2118088).sum := by decide
  have hdescent : baseEnd_2118088 < baseStart_2118088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2118088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2118098 : List Nat := [3, 2, 2, 4, 1, 1, 1, 3, 2, 4]
def baseStart_2118098 : Nat := 118140960795 + 2118098 * 2 ^ 59
def prefixEnd_2118098 : Nat := 4983230072969 + 3 ^ 40 * 2118098 * 2
def baseEnd_2118098 : Nat := 362534115775653055178017

theorem tailTrace_2118098 : CollatzResearch.WordTrace tailWord_2118098 prefixEnd_2118098 362534115775653055178017 := by
  unfold tailWord_2118098
  simp only [CollatzResearch.WordTrace]
  refine ⟨19313345170125040795932737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51502253787000108789153965 19313345170125040795932737)
  ·
    refine ⟨14485008877593780596949553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19313345170125040795932737 14485008877593780596949553)
    ·
      refine ⟨10863756658195335447712165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14485008877593780596949553 10863756658195335447712165)
      ·
        refine ⟨2036954373411625396446031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10863756658195335447712165 2036954373411625396446031)
        ·
          refine ⟨3055431560117438094669047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2036954373411625396446031 3055431560117438094669047)
          ·
            refine ⟨4583147340176157142003571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3055431560117438094669047 4583147340176157142003571)
            ·
              refine ⟨6874721010264235713005357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4583147340176157142003571 6874721010264235713005357)
              ·
                refine ⟨2578020378849088392377009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6874721010264235713005357 2578020378849088392377009)
                ·
                  refine ⟨1933515284136816294282757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2578020378849088392377009 1933515284136816294282757)
                  ·
                    refine ⟨362534115775653055178017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1933515284136816294282757 362534115775653055178017)
                    ·
                      rfl

theorem cell23_2118098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 3, 2, 4].length) (baseStart_2118098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2118098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2118098 prefixEnd_2118098 := by exact prefixLift 2118098
  have htrace : WordTrace (prefixWord ++ tailWord_2118098) baseStart_2118098 baseEnd_2118098 := by
    simpa [prefixWord, tailWord_2118098, baseEnd_2118098] using wordTrace_append hprefix tailTrace_2118098
  have hstable : (prefixWord ++ tailWord_2118098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2118098).length < 2 ^ (prefixWord ++ tailWord_2118098).sum := by decide
  have hdescent : baseEnd_2118098 < baseStart_2118098 := by decide
  rcases family_descends (prefixWord ++ tailWord_2118098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2118147 : List Nat := [1, 1, 1, 3, 2, 1, 3, 1, 1, 6, 3]
def baseStart_2118147 : Nat := 118140960795 + 2118147 * 2 ^ 59
def prefixEnd_2118147 : Nat := 4983230072969 + 3 ^ 40 * 2118147 * 2
def baseEnd_2118147 : Nat := 1087627507879029473821325

theorem tailTrace_2118147 : CollatzResearch.WordTrace tailWord_2118147 prefixEnd_2118147 1087627507879029473821325 := by
  unfold tailWord_2118147
  simp only [CollatzResearch.WordTrace]
  refine ⟨77255167857322644552264695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51503445238215096368176463 77255167857322644552264695)
  ·
    refine ⟨115882751785983966828397043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77255167857322644552264695 115882751785983966828397043)
    ·
      refine ⟨173824127678975950242595565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115882751785983966828397043 173824127678975950242595565)
      ·
        refine ⟨65184047879615981340973337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 173824127678975950242595565 65184047879615981340973337)
        ·
          refine ⟨48888035909711986005730003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65184047879615981340973337 48888035909711986005730003)
          ·
            refine ⟨73332053864567979008595005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48888035909711986005730003 73332053864567979008595005)
            ·
              refine ⟨27499520199212992128223127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73332053864567979008595005 27499520199212992128223127)
              ·
                refine ⟨41249280298819488192334691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27499520199212992128223127 41249280298819488192334691)
                ·
                  refine ⟨61873920448229232288502037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41249280298819488192334691 61873920448229232288502037)
                  ·
                    refine ⟨2900340021010745263523533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 61873920448229232288502037 2900340021010745263523533)
                    ·
                      refine ⟨1087627507879029473821325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2900340021010745263523533 1087627507879029473821325)
                      ·
                        rfl

theorem cell23_2118147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 6, 3].length) (baseStart_2118147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2118147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2118147 prefixEnd_2118147 := by exact prefixLift 2118147
  have htrace : WordTrace (prefixWord ++ tailWord_2118147) baseStart_2118147 baseEnd_2118147 := by
    simpa [prefixWord, tailWord_2118147, baseEnd_2118147] using wordTrace_append hprefix tailTrace_2118147
  have hstable : (prefixWord ++ tailWord_2118147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2118147).length < 2 ^ (prefixWord ++ tailWord_2118147).sum := by decide
  have hdescent : baseEnd_2118147 < baseStart_2118147 := by decide
  rcases family_descends (prefixWord ++ tailWord_2118147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2118189 : List Nat := [1, 5, 4, 1, 1, 2, 1, 2, 2, 1, 3]
def baseStart_2118189 : Nat := 118140960795 + 2118189 * 2 ^ 59
def prefixEnd_2118189 : Nat := 4983230072969 + 3 ^ 40 * 2118189 * 2
def baseEnd_2118189 : Nat := 1087649074066518309496133

theorem tailTrace_2118189 : CollatzResearch.WordTrace tailWord_2118189 prefixEnd_2118189 1087649074066518309496133 := by
  unfold tailWord_2118189
  simp only [CollatzResearch.WordTrace]
  refine ⟨77256699723170485725293621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51504466482113657150195747 77256699723170485725293621)
  ·
    refine ⟨7242815599047233036746277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 77256699723170485725293621 7242815599047233036746277)
    ·
      refine ⟨1358027924821356194389927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7242815599047233036746277 1358027924821356194389927)
      ·
        refine ⟨2037041887232034291584891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1358027924821356194389927 2037041887232034291584891)
        ·
          refine ⟨3055562830848051437377337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2037041887232034291584891 3055562830848051437377337)
          ·
            refine ⟨2291672123136038578033003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3055562830848051437377337 2291672123136038578033003)
            ·
              refine ⟨3437508184704057867049505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2291672123136038578033003 3437508184704057867049505)
              ·
                refine ⟨2578131138528043400287129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3437508184704057867049505 2578131138528043400287129)
                ·
                  refine ⟨1933598353896032550215347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2578131138528043400287129 1933598353896032550215347)
                  ·
                    refine ⟨2900397530844048825323021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1933598353896032550215347 2900397530844048825323021)
                    ·
                      refine ⟨1087649074066518309496133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2900397530844048825323021 1087649074066518309496133)
                      ·
                        rfl

theorem cell23_2118189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_2118189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2118189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2118189 prefixEnd_2118189 := by exact prefixLift 2118189
  have htrace : WordTrace (prefixWord ++ tailWord_2118189) baseStart_2118189 baseEnd_2118189 := by
    simpa [prefixWord, tailWord_2118189, baseEnd_2118189] using wordTrace_append hprefix tailTrace_2118189
  have hstable : (prefixWord ++ tailWord_2118189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2118189).length < 2 ^ (prefixWord ++ tailWord_2118189).sum := by decide
  have hdescent : baseEnd_2118189 < baseStart_2118189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2118189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2118194 : List Nat := [3, 2, 1, 1, 2, 1, 3, 2, 2, 3, 3]
def baseStart_2118194 : Nat := 118140960795 + 2118194 * 2 ^ 59
def prefixEnd_2118194 : Nat := 4983230072969 + 3 ^ 40 * 2118194 * 2
def baseEnd_2118194 : Nat := 1087651641469790789933609

theorem tailTrace_2118194 : CollatzResearch.WordTrace tailWord_2118194 prefixEnd_2118194 1087651641469790789933609 := by
  unfold tailWord_2118194
  simp only [CollatzResearch.WordTrace]
  refine ⟨19314220522038092894806409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51504588058768247719483757 19314220522038092894806409)
  ·
    refine ⟨14485665391528569671104807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19314220522038092894806409 14485665391528569671104807)
    ·
      refine ⟨21728498087292854506657211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14485665391528569671104807 21728498087292854506657211)
      ·
        refine ⟨32592747130939281759985817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21728498087292854506657211 32592747130939281759985817)
        ·
          refine ⟨24444560348204461319989363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32592747130939281759985817 24444560348204461319989363)
          ·
            refine ⟨36666840522306691979984045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24444560348204461319989363 36666840522306691979984045)
            ·
              refine ⟨13750065195865009492494017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36666840522306691979984045 13750065195865009492494017)
              ·
                refine ⟨10312548896898757119370513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13750065195865009492494017 10312548896898757119370513)
                ·
                  refine ⟨7734411672674067839527885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10312548896898757119370513 7734411672674067839527885)
                  ·
                    refine ⟨2900404377252775439822957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7734411672674067839527885 2900404377252775439822957)
                    ·
                      refine ⟨1087651641469790789933609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2900404377252775439822957 1087651641469790789933609)
                      ·
                        rfl

theorem cell23_2118194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 2, 2, 3, 3].length) (baseStart_2118194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2118194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2118194 prefixEnd_2118194 := by exact prefixLift 2118194
  have htrace : WordTrace (prefixWord ++ tailWord_2118194) baseStart_2118194 baseEnd_2118194 := by
    simpa [prefixWord, tailWord_2118194, baseEnd_2118194] using wordTrace_append hprefix tailTrace_2118194
  have hstable : (prefixWord ++ tailWord_2118194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2118194).length < 2 ^ (prefixWord ++ tailWord_2118194).sum := by decide
  have hdescent : baseEnd_2118194 < baseStart_2118194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2118194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2118207 : List Nat := [1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 7]
def baseStart_2118207 : Nat := 118140960795 + 2118207 * 2 ^ 59
def prefixEnd_2118207 : Nat := 4983230072969 + 3 ^ 40 * 2118207 * 2
def baseEnd_2118207 : Nat := 1087658316718299239071049

theorem tailTrace_2118207 : CollatzResearch.WordTrace tailWord_2118207 prefixEnd_2118207 1087658316718299239071049 := by
  unfold tailWord_2118207
  simp only [CollatzResearch.WordTrace]
  refine ⟨77257356237105274799448875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51504904158070183199632583 77257356237105274799448875)
  ·
    refine ⟨115886034355657912199173313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77257356237105274799448875 115886034355657912199173313)
    ·
      refine ⟨86914525766743434149379985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115886034355657912199173313 86914525766743434149379985)
      ·
        refine ⟨65185894325057575612034989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86914525766743434149379985 65185894325057575612034989)
        ·
          refine ⟨24444710371896590854513121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65185894325057575612034989 24444710371896590854513121)
          ·
            refine ⟨18333532778922443140884841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24444710371896590854513121 18333532778922443140884841)
            ·
              refine ⟨13750149584191832355663631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18333532778922443140884841 13750149584191832355663631)
              ·
                refine ⟨20625224376287748533495447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13750149584191832355663631 20625224376287748533495447)
                ·
                  refine ⟨30937836564431622800243171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20625224376287748533495447 30937836564431622800243171)
                  ·
                    refine ⟨46406754846647434200364757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30937836564431622800243171 46406754846647434200364757)
                    ·
                      refine ⟨1087658316718299239071049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 46406754846647434200364757 1087658316718299239071049)
                      ·
                        rfl

theorem cell23_2118207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 7].length) (baseStart_2118207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2118207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2118207 prefixEnd_2118207 := by exact prefixLift 2118207
  have htrace : WordTrace (prefixWord ++ tailWord_2118207) baseStart_2118207 baseEnd_2118207 := by
    simpa [prefixWord, tailWord_2118207, baseEnd_2118207] using wordTrace_append hprefix tailTrace_2118207
  have hstable : (prefixWord ++ tailWord_2118207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2118207).length < 2 ^ (prefixWord ++ tailWord_2118207).sum := by decide
  have hdescent : baseEnd_2118207 < baseStart_2118207 := by decide
  rcases family_descends (prefixWord ++ tailWord_2118207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2118287 : List Nat := [1, 1, 2, 1, 1, 1, 1, 4, 2, 9]
def baseStart_2118287 : Nat := 118140960795 + 2118287 * 2 ^ 59
def prefixEnd_2118287 : Nat := 4983230072969 + 3 ^ 40 * 2118287 * 2
def baseEnd_2118287 : Nat := 362566465056886308690227

theorem tailTrace_2118287 : CollatzResearch.WordTrace tailWord_2118287 prefixEnd_2118287 362566465056886308690227 := by
  unfold tailWord_2118287
  simp only [CollatzResearch.WordTrace]
  refine ⟨77260274076815448462361115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51506849384543632308240743 77260274076815448462361115)
  ·
    refine ⟨115890411115223172693541673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77260274076815448462361115 115890411115223172693541673)
    ·
      refine ⟨86917808336417379520156255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115890411115223172693541673 86917808336417379520156255)
      ·
        refine ⟨130376712504626069280234383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86917808336417379520156255 130376712504626069280234383)
        ·
          refine ⟨195565068756939103920351575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130376712504626069280234383 195565068756939103920351575)
          ·
            refine ⟨293347603135408655880527363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 195565068756939103920351575 293347603135408655880527363)
            ·
              refine ⟨440021404703112983820791045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 293347603135408655880527363 440021404703112983820791045)
              ·
                refine ⟨82504013381833684466398321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 440021404703112983820791045 82504013381833684466398321)
                ·
                  refine ⟨61878010036375263349798741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 82504013381833684466398321 61878010036375263349798741)
                  ·
                    refine ⟨362566465056886308690227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 61878010036375263349798741 362566465056886308690227)
                    ·
                      rfl

theorem cell23_2118287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 9].length) (baseStart_2118287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2118287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2118287 prefixEnd_2118287 := by exact prefixLift 2118287
  have htrace : WordTrace (prefixWord ++ tailWord_2118287) baseStart_2118287 baseEnd_2118287 := by
    simpa [prefixWord, tailWord_2118287, baseEnd_2118287] using wordTrace_append hprefix tailTrace_2118287
  have hstable : (prefixWord ++ tailWord_2118287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2118287).length < 2 ^ (prefixWord ++ tailWord_2118287).sum := by decide
  have hdescent : baseEnd_2118287 < baseStart_2118287 := by decide
  rcases family_descends (prefixWord ++ tailWord_2118287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2118394 : List Nat := [3, 1, 1, 1, 1, 3, 2, 2, 2, 7]
def baseStart_2118394 : Nat := 118140960795 + 2118394 * 2 ^ 59
def prefixEnd_2118394 : Nat := 4983230072969 + 3 ^ 40 * 2118394 * 2
def baseEnd_2118394 : Nat := 362584779200230002477563

theorem tailTrace_2118394 : CollatzResearch.WordTrace tailWord_2118394 prefixEnd_2118394 362584779200230002477563 := by
  unfold tailWord_2118394
  simp only [CollatzResearch.WordTrace]
  refine ⟨19316044171856951434126559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51509451124951870491004157 19316044171856951434126559)
  ·
    refine ⟨28974066257785427151189839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19316044171856951434126559 28974066257785427151189839)
    ·
      refine ⟨43461099386678140726784759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28974066257785427151189839 43461099386678140726784759)
      ·
        refine ⟨65191649080017211090177139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43461099386678140726784759 65191649080017211090177139)
        ·
          refine ⟨97787473620025816635265709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65191649080017211090177139 97787473620025816635265709)
          ·
            refine ⟨36670302607509681238224641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97787473620025816635265709 36670302607509681238224641)
            ·
              refine ⟨27502726955632260928668481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36670302607509681238224641 27502726955632260928668481)
              ·
                refine ⟨20627045216724195696501361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27502726955632260928668481 20627045216724195696501361)
                ·
                  refine ⟨15470283912543146772376021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20627045216724195696501361 15470283912543146772376021)
                  ·
                    refine ⟨362584779200230002477563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15470283912543146772376021 362584779200230002477563)
                    ·
                      rfl

theorem cell23_2118394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 2, 7].length) (baseStart_2118394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2118394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2118394 prefixEnd_2118394 := by exact prefixLift 2118394
  have htrace : WordTrace (prefixWord ++ tailWord_2118394) baseStart_2118394 baseEnd_2118394 := by
    simpa [prefixWord, tailWord_2118394, baseEnd_2118394] using wordTrace_append hprefix tailTrace_2118394
  have hstable : (prefixWord ++ tailWord_2118394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2118394).length < 2 ^ (prefixWord ++ tailWord_2118394).sum := by decide
  have hdescent : baseEnd_2118394 < baseStart_2118394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2118394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2118398 : List Nat := [4, 2, 2, 1, 2, 1, 4, 7]
def baseStart_2118398 : Nat := 118140960795 + 2118398 * 2 ^ 59
def prefixEnd_2118398 : Nat := 4983230072969 + 3 ^ 40 * 2118398 * 2
def baseEnd_2118398 : Nat := 40287273760122518214173

theorem tailTrace_2118398 : CollatzResearch.WordTrace tailWord_2118398 prefixEnd_2118398 40287273760122518214173 := by
  unfold tailWord_2118398
  simp only [CollatzResearch.WordTrace]
  refine ⟨9658040322426664302456481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51509548386275542946434565 9658040322426664302456481)
  ·
    refine ⟨7243530241819998226842361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9658040322426664302456481 7243530241819998226842361)
    ·
      refine ⟨5432647681364998670131771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7243530241819998226842361 5432647681364998670131771)
      ·
        refine ⟨8148971522047498005197657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5432647681364998670131771 8148971522047498005197657)
        ·
          refine ⟨6111728641535623503898243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8148971522047498005197657 6111728641535623503898243)
          ·
            refine ⟨9167592962303435255847365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6111728641535623503898243 9167592962303435255847365)
            ·
              refine ⟨1718923680431894110471381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9167592962303435255847365 1718923680431894110471381)
              ·
                refine ⟨40287273760122518214173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1718923680431894110471381 40287273760122518214173)
                ·
                  rfl

theorem cell23_2118398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 4, 7].length) (baseStart_2118398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2118398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2118398 prefixEnd_2118398 := by exact prefixLift 2118398
  have htrace : WordTrace (prefixWord ++ tailWord_2118398) baseStart_2118398 baseEnd_2118398 := by
    simpa [prefixWord, tailWord_2118398, baseEnd_2118398] using wordTrace_append hprefix tailTrace_2118398
  have hstable : (prefixWord ++ tailWord_2118398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2118398).length < 2 ^ (prefixWord ++ tailWord_2118398).sum := by decide
  have hdescent : baseEnd_2118398 < baseStart_2118398 := by decide
  rcases family_descends (prefixWord ++ tailWord_2118398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2118408 : List Nat := [2, 1, 3, 2, 2, 2, 1, 2, 4, 1, 3]
def baseStart_2118408 : Nat := 118140960795 + 2118408 * 2 ^ 59
def prefixEnd_2118408 : Nat := 4983230072969 + 3 ^ 40 * 2118408 * 2
def baseEnd_2118408 : Nat := 1087761526329852952657625

theorem tailTrace_2118408 : CollatzResearch.WordTrace tailWord_2118408 prefixEnd_2118408 1087761526329852952657625 := by
  unfold tailWord_2118408
  simp only [CollatzResearch.WordTrace]
  refine ⟨38632343654688543063757939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51509791539584724085010585 38632343654688543063757939)
  ·
    refine ⟨57948515482032814595636909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38632343654688543063757939 57948515482032814595636909)
    ·
      refine ⟨21730693305762305473363841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57948515482032814595636909 21730693305762305473363841)
      ·
        refine ⟨16298019979321729105022881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21730693305762305473363841 16298019979321729105022881)
        ·
          refine ⟨12223514984491296828767161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16298019979321729105022881 12223514984491296828767161)
          ·
            refine ⟨9167636238368472621575371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12223514984491296828767161 9167636238368472621575371)
            ·
              refine ⟨13751454357552708932363057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9167636238368472621575371 13751454357552708932363057)
              ·
                refine ⟨10313590768164531699272293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13751454357552708932363057 10313590768164531699272293)
                ·
                  refine ⟨1933798269030849693613555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10313590768164531699272293 1933798269030849693613555)
                  ·
                    refine ⟨2900697403546274540420333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1933798269030849693613555 2900697403546274540420333)
                    ·
                      refine ⟨1087761526329852952657625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2900697403546274540420333 1087761526329852952657625)
                      ·
                        rfl

theorem cell23_2118408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 2, 4, 1, 3].length) (baseStart_2118408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2118408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2118408 prefixEnd_2118408 := by exact prefixLift 2118408
  have htrace : WordTrace (prefixWord ++ tailWord_2118408) baseStart_2118408 baseEnd_2118408 := by
    simpa [prefixWord, tailWord_2118408, baseEnd_2118408] using wordTrace_append hprefix tailTrace_2118408
  have hstable : (prefixWord ++ tailWord_2118408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2118408).length < 2 ^ (prefixWord ++ tailWord_2118408).sum := by decide
  have hdescent : baseEnd_2118408 < baseStart_2118408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2118408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2118451 : List Nat := [1, 1, 1, 2, 6, 1, 1, 2, 2, 1, 5]
def baseStart_2118451 : Nat := 118140960795 + 2118451 * 2 ^ 59
def prefixEnd_2118451 : Nat := 4983230072969 + 3 ^ 40 * 2118451 * 2
def baseEnd_2118451 : Nat := 1087783605997996284419927

theorem tailTrace_2118451 : CollatzResearch.WordTrace tailWord_2118451 prefixEnd_2118451 1087783605997996284419927 := by
  unfold tailWord_2118451
  simp only [CollatzResearch.WordTrace]
  refine ⟨77266255648221304471331207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51510837098814202980887471 77266255648221304471331207)
  ·
    refine ⟨115899383472331956706996811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77266255648221304471331207 115899383472331956706996811)
    ·
      refine ⟨173849075208497935060495217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115899383472331956706996811 173849075208497935060495217)
      ·
        refine ⟨130386806406373451295371413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173849075208497935060495217 130386806406373451295371413)
        ·
          refine ⟨6111881550298755529470535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 130386806406373451295371413 6111881550298755529470535)
          ·
            refine ⟨9167822325448133294205803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6111881550298755529470535 9167822325448133294205803)
            ·
              refine ⟨13751733488172199941308705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9167822325448133294205803 13751733488172199941308705)
              ·
                refine ⟨10313800116129149955981529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13751733488172199941308705 10313800116129149955981529)
                ·
                  refine ⟨7735350087096862466986147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10313800116129149955981529 7735350087096862466986147)
                  ·
                    refine ⟨11603025130645293700479221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7735350087096862466986147 11603025130645293700479221)
                    ·
                      refine ⟨1087783605997996284419927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11603025130645293700479221 1087783605997996284419927)
                      ·
                        rfl

theorem cell23_2118451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 2, 2, 1, 5].length) (baseStart_2118451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2118451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2118451 prefixEnd_2118451 := by exact prefixLift 2118451
  have htrace : WordTrace (prefixWord ++ tailWord_2118451) baseStart_2118451 baseEnd_2118451 := by
    simpa [prefixWord, tailWord_2118451, baseEnd_2118451] using wordTrace_append hprefix tailTrace_2118451
  have hstable : (prefixWord ++ tailWord_2118451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2118451).length < 2 ^ (prefixWord ++ tailWord_2118451).sum := by decide
  have hdescent : baseEnd_2118451 < baseStart_2118451 := by decide
  rcases family_descends (prefixWord ++ tailWord_2118451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2118452 : List Nat := [2, 5, 1, 1, 3, 1, 1, 1, 3, 3, 2]
def baseStart_2118452 : Nat := 118140960795 + 2118452 * 2 ^ 59
def prefixEnd_2118452 : Nat := 4983230072969 + 3 ^ 40 * 2118452 * 2
def baseEnd_2118452 : Nat := 1087784119478650780507423

theorem tailTrace_2118452 : CollatzResearch.WordTrace tailWord_2118452 prefixEnd_2118452 1087784119478650780507423 := by
  unfold tailWord_2118452
  simp only [CollatzResearch.WordTrace]
  refine ⟨38633146060608840821058805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51510861414145121094745073 38633146060608840821058805)
  ·
    refine ⟨3621857443182078826974263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38633146060608840821058805 3621857443182078826974263)
    ·
      refine ⟨5432786164773118240461395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3621857443182078826974263 5432786164773118240461395)
      ·
        refine ⟨8149179247159677360692093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5432786164773118240461395 8149179247159677360692093)
        ·
          refine ⟨3055942217684879010259535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8149179247159677360692093 3055942217684879010259535)
          ·
            refine ⟨4583913326527318515389303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3055942217684879010259535 4583913326527318515389303)
            ·
              refine ⟨6875869989790977773083955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4583913326527318515389303 6875869989790977773083955)
              ·
                refine ⟨10313804984686466659625933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6875869989790977773083955 10313804984686466659625933)
                ·
                  refine ⟨3867676869257424997359725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10313804984686466659625933 3867676869257424997359725)
                  ·
                    refine ⟨1450378825971534374009897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3867676869257424997359725 1450378825971534374009897)
                    ·
                      refine ⟨1087784119478650780507423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1450378825971534374009897 1087784119478650780507423)
                      ·
                        rfl

theorem cell23_2118452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 1, 3, 3, 2].length) (baseStart_2118452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2118452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2118452 prefixEnd_2118452 := by exact prefixLift 2118452
  have htrace : WordTrace (prefixWord ++ tailWord_2118452) baseStart_2118452 baseEnd_2118452 := by
    simpa [prefixWord, tailWord_2118452, baseEnd_2118452] using wordTrace_append hprefix tailTrace_2118452
  have hstable : (prefixWord ++ tailWord_2118452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2118452).length < 2 ^ (prefixWord ++ tailWord_2118452).sum := by decide
  have hdescent : baseEnd_2118452 < baseStart_2118452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2118452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2118482 : List Nat := [3, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2]
def baseStart_2118482 : Nat := 118140960795 + 2118482 * 2 ^ 59
def prefixEnd_2118482 : Nat := 4983230072969 + 3 ^ 40 * 2118482 * 2
def baseEnd_2118482 : Nat := 1087799523898285663132285

theorem tailTrace_2118482 : CollatzResearch.WordTrace tailWord_2118482 prefixEnd_2118482 1087799523898285663132285 := by
  unfold tailWord_2118482
  simp only [CollatzResearch.WordTrace]
  refine ⟨19316846577777249191427425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51511590874072664510473133 19316846577777249191427425)
  ·
    refine ⟨14487634933332936893570569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19316846577777249191427425 14487634933332936893570569)
    ·
      refine ⟨10865726199999702670177927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14487634933332936893570569 10865726199999702670177927)
      ·
        refine ⟨16298589299999554005266891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10865726199999702670177927 16298589299999554005266891)
        ·
          refine ⟨24447883949999331007900337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16298589299999554005266891 24447883949999331007900337)
          ·
            refine ⟨18335912962499498255925253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24447883949999331007900337 18335912962499498255925253)
            ·
              refine ⟨3437983680468655922985985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18335912962499498255925253 3437983680468655922985985)
              ·
                refine ⟨2578487760351491942239489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3437983680468655922985985 2578487760351491942239489)
                ·
                  refine ⟨1933865820263618956679617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2578487760351491942239489 1933865820263618956679617)
                  ·
                    refine ⟨1450399365197714217509713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1933865820263618956679617 1450399365197714217509713)
                    ·
                      refine ⟨1087799523898285663132285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1450399365197714217509713 1087799523898285663132285)
                      ·
                        rfl

theorem cell23_2118482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2].length) (baseStart_2118482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2118482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2118482 prefixEnd_2118482 := by exact prefixLift 2118482
  have htrace : WordTrace (prefixWord ++ tailWord_2118482) baseStart_2118482 baseEnd_2118482 := by
    simpa [prefixWord, tailWord_2118482, baseEnd_2118482] using wordTrace_append hprefix tailTrace_2118482
  have hstable : (prefixWord ++ tailWord_2118482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2118482).length < 2 ^ (prefixWord ++ tailWord_2118482).sum := by decide
  have hdescent : baseEnd_2118482 < baseStart_2118482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2118482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2118501 : List Nat := [1, 3, 1, 3, 1, 1, 2, 2, 4, 5]
def baseStart_2118501 : Nat := 118140960795 + 2118501 * 2 ^ 59
def prefixEnd_2118501 : Nat := 4983230072969 + 3 ^ 40 * 2118501 * 2
def baseEnd_2118501 : Nat := 362603093343573696264899

theorem tailTrace_2118501 : CollatzResearch.WordTrace tailWord_2118501 prefixEnd_2118501 362603093343573696264899 := by
  unfold tailWord_2118501
  simp only [CollatzResearch.WordTrace]
  refine ⟨77268079298040163010651357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51512052865360108673767571 77268079298040163010651357)
  ·
    refine ⟨28975529736765061128994259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77268079298040163010651357 28975529736765061128994259)
    ·
      refine ⟨43463294605147591693491389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28975529736765061128994259 43463294605147591693491389)
      ·
        refine ⟨16298735476930346885059271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43463294605147591693491389 16298735476930346885059271)
        ·
          refine ⟨24448103215395520327588907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16298735476930346885059271 24448103215395520327588907)
          ·
            refine ⟨36672154823093280491383361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24448103215395520327588907 36672154823093280491383361)
            ·
              refine ⟨27504116117319960368537521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36672154823093280491383361 27504116117319960368537521)
              ·
                refine ⟨20628087087989970276403141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27504116117319960368537521 20628087087989970276403141)
                ·
                  refine ⟨3867766328998119426825589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20628087087989970276403141 3867766328998119426825589)
                  ·
                    refine ⟨362603093343573696264899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3867766328998119426825589 362603093343573696264899)
                    ·
                      rfl

theorem cell23_2118501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 4, 5].length) (baseStart_2118501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2118501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2118501 prefixEnd_2118501 := by exact prefixLift 2118501
  have htrace : WordTrace (prefixWord ++ tailWord_2118501) baseStart_2118501 baseEnd_2118501 := by
    simpa [prefixWord, tailWord_2118501, baseEnd_2118501] using wordTrace_append hprefix tailTrace_2118501
  have hstable : (prefixWord ++ tailWord_2118501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2118501).length < 2 ^ (prefixWord ++ tailWord_2118501).sum := by decide
  have hdescent : baseEnd_2118501 < baseStart_2118501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2118501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2118508 : List Nat := [2, 2, 1, 1, 4, 1, 1, 2, 2, 5, 2]
def baseStart_2118508 : Nat := 118140960795 + 2118508 * 2 ^ 59
def prefixEnd_2118508 : Nat := 4983230072969 + 3 ^ 40 * 2118508 * 2
def baseEnd_2118508 : Nat := 1087812874395302561407165

theorem tailTrace_2118508 : CollatzResearch.WordTrace tailWord_2118508 prefixEnd_2118508 1087812874395302561407165 := by
  unfold tailWord_2118508
  simp only [CollatzResearch.WordTrace]
  refine ⟨38634167304507401603078089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51512223072676535470770785 38634167304507401603078089)
  ·
    refine ⟨28975625478380551202308567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38634167304507401603078089 28975625478380551202308567)
    ·
      refine ⟨43463438217570826803462851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28975625478380551202308567 43463438217570826803462851)
      ·
        refine ⟨65195157326356240205194277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43463438217570826803462851 65195157326356240205194277)
        ·
          refine ⟨12224091998691795038473927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65195157326356240205194277 12224091998691795038473927)
          ·
            refine ⟨18336137998037692557710891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12224091998691795038473927 18336137998037692557710891)
            ·
              refine ⟨27504206997056538836566337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18336137998037692557710891 27504206997056538836566337)
              ·
                refine ⟨20628155247792404127424753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27504206997056538836566337 20628155247792404127424753)
                ·
                  refine ⟨15471116435844303095568565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20628155247792404127424753 15471116435844303095568565)
                  ·
                    refine ⟨1450417165860403415209553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15471116435844303095568565 1450417165860403415209553)
                    ·
                      refine ⟨1087812874395302561407165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1450417165860403415209553 1087812874395302561407165)
                      ·
                        rfl

theorem cell23_2118508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 5, 2].length) (baseStart_2118508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2118508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2118508 prefixEnd_2118508 := by exact prefixLift 2118508
  have htrace : WordTrace (prefixWord ++ tailWord_2118508) baseStart_2118508 baseEnd_2118508 := by
    simpa [prefixWord, tailWord_2118508, baseEnd_2118508] using wordTrace_append hprefix tailTrace_2118508
  have hstable : (prefixWord ++ tailWord_2118508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2118508).length < 2 ^ (prefixWord ++ tailWord_2118508).sum := by decide
  have hdescent : baseEnd_2118508 < baseStart_2118508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2118508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2118551 : List Nat := [1, 1, 3, 3, 1, 2, 1, 2, 2, 1, 6]
def baseStart_2118551 : Nat := 118140960795 + 2118551 * 2 ^ 59
def prefixEnd_2118551 : Nat := 4983230072969 + 3 ^ 40 * 2118551 * 2
def baseEnd_2118551 : Nat := 1087834954063445893169467

theorem tailTrace_2118551 : CollatzResearch.WordTrace tailWord_2118551 prefixEnd_2118551 1087834954063445893169467 := by
  unfold tailWord_2118551
  simp only [CollatzResearch.WordTrace]
  refine ⟨77269902947859021549971507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51513268631906014366647671 77269902947859021549971507)
  ·
    refine ⟨115904854421788532324957261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77269902947859021549971507 115904854421788532324957261)
    ·
      refine ⟨43464320408170699621858973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115904854421788532324957261 43464320408170699621858973)
      ·
        refine ⟨16299120153064012358197115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43464320408170699621858973 16299120153064012358197115)
        ·
          refine ⟨24448680229596018537295673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16299120153064012358197115 24448680229596018537295673)
          ·
            refine ⟨18336510172197013902971755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24448680229596018537295673 18336510172197013902971755)
            ·
              refine ⟨27504765258295520854457633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18336510172197013902971755 27504765258295520854457633)
              ·
                refine ⟨20628573943721640640843225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27504765258295520854457633 20628573943721640640843225)
                ·
                  refine ⟨15471430457791230480632419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20628573943721640640843225 15471430457791230480632419)
                  ·
                    refine ⟨23207145686686845720948629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15471430457791230480632419 23207145686686845720948629)
                    ·
                      refine ⟨1087834954063445893169467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23207145686686845720948629 1087834954063445893169467)
                      ·
                        rfl

theorem cell23_2118551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_2118551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2118551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2118551 prefixEnd_2118551 := by exact prefixLift 2118551
  have htrace : WordTrace (prefixWord ++ tailWord_2118551) baseStart_2118551 baseEnd_2118551 := by
    simpa [prefixWord, tailWord_2118551, baseEnd_2118551] using wordTrace_append hprefix tailTrace_2118551
  have hstable : (prefixWord ++ tailWord_2118551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2118551).length < 2 ^ (prefixWord ++ tailWord_2118551).sum := by decide
  have hdescent : baseEnd_2118551 < baseStart_2118551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2118551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2118612 : List Nat := [2, 4, 1, 2, 1, 4, 2, 1, 6]
def baseStart_2118612 : Nat := 118140960795 + 2118612 * 2 ^ 59
def prefixEnd_2118612 : Nat := 4983230072969 + 3 ^ 40 * 2118612 * 2
def baseEnd_2118612 : Nat := 120874030709263350500743

theorem tailTrace_2118612 : CollatzResearch.WordTrace tailWord_2118612 prefixEnd_2118612 120874030709263350500743 := by
  unfold tailWord_2118612
  simp only [CollatzResearch.WordTrace]
  refine ⟨38636063900319014483971045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51514751867092019311961393 38636063900319014483971045)
  ·
    refine ⟨7244261981309815215744571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38636063900319014483971045 7244261981309815215744571)
    ·
      refine ⟨10866392971964722823616857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7244261981309815215744571 10866392971964722823616857)
      ·
        refine ⟨8149794728973542117712643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10866392971964722823616857 8149794728973542117712643)
        ·
          refine ⟨12224692093460313176568965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8149794728973542117712643 12224692093460313176568965)
          ·
            refine ⟨2292129767523808720606681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12224692093460313176568965 2292129767523808720606681)
            ·
              refine ⟨1719097325642856540455011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2292129767523808720606681 1719097325642856540455011)
              ·
                refine ⟨2578645988464284810682517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1719097325642856540455011 2578645988464284810682517)
                ·
                  refine ⟨120874030709263350500743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2578645988464284810682517 120874030709263350500743)
                  ·
                    rfl

theorem cell23_2118612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 2, 1, 6].length) (baseStart_2118612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2118612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2118612 prefixEnd_2118612 := by exact prefixLift 2118612
  have htrace : WordTrace (prefixWord ++ tailWord_2118612) baseStart_2118612 baseEnd_2118612 := by
    simpa [prefixWord, tailWord_2118612, baseEnd_2118612] using wordTrace_append hprefix tailTrace_2118612
  have hstable : (prefixWord ++ tailWord_2118612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2118612).length < 2 ^ (prefixWord ++ tailWord_2118612).sum := by decide
  have hdescent : baseEnd_2118612 < baseStart_2118612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2118612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2118668 : List Nat := [2, 2, 1, 2, 3, 2, 3, 8]
def baseStart_2118668 : Nat := 118140960795 + 2118668 * 2 ^ 59
def prefixEnd_2118668 : Nat := 4983230072969 + 3 ^ 40 * 2118668 * 2
def baseEnd_2118668 : Nat := 40292408566667479089127

theorem tailTrace_2118668 : CollatzResearch.WordTrace tailWord_2118668 prefixEnd_2118668 40292408566667479089127 := by
  unfold tailWord_2118668
  simp only [CollatzResearch.WordTrace]
  refine ⟨38637085144217575265990329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51516113525623433687987105 38637085144217575265990329)
  ·
    refine ⟨28977813858163181449492747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38637085144217575265990329 28977813858163181449492747)
    ·
      refine ⟨43466720787244772174239121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28977813858163181449492747 43466720787244772174239121)
      ·
        refine ⟨32600040590433579130679341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43466720787244772174239121 32600040590433579130679341)
        ·
          refine ⟨12225015221412592174004753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32600040590433579130679341 12225015221412592174004753)
          ·
            refine ⟨9168761416059444130503565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12225015221412592174004753 9168761416059444130503565)
            ·
              refine ⟨3438285531022291548938837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9168761416059444130503565 3438285531022291548938837)
              ·
                refine ⟨40292408566667479089127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3438285531022291548938837 40292408566667479089127)
                ·
                  rfl

theorem cell23_2118668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 8].length) (baseStart_2118668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2118668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2118668 prefixEnd_2118668 := by exact prefixLift 2118668
  have htrace : WordTrace (prefixWord ++ tailWord_2118668) baseStart_2118668 baseEnd_2118668 := by
    simpa [prefixWord, tailWord_2118668, baseEnd_2118668] using wordTrace_append hprefix tailTrace_2118668
  have hstable : (prefixWord ++ tailWord_2118668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2118668).length < 2 ^ (prefixWord ++ tailWord_2118668).sum := by decide
  have hdescent : baseEnd_2118668 < baseStart_2118668 := by decide
  rcases family_descends (prefixWord ++ tailWord_2118668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2118679 : List Nat := [1, 1, 3, 5, 1, 2, 1, 2, 3, 2, 2]
def baseStart_2118679 : Nat := 118140960795 + 2118679 * 2 ^ 59
def prefixEnd_2118679 : Nat := 4983230072969 + 3 ^ 40 * 2118679 * 2
def baseEnd_2118679 : Nat := 1087900679587221392368879

theorem tailTrace_2118679 : CollatzResearch.WordTrace tailWord_2118679 prefixEnd_2118679 1087900679587221392368879 := by
  unfold tailWord_2118679
  simp only [CollatzResearch.WordTrace]
  refine ⟨77274571491395299410631091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51516380994263532940420727 77274571491395299410631091)
  ·
    refine ⟨115911857237092949115946637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77274571491395299410631091 115911857237092949115946637)
    ·
      refine ⟨43466946463909855918479989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115911857237092949115946637 43466946463909855918479989)
      ·
        refine ⟨4075026230991548992357499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 43466946463909855918479989 4075026230991548992357499)
        ·
          refine ⟨6112539346487323488536249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4075026230991548992357499 6112539346487323488536249)
          ·
            refine ⟨4584404509865492616402187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6112539346487323488536249 4584404509865492616402187)
            ·
              refine ⟨6876606764798238924603281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4584404509865492616402187 6876606764798238924603281)
              ·
                refine ⟨5157455073598679193452461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6876606764798238924603281 5157455073598679193452461)
                ·
                  refine ⟨1934045652599504697544673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5157455073598679193452461 1934045652599504697544673)
                  ·
                    refine ⟨1450534239449628523158505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1934045652599504697544673 1450534239449628523158505)
                    ·
                      refine ⟨1087900679587221392368879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1450534239449628523158505 1087900679587221392368879)
                      ·
                        rfl

theorem cell23_2118679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_2118679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2118679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2118679 prefixEnd_2118679 := by exact prefixLift 2118679
  have htrace : WordTrace (prefixWord ++ tailWord_2118679) baseStart_2118679 baseEnd_2118679 := by
    simpa [prefixWord, tailWord_2118679, baseEnd_2118679] using wordTrace_append hprefix tailTrace_2118679
  have hstable : (prefixWord ++ tailWord_2118679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2118679).length < 2 ^ (prefixWord ++ tailWord_2118679).sum := by decide
  have hdescent : baseEnd_2118679 < baseStart_2118679 := by decide
  rcases family_descends (prefixWord ++ tailWord_2118679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2118712 : List Nat := [2, 1, 2, 1, 5, 2, 1, 1, 4, 1, 3]
def baseStart_2118712 : Nat := 118140960795 + 2118712 * 2 ^ 59
def prefixEnd_2118712 : Nat := 4983230072969 + 3 ^ 40 * 2118712 * 2
def baseEnd_2118712 : Nat := 1087917624448819763256227

theorem tailTrace_2118712 : CollatzResearch.WordTrace tailWord_2118712 prefixEnd_2118712 1087917624448819763256227 := by
  unfold tailWord_2118712
  simp only [CollatzResearch.WordTrace]
  refine ⟨38637887550137873023291195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51517183400183830697721593 38637887550137873023291195)
  ·
    refine ⟨57956831325206809534936793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38637887550137873023291195 57956831325206809534936793)
    ·
      refine ⟨43467623493905107151202595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57956831325206809534936793 43467623493905107151202595)
      ·
        refine ⟨65201435240857660726803893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43467623493905107151202595 65201435240857660726803893)
        ·
          refine ⟨6112634553830405693137865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 65201435240857660726803893 6112634553830405693137865)
          ·
            refine ⟨4584475915372804269853399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6112634553830405693137865 4584475915372804269853399)
            ·
              refine ⟨6876713873059206404780099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4584475915372804269853399 6876713873059206404780099)
              ·
                refine ⟨10315070809588809607170149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6876713873059206404780099 10315070809588809607170149)
                ·
                  refine ⟨1934075776797901801344403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10315070809588809607170149 1934075776797901801344403)
                  ·
                    refine ⟨2901113665196852702016605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1934075776797901801344403 2901113665196852702016605)
                    ·
                      refine ⟨1087917624448819763256227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2901113665196852702016605 1087917624448819763256227)
                      ·
                        rfl

theorem cell23_2118712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 1, 4, 1, 3].length) (baseStart_2118712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2118712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2118712 prefixEnd_2118712 := by exact prefixLift 2118712
  have htrace : WordTrace (prefixWord ++ tailWord_2118712) baseStart_2118712 baseEnd_2118712 := by
    simpa [prefixWord, tailWord_2118712, baseEnd_2118712] using wordTrace_append hprefix tailTrace_2118712
  have hstable : (prefixWord ++ tailWord_2118712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2118712).length < 2 ^ (prefixWord ++ tailWord_2118712).sum := by decide
  have hdescent : baseEnd_2118712 < baseStart_2118712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2118712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2118728 : List Nat := [2, 1, 3, 1, 1, 1, 3, 3, 2, 6]
def baseStart_2118728 : Nat := 118140960795 + 2118728 * 2 ^ 59
def prefixEnd_2118728 : Nat := 4983230072969 + 3 ^ 40 * 2118728 * 2
def baseEnd_2118728 : Nat := 362641946713097233552051

theorem tailTrace_2118728 : CollatzResearch.WordTrace tailWord_2118728 prefixEnd_2118728 362641946713097233552051 := by
  unfold tailWord_2118728
  simp only [CollatzResearch.WordTrace]
  refine ⟨38638179334108890389582419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51517572445478520519443225 38638179334108890389582419)
  ·
    refine ⟨57957269001163335584373629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38638179334108890389582419 57957269001163335584373629)
    ·
      refine ⟨21733975875436250844140111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57957269001163335584373629 21733975875436250844140111)
      ·
        refine ⟨32600963813154376266210167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21733975875436250844140111 32600963813154376266210167)
        ·
          refine ⟨48901445719731564399315251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32600963813154376266210167 48901445719731564399315251)
          ·
            refine ⟨73352168579597346598972877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48901445719731564399315251 73352168579597346598972877)
            ·
              refine ⟨27507063217349004974614829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73352168579597346598972877 27507063217349004974614829)
              ·
                refine ⟨10315148706505876865480561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27507063217349004974614829 10315148706505876865480561)
                ·
                  refine ⟨7736361529879407649110421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10315148706505876865480561 7736361529879407649110421)
                  ·
                    refine ⟨362641946713097233552051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7736361529879407649110421 362641946713097233552051)
                    ·
                      rfl

theorem cell23_2118728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 3, 2, 6].length) (baseStart_2118728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2118728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2118728 prefixEnd_2118728 := by exact prefixLift 2118728
  have htrace : WordTrace (prefixWord ++ tailWord_2118728) baseStart_2118728 baseEnd_2118728 := by
    simpa [prefixWord, tailWord_2118728, baseEnd_2118728] using wordTrace_append hprefix tailTrace_2118728
  have hstable : (prefixWord ++ tailWord_2118728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2118728).length < 2 ^ (prefixWord ++ tailWord_2118728).sum := by decide
  have hdescent : baseEnd_2118728 < baseStart_2118728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2118728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2118752 : List Nat := [2, 1, 1, 3, 2, 2, 1, 1, 6, 2, 2]
def baseStart_2118752 : Nat := 118140960795 + 2118752 * 2 ^ 59
def prefixEnd_2118752 : Nat := 4983230072969 + 3 ^ 40 * 2118752 * 2
def baseEnd_2118752 : Nat := 1087938163674999606756043

theorem tailTrace_2118752 : CollatzResearch.WordTrace tailWord_2118752 prefixEnd_2118752 1087938163674999606756043 := by
  unfold tailWord_2118752
  simp only [CollatzResearch.WordTrace]
  refine ⟨38638617010065416439019255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51518156013420555252025673 38638617010065416439019255)
  ·
    refine ⟨57957925515098124658528883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38638617010065416439019255 57957925515098124658528883)
    ·
      refine ⟨86936888272647186987793325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57957925515098124658528883 86936888272647186987793325)
      ·
        refine ⟨32601333102242695120422497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86936888272647186987793325 32601333102242695120422497)
        ·
          refine ⟨24450999826682021340316873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32601333102242695120422497 24450999826682021340316873)
          ·
            refine ⟨18338249870011516005237655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24450999826682021340316873 18338249870011516005237655)
            ·
              refine ⟨27507374805017274007856483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18338249870011516005237655 27507374805017274007856483)
              ·
                refine ⟨41261062207525911011784725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27507374805017274007856483 41261062207525911011784725)
                ·
                  refine ⟨1934112290977777078677409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 41261062207525911011784725 1934112290977777078677409)
                  ·
                    refine ⟨1450584218233332809008057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1934112290977777078677409 1450584218233332809008057)
                    ·
                      refine ⟨1087938163674999606756043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1450584218233332809008057 1087938163674999606756043)
                      ·
                        rfl

theorem cell23_2118752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 6, 2, 2].length) (baseStart_2118752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2118752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2118752 prefixEnd_2118752 := by exact prefixLift 2118752
  have htrace : WordTrace (prefixWord ++ tailWord_2118752) baseStart_2118752 baseEnd_2118752 := by
    simpa [prefixWord, tailWord_2118752, baseEnd_2118752] using wordTrace_append hprefix tailTrace_2118752
  have hstable : (prefixWord ++ tailWord_2118752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2118752).length < 2 ^ (prefixWord ++ tailWord_2118752).sum := by decide
  have hdescent : baseEnd_2118752 < baseStart_2118752 := by decide
  rcases family_descends (prefixWord ++ tailWord_2118752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2118768 : List Nat := [2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 7]
def baseStart_2118768 : Nat := 118140960795 + 2118768 * 2 ^ 59
def prefixEnd_2118768 : Nat := 4983230072969 + 3 ^ 40 * 2118768 * 2
def baseEnd_2118768 : Nat := 1087946379365471544155969

theorem tailTrace_2118768 : CollatzResearch.WordTrace tailWord_2118768 prefixEnd_2118768 1087946379365471544155969 := by
  unfold tailWord_2118768
  simp only [CollatzResearch.WordTrace]
  refine ⟨38638908794036433805310479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51518545058715245073747305 38638908794036433805310479)
  ·
    refine ⟨57958363191054650707965719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38638908794036433805310479 57958363191054650707965719)
    ·
      refine ⟨86937544786581976061948579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57958363191054650707965719 86937544786581976061948579)
      ·
        refine ⟨130406317179872964092922869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86937544786581976061948579 130406317179872964092922869)
        ·
          refine ⟨12225592235613090383711519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 130406317179872964092922869 12225592235613090383711519)
          ·
            refine ⟨18338388353419635575567279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12225592235613090383711519 18338388353419635575567279)
            ·
              refine ⟨27507582530129453363350919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18338388353419635575567279 27507582530129453363350919)
              ·
                refine ⟨41261373795194180045026379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27507582530129453363350919 41261373795194180045026379)
                ·
                  refine ⟨61892060692791270067539569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41261373795194180045026379 61892060692791270067539569)
                  ·
                    refine ⟨46419045519593452550654677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 61892060692791270067539569 46419045519593452550654677)
                    ·
                      refine ⟨1087946379365471544155969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 46419045519593452550654677 1087946379365471544155969)
                      ·
                        rfl

theorem cell23_2118768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 7].length) (baseStart_2118768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2118768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2118768 prefixEnd_2118768 := by exact prefixLift 2118768
  have htrace : WordTrace (prefixWord ++ tailWord_2118768) baseStart_2118768 baseEnd_2118768 := by
    simpa [prefixWord, tailWord_2118768, baseEnd_2118768] using wordTrace_append hprefix tailTrace_2118768
  have hstable : (prefixWord ++ tailWord_2118768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2118768).length < 2 ^ (prefixWord ++ tailWord_2118768).sum := by decide
  have hdescent : baseEnd_2118768 < baseStart_2118768 := by decide
  rcases family_descends (prefixWord ++ tailWord_2118768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2118826 : List Nat := [3, 1, 5, 1, 1, 1, 4, 2, 5]
def baseStart_2118826 : Nat := 118140960795 + 2118826 * 2 ^ 59
def prefixEnd_2118826 : Nat := 4983230072969 + 3 ^ 40 * 2118826 * 2
def baseEnd_2118826 : Nat := 120886240138159146358967

theorem tailTrace_2118826 : CollatzResearch.WordTrace tailWord_2118826 prefixEnd_2118826 120886240138159146358967 := by
  unfold tailWord_2118826
  simp only [CollatzResearch.WordTrace]
  refine ⟨19319983255465685879058083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51519955347908495677488221 19319983255465685879058083)
  ·
    refine ⟨28979974883198528818587125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19319983255465685879058083 28979974883198528818587125)
    ·
      refine ⟨2716872645299862076742543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28979974883198528818587125 2716872645299862076742543)
      ·
        refine ⟨4075308967949793115113815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2716872645299862076742543 4075308967949793115113815)
        ·
          refine ⟨6112963451924689672670723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4075308967949793115113815 6112963451924689672670723)
          ·
            refine ⟨9169445177887034509006085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6112963451924689672670723 9169445177887034509006085)
            ·
              refine ⟨1719270970853818970438641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9169445177887034509006085 1719270970853818970438641)
              ·
                refine ⟨1289453228140364227828981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1719270970853818970438641 1289453228140364227828981)
                ·
                  refine ⟨120886240138159146358967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1289453228140364227828981 120886240138159146358967)
                  ·
                    rfl

theorem cell23_2118826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 4, 2, 5].length) (baseStart_2118826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2118826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2118826 prefixEnd_2118826 := by exact prefixLift 2118826
  have htrace : WordTrace (prefixWord ++ tailWord_2118826) baseStart_2118826 baseEnd_2118826 := by
    simpa [prefixWord, tailWord_2118826, baseEnd_2118826] using wordTrace_append hprefix tailTrace_2118826
  have hstable : (prefixWord ++ tailWord_2118826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2118826).length < 2 ^ (prefixWord ++ tailWord_2118826).sum := by decide
  have hdescent : baseEnd_2118826 < baseStart_2118826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2118826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2118943 : List Nat := [1, 1, 2, 4, 5, 1, 1, 1, 3, 1, 3]
def baseStart_2118943 : Nat := 118140960795 + 2118943 * 2 ^ 59
def prefixEnd_2118943 : Nat := 4983230072969 + 3 ^ 40 * 2118943 * 2
def baseEnd_2118943 : Nat := 1088036238480008359467665

theorem tailTrace_2118943 : CollatzResearch.WordTrace tailWord_2118943 prefixEnd_2118943 1088036238480008359467665 := by
  unfold tailWord_2118943
  simp only [CollatzResearch.WordTrace]
  refine ⟨77284200362438872498241483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51522800241625914998827655 77284200362438872498241483)
  ·
    refine ⟨115926300543658308747362225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77284200362438872498241483 115926300543658308747362225)
    ·
      refine ⟨86944725407743731560521669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115926300543658308747362225 86944725407743731560521669)
      ·
        refine ⟨16302136013951949667597813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 86944725407743731560521669 16302136013951949667597813)
        ·
          refine ⟨1528325251307995281337295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16302136013951949667597813 1528325251307995281337295)
          ·
            refine ⟨2292487876961992922005943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1528325251307995281337295 2292487876961992922005943)
            ·
              refine ⟨3438731815442989383008915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2292487876961992922005943 3438731815442989383008915)
              ·
                refine ⟨5158097723164484074513373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3438731815442989383008915 5158097723164484074513373)
                ·
                  refine ⟨1934286646186681527942515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5158097723164484074513373 1934286646186681527942515)
                  ·
                    refine ⟨2901429969280022291913773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1934286646186681527942515 2901429969280022291913773)
                    ·
                      refine ⟨1088036238480008359467665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2901429969280022291913773 1088036238480008359467665)
                      ·
                        rfl

theorem cell23_2118943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 1, 3, 1, 3].length) (baseStart_2118943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2118943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2118943 prefixEnd_2118943 := by exact prefixLift 2118943
  have htrace : WordTrace (prefixWord ++ tailWord_2118943) baseStart_2118943 baseEnd_2118943 := by
    simpa [prefixWord, tailWord_2118943, baseEnd_2118943] using wordTrace_append hprefix tailTrace_2118943
  have hstable : (prefixWord ++ tailWord_2118943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2118943).length < 2 ^ (prefixWord ++ tailWord_2118943).sum := by decide
  have hdescent : baseEnd_2118943 < baseStart_2118943 := by decide
  rcases family_descends (prefixWord ++ tailWord_2118943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2118962 : List Nat := [3, 2, 1, 1, 4, 1, 2, 1, 1, 1, 6]
def baseStart_2118962 : Nat := 118140960795 + 2118962 * 2 ^ 59
def prefixEnd_2118962 : Nat := 4983230072969 + 3 ^ 40 * 2118962 * 2
def baseEnd_2118962 : Nat := 1088045994612443785130077

theorem tailTrace_2118962 : CollatzResearch.WordTrace tailWord_2118962 prefixEnd_2118962 1088045994612443785130077 := by
  unfold tailWord_2118962
  simp only [CollatzResearch.WordTrace]
  refine ⟨19321223337342509685795785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51523262232913359162122093 19321223337342509685795785)
  ·
    refine ⟨14490917503006882264346839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19321223337342509685795785 14490917503006882264346839)
    ·
      refine ⟨21736376254510323396520259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14490917503006882264346839 21736376254510323396520259)
      ·
        refine ⟨32604564381765485094780389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21736376254510323396520259 32604564381765485094780389)
        ·
          refine ⟨6113355821581028455271323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32604564381765485094780389 6113355821581028455271323)
          ·
            refine ⟨9170033732371542682906985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6113355821581028455271323 9170033732371542682906985)
            ·
              refine ⟨6877525299278657012180239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9170033732371542682906985 6877525299278657012180239)
              ·
                refine ⟨10316287948917985518270359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6877525299278657012180239 10316287948917985518270359)
                ·
                  refine ⟨15474431923376978277405539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10316287948917985518270359 15474431923376978277405539)
                  ·
                    refine ⟨23211647885065467416108309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15474431923376978277405539 23211647885065467416108309)
                    ·
                      refine ⟨1088045994612443785130077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23211647885065467416108309 1088045994612443785130077)
                      ·
                        rfl

theorem cell23_2118962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 1, 1, 1, 6].length) (baseStart_2118962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2118962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2118962 prefixEnd_2118962 := by exact prefixLift 2118962
  have htrace : WordTrace (prefixWord ++ tailWord_2118962) baseStart_2118962 baseEnd_2118962 := by
    simpa [prefixWord, tailWord_2118962, baseEnd_2118962] using wordTrace_append hprefix tailTrace_2118962
  have hstable : (prefixWord ++ tailWord_2118962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2118962).length < 2 ^ (prefixWord ++ tailWord_2118962).sum := by decide
  have hdescent : baseEnd_2118962 < baseStart_2118962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2118962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2118989 : List Nat := [1, 6, 1, 3, 1, 11]
def baseStart_2118989 : Nat := 118140960795 + 2118989 * 2 ^ 59
def prefixEnd_2118989 : Nat := 4983230072969 + 3 ^ 40 * 2118989 * 2
def baseEnd_2118989 : Nat := 4477612586790597446471

theorem tailTrace_2118989 : CollatzResearch.WordTrace tailWord_2118989 prefixEnd_2118989 4477612586790597446471 := by
  unfold tailWord_2118989
  simp only [CollatzResearch.WordTrace]
  refine ⟨77285878120272222354416021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51523918746848148236277347 77285878120272222354416021)
  ·
    refine ⟨3622775536887760422863251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 77285878120272222354416021 3622775536887760422863251)
    ·
      refine ⟨5434163305331640634294877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3622775536887760422863251 5434163305331640634294877)
      ·
        refine ⟨2037811239499365237860579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5434163305331640634294877 2037811239499365237860579)
        ·
          refine ⟨3056716859249047856790869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2037811239499365237860579 3056716859249047856790869)
          ·
            refine ⟨4477612586790597446471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 3056716859249047856790869 4477612586790597446471)
            ·
              rfl

theorem cell23_2118989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 11].length) (baseStart_2118989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2118989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2118989 prefixEnd_2118989 := by exact prefixLift 2118989
  have htrace : WordTrace (prefixWord ++ tailWord_2118989) baseStart_2118989 baseEnd_2118989 := by
    simpa [prefixWord, tailWord_2118989, baseEnd_2118989] using wordTrace_append hprefix tailTrace_2118989
  have hstable : (prefixWord ++ tailWord_2118989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2118989).length < 2 ^ (prefixWord ++ tailWord_2118989).sum := by decide
  have hdescent : baseEnd_2118989 < baseStart_2118989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2118989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2119016 : List Nat := [2, 1, 4, 2, 3, 1, 2, 1, 1, 3, 3]
def baseStart_2119016 : Nat := 118140960795 + 2119016 * 2 ^ 59
def prefixEnd_2119016 : Nat := 4983230072969 + 3 ^ 40 * 2119016 * 2
def baseEnd_2119016 : Nat := 1088073722567786573854829

theorem tailTrace_2119016 : CollatzResearch.WordTrace tailWord_2119016 prefixEnd_2119016 1088073722567786573854829 := by
  unfold tailWord_2119016
  simp only [CollatzResearch.WordTrace]
  refine ⟨38643431445587202982824451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51524575260782937310432601 38643431445587202982824451)
  ·
    refine ⟨57965147168380804474236677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38643431445587202982824451 57965147168380804474236677)
    ·
      refine ⟨10868465094071400838919377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57965147168380804474236677 10868465094071400838919377)
      ·
        refine ⟨8151348820553550629189533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10868465094071400838919377 8151348820553550629189533)
        ·
          refine ⟨3056755807707581485946075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8151348820553550629189533 3056755807707581485946075)
          ·
            refine ⟨4585133711561372228919113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3056755807707581485946075 4585133711561372228919113)
            ·
              refine ⟨3438850283671029171689335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4585133711561372228919113 3438850283671029171689335)
              ·
                refine ⟨5158275425506543757534003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3438850283671029171689335 5158275425506543757534003)
                ·
                  refine ⟨7737413138259815636301005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5158275425506543757534003 7737413138259815636301005)
                  ·
                    refine ⟨2901529926847430863612877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7737413138259815636301005 2901529926847430863612877)
                    ·
                      refine ⟨1088073722567786573854829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2901529926847430863612877 1088073722567786573854829)
                      ·
                        rfl

theorem cell23_2119016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_2119016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2119016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2119016 prefixEnd_2119016 := by exact prefixLift 2119016
  have htrace : WordTrace (prefixWord ++ tailWord_2119016) baseStart_2119016 baseEnd_2119016 := by
    simpa [prefixWord, tailWord_2119016, baseEnd_2119016] using wordTrace_append hprefix tailTrace_2119016
  have hstable : (prefixWord ++ tailWord_2119016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2119016).length < 2 ^ (prefixWord ++ tailWord_2119016).sum := by decide
  have hdescent : baseEnd_2119016 < baseStart_2119016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2119016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2119026 : List Nat := [3, 2, 1, 2, 1, 2, 2, 4, 1, 3, 2]
def baseStart_2119026 : Nat := 118140960795 + 2119026 * 2 ^ 59
def prefixEnd_2119026 : Nat := 4983230072969 + 3 ^ 40 * 2119026 * 2
def baseEnd_2119026 : Nat := 1088078857374331534729783

theorem tailTrace_2119026 : CollatzResearch.WordTrace tailWord_2119026 prefixEnd_2119026 1088078857374331534729783 := by
  unfold tailWord_2119026
  simp only [CollatzResearch.WordTrace]
  refine ⟨19321806905284544418378233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51524818414092118449008621 19321806905284544418378233)
  ·
    refine ⟨14491355178963408313783675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19321806905284544418378233 14491355178963408313783675)
    ·
      refine ⟨21737032768445112470675513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14491355178963408313783675 21737032768445112470675513)
      ·
        refine ⟨16302774576333834353006635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21737032768445112470675513 16302774576333834353006635)
        ·
          refine ⟨24454161864500751529509953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16302774576333834353006635 24454161864500751529509953)
          ·
            refine ⟨18340621398375563647132465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24454161864500751529509953 18340621398375563647132465)
            ·
              refine ⟨13755466048781672735349349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18340621398375563647132465 13755466048781672735349349)
              ·
                refine ⟨2579149884146563637878003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13755466048781672735349349 2579149884146563637878003)
                ·
                  refine ⟨3868724826219845456817005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2579149884146563637878003 3868724826219845456817005)
                  ·
                    refine ⟨1450771809832442046306377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3868724826219845456817005 1450771809832442046306377)
                    ·
                      refine ⟨1088078857374331534729783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1450771809832442046306377 1088078857374331534729783)
                      ·
                        rfl

theorem cell23_2119026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 4, 1, 3, 2].length) (baseStart_2119026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2119026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2119026 prefixEnd_2119026 := by exact prefixLift 2119026
  have htrace : WordTrace (prefixWord ++ tailWord_2119026) baseStart_2119026 baseEnd_2119026 := by
    simpa [prefixWord, tailWord_2119026, baseEnd_2119026] using wordTrace_append hprefix tailTrace_2119026
  have hstable : (prefixWord ++ tailWord_2119026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2119026).length < 2 ^ (prefixWord ++ tailWord_2119026).sum := by decide
  have hdescent : baseEnd_2119026 < baseStart_2119026 := by decide
  rcases family_descends (prefixWord ++ tailWord_2119026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2119043 : List Nat := [1, 1, 1, 3, 5, 1, 4, 1, 1, 3, 2]
def baseStart_2119043 : Nat := 118140960795 + 2119043 * 2 ^ 59
def prefixEnd_2119043 : Nat := 4983230072969 + 3 ^ 40 * 2119043 * 2
def baseEnd_2119043 : Nat := 1088087586545457968217205

theorem tailTrace_2119043 : CollatzResearch.WordTrace tailWord_2119043 prefixEnd_2119043 1088087586545457968217205 := by
  unfold tailWord_2119043
  simp only [CollatzResearch.WordTrace]
  refine ⟨77287847662076589576881783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51525231774717726384587855 77287847662076589576881783)
  ·
    refine ⟨115931771493114884365322675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77287847662076589576881783 115931771493114884365322675)
    ·
      refine ⟨173897657239672326547984013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115931771493114884365322675 173897657239672326547984013)
      ·
        refine ⟨65211621464877122455494005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 173897657239672326547984013 65211621464877122455494005)
        ·
          refine ⟨6113589512332230230202563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 65211621464877122455494005 6113589512332230230202563)
          ·
            refine ⟨9170384268498345345303845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6113589512332230230202563 9170384268498345345303845)
            ·
              refine ⟨1719447050343439752244471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9170384268498345345303845 1719447050343439752244471)
              ·
                refine ⟨2579170575515159628366707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1719447050343439752244471 2579170575515159628366707)
                ·
                  refine ⟨3868755863272739442550061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2579170575515159628366707 3868755863272739442550061)
                  ·
                    refine ⟨1450783448727277290956273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3868755863272739442550061 1450783448727277290956273)
                    ·
                      refine ⟨1088087586545457968217205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1450783448727277290956273 1088087586545457968217205)
                      ·
                        rfl

theorem cell23_2119043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 4, 1, 1, 3, 2].length) (baseStart_2119043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2119043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2119043 prefixEnd_2119043 := by exact prefixLift 2119043
  have htrace : WordTrace (prefixWord ++ tailWord_2119043) baseStart_2119043 baseEnd_2119043 := by
    simpa [prefixWord, tailWord_2119043, baseEnd_2119043] using wordTrace_append hprefix tailTrace_2119043
  have hstable : (prefixWord ++ tailWord_2119043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2119043).length < 2 ^ (prefixWord ++ tailWord_2119043).sum := by decide
  have hdescent : baseEnd_2119043 < baseStart_2119043 := by decide
  rcases family_descends (prefixWord ++ tailWord_2119043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2119052 : List Nat := [2, 2, 1, 2, 1, 3, 1, 1, 4, 2, 4]
def baseStart_2119052 : Nat := 118140960795 + 2119052 * 2 ^ 59
def prefixEnd_2119052 : Nat := 4983230072969 + 3 ^ 40 * 2119052 * 2
def baseEnd_2119052 : Nat := 1088092207871348433004663

theorem tailTrace_2119052 : CollatzResearch.WordTrace tailWord_2119052 prefixEnd_2119052 1088092207871348433004663 := by
  unfold tailWord_2119052
  simp only [CollatzResearch.WordTrace]
  refine ⟨38644087959521992056979705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51525450612695989409306273 38644087959521992056979705)
  ·
    refine ⟨28983065969641494042734779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38644087959521992056979705 28983065969641494042734779)
    ·
      refine ⟨43474598954462241064102169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28983065969641494042734779 43474598954462241064102169)
      ·
        refine ⟨32605949215846680798076627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43474598954462241064102169 32605949215846680798076627)
        ·
          refine ⟨48908923823770021197114941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32605949215846680798076627 48908923823770021197114941)
          ·
            refine ⟨18340846433913757948918103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48908923823770021197114941 18340846433913757948918103)
            ·
              refine ⟨27511269650870636923377155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18340846433913757948918103 27511269650870636923377155)
              ·
                refine ⟨41266904476305955385065733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27511269650870636923377155 41266904476305955385065733)
                ·
                  refine ⟨7737544589307366634699825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41266904476305955385065733 7737544589307366634699825)
                  ·
                    refine ⟨5803158441980524976024869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7737544589307366634699825 5803158441980524976024869)
                    ·
                      refine ⟨1088092207871348433004663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5803158441980524976024869 1088092207871348433004663)
                      ·
                        rfl

theorem cell23_2119052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 4, 2, 4].length) (baseStart_2119052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2119052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2119052 prefixEnd_2119052 := by exact prefixLift 2119052
  have htrace : WordTrace (prefixWord ++ tailWord_2119052) baseStart_2119052 baseEnd_2119052 := by
    simpa [prefixWord, tailWord_2119052, baseEnd_2119052] using wordTrace_append hprefix tailTrace_2119052
  have hstable : (prefixWord ++ tailWord_2119052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2119052).length < 2 ^ (prefixWord ++ tailWord_2119052).sum := by decide
  have hdescent : baseEnd_2119052 < baseStart_2119052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2119052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2119069 : List Nat := [1, 4, 2, 1, 3, 1, 2, 1, 2, 2, 4]
def baseStart_2119069 : Nat := 118140960795 + 2119069 * 2 ^ 59
def prefixEnd_2119069 : Nat := 4983230072969 + 3 ^ 40 * 2119069 * 2
def baseEnd_2119069 : Nat := 1088100937042474866492085

theorem tailTrace_2119069 : CollatzResearch.WordTrace tailWord_2119069 prefixEnd_2119069 1088100937042474866492085 := by
  unfold tailWord_2119069
  simp only [CollatzResearch.WordTrace]
  refine ⟨77288795959982396017328261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51525863973321597344885507 77288795959982396017328261)
  ·
    refine ⟨14491649242496699253249049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77288795959982396017328261 14491649242496699253249049)
    ·
      refine ⟨10868736931872524439936787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14491649242496699253249049 10868736931872524439936787)
      ·
        refine ⟨16303105397808786659905181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10868736931872524439936787 16303105397808786659905181)
        ·
          refine ⟨6113664524178294997464443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16303105397808786659905181 6113664524178294997464443)
          ·
            refine ⟨9170496786267442496196665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6113664524178294997464443 9170496786267442496196665)
            ·
              refine ⟨6877872589700581872147499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9170496786267442496196665 6877872589700581872147499)
              ·
                refine ⟨10316808884550872808221249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6877872589700581872147499 10316808884550872808221249)
                ·
                  refine ⟨7737606663413154606165937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10316808884550872808221249 7737606663413154606165937)
                  ·
                    refine ⟨5803204997559865954624453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7737606663413154606165937 5803204997559865954624453)
                    ·
                      refine ⟨1088100937042474866492085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5803204997559865954624453 1088100937042474866492085)
                      ·
                        rfl

theorem cell23_2119069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_2119069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2119069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2119069 prefixEnd_2119069 := by exact prefixLift 2119069
  have htrace : WordTrace (prefixWord ++ tailWord_2119069) baseStart_2119069 baseEnd_2119069 := by
    simpa [prefixWord, tailWord_2119069, baseEnd_2119069] using wordTrace_append hprefix tailTrace_2119069
  have hstable : (prefixWord ++ tailWord_2119069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2119069).length < 2 ^ (prefixWord ++ tailWord_2119069).sum := by decide
  have hdescent : baseEnd_2119069 < baseStart_2119069 := by decide
  rcases family_descends (prefixWord ++ tailWord_2119069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2119124 : List Nat := [2, 4, 1, 2, 4, 1, 2, 1, 2, 2, 2]
def baseStart_2119124 : Nat := 118140960795 + 2119124 * 2 ^ 59
def prefixEnd_2119124 : Nat := 4983230072969 + 3 ^ 40 * 2119124 * 2
def baseEnd_2119124 : Nat := 1088129178478472151304333

theorem tailTrace_2119124 : CollatzResearch.WordTrace tailWord_2119124 prefixEnd_2119124 1088129178478472151304333 := by
  unfold tailWord_2119124
  simp only [CollatzResearch.WordTrace]
  refine ⟨38645400987391570205290213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51527201316522093607053617 38645400987391570205290213)
  ·
    refine ⟨7246012685135919413491915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38645400987391570205290213 7246012685135919413491915)
    ·
      refine ⟨10869019027703879120237873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7246012685135919413491915 10869019027703879120237873)
      ·
        refine ⟨8151764270777909340178405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10869019027703879120237873 8151764270777909340178405)
        ·
          refine ⟨1528455800770858001283451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8151764270777909340178405 1528455800770858001283451)
          ·
            refine ⟨2292683701156287001925177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1528455800770858001283451 2292683701156287001925177)
            ·
              refine ⟨1719512775867215251443883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2292683701156287001925177 1719512775867215251443883)
              ·
                refine ⟨2579269163800822877165825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1719512775867215251443883 2579269163800822877165825)
                ·
                  refine ⟨1934451872850617157874369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2579269163800822877165825 1934451872850617157874369)
                  ·
                    refine ⟨1450838904637962868405777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1934451872850617157874369 1450838904637962868405777)
                    ·
                      refine ⟨1088129178478472151304333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1450838904637962868405777 1088129178478472151304333)
                      ·
                        rfl

theorem cell23_2119124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 2, 1, 2, 2, 2].length) (baseStart_2119124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2119124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2119124 prefixEnd_2119124 := by exact prefixLift 2119124
  have htrace : WordTrace (prefixWord ++ tailWord_2119124) baseStart_2119124 baseEnd_2119124 := by
    simpa [prefixWord, tailWord_2119124, baseEnd_2119124] using wordTrace_append hprefix tailTrace_2119124
  have hstable : (prefixWord ++ tailWord_2119124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2119124).length < 2 ^ (prefixWord ++ tailWord_2119124).sum := by decide
  have hdescent : baseEnd_2119124 < baseStart_2119124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2119124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2119199 : List Nat := [1, 1, 2, 4, 1, 1, 4, 1, 3, 5]
def baseStart_2119199 : Nat := 118140960795 + 2119199 * 2 ^ 59
def prefixEnd_2119199 : Nat := 4983230072969 + 3 ^ 40 * 2119199 * 2
def baseEnd_2119199 : Nat := 362722563175853119288829

theorem tailTrace_2119199 : CollatzResearch.WordTrace tailWord_2119199 prefixEnd_2119199 362722563175853119288829 := by
  unfold tailWord_2119199
  simp only [CollatzResearch.WordTrace]
  refine ⟨77293537449511428219560651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51529024966340952146373767 77293537449511428219560651)
  ·
    refine ⟨115940306174267142329340977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77293537449511428219560651 115940306174267142329340977)
    ·
      refine ⟨86955229630700356747005733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115940306174267142329340977 86955229630700356747005733)
      ·
        refine ⟨16304105555756316890063575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 86955229630700356747005733 16304105555756316890063575)
        ·
          refine ⟨24456158333634475335095363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16304105555756316890063575 24456158333634475335095363)
          ·
            refine ⟨36684237500451713002643045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24456158333634475335095363 36684237500451713002643045)
            ·
              refine ⟨6878294531334696187995571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36684237500451713002643045 6878294531334696187995571)
              ·
                refine ⟨10317441797002044281993357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6878294531334696187995571 10317441797002044281993357)
                ·
                  refine ⟨3869040673875766605747509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10317441797002044281993357 3869040673875766605747509)
                  ·
                    refine ⟨362722563175853119288829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3869040673875766605747509 362722563175853119288829)
                    ·
                      rfl

theorem cell23_2119199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 1, 3, 5].length) (baseStart_2119199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2119199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2119199 prefixEnd_2119199 := by exact prefixLift 2119199
  have htrace : WordTrace (prefixWord ++ tailWord_2119199) baseStart_2119199 baseEnd_2119199 := by
    simpa [prefixWord, tailWord_2119199, baseEnd_2119199] using wordTrace_append hprefix tailTrace_2119199
  have hstable : (prefixWord ++ tailWord_2119199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2119199).length < 2 ^ (prefixWord ++ tailWord_2119199).sum := by decide
  have hdescent : baseEnd_2119199 < baseStart_2119199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2119199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2119249 : List Nat := [1, 2, 2, 1, 3, 2, 3, 1, 1, 1, 6]
def baseStart_2119249 : Nat := 118140960795 + 2119249 * 2 ^ 59
def prefixEnd_2119249 : Nat := 4983230072969 + 3 ^ 40 * 2119249 * 2
def baseEnd_2119249 : Nat := 1088193363560284162241257

theorem tailTrace_2119249 : CollatzResearch.WordTrace tailWord_2119249 prefixEnd_2119249 1088193363560284162241257 := by
  unfold tailWord_2119249
  simp only [CollatzResearch.WordTrace]
  refine ⟨77295361099330286758880801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51530240732886857839253867 77295361099330286758880801)
  ·
    refine ⟨57971520824497715069160601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77295361099330286758880801 57971520824497715069160601)
    ·
      refine ⟨43478640618373286301870451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57971520824497715069160601 43478640618373286301870451)
      ·
        refine ⟨65217960927559929452805677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43478640618373286301870451 65217960927559929452805677)
        ·
          refine ⟨24456735347834973544802129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65217960927559929452805677 24456735347834973544802129)
          ·
            refine ⟨18342551510876230158601597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24456735347834973544802129 18342551510876230158601597)
            ·
              refine ⟨6878456816578586309475599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18342551510876230158601597 6878456816578586309475599)
              ·
                refine ⟨10317685224867879464213399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6878456816578586309475599 10317685224867879464213399)
                ·
                  refine ⟨15476527837301819196320099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10317685224867879464213399 15476527837301819196320099)
                  ·
                    refine ⟨23214791755952728794480149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15476527837301819196320099 23214791755952728794480149)
                    ·
                      refine ⟨1088193363560284162241257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23214791755952728794480149 1088193363560284162241257)
                      ·
                        rfl

theorem cell23_2119249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 1, 1, 1, 6].length) (baseStart_2119249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2119249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2119249 prefixEnd_2119249 := by exact prefixLift 2119249
  have htrace : WordTrace (prefixWord ++ tailWord_2119249) baseStart_2119249 baseEnd_2119249 := by
    simpa [prefixWord, tailWord_2119249, baseEnd_2119249] using wordTrace_append hprefix tailTrace_2119249
  have hstable : (prefixWord ++ tailWord_2119249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2119249).length < 2 ^ (prefixWord ++ tailWord_2119249).sum := by decide
  have hdescent : baseEnd_2119249 < baseStart_2119249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2119249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2119289 : List Nat := [1, 2, 1, 3, 3, 1, 2, 1, 2, 7]
def baseStart_2119289 : Nat := 118140960795 + 2119289 * 2 ^ 59
def prefixEnd_2119289 : Nat := 4983230072969 + 3 ^ 40 * 2119289 * 2
def baseEnd_2119289 : Nat := 362737967595488001913691

theorem tailTrace_2119289 : CollatzResearch.WordTrace tailWord_2119289 prefixEnd_2119289 362737967595488001913691 := by
  unfold tailWord_2119289
  simp only [CollatzResearch.WordTrace]
  refine ⟨77296820019185373590336921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51531213346123582393557947 77296820019185373590336921)
  ·
    refine ⟨57972615014389030192752691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77296820019185373590336921 57972615014389030192752691)
    ·
      refine ⟨86958922521583545289129037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57972615014389030192752691 86958922521583545289129037)
      ·
        refine ⟨32609595945593829483423389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86958922521583545289129037 32609595945593829483423389)
        ·
          refine ⟨12228598479597686056283771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32609595945593829483423389 12228598479597686056283771)
          ·
            refine ⟨18342897719396529084425657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12228598479597686056283771 18342897719396529084425657)
            ·
              refine ⟨13757173289547396813319243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18342897719396529084425657 13757173289547396813319243)
              ·
                refine ⟨20635759934321095219978865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13757173289547396813319243 20635759934321095219978865)
                ·
                  refine ⟨15476819950740821414984149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20635759934321095219978865 15476819950740821414984149)
                  ·
                    refine ⟨362737967595488001913691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15476819950740821414984149 362737967595488001913691)
                    ·
                      rfl

theorem cell23_2119289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 2, 7].length) (baseStart_2119289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2119289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2119289 prefixEnd_2119289 := by exact prefixLift 2119289
  have htrace : WordTrace (prefixWord ++ tailWord_2119289) baseStart_2119289 baseEnd_2119289 := by
    simpa [prefixWord, tailWord_2119289, baseEnd_2119289] using wordTrace_append hprefix tailTrace_2119289
  have hstable : (prefixWord ++ tailWord_2119289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2119289).length < 2 ^ (prefixWord ++ tailWord_2119289).sum := by decide
  have hdescent : baseEnd_2119289 < baseStart_2119289 := by decide
  rcases family_descends (prefixWord ++ tailWord_2119289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2119313 : List Nat := [1, 2, 2, 1, 1, 1, 1, 8, 1, 3, 2]
def baseStart_2119313 : Nat := 118140960795 + 2119313 * 2 ^ 59
def prefixEnd_2119313 : Nat := 4983230072969 + 3 ^ 40 * 2119313 * 2
def baseEnd_2119313 : Nat := 1088226226322171911840963

theorem tailTrace_2119313 : CollatzResearch.WordTrace tailWord_2119313 prefixEnd_2119313 1088226226322171911840963 := by
  unfold tailWord_2119313
  simp only [CollatzResearch.WordTrace]
  refine ⟨77297695371098425689210593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51531796914065617126140395 77297695371098425689210593)
  ·
    refine ⟨57973271528323819266907945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77297695371098425689210593 57973271528323819266907945)
    ·
      refine ⟨43479953646242864450180959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57973271528323819266907945 43479953646242864450180959)
      ·
        refine ⟨65219930469364296675271439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43479953646242864450180959 65219930469364296675271439)
        ·
          refine ⟨97829895704046445012907159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65219930469364296675271439 97829895704046445012907159)
          ·
            refine ⟨146744843556069667519360739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97829895704046445012907159 146744843556069667519360739)
            ·
              refine ⟨220117265334104501279041109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146744843556069667519360739 220117265334104501279041109)
              ·
                refine ⟨2579499203134037124363763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 220117265334104501279041109 2579499203134037124363763)
                ·
                  refine ⟨3869248804701055686545645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2579499203134037124363763 3869248804701055686545645)
                  ·
                    refine ⟨1450968301762895882454617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3869248804701055686545645 1450968301762895882454617)
                    ·
                      refine ⟨1088226226322171911840963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1450968301762895882454617 1088226226322171911840963)
                      ·
                        rfl

theorem cell23_2119313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 3, 2].length) (baseStart_2119313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2119313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2119313 prefixEnd_2119313 := by exact prefixLift 2119313
  have htrace : WordTrace (prefixWord ++ tailWord_2119313) baseStart_2119313 baseEnd_2119313 := by
    simpa [prefixWord, tailWord_2119313, baseEnd_2119313] using wordTrace_append hprefix tailTrace_2119313
  have hstable : (prefixWord ++ tailWord_2119313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2119313).length < 2 ^ (prefixWord ++ tailWord_2119313).sum := by decide
  have hdescent : baseEnd_2119313 < baseStart_2119313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2119313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2119346 : List Nat := [3, 2, 1, 1, 1, 2, 3, 1, 2, 4, 3]
def baseStart_2119346 : Nat := 118140960795 + 2119346 * 2 ^ 59
def prefixEnd_2119346 : Nat := 4983230072969 + 3 ^ 40 * 2119346 * 2
def baseEnd_2119346 : Nat := 1088243171183770282728311

theorem tailTrace_2119346 : CollatzResearch.WordTrace tailWord_2119346 prefixEnd_2119346 1088243171183770282728311 := by
  unfold tailWord_2119346
  simp only [CollatzResearch.WordTrace]
  refine ⟨19324724744994718081290473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51532599319985914883441261 19324724744994718081290473)
  ·
    refine ⟨14493543558746038560967855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19324724744994718081290473 14493543558746038560967855)
    ·
      refine ⟨21740315338119057841451783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14493543558746038560967855 21740315338119057841451783)
      ·
        refine ⟨32610473007178586762177675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21740315338119057841451783 32610473007178586762177675)
        ·
          refine ⟨48915709510767880143266513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32610473007178586762177675 48915709510767880143266513)
          ·
            refine ⟨36686782133075910107449885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48915709510767880143266513 36686782133075910107449885)
            ·
              refine ⟨13757543299903466290293707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36686782133075910107449885 13757543299903466290293707)
              ·
                refine ⟨20636314949855199435440561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13757543299903466290293707 20636314949855199435440561)
                ·
                  refine ⟨15477236212391399576580421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20636314949855199435440561 15477236212391399576580421)
                  ·
                    refine ⟨2901981789823387420608829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15477236212391399576580421 2901981789823387420608829)
                    ·
                      refine ⟨1088243171183770282728311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2901981789823387420608829 1088243171183770282728311)
                      ·
                        rfl

theorem cell23_2119346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 2, 4, 3].length) (baseStart_2119346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2119346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2119346 prefixEnd_2119346 := by exact prefixLift 2119346
  have htrace : WordTrace (prefixWord ++ tailWord_2119346) baseStart_2119346 baseEnd_2119346 := by
    simpa [prefixWord, tailWord_2119346, baseEnd_2119346] using wordTrace_append hprefix tailTrace_2119346
  have hstable : (prefixWord ++ tailWord_2119346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2119346).length < 2 ^ (prefixWord ++ tailWord_2119346).sum := by decide
  have hdescent : baseEnd_2119346 < baseStart_2119346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2119346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2119356 : List Nat := [2, 2, 2, 3, 1, 2, 1, 1, 1, 4, 4]
def baseStart_2119356 : Nat := 118140960795 + 2119356 * 2 ^ 59
def prefixEnd_2119356 : Nat := 4983230072969 + 3 ^ 40 * 2119356 * 2
def baseEnd_2119356 : Nat := 1088248305990315243603265

theorem tailTrace_2119356 : CollatzResearch.WordTrace tailWord_2119356 prefixEnd_2119356 1088248305990315243603265 := by
  unfold tailWord_2119356
  simp only [CollatzResearch.WordTrace]
  refine ⟨38649631854971322016512961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51532842473295096022017281 38649631854971322016512961)
  ·
    refine ⟨28987223891228491512384721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38649631854971322016512961 28987223891228491512384721)
    ·
      refine ⟨21740417918421368634288541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28987223891228491512384721 21740417918421368634288541)
      ·
        refine ⟨8152656719408013237858203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21740417918421368634288541 8152656719408013237858203)
        ·
          refine ⟨12228985079112019856787305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8152656719408013237858203 12228985079112019856787305)
          ·
            refine ⟨9171738809334014892590479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12228985079112019856787305 9171738809334014892590479)
            ·
              refine ⟨13757608214001022338885719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9171738809334014892590479 13757608214001022338885719)
              ·
                refine ⟨20636412321001533508328579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13757608214001022338885719 20636412321001533508328579)
                ·
                  refine ⟨30954618481502300262492869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20636412321001533508328579 30954618481502300262492869)
                  ·
                    refine ⟨5803990965281681299217413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30954618481502300262492869 5803990965281681299217413)
                    ·
                      refine ⟨1088248305990315243603265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5803990965281681299217413 1088248305990315243603265)
                      ·
                        rfl

theorem cell23_2119356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_2119356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2119356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2119356 prefixEnd_2119356 := by exact prefixLift 2119356
  have htrace : WordTrace (prefixWord ++ tailWord_2119356) baseStart_2119356 baseEnd_2119356 := by
    simpa [prefixWord, tailWord_2119356, baseEnd_2119356] using wordTrace_append hprefix tailTrace_2119356
  have hstable : (prefixWord ++ tailWord_2119356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2119356).length < 2 ^ (prefixWord ++ tailWord_2119356).sum := by decide
  have hdescent : baseEnd_2119356 < baseStart_2119356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2119356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2119360 : List Nat := [2, 1, 1, 2, 4, 1, 1, 5, 2, 2, 2]
def baseStart_2119360 : Nat := 118140960795 + 2119360 * 2 ^ 59
def prefixEnd_2119360 : Nat := 4983230072969 + 3 ^ 40 * 2119360 * 2
def baseEnd_2119360 : Nat := 1088250359912933227953247

theorem tailTrace_2119360 : CollatzResearch.WordTrace tailWord_2119360 prefixEnd_2119360 1088250359912933227953247 := by
  unfold tailWord_2119360
  simp only [CollatzResearch.WordTrace]
  refine ⟨38649704800964076358085767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51532939734618768477447689 38649704800964076358085767)
  ·
    refine ⟨57974557201446114537128651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38649704800964076358085767 57974557201446114537128651)
    ·
      refine ⟨86961835802169171805692977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57974557201446114537128651 86961835802169171805692977)
      ·
        refine ⟨65221376851626878854269733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86961835802169171805692977 65221376851626878854269733)
        ·
          refine ⟨12229008159680039785175575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65221376851626878854269733 12229008159680039785175575)
          ·
            refine ⟨18343512239520059677763363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12229008159680039785175575 18343512239520059677763363)
            ·
              refine ⟨27515268359280089516645045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18343512239520059677763363 27515268359280089516645045)
              ·
                refine ⟨2579556408682508392185473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27515268359280089516645045 2579556408682508392185473)
                ·
                  refine ⟨1934667306511881294139105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2579556408682508392185473 1934667306511881294139105)
                  ·
                    refine ⟨1451000479883910970604329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1934667306511881294139105 1451000479883910970604329)
                    ·
                      refine ⟨1088250359912933227953247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1451000479883910970604329 1088250359912933227953247)
                      ·
                        rfl

theorem cell23_2119360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 5, 2, 2, 2].length) (baseStart_2119360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2119360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2119360 prefixEnd_2119360 := by exact prefixLift 2119360
  have htrace : WordTrace (prefixWord ++ tailWord_2119360) baseStart_2119360 baseEnd_2119360 := by
    simpa [prefixWord, tailWord_2119360, baseEnd_2119360] using wordTrace_append hprefix tailTrace_2119360
  have hstable : (prefixWord ++ tailWord_2119360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2119360).length < 2 ^ (prefixWord ++ tailWord_2119360).sum := by decide
  have hdescent : baseEnd_2119360 < baseStart_2119360 := by decide
  rcases family_descends (prefixWord ++ tailWord_2119360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2119383 : List Nat := [1, 1, 3, 2, 1, 3, 4, 3, 5]
def baseStart_2119383 : Nat := 118140960795 + 2119383 * 2 ^ 59
def prefixEnd_2119383 : Nat := 4983230072969 + 3 ^ 40 * 2119383 * 2
def baseEnd_2119383 : Nat := 120918018885331848662849

theorem tailTrace_2119383 : CollatzResearch.WordTrace tailWord_2119383 prefixEnd_2119383 120918018885331848662849 := by
  unfold tailWord_2119383
  simp only [CollatzResearch.WordTrace]
  refine ⟨77300248480844827644258803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51533498987229885096172535 77300248480844827644258803)
  ·
    refine ⟨115950372721267241466388205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77300248480844827644258803 115950372721267241466388205)
    ·
      refine ⟨43481389770475215549895577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115950372721267241466388205 43481389770475215549895577)
      ·
        refine ⟨32611042327856411662421683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43481389770475215549895577 32611042327856411662421683)
        ·
          refine ⟨48916563491784617493632525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32611042327856411662421683 48916563491784617493632525)
          ·
            refine ⟨18343711309419231560112197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48916563491784617493632525 18343711309419231560112197)
            ·
              refine ⟨3439445870516105917521037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18343711309419231560112197 3439445870516105917521037)
              ·
                refine ⟨1289792201443539719070389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3439445870516105917521037 1289792201443539719070389)
                ·
                  refine ⟨120918018885331848662849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1289792201443539719070389 120918018885331848662849)
                  ·
                    rfl

theorem cell23_2119383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 3, 5].length) (baseStart_2119383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2119383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2119383 prefixEnd_2119383 := by exact prefixLift 2119383
  have htrace : WordTrace (prefixWord ++ tailWord_2119383) baseStart_2119383 baseEnd_2119383 := by
    simpa [prefixWord, tailWord_2119383, baseEnd_2119383] using wordTrace_append hprefix tailTrace_2119383
  have hstable : (prefixWord ++ tailWord_2119383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2119383).length < 2 ^ (prefixWord ++ tailWord_2119383).sum := by decide
  have hdescent : baseEnd_2119383 < baseStart_2119383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2119383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2119396 : List Nat := [2, 3, 1, 1, 1, 3, 2, 1, 4, 5]
def baseStart_2119396 : Nat := 118140960795 + 2119396 * 2 ^ 59
def prefixEnd_2119396 : Nat := 4983230072969 + 3 ^ 40 * 2119396 * 2
def baseEnd_2119396 : Nat := 362756281738831695701027

theorem tailTrace_2119396 : CollatzResearch.WordTrace tailWord_2119396 prefixEnd_2119396 362756281738831695701027 := by
  unfold tailWord_2119396
  simp only [CollatzResearch.WordTrace]
  refine ⟨38650361314898865432241021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51533815086531820576321361 38650361314898865432241021)
  ·
    refine ⟨14493885493087074537090383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38650361314898865432241021 14493885493087074537090383)
    ·
      refine ⟨21740828239630611805635575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14493885493087074537090383 21740828239630611805635575)
      ·
        refine ⟨32611242359445917708453363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21740828239630611805635575 32611242359445917708453363)
        ·
          refine ⟨48916863539168876562680045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32611242359445917708453363 48916863539168876562680045)
          ·
            refine ⟨18343823827188328711005017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48916863539168876562680045 18343823827188328711005017)
            ·
              refine ⟨13757867870391246533253763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18343823827188328711005017 13757867870391246533253763)
              ·
                refine ⟨20636801805586869799880645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13757867870391246533253763 20636801805586869799880645)
                ·
                  refine ⟨3869400338547538087477621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20636801805586869799880645 3869400338547538087477621)
                  ·
                    refine ⟨362756281738831695701027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3869400338547538087477621 362756281738831695701027)
                    ·
                      rfl

theorem cell23_2119396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 4, 5].length) (baseStart_2119396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2119396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2119396 prefixEnd_2119396 := by exact prefixLift 2119396
  have htrace : WordTrace (prefixWord ++ tailWord_2119396) baseStart_2119396 baseEnd_2119396 := by
    simpa [prefixWord, tailWord_2119396, baseEnd_2119396] using wordTrace_append hprefix tailTrace_2119396
  have hstable : (prefixWord ++ tailWord_2119396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2119396).length < 2 ^ (prefixWord ++ tailWord_2119396).sum := by decide
  have hdescent : baseEnd_2119396 < baseStart_2119396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2119396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2119406 : List Nat := [4, 1, 2, 1, 1, 2, 2, 1, 1, 1, 7]
def baseStart_2119406 : Nat := 118140960795 + 2119406 * 2 ^ 59
def prefixEnd_2119406 : Nat := 4983230072969 + 3 ^ 40 * 2119406 * 2
def baseEnd_2119406 : Nat := 1088273980023040047978035

theorem tailTrace_2119406 : CollatzResearch.WordTrace tailWord_2119406 prefixEnd_2119406 1088273980023040047978035 := by
  unfold tailWord_2119406
  simp only [CollatzResearch.WordTrace]
  refine ⟨9662635919970187821543259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51534058239841001714897381 9662635919970187821543259)
  ·
    refine ⟨14493953879955281732314889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9662635919970187821543259 14493953879955281732314889)
    ·
      refine ⟨10870465409966461299236167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14493953879955281732314889 10870465409966461299236167)
      ·
        refine ⟨16305698114949691948854251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10870465409966461299236167 16305698114949691948854251)
        ·
          refine ⟨24458547172424537923281377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16305698114949691948854251 24458547172424537923281377)
          ·
            refine ⟨18343910379318403442461033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24458547172424537923281377 18343910379318403442461033)
            ·
              refine ⟨13757932784488802581845775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18343910379318403442461033 13757932784488802581845775)
              ·
                refine ⟨20636899176733203872768663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13757932784488802581845775 20636899176733203872768663)
                ·
                  refine ⟨30955348765099805809152995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20636899176733203872768663 30955348765099805809152995)
                  ·
                    refine ⟨46433023147649708713729493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30955348765099805809152995 46433023147649708713729493)
                    ·
                      refine ⟨1088273980023040047978035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 46433023147649708713729493 1088273980023040047978035)
                      ·
                        rfl

theorem cell23_2119406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_2119406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2119406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2119406 prefixEnd_2119406 := by exact prefixLift 2119406
  have htrace : WordTrace (prefixWord ++ tailWord_2119406) baseStart_2119406 baseEnd_2119406 := by
    simpa [prefixWord, tailWord_2119406, baseEnd_2119406] using wordTrace_append hprefix tailTrace_2119406
  have hstable : (prefixWord ++ tailWord_2119406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2119406).length < 2 ^ (prefixWord ++ tailWord_2119406).sum := by decide
  have hdescent : baseEnd_2119406 < baseStart_2119406 := by decide
  rcases family_descends (prefixWord ++ tailWord_2119406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2119416 : List Nat := [2, 1, 2, 1, 1, 2, 2, 1, 6, 1, 4]
def baseStart_2119416 : Nat := 118140960795 + 2119416 * 2 ^ 59
def prefixEnd_2119416 : Nat := 4983230072969 + 3 ^ 40 * 2119416 * 2
def baseEnd_2119416 : Nat := 1088279114829585008852989

theorem tailTrace_2119416 : CollatzResearch.WordTrace tailWord_2119416 prefixEnd_2119416 1088279114829585008852989 := by
  unfold tailWord_2119416
  simp only [CollatzResearch.WordTrace]
  refine ⟨38650726044862637140105051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51534301393150182853473401 38650726044862637140105051)
  ·
    refine ⟨57976089067293955710157577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38650726044862637140105051 57976089067293955710157577)
    ·
      refine ⟨43482066800470466782618183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57976089067293955710157577 43482066800470466782618183)
      ·
        refine ⟨65223100200705700173927275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43482066800470466782618183 65223100200705700173927275)
        ·
          refine ⟨97834650301058550260890913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65223100200705700173927275 97834650301058550260890913)
          ·
            refine ⟨73375987725793912695668185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97834650301058550260890913 73375987725793912695668185)
            ·
              refine ⟨55031990794345434521751139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73375987725793912695668185 55031990794345434521751139)
              ·
                refine ⟨82547986191518151782626709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55031990794345434521751139 82547986191518151782626709)
                ·
                  refine ⟨3869436852727413364810627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 82547986191518151782626709 3869436852727413364810627)
                  ·
                    refine ⟨5804155279091120047215941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3869436852727413364810627 5804155279091120047215941)
                    ·
                      refine ⟨1088279114829585008852989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5804155279091120047215941 1088279114829585008852989)
                      ·
                        rfl

theorem cell23_2119416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 6, 1, 4].length) (baseStart_2119416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2119416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2119416 prefixEnd_2119416 := by exact prefixLift 2119416
  have htrace : WordTrace (prefixWord ++ tailWord_2119416) baseStart_2119416 baseEnd_2119416 := by
    simpa [prefixWord, tailWord_2119416, baseEnd_2119416] using wordTrace_append hprefix tailTrace_2119416
  have hstable : (prefixWord ++ tailWord_2119416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2119416).length < 2 ^ (prefixWord ++ tailWord_2119416).sum := by decide
  have hdescent : baseEnd_2119416 < baseStart_2119416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2119416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2119456 : List Nat := [2, 1, 1, 5, 1, 1, 1, 3, 8]
def baseStart_2119456 : Nat := 118140960795 + 2119456 * 2 ^ 59
def prefixEnd_2119456 : Nat := 4983230072969 + 3 ^ 40 * 2119456 * 2
def baseEnd_2119456 : Nat := 120922183783973872483645

theorem tailTrace_2119456 : CollatzResearch.WordTrace tailWord_2119456 prefixEnd_2119456 120922183783973872483645 := by
  unfold tailWord_2119456
  simp only [CollatzResearch.WordTrace]
  refine ⟨38651455504790180555833111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51535274006386907407777481 38651455504790180555833111)
  ·
    refine ⟨57977183257185270833749667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38651455504790180555833111 57977183257185270833749667)
    ·
      refine ⟨86965774885777906250624501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57977183257185270833749667 86965774885777906250624501)
      ·
        refine ⟨8153041395541678710996047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 86965774885777906250624501 8153041395541678710996047)
        ·
          refine ⟨12229562093312518066494071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8153041395541678710996047 12229562093312518066494071)
          ·
            refine ⟨18344343139968777099741107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12229562093312518066494071 18344343139968777099741107)
            ·
              refine ⟨27516514709953165649611661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18344343139968777099741107 27516514709953165649611661)
              ·
                refine ⟨10318693016232437118604373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27516514709953165649611661 10318693016232437118604373)
                ·
                  refine ⟨120922183783973872483645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10318693016232437118604373 120922183783973872483645)
                  ·
                    rfl

theorem cell23_2119456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 3, 8].length) (baseStart_2119456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2119456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2119456 prefixEnd_2119456 := by exact prefixLift 2119456
  have htrace : WordTrace (prefixWord ++ tailWord_2119456) baseStart_2119456 baseEnd_2119456 := by
    simpa [prefixWord, tailWord_2119456, baseEnd_2119456] using wordTrace_append hprefix tailTrace_2119456
  have hstable : (prefixWord ++ tailWord_2119456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2119456).length < 2 ^ (prefixWord ++ tailWord_2119456).sum := by decide
  have hdescent : baseEnd_2119456 < baseStart_2119456 := by decide
  rcases family_descends (prefixWord ++ tailWord_2119456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2119460 : List Nat := [2, 3, 1, 3, 2, 1, 3, 1, 3, 4]
def baseStart_2119460 : Nat := 118140960795 + 2119460 * 2 ^ 59
def prefixEnd_2119460 : Nat := 4983230072969 + 3 ^ 40 * 2119460 * 2
def baseEnd_2119460 : Nat := 362767235992794278900929

theorem tailTrace_2119460 : CollatzResearch.WordTrace tailWord_2119460 prefixEnd_2119460 362767235992794278900929 := by
  unfold tailWord_2119460
  simp only [CollatzResearch.WordTrace]
  refine ⟨38651528450782934897405917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51535371267710579863207889 38651528450782934897405917)
  ·
    refine ⟨14494323169043600586527219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38651528450782934897405917 14494323169043600586527219)
    ·
      refine ⟨21741484753565400879790829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14494323169043600586527219 21741484753565400879790829)
      ·
        refine ⟨8153056782587025329921561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21741484753565400879790829 8153056782587025329921561)
        ·
          refine ⟨6114792586940268997441171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8153056782587025329921561 6114792586940268997441171)
          ·
            refine ⟨9172188880410403496161757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6114792586940268997441171 9172188880410403496161757)
            ·
              refine ⟨3439570830153901311060659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9172188880410403496161757 3439570830153901311060659)
              ·
                refine ⟨5159356245230851966590989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3439570830153901311060659 5159356245230851966590989)
                ·
                  refine ⟨1934758591961569487471621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5159356245230851966590989 1934758591961569487471621)
                  ·
                    refine ⟨362767235992794278900929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1934758591961569487471621 362767235992794278900929)
                    ·
                      rfl

theorem cell23_2119460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 1, 3, 4].length) (baseStart_2119460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2119460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2119460 prefixEnd_2119460 := by exact prefixLift 2119460
  have htrace : WordTrace (prefixWord ++ tailWord_2119460) baseStart_2119460 baseEnd_2119460 := by
    simpa [prefixWord, tailWord_2119460, baseEnd_2119460] using wordTrace_append hprefix tailTrace_2119460
  have hstable : (prefixWord ++ tailWord_2119460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2119460).length < 2 ^ (prefixWord ++ tailWord_2119460).sum := by decide
  have hdescent : baseEnd_2119460 < baseStart_2119460 := by decide
  rcases family_descends (prefixWord ++ tailWord_2119460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2119473 : List Nat := [1, 2, 2, 3, 2, 3, 1, 3, 6]
def baseStart_2119473 : Nat := 118140960795 + 2119473 * 2 ^ 59
def prefixEnd_2119473 : Nat := 4983230072969 + 3 ^ 40 * 2119473 * 2
def baseEnd_2119473 : Nat := 120923153691876809537803

theorem tailTrace_2119473 : CollatzResearch.WordTrace tailWord_2119473 prefixEnd_2119473 120923153691876809537803 := by
  unfold tailWord_2119473
  simp only [CollatzResearch.WordTrace]
  refine ⟨77303531050518773015035073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51535687367012515343356715 77303531050518773015035073)
  ·
    refine ⟨57977648287889079761276305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77303531050518773015035073 57977648287889079761276305)
    ·
      refine ⟨43483236215916809820957229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57977648287889079761276305 43483236215916809820957229)
      ·
        refine ⟨16306213580968803682858961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43483236215916809820957229 16306213580968803682858961)
        ·
          refine ⟨12229660185726602762144221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16306213580968803682858961 12229660185726602762144221)
          ·
            refine ⟨4586122569647476035804083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12229660185726602762144221 4586122569647476035804083)
            ·
              refine ⟨6879183854471214053706125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4586122569647476035804083 6879183854471214053706125)
              ·
                refine ⟨2579693945426705270139797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6879183854471214053706125 2579693945426705270139797)
                ·
                  refine ⟨120923153691876809537803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2579693945426705270139797 120923153691876809537803)
                  ·
                    rfl

theorem cell23_2119473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 3, 6].length) (baseStart_2119473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2119473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2119473 prefixEnd_2119473 := by exact prefixLift 2119473
  have htrace : WordTrace (prefixWord ++ tailWord_2119473) baseStart_2119473 baseEnd_2119473 := by
    simpa [prefixWord, tailWord_2119473, baseEnd_2119473] using wordTrace_append hprefix tailTrace_2119473
  have hstable : (prefixWord ++ tailWord_2119473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2119473).length < 2 ^ (prefixWord ++ tailWord_2119473).sum := by decide
  have hdescent : baseEnd_2119473 < baseStart_2119473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2119473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2119511 : List Nat := [1, 1, 3, 2, 6, 1, 2, 2, 1, 4]
def baseStart_2119511 : Nat := 118140960795 + 2119511 * 2 ^ 59
def prefixEnd_2119511 : Nat := 4983230072969 + 3 ^ 40 * 2119511 * 2
def baseEnd_2119511 : Nat := 362775965163920712388351

theorem tailTrace_2119511 : CollatzResearch.WordTrace tailWord_2119511 prefixEnd_2119511 362775965163920712388351 := by
  unfold tailWord_2119511
  simp only [CollatzResearch.WordTrace]
  refine ⟨77304917024381105504918387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51536611349587403669945591 77304917024381105504918387)
  ·
    refine ⟨115957375536571658257377581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77304917024381105504918387 115957375536571658257377581)
    ·
      refine ⟨43484015826214371846516593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115957375536571658257377581 43484015826214371846516593)
      ·
        refine ⟨32613011869660778884887445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43484015826214371846516593 32613011869660778884887445)
        ·
          refine ⟨1528734931390349010229099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 32613011869660778884887445 1528734931390349010229099)
          ·
            refine ⟨2293102397085523515343649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1528734931390349010229099 2293102397085523515343649)
            ·
              refine ⟨1719826797814142636507737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2293102397085523515343649 1719826797814142636507737)
              ·
                refine ⟨1289870098360606977380803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1719826797814142636507737 1289870098360606977380803)
                ·
                  refine ⟨1934805147540910466071205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1289870098360606977380803 1934805147540910466071205)
                  ·
                    refine ⟨362775965163920712388351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1934805147540910466071205 362775965163920712388351)
                    ·
                      rfl

theorem cell23_2119511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 2, 2, 1, 4].length) (baseStart_2119511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2119511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2119511 prefixEnd_2119511 := by exact prefixLift 2119511
  have htrace : WordTrace (prefixWord ++ tailWord_2119511) baseStart_2119511 baseEnd_2119511 := by
    simpa [prefixWord, tailWord_2119511, baseEnd_2119511] using wordTrace_append hprefix tailTrace_2119511
  have hstable : (prefixWord ++ tailWord_2119511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2119511).length < 2 ^ (prefixWord ++ tailWord_2119511).sum := by decide
  have hdescent : baseEnd_2119511 < baseStart_2119511 := by decide
  rcases family_descends (prefixWord ++ tailWord_2119511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2119533 : List Nat := [1, 5, 1, 1, 1, 1, 3, 3, 1, 6]
def baseStart_2119533 : Nat := 118140960795 + 2119533 * 2 ^ 59
def prefixEnd_2119533 : Nat := 4983230072969 + 3 ^ 40 * 2119533 * 2
def baseEnd_2119533 : Nat := 362779730688720350363317

theorem tailTrace_2119533 : CollatzResearch.WordTrace tailWord_2119533 prefixEnd_2119533 362779730688720350363317 := by
  unfold tailWord_2119533
  simp only [CollatzResearch.WordTrace]
  refine ⟨77305719430301403262219253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51537146286867602174812835 77305719430301403262219253)
  ·
    refine ⟨7247411196590756555833055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 77305719430301403262219253 7247411196590756555833055)
    ·
      refine ⟨10871116794886134833749583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7247411196590756555833055 10871116794886134833749583)
      ·
        refine ⟨16306675192329202250624375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10871116794886134833749583 16306675192329202250624375)
        ·
          refine ⟨24460012788493803375936563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16306675192329202250624375 24460012788493803375936563)
          ·
            refine ⟨36690019182740705063904845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24460012788493803375936563 36690019182740705063904845)
            ·
              refine ⟨13758757193527764398964317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36690019182740705063904845 13758757193527764398964317)
              ·
                refine ⟨5159533947572911649611619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13758757193527764398964317 5159533947572911649611619)
                ·
                  refine ⟨7739300921359367474417429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5159533947572911649611619 7739300921359367474417429)
                  ·
                    refine ⟨362779730688720350363317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7739300921359367474417429 362779730688720350363317)
                    ·
                      rfl

theorem cell23_2119533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 3, 1, 6].length) (baseStart_2119533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2119533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2119533 prefixEnd_2119533 := by exact prefixLift 2119533
  have htrace : WordTrace (prefixWord ++ tailWord_2119533) baseStart_2119533 baseEnd_2119533 := by
    simpa [prefixWord, tailWord_2119533, baseEnd_2119533] using wordTrace_append hprefix tailTrace_2119533
  have hstable : (prefixWord ++ tailWord_2119533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2119533).length < 2 ^ (prefixWord ++ tailWord_2119533).sum := by decide
  have hdescent : baseEnd_2119533 < baseStart_2119533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2119533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2119546 : List Nat := [3, 1, 1, 1, 1, 1, 4, 11]
def baseStart_2119546 : Nat := 118140960795 + 2119546 * 2 ^ 59
def prefixEnd_2119546 : Nat := 4983230072969 + 3 ^ 40 * 2119546 * 2
def baseEnd_2119546 : Nat := 40309106196839611119533

theorem tailTrace_2119546 : CollatzResearch.WordTrace tailWord_2119546 prefixEnd_2119546 40309106196839611119533 := by
  unfold tailWord_2119546
  simp only [CollatzResearch.WordTrace]
  refine ⟨19326548394813576620610623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51537462386169537654961661 19326548394813576620610623)
  ·
    refine ⟨28989822592220364930915935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19326548394813576620610623 28989822592220364930915935)
    ·
      refine ⟨43484733888330547396373903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28989822592220364930915935 43484733888330547396373903)
      ·
        refine ⟨65227100832495821094560855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43484733888330547396373903 65227100832495821094560855)
        ·
          refine ⟨97840651248743731641841283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65227100832495821094560855 97840651248743731641841283)
          ·
            refine ⟨146760976873115597462761925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97840651248743731641841283 146760976873115597462761925)
            ·
              refine ⟨27517683163709174524267861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 146760976873115597462761925 27517683163709174524267861)
              ·
                refine ⟨40309106196839611119533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 27517683163709174524267861 40309106196839611119533)
                ·
                  rfl

theorem cell23_2119546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 11].length) (baseStart_2119546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2119546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2119546 prefixEnd_2119546 := by exact prefixLift 2119546
  have htrace : WordTrace (prefixWord ++ tailWord_2119546) baseStart_2119546 baseEnd_2119546 := by
    simpa [prefixWord, tailWord_2119546, baseEnd_2119546] using wordTrace_append hprefix tailTrace_2119546
  have hstable : (prefixWord ++ tailWord_2119546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2119546).length < 2 ^ (prefixWord ++ tailWord_2119546).sum := by decide
  have hdescent : baseEnd_2119546 < baseStart_2119546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2119546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2119641 : List Nat := [1, 2, 1, 2, 6, 2, 2, 1, 2, 1, 3]
def baseStart_2119641 : Nat := 118140960795 + 2119641 * 2 ^ 59
def prefixEnd_2119641 : Nat := 4983230072969 + 3 ^ 40 * 2119641 * 2
def baseEnd_2119641 : Nat := 1088394647976846628539455

theorem tailTrace_2119641 : CollatzResearch.WordTrace tailWord_2119641 prefixEnd_2119641 1088394647976846628539455 := by
  unfold tailWord_2119641
  simp only [CollatzResearch.WordTrace]
  refine ⟨77309658513910137707150777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51539772342606758471433851 77309658513910137707150777)
  ·
    refine ⟨57982243885432603280363083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77309658513910137707150777 57982243885432603280363083)
    ·
      refine ⟨86973365828148904920544625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57982243885432603280363083 86973365828148904920544625)
      ·
        refine ⟨65230024371111678690408469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86973365828148904920544625 65230024371111678690408469)
        ·
          refine ⟨3057657392395859938612897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 65230024371111678690408469 3057657392395859938612897)
          ·
            refine ⟨2293243044296894953959673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3057657392395859938612897 2293243044296894953959673)
            ·
              refine ⟨1719932283222671215469755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2293243044296894953959673 1719932283222671215469755)
              ·
                refine ⟨2579898424834006823204633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1719932283222671215469755 2579898424834006823204633)
                ·
                  refine ⟨1934923818625505117403475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2579898424834006823204633 1934923818625505117403475)
                  ·
                    refine ⟨2902385727938257676105213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1934923818625505117403475 2902385727938257676105213)
                    ·
                      refine ⟨1088394647976846628539455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2902385727938257676105213 1088394647976846628539455)
                      ·
                        rfl

theorem cell23_2119641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 2, 1, 2, 1, 3].length) (baseStart_2119641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2119641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2119641 prefixEnd_2119641 := by exact prefixLift 2119641
  have htrace : WordTrace (prefixWord ++ tailWord_2119641) baseStart_2119641 baseEnd_2119641 := by
    simpa [prefixWord, tailWord_2119641, baseEnd_2119641] using wordTrace_append hprefix tailTrace_2119641
  have hstable : (prefixWord ++ tailWord_2119641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2119641).length < 2 ^ (prefixWord ++ tailWord_2119641).sum := by decide
  have hdescent : baseEnd_2119641 < baseStart_2119641 := by decide
  rcases family_descends (prefixWord ++ tailWord_2119641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2119687 : List Nat := [1, 1, 4, 3, 1, 3, 1, 4, 5]
def baseStart_2119687 : Nat := 118140960795 + 2119687 * 2 ^ 59
def prefixEnd_2119687 : Nat := 4983230072969 + 3 ^ 40 * 2119687 * 2
def baseEnd_2119687 : Nat := 120935363120772605396027

theorem tailTrace_2119687 : CollatzResearch.WordTrace tailWord_2119687 prefixEnd_2119687 120935363120772605396027 := by
  unfold tailWord_2119687
  simp only [CollatzResearch.WordTrace]
  refine ⟨77311336271743487563325315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51540890847828991708883543 77311336271743487563325315)
  ·
    refine ⟨115967004407615231344987973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77311336271743487563325315 115967004407615231344987973)
    ·
      refine ⟨21743813326427855877185245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 115967004407615231344987973 21743813326427855877185245)
      ·
        refine ⟨8153929997410445953944467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21743813326427855877185245 8153929997410445953944467)
        ·
          refine ⟨12230894996115668930916701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8153929997410445953944467 12230894996115668930916701)
          ·
            refine ⟨4586585623543375849093763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12230894996115668930916701 4586585623543375849093763)
            ·
              refine ⟨6879878435315063773640645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4586585623543375849093763 6879878435315063773640645)
              ·
                refine ⟨1289977206621574457557621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6879878435315063773640645 1289977206621574457557621)
                ·
                  refine ⟨120935363120772605396027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1289977206621574457557621 120935363120772605396027)
                  ·
                    rfl

theorem cell23_2119687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 4, 5].length) (baseStart_2119687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2119687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2119687 prefixEnd_2119687 := by exact prefixLift 2119687
  have htrace : WordTrace (prefixWord ++ tailWord_2119687) baseStart_2119687 baseEnd_2119687 := by
    simpa [prefixWord, tailWord_2119687, baseEnd_2119687] using wordTrace_append hprefix tailTrace_2119687
  have hstable : (prefixWord ++ tailWord_2119687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2119687).length < 2 ^ (prefixWord ++ tailWord_2119687).sum := by decide
  have hdescent : baseEnd_2119687 < baseStart_2119687 := by decide
  rcases family_descends (prefixWord ++ tailWord_2119687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2119717 : List Nat := [1, 3, 1, 2, 2, 5, 1, 1, 2, 5]
def baseStart_2119717 : Nat := 118140960795 + 2119717 * 2 ^ 59
def prefixEnd_2119717 : Nat := 4983230072969 + 3 ^ 40 * 2119717 * 2
def baseEnd_2119717 : Nat := 362811224168862777063035

theorem tailTrace_2119717 : CollatzResearch.WordTrace tailWord_2119717 prefixEnd_2119717 362811224168862777063035 := by
  unfold tailWord_2119717
  simp only [CollatzResearch.WordTrace]
  refine ⟨77312430461634802686917405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51541620307756535124611603 77312430461634802686917405)
  ·
    refine ⟨28992161423113051007594027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77312430461634802686917405 28992161423113051007594027)
    ·
      refine ⟨43488242134669576511391041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28992161423113051007594027 43488242134669576511391041)
      ·
        refine ⟨32616181601002182383543281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43488242134669576511391041 32616181601002182383543281)
        ·
          refine ⟨24462136200751636787657461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32616181601002182383543281 24462136200751636787657461)
          ·
            refine ⟨2293325268820465948842887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24462136200751636787657461 2293325268820465948842887)
            ·
              refine ⟨3439987903230698923264331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2293325268820465948842887 3439987903230698923264331)
              ·
                refine ⟨5159981854846048384896497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3439987903230698923264331 5159981854846048384896497)
                ·
                  refine ⟨3869986391134536288672373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5159981854846048384896497 3869986391134536288672373)
                  ·
                    refine ⟨362811224168862777063035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3869986391134536288672373 362811224168862777063035)
                    ·
                      rfl

theorem cell23_2119717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 1, 2, 5].length) (baseStart_2119717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2119717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2119717 prefixEnd_2119717 := by exact prefixLift 2119717
  have htrace : WordTrace (prefixWord ++ tailWord_2119717) baseStart_2119717 baseEnd_2119717 := by
    simpa [prefixWord, tailWord_2119717, baseEnd_2119717] using wordTrace_append hprefix tailTrace_2119717
  have hstable : (prefixWord ++ tailWord_2119717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2119717).length < 2 ^ (prefixWord ++ tailWord_2119717).sum := by decide
  have hdescent : baseEnd_2119717 < baseStart_2119717 := by decide
  rcases family_descends (prefixWord ++ tailWord_2119717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2119723 : List Nat := [1, 1, 1, 1, 2, 1, 4, 2, 2, 3, 5]
def baseStart_2119723 : Nat := 118140960795 + 2119723 * 2 ^ 59
def prefixEnd_2119723 : Nat := 4983230072969 + 3 ^ 40 * 2119723 * 2
def baseEnd_2119723 : Nat := 1088436753390515307714077

theorem tailTrace_2119723 : CollatzResearch.WordTrace tailWord_2119723 prefixEnd_2119723 1088436753390515307714077 := by
  unfold tailWord_2119723
  simp only [CollatzResearch.WordTrace]
  refine ⟨77312649299613065711635823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51541766199742043807757215 77312649299613065711635823)
  ·
    refine ⟨115968973949419598567453735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77312649299613065711635823 115968973949419598567453735)
    ·
      refine ⟨173953460924129397851180603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115968973949419598567453735 173953460924129397851180603)
      ·
        refine ⟨260930191386194096776770905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173953460924129397851180603 260930191386194096776770905)
        ·
          refine ⟨195697643539645572582578179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 260930191386194096776770905 195697643539645572582578179)
          ·
            refine ⟨293546465309468358873867269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 195697643539645572582578179 293546465309468358873867269)
            ·
              refine ⟨55039962245525317288850113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 293546465309468358873867269 55039962245525317288850113)
              ·
                refine ⟨41279971684143987966637585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55039962245525317288850113 41279971684143987966637585)
                ·
                  refine ⟨30959978763107990974978189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41279971684143987966637585 30959978763107990974978189)
                  ·
                    refine ⟨11609992036165496615616821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30959978763107990974978189 11609992036165496615616821)
                    ·
                      refine ⟨1088436753390515307714077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11609992036165496615616821 1088436753390515307714077)
                      ·
                        rfl

theorem cell23_2119723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 3, 5].length) (baseStart_2119723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2119723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2119723 prefixEnd_2119723 := by exact prefixLift 2119723
  have htrace : WordTrace (prefixWord ++ tailWord_2119723) baseStart_2119723 baseEnd_2119723 := by
    simpa [prefixWord, tailWord_2119723, baseEnd_2119723] using wordTrace_append hprefix tailTrace_2119723
  have hstable : (prefixWord ++ tailWord_2119723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2119723).length < 2 ^ (prefixWord ++ tailWord_2119723).sum := by decide
  have hdescent : baseEnd_2119723 < baseStart_2119723 := by decide
  rcases family_descends (prefixWord ++ tailWord_2119723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2119757 : List Nat := [1, 6, 1, 1, 1, 1, 1, 1, 3, 4, 3]
def baseStart_2119757 : Nat := 118140960795 + 2119757 * 2 ^ 59
def prefixEnd_2119757 : Nat := 4983230072969 + 3 ^ 40 * 2119757 * 2
def baseEnd_2119757 : Nat := 1088454211732768174688921

theorem tailTrace_2119757 : CollatzResearch.WordTrace tailWord_2119757 prefixEnd_2119757 1088454211732768174688921 := by
  unfold tailWord_2119757
  simp only [CollatzResearch.WordTrace]
  refine ⟨77313889381489889518373525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51542592920993259678915683 77313889381489889518373525)
  ·
    refine ⟨3624088564757338571173759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 77313889381489889518373525 3624088564757338571173759)
    ·
      refine ⟨5436132847136007856760639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3624088564757338571173759 5436132847136007856760639)
      ·
        refine ⟨8154199270704011785140959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5436132847136007856760639 8154199270704011785140959)
        ·
          refine ⟨12231298906056017677711439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8154199270704011785140959 12231298906056017677711439)
          ·
            refine ⟨18346948359084026516567159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12231298906056017677711439 18346948359084026516567159)
            ·
              refine ⟨27520422538626039774850739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18346948359084026516567159 27520422538626039774850739)
              ·
                refine ⟨41280633807939059662276109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27520422538626039774850739 41280633807939059662276109)
                ·
                  refine ⟨15480237677977147373353541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41280633807939059662276109 15480237677977147373353541)
                  ·
                    refine ⟨2902544564620715132503789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15480237677977147373353541 2902544564620715132503789)
                    ·
                      refine ⟨1088454211732768174688921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2902544564620715132503789 1088454211732768174688921)
                      ·
                        rfl

theorem cell23_2119757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_2119757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2119757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2119757 prefixEnd_2119757 := by exact prefixLift 2119757
  have htrace : WordTrace (prefixWord ++ tailWord_2119757) baseStart_2119757 baseEnd_2119757 := by
    simpa [prefixWord, tailWord_2119757, baseEnd_2119757] using wordTrace_append hprefix tailTrace_2119757
  have hstable : (prefixWord ++ tailWord_2119757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2119757).length < 2 ^ (prefixWord ++ tailWord_2119757).sum := by decide
  have hdescent : baseEnd_2119757 < baseStart_2119757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2119757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2119763 : List Nat := [1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 8]
def baseStart_2119763 : Nat := 118140960795 + 2119763 * 2 ^ 59
def prefixEnd_2119763 : Nat := 4983230072969 + 3 ^ 40 * 2119763 * 2
def baseEnd_2119763 : Nat := 1088457292616695151213893

theorem tailTrace_2119763 : CollatzResearch.WordTrace tailWord_2119763 prefixEnd_2119763 1088457292616695151213893 := by
  unfold tailWord_2119763
  simp only [CollatzResearch.WordTrace]
  refine ⟨77314108219468152543091943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51542738812978768362061295 77314108219468152543091943)
  ·
    refine ⟨115971162329202228814637915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77314108219468152543091943 115971162329202228814637915)
    ·
      refine ⟨173956743493803343221956873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115971162329202228814637915 173956743493803343221956873)
      ·
        refine ⟨130467557620352507416467655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173956743493803343221956873 130467557620352507416467655)
        ·
          refine ⟨195701336430528761124701483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130467557620352507416467655 195701336430528761124701483)
          ·
            refine ⟨293552004645793141687052225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 195701336430528761124701483 293552004645793141687052225)
            ·
              refine ⟨220164003484344856265289169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 293552004645793141687052225 220164003484344856265289169)
              ·
                refine ⟨165123002613258642198966877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 220164003484344856265289169 165123002613258642198966877)
                ·
                  refine ⟨61921125979971990824612579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 165123002613258642198966877 61921125979971990824612579)
                  ·
                    refine ⟨92881688969957986236918869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 61921125979971990824612579 92881688969957986236918869)
                    ·
                      refine ⟨1088457292616695151213893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 92881688969957986236918869 1088457292616695151213893)
                      ·
                        rfl

theorem cell23_2119763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 8].length) (baseStart_2119763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2119763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2119763 prefixEnd_2119763 := by exact prefixLift 2119763
  have htrace : WordTrace (prefixWord ++ tailWord_2119763) baseStart_2119763 baseEnd_2119763 := by
    simpa [prefixWord, tailWord_2119763, baseEnd_2119763] using wordTrace_append hprefix tailTrace_2119763
  have hstable : (prefixWord ++ tailWord_2119763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2119763).length < 2 ^ (prefixWord ++ tailWord_2119763).sum := by decide
  have hdescent : baseEnd_2119763 < baseStart_2119763 := by decide
  rcases family_descends (prefixWord ++ tailWord_2119763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2119770 : List Nat := [3, 1, 1, 2, 1, 1, 3, 1, 2, 5, 3]
def baseStart_2119770 : Nat := 118140960795 + 2119770 * 2 ^ 59
def prefixEnd_2119770 : Nat := 4983230072969 + 3 ^ 40 * 2119770 * 2
def baseEnd_2119770 : Nat := 1088460886981276623826361

theorem tailTrace_2119770 : CollatzResearch.WordTrace tailWord_2119770 prefixEnd_2119770 1088460886981276623826361 := by
  unfold tailWord_2119770
  simp only [CollatzResearch.WordTrace]
  refine ⟨19328590882610698184649191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51542909020295195159064509 19328590882610698184649191)
  ·
    refine ⟨28992886323916047276973787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19328590882610698184649191 28992886323916047276973787)
    ·
      refine ⟨43489329485874070915460681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28992886323916047276973787 43489329485874070915460681)
      ·
        refine ⟨32616997114405553186595511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43489329485874070915460681 32616997114405553186595511)
        ·
          refine ⟨48925495671608329779893267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32616997114405553186595511 48925495671608329779893267)
          ·
            refine ⟨73388243507412494669839901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48925495671608329779893267 73388243507412494669839901)
            ·
              refine ⟨27520591315279685501189963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73388243507412494669839901 27520591315279685501189963)
              ·
                refine ⟨41280886972919528251784945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27520591315279685501189963 41280886972919528251784945)
                ·
                  refine ⟨30960665229689646188838709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41280886972919528251784945 30960665229689646188838709)
                  ·
                    refine ⟨2902562365283404330203629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30960665229689646188838709 2902562365283404330203629)
                    ·
                      refine ⟨1088460886981276623826361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2902562365283404330203629 1088460886981276623826361)
                      ·
                        rfl

theorem cell23_2119770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 2, 5, 3].length) (baseStart_2119770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2119770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2119770 prefixEnd_2119770 := by exact prefixLift 2119770
  have htrace : WordTrace (prefixWord ++ tailWord_2119770) baseStart_2119770 baseEnd_2119770 := by
    simpa [prefixWord, tailWord_2119770, baseEnd_2119770] using wordTrace_append hprefix tailTrace_2119770
  have hstable : (prefixWord ++ tailWord_2119770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2119770).length < 2 ^ (prefixWord ++ tailWord_2119770).sum := by decide
  have hdescent : baseEnd_2119770 < baseStart_2119770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2119770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2119781 : List Nat := [1, 3, 1, 3, 2, 4, 1, 3, 1, 4]
def baseStart_2119781 : Nat := 118140960795 + 2119781 * 2 ^ 59
def prefixEnd_2119781 : Nat := 4983230072969 + 3 ^ 40 * 2119781 * 2
def baseEnd_2119781 : Nat := 362822178422825360262937

theorem tailTrace_2119781 : CollatzResearch.WordTrace tailWord_2119781 prefixEnd_2119781 362822178422825360262937 := by
  unfold tailWord_2119781
  simp only [CollatzResearch.WordTrace]
  refine ⟨77314764733402941617247197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51543176488935294411498131 77314764733402941617247197)
  ·
    refine ⟨28993036775026103106467699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77314764733402941617247197 28993036775026103106467699)
    ·
      refine ⟨43489555162539154659701549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28993036775026103106467699 43489555162539154659701549)
      ·
        refine ⟨16308583185952182997388081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43489555162539154659701549 16308583185952182997388081)
        ·
          refine ⟨12231437389464137248041061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16308583185952182997388081 12231437389464137248041061)
          ·
            refine ⟨2293394510524525734007699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12231437389464137248041061 2293394510524525734007699)
            ·
              refine ⟨3440091765786788601011549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2293394510524525734007699 3440091765786788601011549)
              ·
                refine ⟨1290034412170045725379331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3440091765786788601011549 1290034412170045725379331)
                ·
                  refine ⟨1935051618255068588068997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1290034412170045725379331 1935051618255068588068997)
                  ·
                    refine ⟨362822178422825360262937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1935051618255068588068997 362822178422825360262937)
                    ·
                      rfl

theorem cell23_2119781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 3, 1, 4].length) (baseStart_2119781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2119781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2119781 prefixEnd_2119781 := by exact prefixLift 2119781
  have htrace : WordTrace (prefixWord ++ tailWord_2119781) baseStart_2119781 baseEnd_2119781 := by
    simpa [prefixWord, tailWord_2119781, baseEnd_2119781] using wordTrace_append hprefix tailTrace_2119781
  have hstable : (prefixWord ++ tailWord_2119781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2119781).length < 2 ^ (prefixWord ++ tailWord_2119781).sum := by decide
  have hdescent : baseEnd_2119781 < baseStart_2119781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2119781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2119798 : List Nat := [5, 1, 1, 2, 1, 3, 3, 2, 1, 4]
def baseStart_2119798 : Nat := 118140960795 + 2119798 * 2 ^ 59
def prefixEnd_2119798 : Nat := 4983230072969 + 3 ^ 40 * 2119798 * 2
def baseEnd_2119798 : Nat := 362825088146534171425411

theorem tailTrace_2119798 : CollatzResearch.WordTrace tailWord_2119798 prefixEnd_2119798 362825088146534171425411 := by
  unfold tailWord_2119798
  simp only [CollatzResearch.WordTrace]
  refine ⟨4832211548396334595038503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 51543589849560902347077365 4832211548396334595038503)
  ·
    refine ⟨7248317322594501892557755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4832211548396334595038503 7248317322594501892557755)
    ·
      refine ⟨10872475983891752838836633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7248317322594501892557755 10872475983891752838836633)
      ·
        refine ⟨8154356987918814629127475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10872475983891752838836633 8154356987918814629127475)
        ·
          refine ⟨12231535481878221943691213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8154356987918814629127475 12231535481878221943691213)
          ·
            refine ⟨4586825805704333228884205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12231535481878221943691213 4586825805704333228884205)
            ·
              refine ⟨1720059677139124960831577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4586825805704333228884205 1720059677139124960831577)
              ·
                refine ⟨1290044757854343720623683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1720059677139124960831577 1290044757854343720623683)
                ·
                  refine ⟨1935067136781515580935525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1290044757854343720623683 1935067136781515580935525)
                  ·
                    refine ⟨362825088146534171425411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1935067136781515580935525 362825088146534171425411)
                    ·
                      rfl

theorem cell23_2119798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 3, 2, 1, 4].length) (baseStart_2119798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2119798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2119798 prefixEnd_2119798 := by exact prefixLift 2119798
  have htrace : WordTrace (prefixWord ++ tailWord_2119798) baseStart_2119798 baseEnd_2119798 := by
    simpa [prefixWord, tailWord_2119798, baseEnd_2119798] using wordTrace_append hprefix tailTrace_2119798
  have hstable : (prefixWord ++ tailWord_2119798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2119798).length < 2 ^ (prefixWord ++ tailWord_2119798).sum := by decide
  have hdescent : baseEnd_2119798 < baseStart_2119798 := by decide
  rcases family_descends (prefixWord ++ tailWord_2119798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2119804 : List Nat := [2, 2, 2, 1, 1, 4, 3, 1, 3, 1, 3]
def baseStart_2119804 : Nat := 118140960795 + 2119804 * 2 ^ 59
def prefixEnd_2119804 : Nat := 4983230072969 + 3 ^ 40 * 2119804 * 2
def baseEnd_2119804 : Nat := 1088478345323529490801205

theorem tailTrace_2119804 : CollatzResearch.WordTrace tailWord_2119804 prefixEnd_2119804 1088478345323529490801205 := by
  unfold tailWord_2119804
  simp only [CollatzResearch.WordTrace]
  refine ⟨38657801806159808272667233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51543735741546411030222977 38657801806159808272667233)
  ·
    refine ⟨28993351354619856204500425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38657801806159808272667233 28993351354619856204500425)
    ·
      refine ⟨21745013515964892153375319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28993351354619856204500425 21745013515964892153375319)
      ·
        refine ⟨32617520273947338230062979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21745013515964892153375319 32617520273947338230062979)
        ·
          refine ⟨48926280410921007345094469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32617520273947338230062979 48926280410921007345094469)
          ·
            refine ⟨9173677577047688877205213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48926280410921007345094469 9173677577047688877205213)
            ·
              refine ⟨3440129091392883328951955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9173677577047688877205213 3440129091392883328951955)
              ·
                refine ⟨5160193637089324993427933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3440129091392883328951955 5160193637089324993427933)
                ·
                  refine ⟨1935072613908496872535475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5160193637089324993427933 1935072613908496872535475)
                  ·
                    refine ⟨2902608920862745308803213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1935072613908496872535475 2902608920862745308803213)
                    ·
                      refine ⟨1088478345323529490801205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2902608920862745308803213 1088478345323529490801205)
                      ·
                        rfl

theorem cell23_2119804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 1, 3, 1, 3].length) (baseStart_2119804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2119804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2119804 prefixEnd_2119804 := by exact prefixLift 2119804
  have htrace : WordTrace (prefixWord ++ tailWord_2119804) baseStart_2119804 baseEnd_2119804 := by
    simpa [prefixWord, tailWord_2119804, baseEnd_2119804] using wordTrace_append hprefix tailTrace_2119804
  have hstable : (prefixWord ++ tailWord_2119804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2119804).length < 2 ^ (prefixWord ++ tailWord_2119804).sum := by decide
  have hdescent : baseEnd_2119804 < baseStart_2119804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2119804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2119831 : List Nat := [1, 1, 3, 3, 4, 1, 2, 1, 2, 3, 2]
def baseStart_2119831 : Nat := 118140960795 + 2119831 * 2 ^ 59
def prefixEnd_2119831 : Nat := 4983230072969 + 3 ^ 40 * 2119831 * 2
def baseEnd_2119831 : Nat := 1088492209301200885163581

theorem tailTrace_2119831 : CollatzResearch.WordTrace tailWord_2119831 prefixEnd_2119831 1088492209301200885163581 := by
  unfold tailWord_2119831
  simp only [CollatzResearch.WordTrace]
  refine ⟨77316588383221800156567347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51544392255481200104378231 77316588383221800156567347)
  ·
    refine ⟨115974882574832700234851021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77316588383221800156567347 115974882574832700234851021)
    ·
      refine ⟨43490580965562262588069133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115974882574832700234851021 43490580965562262588069133)
      ·
        refine ⟨16308967862085848470525925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43490580965562262588069133 16308967862085848470525925)
        ·
          refine ⟨3057931474141096588223611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16308967862085848470525925 3057931474141096588223611)
          ·
            refine ⟨4586897211211644882335417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3057931474141096588223611 4586897211211644882335417)
            ·
              refine ⟨3440172908408733661751563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4586897211211644882335417 3440172908408733661751563)
              ·
                refine ⟨5160259362613100492627345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3440172908408733661751563 5160259362613100492627345)
                ·
                  refine ⟨3870194521959825369470509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5160259362613100492627345 3870194521959825369470509)
                  ·
                    refine ⟨1451322945734934513551441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3870194521959825369470509 1451322945734934513551441)
                    ·
                      refine ⟨1088492209301200885163581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1451322945734934513551441 1088492209301200885163581)
                      ·
                        rfl

theorem cell23_2119831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 1, 2, 3, 2].length) (baseStart_2119831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2119831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2119831 prefixEnd_2119831 := by exact prefixLift 2119831
  have htrace : WordTrace (prefixWord ++ tailWord_2119831) baseStart_2119831 baseEnd_2119831 := by
    simpa [prefixWord, tailWord_2119831, baseEnd_2119831] using wordTrace_append hprefix tailTrace_2119831
  have hstable : (prefixWord ++ tailWord_2119831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2119831).length < 2 ^ (prefixWord ++ tailWord_2119831).sum := by decide
  have hdescent : baseEnd_2119831 < baseStart_2119831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2119831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2119837 : List Nat := [1, 4, 2, 1, 1, 4, 1, 2, 1, 6]
def baseStart_2119837 : Nat := 118140960795 + 2119837 * 2 ^ 59
def prefixEnd_2119837 : Nat := 4983230072969 + 3 ^ 40 * 2119837 * 2
def baseEnd_2119837 : Nat := 362831763395042620562851

theorem tailTrace_2119837 : CollatzResearch.WordTrace tailWord_2119837 prefixEnd_2119837 362831763395042620562851 := by
  unfold tailWord_2119837
  simp only [CollatzResearch.WordTrace]
  refine ⟨77316807221200063181285765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51544538147466708787523843 77316807221200063181285765)
  ·
    refine ⟨14496901353975011846491081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77316807221200063181285765 14496901353975011846491081)
    ·
      refine ⟨10872676015481258884868311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14496901353975011846491081 10872676015481258884868311)
      ·
        refine ⟨16309014023221888327302467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10872676015481258884868311 16309014023221888327302467)
        ·
          refine ⟨24463521034832832490953701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16309014023221888327302467 24463521034832832490953701)
          ·
            refine ⟨4586910194031156092053819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24463521034832832490953701 4586910194031156092053819)
            ·
              refine ⟨6880365291046734138080729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4586910194031156092053819 6880365291046734138080729)
              ·
                refine ⟨5160273968285050603560547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6880365291046734138080729 5160273968285050603560547)
                ·
                  refine ⟨7740410952427575905340821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5160273968285050603560547 7740410952427575905340821)
                  ·
                    refine ⟨362831763395042620562851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7740410952427575905340821 362831763395042620562851)
                    ·
                      rfl

theorem cell23_2119837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 2, 1, 6].length) (baseStart_2119837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2119837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2119837 prefixEnd_2119837 := by exact prefixLift 2119837
  have htrace : WordTrace (prefixWord ++ tailWord_2119837) baseStart_2119837 baseEnd_2119837 := by
    simpa [prefixWord, tailWord_2119837, baseEnd_2119837] using wordTrace_append hprefix tailTrace_2119837
  have hstable : (prefixWord ++ tailWord_2119837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2119837).length < 2 ^ (prefixWord ++ tailWord_2119837).sum := by decide
  have hdescent : baseEnd_2119837 < baseStart_2119837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2119837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2119877 : List Nat := [1, 3, 1, 1, 1, 1, 5, 3, 1, 3, 3]
def baseStart_2119877 : Nat := 118140960795 + 2119877 * 2 ^ 59
def prefixEnd_2119877 : Nat := 4983230072969 + 3 ^ 40 * 2119877 * 2
def baseEnd_2119877 : Nat := 1088515829411307705188369

theorem tailTrace_2119877 : CollatzResearch.WordTrace tailWord_2119877 prefixEnd_2119877 1088515829411307705188369 := by
  unfold tailWord_2119877
  simp only [CollatzResearch.WordTrace]
  refine ⟨77318266141055150012741885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51545510760703433341827923 77318266141055150012741885)
  ·
    refine ⟨28994349802895681254778207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77318266141055150012741885 28994349802895681254778207)
    ·
      refine ⟨43491524704343521882167311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28994349802895681254778207 43491524704343521882167311)
      ·
        refine ⟨65237287056515282823250967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43491524704343521882167311 65237287056515282823250967)
        ·
          refine ⟨97855930584772924234876451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65237287056515282823250967 97855930584772924234876451)
          ·
            refine ⟨146783895877159386352314677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97855930584772924234876451 146783895877159386352314677)
            ·
              refine ⟨13760990238483692470529501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 146783895877159386352314677 13760990238483692470529501)
              ·
                refine ⟨5160371339431384676448563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13760990238483692470529501 5160371339431384676448563)
                ·
                  refine ⟨7740557009147077014672845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5160371339431384676448563 7740557009147077014672845)
                  ·
                    refine ⟨2902708878430153880502317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7740557009147077014672845 2902708878430153880502317)
                    ·
                      refine ⟨1088515829411307705188369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2902708878430153880502317 1088515829411307705188369)
                      ·
                        rfl

theorem cell23_2119877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 3, 1, 3, 3].length) (baseStart_2119877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2119877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2119877 prefixEnd_2119877 := by exact prefixLift 2119877
  have htrace : WordTrace (prefixWord ++ tailWord_2119877) baseStart_2119877 baseEnd_2119877 := by
    simpa [prefixWord, tailWord_2119877, baseEnd_2119877] using wordTrace_append hprefix tailTrace_2119877
  have hstable : (prefixWord ++ tailWord_2119877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2119877).length < 2 ^ (prefixWord ++ tailWord_2119877).sum := by decide
  have hdescent : baseEnd_2119877 < baseStart_2119877 := by decide
  rcases family_descends (prefixWord ++ tailWord_2119877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2119880 : List Nat := [2, 1, 3, 1, 2, 1, 1, 1, 4, 7]
def baseStart_2119880 : Nat := 118140960795 + 2119880 * 2 ^ 59
def prefixEnd_2119880 : Nat := 4983230072969 + 3 ^ 40 * 2119880 * 2
def baseEnd_2119880 : Nat := 362839123284423731150285

theorem tailTrace_2119880 : CollatzResearch.WordTrace tailWord_2119880 prefixEnd_2119880 362839123284423731150285 := by
  unfold tailWord_2119880
  simp only [CollatzResearch.WordTrace]
  refine ⟨38659187780022140762550547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51545583706696187683400729 38659187780022140762550547)
  ·
    refine ⟨57988781670033211143825821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38659187780022140762550547 57988781670033211143825821)
    ·
      refine ⟨21745793126262454178934683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57988781670033211143825821 21745793126262454178934683)
      ·
        refine ⟨32618689689393681268402025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21745793126262454178934683 32618689689393681268402025)
        ·
          refine ⟨24464017267045260951301519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32618689689393681268402025 24464017267045260951301519)
          ·
            refine ⟨36696025900567891426952279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24464017267045260951301519 36696025900567891426952279)
            ·
              refine ⟨55044038850851837140428419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36696025900567891426952279 55044038850851837140428419)
              ·
                refine ⟨82566058276277755710642629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55044038850851837140428419 82566058276277755710642629)
                ·
                  refine ⟨15481135926802079195745493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 82566058276277755710642629 15481135926802079195745493)
                  ·
                    refine ⟨362839123284423731150285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15481135926802079195745493 362839123284423731150285)
                    ·
                      rfl

theorem cell23_2119880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 4, 7].length) (baseStart_2119880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2119880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2119880 prefixEnd_2119880 := by exact prefixLift 2119880
  have htrace : WordTrace (prefixWord ++ tailWord_2119880) baseStart_2119880 baseEnd_2119880 := by
    simpa [prefixWord, tailWord_2119880, baseEnd_2119880] using wordTrace_append hprefix tailTrace_2119880
  have hstable : (prefixWord ++ tailWord_2119880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2119880).length < 2 ^ (prefixWord ++ tailWord_2119880).sum := by decide
  have hdescent : baseEnd_2119880 < baseStart_2119880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2119880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2119911 : List Nat := [1, 1, 5, 3, 1, 2, 1, 1, 4, 1, 3]
def baseStart_2119911 : Nat := 118140960795 + 2119911 * 2 ^ 59
def prefixEnd_2119911 : Nat := 4983230072969 + 3 ^ 40 * 2119911 * 2
def baseEnd_2119911 : Nat := 1088533287753560572163213

theorem tailTrace_2119911 : CollatzResearch.WordTrace tailWord_2119911 prefixEnd_2119911 1088533287753560572163213 := by
  unfold tailWord_2119911
  simp only [CollatzResearch.WordTrace]
  refine ⟨77319506222931973819479587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51546337481954649212986391 77319506222931973819479587)
  ·
    refine ⟨115979259334397960729219381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77319506222931973819479587 115979259334397960729219381)
    ·
      refine ⟨10873055562599808818364317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 115979259334397960729219381 10873055562599808818364317)
      ·
        refine ⟨4077395835974928306886619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10873055562599808818364317 4077395835974928306886619)
        ·
          refine ⟨6116093753962392460329929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4077395835974928306886619 6116093753962392460329929)
          ·
            refine ⟨4587070315471794345247447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6116093753962392460329929 4587070315471794345247447)
            ·
              refine ⟨6880605473207691517871171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4587070315471794345247447 6880605473207691517871171)
              ·
                refine ⟨10320908209811537276806757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6880605473207691517871171 10320908209811537276806757)
                ·
                  refine ⟨1935170289339663239401267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10320908209811537276806757 1935170289339663239401267)
                  ·
                    refine ⟨2902755434009494859101901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1935170289339663239401267 2902755434009494859101901)
                    ·
                      refine ⟨1088533287753560572163213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2902755434009494859101901 1088533287753560572163213)
                      ·
                        rfl

theorem cell23_2119911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_2119911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2119911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2119911 prefixEnd_2119911 := by exact prefixLift 2119911
  have htrace : WordTrace (prefixWord ++ tailWord_2119911) baseStart_2119911 baseEnd_2119911 := by
    simpa [prefixWord, tailWord_2119911, baseEnd_2119911] using wordTrace_append hprefix tailTrace_2119911
  have hstable : (prefixWord ++ tailWord_2119911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2119911).length < 2 ^ (prefixWord ++ tailWord_2119911).sum := by decide
  have hdescent : baseEnd_2119911 < baseStart_2119911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2119911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2119937 : List Nat := [1, 2, 4, 1, 1, 2, 2, 2, 2, 1, 5]
def baseStart_2119937 : Nat := 118140960795 + 2119937 * 2 ^ 59
def prefixEnd_2119937 : Nat := 4983230072969 + 3 ^ 40 * 2119937 * 2
def baseEnd_2119937 : Nat := 1088546638250577470438093

theorem tailTrace_2119937 : CollatzResearch.WordTrace tailWord_2119937 prefixEnd_2119937 1088546638250577470438093 := by
  unfold tailWord_2119937
  simp only [CollatzResearch.WordTrace]
  refine ⟨77320454520837780259926065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51546969680558520173284043 77320454520837780259926065)
  ·
    refine ⟨57990340890628335194944549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77320454520837780259926065 57990340890628335194944549)
    ·
      refine ⟨10873188916992812849052103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57990340890628335194944549 10873188916992812849052103)
      ·
        refine ⟨16309783375489219273578155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10873188916992812849052103 16309783375489219273578155)
        ·
          refine ⟨24464675063233828910367233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16309783375489219273578155 24464675063233828910367233)
          ·
            refine ⟨18348506297425371682775425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24464675063233828910367233 18348506297425371682775425)
            ·
              refine ⟨13761379723069028762081569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18348506297425371682775425 13761379723069028762081569)
              ·
                refine ⟨10321034792301771571561177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13761379723069028762081569 10321034792301771571561177)
                ·
                  refine ⟨7740776094226328678670883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10321034792301771571561177 7740776094226328678670883)
                  ·
                    refine ⟨11611164141339493018006325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7740776094226328678670883 11611164141339493018006325)
                    ·
                      refine ⟨1088546638250577470438093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11611164141339493018006325 1088546638250577470438093)
                      ·
                        rfl

theorem cell23_2119937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_2119937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2119937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2119937 prefixEnd_2119937 := by exact prefixLift 2119937
  have htrace : WordTrace (prefixWord ++ tailWord_2119937) baseStart_2119937 baseEnd_2119937 := by
    simpa [prefixWord, tailWord_2119937, baseEnd_2119937] using wordTrace_append hprefix tailTrace_2119937
  have hstable : (prefixWord ++ tailWord_2119937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2119937).length < 2 ^ (prefixWord ++ tailWord_2119937).sum := by decide
  have hdescent : baseEnd_2119937 < baseStart_2119937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2119937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2119938 : List Nat := [3, 4, 1, 1, 2, 1, 1, 4, 1, 3, 2]
def baseStart_2119938 : Nat := 118140960795 + 2119938 * 2 ^ 59
def prefixEnd_2119938 : Nat := 4983230072969 + 3 ^ 40 * 2119938 * 2
def baseEnd_2119938 : Nat := 1088547151731231966525589

theorem tailTrace_2119938 : CollatzResearch.WordTrace tailWord_2119938 prefixEnd_2119938 1088547151731231966525589 := by
  unfold tailWord_2119938
  simp only [CollatzResearch.WordTrace]
  refine ⟨19330122748458539357678117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51546993995889438287141645 19330122748458539357678117)
  ·
    refine ⟨3624398015335976129564647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19330122748458539357678117 3624398015335976129564647)
    ·
      refine ⟨5436597023003964194346971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3624398015335976129564647 5436597023003964194346971)
      ·
        refine ⟨8154895534505946291520457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5436597023003964194346971 8154895534505946291520457)
        ·
          refine ⟨6116171650879459718640343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8154895534505946291520457 6116171650879459718640343)
          ·
            refine ⟨9174257476319189577960515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6116171650879459718640343 9174257476319189577960515)
            ·
              refine ⟨13761386214478784366940773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9174257476319189577960515 13761386214478784366940773)
              ·
                refine ⟨2580259915214772068801395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13761386214478784366940773 2580259915214772068801395)
                ·
                  refine ⟨3870389872822158103202093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2580259915214772068801395 3870389872822158103202093)
                  ·
                    refine ⟨1451396202308309288700785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3870389872822158103202093 1451396202308309288700785)
                    ·
                      refine ⟨1088547151731231966525589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1451396202308309288700785 1088547151731231966525589)
                      ·
                        rfl

theorem cell23_2119938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 4, 1, 3, 2].length) (baseStart_2119938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2119938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2119938 prefixEnd_2119938 := by exact prefixLift 2119938
  have htrace : WordTrace (prefixWord ++ tailWord_2119938) baseStart_2119938 baseEnd_2119938 := by
    simpa [prefixWord, tailWord_2119938, baseEnd_2119938] using wordTrace_append hprefix tailTrace_2119938
  have hstable : (prefixWord ++ tailWord_2119938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2119938).length < 2 ^ (prefixWord ++ tailWord_2119938).sum := by decide
  have hdescent : baseEnd_2119938 < baseStart_2119938 := by decide
  rcases family_descends (prefixWord ++ tailWord_2119938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2119987 : List Nat := [1, 1, 1, 2, 5, 1, 1, 2, 4, 5]
def baseStart_2119987 : Nat := 118140960795 + 2119987 * 2 ^ 59
def prefixEnd_2119987 : Nat := 4983230072969 + 3 ^ 40 * 2119987 * 2
def baseEnd_2119987 : Nat := 362857437427767424937621

theorem tailTrace_2119987 : CollatzResearch.WordTrace tailWord_2119987 prefixEnd_2119987 362857437427767424937621 := by
  unfold tailWord_2119987
  simp only [CollatzResearch.WordTrace]
  refine ⟨77322278170656638799246215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51548185447104425866164143 77322278170656638799246215)
  ·
    refine ⟨115983417255984958198869323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77322278170656638799246215 115983417255984958198869323)
    ·
      refine ⟨173975125883977437298303985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115983417255984958198869323 173975125883977437298303985)
      ·
        refine ⟨130481344412983077973727989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173975125883977437298303985 130481344412983077973727989)
        ·
          refine ⟨12232626038717163560036999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 130481344412983077973727989 12232626038717163560036999)
          ·
            refine ⟨18348939058075745340055499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12232626038717163560036999 18348939058075745340055499)
            ·
              refine ⟨27523408587113618010083249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18348939058075745340055499 27523408587113618010083249)
              ·
                refine ⟨20642556440335213507562437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27523408587113618010083249 20642556440335213507562437)
                ·
                  refine ⟨3870479332562852532667957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20642556440335213507562437 3870479332562852532667957)
                  ·
                    refine ⟨362857437427767424937621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3870479332562852532667957 362857437427767424937621)
                    ·
                      rfl

theorem cell23_2119987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 4, 5].length) (baseStart_2119987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2119987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2119987 prefixEnd_2119987 := by exact prefixLift 2119987
  have htrace : WordTrace (prefixWord ++ tailWord_2119987) baseStart_2119987 baseEnd_2119987 := by
    simpa [prefixWord, tailWord_2119987, baseEnd_2119987] using wordTrace_append hprefix tailTrace_2119987
  have hstable : (prefixWord ++ tailWord_2119987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2119987).length < 2 ^ (prefixWord ++ tailWord_2119987).sum := by decide
  have hdescent : baseEnd_2119987 < baseStart_2119987 := by decide
  rcases family_descends (prefixWord ++ tailWord_2119987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2120061 : List Nat := [1, 4, 1, 1, 2, 3, 3, 1, 2, 2, 3]
def baseStart_2120061 : Nat := 118140960795 + 2120061 * 2 ^ 59
def prefixEnd_2120061 : Nat := 4983230072969 + 3 ^ 40 * 2120061 * 2
def baseEnd_2120061 : Nat := 1088610309851734985287523

theorem tailTrace_2120061 : CollatzResearch.WordTrace tailWord_2120061 prefixEnd_2120061 1088610309851734985287523 := by
  unfold tailWord_2120061
  simp only [CollatzResearch.WordTrace]
  refine ⟨77324977172388549437440037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51549984781592366291626691 77324977172388549437440037)
  ·
    refine ⟨14498433219822853019520007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77324977172388549437440037 14498433219822853019520007)
    ·
      refine ⟨21747649829734279529280011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14498433219822853019520007 21747649829734279529280011)
      ·
        refine ⟨32621474744601419293920017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21747649829734279529280011 32621474744601419293920017)
        ·
          refine ⟨24466106058451064470440013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32621474744601419293920017 24466106058451064470440013)
          ·
            refine ⟨9174789771919149176415005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24466106058451064470440013 9174789771919149176415005)
            ·
              refine ⟨3440546164469680941155627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9174789771919149176415005 3440546164469680941155627)
              ·
                refine ⟨5160819246704521411733441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3440546164469680941155627 5160819246704521411733441)
                ·
                  refine ⟨3870614435028391058800081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5160819246704521411733441 3870614435028391058800081)
                  ·
                    refine ⟨2902960826271293294100061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3870614435028391058800081 2902960826271293294100061)
                    ·
                      refine ⟨1088610309851734985287523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2902960826271293294100061 1088610309851734985287523)
                      ·
                        rfl

theorem cell23_2120061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 1, 2, 2, 3].length) (baseStart_2120061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2120061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2120061 prefixEnd_2120061 := by exact prefixLift 2120061
  have htrace : WordTrace (prefixWord ++ tailWord_2120061) baseStart_2120061 baseEnd_2120061 := by
    simpa [prefixWord, tailWord_2120061, baseEnd_2120061] using wordTrace_append hprefix tailTrace_2120061
  have hstable : (prefixWord ++ tailWord_2120061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2120061).length < 2 ^ (prefixWord ++ tailWord_2120061).sum := by decide
  have hdescent : baseEnd_2120061 < baseStart_2120061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2120061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2120068 : List Nat := [2, 3, 2, 1, 1, 2, 4, 3, 1, 4]
def baseStart_2120068 : Nat := 118140960795 + 2120068 * 2 ^ 59
def prefixEnd_2120068 : Nat := 4983230072969 + 3 ^ 40 * 2120068 * 2
def baseEnd_2120068 : Nat := 362871301405438819299997

theorem tailTrace_2120068 : CollatzResearch.WordTrace tailWord_2120068 prefixEnd_2120068 362871301405438819299997 := by
  unfold tailWord_2120068
  simp only [CollatzResearch.WordTrace]
  refine ⟨38662616241681594816472429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51550154988908793088629905 38662616241681594816472429)
  ·
    refine ⟨14498481090630598056177161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38662616241681594816472429 14498481090630598056177161)
    ·
      refine ⟨10873860817972948542132871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14498481090630598056177161 10873860817972948542132871)
      ·
        refine ⟨16310791226959422813199307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10873860817972948542132871 16310791226959422813199307)
        ·
          refine ⟨24466186840439134219798961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16310791226959422813199307 24466186840439134219798961)
          ·
            refine ⟨18349640130329350664849221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24466186840439134219798961 18349640130329350664849221)
            ·
              refine ⟨3440557524436753249659229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18349640130329350664849221 3440557524436753249659229)
              ·
                refine ⟨1290209071663782468622211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3440557524436753249659229 1290209071663782468622211)
                ·
                  refine ⟨1935313607495673702933317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1290209071663782468622211 1935313607495673702933317)
                  ·
                    refine ⟨362871301405438819299997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1935313607495673702933317 362871301405438819299997)
                    ·
                      rfl

theorem cell23_2120068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 3, 1, 4].length) (baseStart_2120068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2120068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2120068 prefixEnd_2120068 := by exact prefixLift 2120068
  have htrace : WordTrace (prefixWord ++ tailWord_2120068) baseStart_2120068 baseEnd_2120068 := by
    simpa [prefixWord, tailWord_2120068, baseEnd_2120068] using wordTrace_append hprefix tailTrace_2120068
  have hstable : (prefixWord ++ tailWord_2120068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2120068).length < 2 ^ (prefixWord ++ tailWord_2120068).sum := by decide
  have hdescent : baseEnd_2120068 < baseStart_2120068 := by decide
  rcases family_descends (prefixWord ++ tailWord_2120068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2120125 : List Nat := [1, 4, 1, 2, 2, 2, 3, 3, 1, 1, 3]
def baseStart_2120125 : Nat := 118140960795 + 2120125 * 2 ^ 59
def prefixEnd_2120125 : Nat := 4983230072969 + 3 ^ 40 * 2120125 * 2
def baseEnd_2120125 : Nat := 1088643172613622734887229

theorem tailTrace_2120125 : CollatzResearch.WordTrace tailWord_2120125 prefixEnd_2120125 1088643172613622734887229 := by
  unfold tailWord_2120125
  simp only [CollatzResearch.WordTrace]
  refine ⟨77327311444156688367769829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51551540962771125578513219 77327311444156688367769829)
  ·
    refine ⟨14498870895779379068956843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77327311444156688367769829 14498870895779379068956843)
    ·
      refine ⟨21748306343669068603435265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14498870895779379068956843 21748306343669068603435265)
      ·
        refine ⟨16311229757751801452576449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21748306343669068603435265 16311229757751801452576449)
        ·
          refine ⟨12233422318313851089432337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16311229757751801452576449 12233422318313851089432337)
          ·
            refine ⟨9175066738735388317074253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12233422318313851089432337 9175066738735388317074253)
            ·
              refine ⟨3440650027025770618902845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9175066738735388317074253 3440650027025770618902845)
              ·
                refine ⟨1290243760134663982088567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3440650027025770618902845 1290243760134663982088567)
                ·
                  refine ⟨1935365640201995973132851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1290243760134663982088567 1935365640201995973132851)
                  ·
                    refine ⟨2903048460302993959699277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1935365640201995973132851 2903048460302993959699277)
                    ·
                      refine ⟨1088643172613622734887229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2903048460302993959699277 1088643172613622734887229)
                      ·
                        rfl

theorem cell23_2120125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 3, 1, 1, 3].length) (baseStart_2120125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2120125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2120125 prefixEnd_2120125 := by exact prefixLift 2120125
  have htrace : WordTrace (prefixWord ++ tailWord_2120125) baseStart_2120125 baseEnd_2120125 := by
    simpa [prefixWord, tailWord_2120125, baseEnd_2120125] using wordTrace_append hprefix tailTrace_2120125
  have hstable : (prefixWord ++ tailWord_2120125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2120125).length < 2 ^ (prefixWord ++ tailWord_2120125).sum := by decide
  have hdescent : baseEnd_2120125 < baseStart_2120125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2120125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2120137 : List Nat := [1, 2, 1, 1, 2, 1, 15]
def baseStart_2120137 : Nat := 118140960795 + 2120137 * 2 ^ 59
def prefixEnd_2120137 : Nat := 4983230072969 + 3 ^ 40 * 2120137 * 2
def baseEnd_2120137 : Nat := 13440115239277489974533

theorem tailTrace_2120137 : CollatzResearch.WordTrace tailWord_2120137 prefixEnd_2120137 13440115239277489974533 := by
  unfold tailWord_2120137
  simp only [CollatzResearch.WordTrace]
  refine ⟨77327749120113214417206665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51551832746742142944804443 77327749120113214417206665)
  ·
    refine ⟨57995811840084910812904999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77327749120113214417206665 57995811840084910812904999)
    ·
      refine ⟨86993717760127366219357499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57995811840084910812904999 86993717760127366219357499)
      ·
        refine ⟨130490576640191049329036249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86993717760127366219357499 130490576640191049329036249)
        ·
          refine ⟨97867932480143286996777187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130490576640191049329036249 97867932480143286996777187)
          ·
            refine ⟨146801898720214930495165781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97867932480143286996777187 146801898720214930495165781)
            ·
              refine ⟨13440115239277489974533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 15 146801898720214930495165781 13440115239277489974533)
              ·
                rfl

theorem cell23_2120137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 15].length) (baseStart_2120137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2120137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2120137 prefixEnd_2120137 := by exact prefixLift 2120137
  have htrace : WordTrace (prefixWord ++ tailWord_2120137) baseStart_2120137 baseEnd_2120137 := by
    simpa [prefixWord, tailWord_2120137, baseEnd_2120137] using wordTrace_append hprefix tailTrace_2120137
  have hstable : (prefixWord ++ tailWord_2120137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2120137).length < 2 ^ (prefixWord ++ tailWord_2120137).sum := by decide
  have hdescent : baseEnd_2120137 < baseStart_2120137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2120137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2120154 : List Nat := [3, 1, 1, 2, 3, 1, 4, 8]
def baseStart_2120154 : Nat := 118140960795 + 2120154 * 2 ^ 59
def prefixEnd_2120154 : Nat := 4983230072969 + 3 ^ 40 * 2120154 * 2
def baseEnd_2120154 : Nat := 40320669020466782274985

theorem tailTrace_2120154 : CollatzResearch.WordTrace tailWord_2120154 prefixEnd_2120154 40320669020466782274985 := by
  unfold tailWord_2120154
  simp only [CollatzResearch.WordTrace]
  refine ⟨19332092290262906580143879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51552246107367750880383677 19332092290262906580143879)
  ·
    refine ⟨28998138435394359870215819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19332092290262906580143879 28998138435394359870215819)
    ·
      refine ⟨43497207653091539805323729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28998138435394359870215819 43497207653091539805323729)
      ·
        refine ⟨32622905739818654853992797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43497207653091539805323729 32622905739818654853992797)
        ·
          refine ⟨12233589652431995570247299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32622905739818654853992797 12233589652431995570247299)
          ·
            refine ⟨18350384478647993355370949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12233589652431995570247299 18350384478647993355370949)
            ·
              refine ⟨3440697089746498754132053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18350384478647993355370949 3440697089746498754132053)
              ·
                refine ⟨40320669020466782274985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3440697089746498754132053 40320669020466782274985)
                ·
                  rfl

theorem cell23_2120154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 8].length) (baseStart_2120154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2120154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2120154 prefixEnd_2120154 := by exact prefixLift 2120154
  have htrace : WordTrace (prefixWord ++ tailWord_2120154) baseStart_2120154 baseEnd_2120154 := by
    simpa [prefixWord, tailWord_2120154, baseEnd_2120154] using wordTrace_append hprefix tailTrace_2120154
  have hstable : (prefixWord ++ tailWord_2120154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2120154).length < 2 ^ (prefixWord ++ tailWord_2120154).sum := by decide
  have hdescent : baseEnd_2120154 < baseStart_2120154 := by decide
  rcases family_descends (prefixWord ++ tailWord_2120154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2120162 : List Nat := [3, 3, 3, 2, 1, 2, 1, 2, 1, 5]
def baseStart_2120162 : Nat := 118140960795 + 2120162 * 2 ^ 59
def prefixEnd_2120162 : Nat := 4983230072969 + 3 ^ 40 * 2120162 * 2
def baseEnd_2120162 : Nat := 362887390465946363374853

theorem tailTrace_2120162 : CollatzResearch.WordTrace tailWord_2120162 prefixEnd_2120162 362887390465946363374853 := by
  unfold tailWord_2120162
  simp only [CollatzResearch.WordTrace]
  refine ⟨19332165236255660921716685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51552440630015095791244493 19332165236255660921716685)
  ·
    refine ⟨7249561963595872845643757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19332165236255660921716685 7249561963595872845643757)
    ·
      refine ⟨2718585736348452317116409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7249561963595872845643757 2718585736348452317116409)
      ·
        refine ⟨2038939302261339237837307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2718585736348452317116409 2038939302261339237837307)
        ·
          refine ⟨3058408953392008856755961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2038939302261339237837307 3058408953392008856755961)
          ·
            refine ⟨2293806715044006642566971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3058408953392008856755961 2293806715044006642566971)
            ·
              refine ⟨3440710072566009963850457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2293806715044006642566971 3440710072566009963850457)
              ·
                refine ⟨2580532554424507472887843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3440710072566009963850457 2580532554424507472887843)
                ·
                  refine ⟨3870798831636761209331765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2580532554424507472887843 3870798831636761209331765)
                  ·
                    refine ⟨362887390465946363374853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3870798831636761209331765 362887390465946363374853)
                    ·
                      rfl

theorem cell23_2120162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_2120162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2120162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2120162 prefixEnd_2120162 := by exact prefixLift 2120162
  have htrace : WordTrace (prefixWord ++ tailWord_2120162) baseStart_2120162 baseEnd_2120162 := by
    simpa [prefixWord, tailWord_2120162, baseEnd_2120162] using wordTrace_append hprefix tailTrace_2120162
  have hstable : (prefixWord ++ tailWord_2120162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2120162).length < 2 ^ (prefixWord ++ tailWord_2120162).sum := by decide
  have hdescent : baseEnd_2120162 < baseStart_2120162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2120162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2120165 : List Nat := [1, 3, 1, 5, 2, 2, 1, 2, 1, 1, 4]
def baseStart_2120165 : Nat := 118140960795 + 2120165 * 2 ^ 59
def prefixEnd_2120165 : Nat := 4983230072969 + 3 ^ 40 * 2120165 * 2
def baseEnd_2120165 : Nat := 1088663711839802578387045

theorem tailTrace_2120165 : CollatzResearch.WordTrace tailWord_2120165 prefixEnd_2120165 1088663711839802578387045 := by
  unfold tailWord_2120165
  simp only [CollatzResearch.WordTrace]
  refine ⟨77328770364011775199225949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51552513576007850132817299 77328770364011775199225949)
  ·
    refine ⟨28998288886504415699709731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77328770364011775199225949 28998288886504415699709731)
    ·
      refine ⟨43497433329756623549564597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28998288886504415699709731 43497433329756623549564597)
      ·
        refine ⟨4077884374664683457771681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 43497433329756623549564597 4077884374664683457771681)
        ·
          refine ⟨3058413280998512593328761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4077884374664683457771681 3058413280998512593328761)
          ·
            refine ⟨2293809960748884444996571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3058413280998512593328761 2293809960748884444996571)
            ·
              refine ⟨3440714941123326667494857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2293809960748884444996571 3440714941123326667494857)
              ·
                refine ⟨2580536205842495000621143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3440714941123326667494857 2580536205842495000621143)
                ·
                  refine ⟨3870804308763742500931715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2580536205842495000621143 3870804308763742500931715)
                  ·
                    refine ⟨5806206463145613751397573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3870804308763742500931715 5806206463145613751397573)
                    ·
                      refine ⟨1088663711839802578387045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5806206463145613751397573 1088663711839802578387045)
                      ·
                        rfl

theorem cell23_2120165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_2120165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2120165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2120165 prefixEnd_2120165 := by exact prefixLift 2120165
  have htrace : WordTrace (prefixWord ++ tailWord_2120165) baseStart_2120165 baseEnd_2120165 := by
    simpa [prefixWord, tailWord_2120165, baseEnd_2120165] using wordTrace_append hprefix tailTrace_2120165
  have hstable : (prefixWord ++ tailWord_2120165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2120165).length < 2 ^ (prefixWord ++ tailWord_2120165).sum := by decide
  have hdescent : baseEnd_2120165 < baseStart_2120165 := by decide
  rcases family_descends (prefixWord ++ tailWord_2120165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2120168 : List Nat := [2, 1, 4, 1, 1, 3, 3, 2, 1, 2, 3]
def baseStart_2120168 : Nat := 118140960795 + 2120168 * 2 ^ 59
def prefixEnd_2120168 : Nat := 4983230072969 + 3 ^ 40 * 2120168 * 2
def baseEnd_2120168 : Nat := 1088665252281766066649531

theorem tailTrace_2120168 : CollatzResearch.WordTrace tailWord_2120168 prefixEnd_2120168 1088665252281766066649531 := by
  unfold tailWord_2120168
  simp only [CollatzResearch.WordTrace]
  refine ⟨38664439891500453355792579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51552586522000604474390105 38664439891500453355792579)
  ·
    refine ⟨57996659837250680033688869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38664439891500453355792579 57996659837250680033688869)
    ·
      refine ⟨10874373719484502506316663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57996659837250680033688869 10874373719484502506316663)
      ·
        refine ⟨16311560579226753759474995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10874373719484502506316663 16311560579226753759474995)
        ·
          refine ⟨24467340868840130639212493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16311560579226753759474995 24467340868840130639212493)
          ·
            refine ⟨9175252825815048989704685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24467340868840130639212493 9175252825815048989704685)
            ·
              refine ⟨3440719809680643371139257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9175252825815048989704685 3440719809680643371139257)
              ·
                refine ⟨2580539857260482528354443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3440719809680643371139257 2580539857260482528354443)
                ·
                  refine ⟨3870809785890723792531665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2580539857260482528354443 3870809785890723792531665)
                  ·
                    refine ⟨2903107339418042844398749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3870809785890723792531665 2903107339418042844398749)
                    ·
                      refine ⟨1088665252281766066649531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2903107339418042844398749 1088665252281766066649531)
                      ·
                        rfl

theorem cell23_2120168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 2, 1, 2, 3].length) (baseStart_2120168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2120168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2120168 prefixEnd_2120168 := by exact prefixLift 2120168
  have htrace : WordTrace (prefixWord ++ tailWord_2120168) baseStart_2120168 baseEnd_2120168 := by
    simpa [prefixWord, tailWord_2120168, baseEnd_2120168] using wordTrace_append hprefix tailTrace_2120168
  have hstable : (prefixWord ++ tailWord_2120168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2120168).length < 2 ^ (prefixWord ++ tailWord_2120168).sum := by decide
  have hdescent : baseEnd_2120168 < baseStart_2120168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2120168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2120178 : List Nat := [3, 2, 1, 4, 2, 1, 1, 2, 1, 2, 4]
def baseStart_2120178 : Nat := 118140960795 + 2120178 * 2 ^ 59
def prefixEnd_2120178 : Nat := 4983230072969 + 3 ^ 40 * 2120178 * 2
def baseEnd_2120178 : Nat := 1088670387088311027524485

theorem tailTrace_2120178 : CollatzResearch.WordTrace tailWord_2120178 prefixEnd_2120178 1088670387088311027524485 := by
  unfold tailWord_2120178
  simp only [CollatzResearch.WordTrace]
  refine ⟨19332311128241169604862297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51552829675309785612966125 19332311128241169604862297)
  ·
    refine ⟨14499233346180877203646723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19332311128241169604862297 14499233346180877203646723)
    ·
      refine ⟨21748850019271315805470085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14499233346180877203646723 21748850019271315805470085)
      ·
        refine ⟨4077909378613371713525641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21748850019271315805470085 4077909378613371713525641)
        ·
          refine ⟨3058432033960028785144231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4077909378613371713525641 3058432033960028785144231)
          ·
            refine ⟨4587648050940043177716347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3058432033960028785144231 4587648050940043177716347)
            ·
              refine ⟨6881472076410064766574521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4587648050940043177716347 6881472076410064766574521)
              ·
                refine ⟨5161104057307548574930891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6881472076410064766574521 5161104057307548574930891)
                ·
                  refine ⟨7741656085961322862396337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5161104057307548574930891 7741656085961322862396337)
                  ·
                    refine ⟨5806242064470992146797253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7741656085961322862396337 5806242064470992146797253)
                    ·
                      refine ⟨1088670387088311027524485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5806242064470992146797253 1088670387088311027524485)
                      ·
                        rfl

theorem cell23_2120178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_2120178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2120178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2120178 prefixEnd_2120178 := by exact prefixLift 2120178
  have htrace : WordTrace (prefixWord ++ tailWord_2120178) baseStart_2120178 baseEnd_2120178 := by
    simpa [prefixWord, tailWord_2120178, baseEnd_2120178] using wordTrace_append hprefix tailTrace_2120178
  have hstable : (prefixWord ++ tailWord_2120178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2120178).length < 2 ^ (prefixWord ++ tailWord_2120178).sum := by decide
  have hdescent : baseEnd_2120178 < baseStart_2120178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2120178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2120182 : List Nat := [5, 1, 1, 1, 2, 1, 2, 5, 1, 2, 2]
def baseStart_2120182 : Nat := 118140960795 + 2120182 * 2 ^ 59
def prefixEnd_2120182 : Nat := 4983230072969 + 3 ^ 40 * 2120182 * 2
def baseEnd_2120182 : Nat := 1088672441010929011874467

theorem tailTrace_2120182 : CollatzResearch.WordTrace tailWord_2120182 prefixEnd_2120182 1088672441010929011874467 := by
  unfold tailWord_2120182
  simp only [CollatzResearch.WordTrace]
  refine ⟨4833086900309386693912175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 51552926936633458068396533 4833086900309386693912175)
  ·
    refine ⟨7249630350464080040868263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4833086900309386693912175 7249630350464080040868263)
    ·
      refine ⟨10874445525696120061302395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7249630350464080040868263 10874445525696120061302395)
      ·
        refine ⟨16311668288544180091953593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10874445525696120061302395 16311668288544180091953593)
        ·
          refine ⟨12233751216408135068965195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16311668288544180091953593 12233751216408135068965195)
          ·
            refine ⟨18350626824612202603447793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12233751216408135068965195 18350626824612202603447793)
            ·
              refine ⟨13762970118459151952585845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18350626824612202603447793 13762970118459151952585845)
              ·
                refine ⟨1290278448605545495554923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13762970118459151952585845 1290278448605545495554923)
                ·
                  refine ⟨1935417672908318243332385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1290278448605545495554923 1935417672908318243332385)
                  ·
                    refine ⟨1451563254681238682499289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1935417672908318243332385 1451563254681238682499289)
                    ·
                      refine ⟨1088672441010929011874467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1451563254681238682499289 1088672441010929011874467)
                      ·
                        rfl

theorem cell23_2120182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 5, 1, 2, 2].length) (baseStart_2120182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2120182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2120182 prefixEnd_2120182 := by exact prefixLift 2120182
  have htrace : WordTrace (prefixWord ++ tailWord_2120182) baseStart_2120182 baseEnd_2120182 := by
    simpa [prefixWord, tailWord_2120182, baseEnd_2120182] using wordTrace_append hprefix tailTrace_2120182
  have hstable : (prefixWord ++ tailWord_2120182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2120182).length < 2 ^ (prefixWord ++ tailWord_2120182).sum := by decide
  have hdescent : baseEnd_2120182 < baseStart_2120182 := by decide
  rcases family_descends (prefixWord ++ tailWord_2120182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2120205 : List Nat := [1, 7, 1, 1, 1, 3, 1, 8]
def baseStart_2120205 : Nat := 118140960795 + 2120205 * 2 ^ 59
def prefixEnd_2120205 : Nat := 4983230072969 + 3 ^ 40 * 2120205 * 2
def baseEnd_2120205 : Nat := 40321638928369719329143

theorem tailTrace_2120205 : CollatzResearch.WordTrace tailWord_2120205 prefixEnd_2120205 40321638928369719329143 := by
  unfold tailWord_2120205
  simp only [CollatzResearch.WordTrace]
  refine ⟨77330229283866862030682069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51553486189244574687121379 77330229283866862030682069)
  ·
    refine ⟨1812427248840629578844111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 77330229283866862030682069 1812427248840629578844111)
    ·
      refine ⟨2718640873260944368266167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1812427248840629578844111 2718640873260944368266167)
      ·
        refine ⟨4077961309891416552399251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2718640873260944368266167 4077961309891416552399251)
        ·
          refine ⟨6116941964837124828598877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4077961309891416552399251 6116941964837124828598877)
          ·
            refine ⟨2293853236813921810724579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6116941964837124828598877 2293853236813921810724579)
            ·
              refine ⟨3440779855220882716086869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2293853236813921810724579 3440779855220882716086869)
              ·
                refine ⟨40321638928369719329143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3440779855220882716086869 40321638928369719329143)
                ·
                  rfl

theorem cell23_2120205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 8].length) (baseStart_2120205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2120205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2120205 prefixEnd_2120205 := by exact prefixLift 2120205
  have htrace : WordTrace (prefixWord ++ tailWord_2120205) baseStart_2120205 baseEnd_2120205 := by
    simpa [prefixWord, tailWord_2120205, baseEnd_2120205] using wordTrace_append hprefix tailTrace_2120205
  have hstable : (prefixWord ++ tailWord_2120205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2120205).length < 2 ^ (prefixWord ++ tailWord_2120205).sum := by decide
  have hdescent : baseEnd_2120205 < baseStart_2120205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2120205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2120215 : List Nat := [1, 1, 3, 6, 1, 1, 2, 1, 1, 3, 3]
def baseStart_2120215 : Nat := 118140960795 + 2120215 * 2 ^ 59
def prefixEnd_2120215 : Nat := 4983230072969 + 3 ^ 40 * 2120215 * 2
def baseEnd_2120215 : Nat := 1088689385872527382761815

theorem tailTrace_2120215 : CollatzResearch.WordTrace tailWord_2120215 prefixEnd_2120215 1088689385872527382761815 := by
  unfold tailWord_2120215
  simp only [CollatzResearch.WordTrace]
  refine ⟨77330594013830633738546099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51553729342553755825697399 77330594013830633738546099)
  ·
    refine ⟨115995891020745950607819149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77330594013830633738546099 115995891020745950607819149)
    ·
      refine ⟨43498459132779731477932181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115995891020745950607819149 43498459132779731477932181)
      ·
        refine ⟨2038990271849049913028071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 43498459132779731477932181 2038990271849049913028071)
        ·
          refine ⟨3058485407773574869542107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2038990271849049913028071 3058485407773574869542107)
          ·
            refine ⟨4587728111660362304313161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3058485407773574869542107 4587728111660362304313161)
            ·
              refine ⟨3440796083745271728234871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4587728111660362304313161 3440796083745271728234871)
              ·
                refine ⟨5161194125617907592352307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3440796083745271728234871 5161194125617907592352307)
                ·
                  refine ⟨7741791188426861388528461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5161194125617907592352307 7741791188426861388528461)
                  ·
                    refine ⟨2903171695660073020698173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7741791188426861388528461 2903171695660073020698173)
                    ·
                      refine ⟨1088689385872527382761815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2903171695660073020698173 1088689385872527382761815)
                      ·
                        rfl

theorem cell23_2120215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_2120215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2120215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2120215 prefixEnd_2120215 := by exact prefixLift 2120215
  have htrace : WordTrace (prefixWord ++ tailWord_2120215) baseStart_2120215 baseEnd_2120215 := by
    simpa [prefixWord, tailWord_2120215, baseEnd_2120215] using wordTrace_append hprefix tailTrace_2120215
  have hstable : (prefixWord ++ tailWord_2120215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2120215).length < 2 ^ (prefixWord ++ tailWord_2120215).sum := by decide
  have hdescent : baseEnd_2120215 < baseStart_2120215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2120215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2120261 : List Nat := [1, 3, 1, 1, 1, 6, 2, 1, 7]
def baseStart_2120261 : Nat := 118140960795 + 2120261 * 2 ^ 59
def prefixEnd_2120261 : Nat := 4983230072969 + 3 ^ 40 * 2120261 * 2
def baseEnd_2120261 : Nat := 120968111775848244754067

theorem tailTrace_2120261 : CollatzResearch.WordTrace tailWord_2120261 prefixEnd_2120261 120968111775848244754067 := by
  unfold tailWord_2120261
  simp only [CollatzResearch.WordTrace]
  refine ⟨77332271771663983594720637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51554847847775989063147091 77332271771663983594720637)
  ·
    refine ⟨28999601914373993848020239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77332271771663983594720637 28999601914373993848020239)
    ·
      refine ⟨43499402871560990772030359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28999601914373993848020239 43499402871560990772030359)
      ·
        refine ⟨65249104307341486158045539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43499402871560990772030359 65249104307341486158045539)
        ·
          refine ⟨97873656461012229237068309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65249104307341486158045539 97873656461012229237068309)
          ·
            refine ⟨4587827646609948245487577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 97873656461012229237068309 4587827646609948245487577)
            ·
              refine ⟨3440870734957461184115683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4587827646609948245487577 3440870734957461184115683)
              ·
                refine ⟨5161306102436191776173525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3440870734957461184115683 5161306102436191776173525)
                ·
                  refine ⟨120968111775848244754067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5161306102436191776173525 120968111775848244754067)
                  ·
                    rfl

theorem cell23_2120261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 1, 7].length) (baseStart_2120261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2120261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2120261 prefixEnd_2120261 := by exact prefixLift 2120261
  have htrace : WordTrace (prefixWord ++ tailWord_2120261) baseStart_2120261 baseEnd_2120261 := by
    simpa [prefixWord, tailWord_2120261, baseEnd_2120261] using wordTrace_append hprefix tailTrace_2120261
  have hstable : (prefixWord ++ tailWord_2120261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2120261).length < 2 ^ (prefixWord ++ tailWord_2120261).sum := by decide
  have hdescent : baseEnd_2120261 < baseStart_2120261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2120261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2120271 : List Nat := [1, 1, 2, 1, 1, 2, 6, 1, 2, 3, 3]
def baseStart_2120271 : Nat := 118140960795 + 2120271 * 2 ^ 59
def prefixEnd_2120271 : Nat := 4983230072969 + 3 ^ 40 * 2120271 * 2
def baseEnd_2120271 : Nat := 1088718140789179163661557

theorem tailTrace_2120271 : CollatzResearch.WordTrace tailWord_2120271 prefixEnd_2120271 1088718140789179163661557 := by
  unfold tailWord_2120271
  simp only [CollatzResearch.WordTrace]
  refine ⟨77332636501627755302584667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51555091001085170201723111 77332636501627755302584667)
  ·
    refine ⟨115998954752441632953877001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77332636501627755302584667 115998954752441632953877001)
    ·
      refine ⟨86999216064331224715407751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115998954752441632953877001 86999216064331224715407751)
      ·
        refine ⟨130498824096496837073111627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86999216064331224715407751 130498824096496837073111627)
        ·
          refine ⟨195748236144745255609667441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130498824096496837073111627 195748236144745255609667441)
          ·
            refine ⟨146811177108558941707250581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 195748236144745255609667441 146811177108558941707250581)
            ·
              refine ⟨6881773926963700392527371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 146811177108558941707250581 6881773926963700392527371)
              ·
                refine ⟨10322660890445550588791057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6881773926963700392527371 10322660890445550588791057)
                ·
                  refine ⟨7741995667834162941593293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10322660890445550588791057 7741995667834162941593293)
                  ·
                    refine ⟨2903248375437811103097485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7741995667834162941593293 2903248375437811103097485)
                    ·
                      refine ⟨1088718140789179163661557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2903248375437811103097485 1088718140789179163661557)
                      ·
                        rfl

theorem cell23_2120271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 1, 2, 3, 3].length) (baseStart_2120271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2120271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2120271 prefixEnd_2120271 := by exact prefixLift 2120271
  have htrace : WordTrace (prefixWord ++ tailWord_2120271) baseStart_2120271 baseEnd_2120271 := by
    simpa [prefixWord, tailWord_2120271, baseEnd_2120271] using wordTrace_append hprefix tailTrace_2120271
  have hstable : (prefixWord ++ tailWord_2120271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2120271).length < 2 ^ (prefixWord ++ tailWord_2120271).sum := by decide
  have hdescent : baseEnd_2120271 < baseStart_2120271 := by decide
  rcases family_descends (prefixWord ++ tailWord_2120271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2120291 : List Nat := [1, 1, 1, 5, 1, 2, 2, 3, 2, 5]
def baseStart_2120291 : Nat := 118140960795 + 2120291 * 2 ^ 59
def prefixEnd_2120291 : Nat := 4983230072969 + 3 ^ 40 * 2120291 * 2
def baseEnd_2120291 : Nat := 362909470134089695137155

theorem tailTrace_2120291 : CollatzResearch.WordTrace tailWord_2120291 prefixEnd_2120291 362909470134089695137155 := by
  unfold tailWord_2120291
  simp only [CollatzResearch.WordTrace]
  refine ⟨77333365961555298718312727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51555577307703532478875151 77333365961555298718312727)
  ·
    refine ⟨116000048942332948077469091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77333365961555298718312727 116000048942332948077469091)
    ·
      refine ⟨174000073413499422116203637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116000048942332948077469091 174000073413499422116203637)
      ·
        refine ⟨16312506882515570823394091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 174000073413499422116203637 16312506882515570823394091)
        ·
          refine ⟨24468760323773356235091137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16312506882515570823394091 24468760323773356235091137)
          ·
            refine ⟨18351570242830017176318353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24468760323773356235091137 18351570242830017176318353)
            ·
              refine ⟨13763677682122512882238765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18351570242830017176318353 13763677682122512882238765)
              ·
                refine ⟨5161379130795942330839537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13763677682122512882238765 5161379130795942330839537)
                ·
                  refine ⟨3871034348096956748129653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5161379130795942330839537 3871034348096956748129653)
                  ·
                    refine ⟨362909470134089695137155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3871034348096956748129653 362909470134089695137155)
                    ·
                      rfl

theorem cell23_2120291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 3, 2, 5].length) (baseStart_2120291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2120291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2120291 prefixEnd_2120291 := by exact prefixLift 2120291
  have htrace : WordTrace (prefixWord ++ tailWord_2120291) baseStart_2120291 baseEnd_2120291 := by
    simpa [prefixWord, tailWord_2120291, baseEnd_2120291] using wordTrace_append hprefix tailTrace_2120291
  have hstable : (prefixWord ++ tailWord_2120291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2120291).length < 2 ^ (prefixWord ++ tailWord_2120291).sum := by decide
  have hdescent : baseEnd_2120291 < baseStart_2120291 := by decide
  rcases family_descends (prefixWord ++ tailWord_2120291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2120311 : List Nat := [1, 1, 3, 1, 1, 3, 3, 1, 4, 1, 4]
def baseStart_2120311 : Nat := 118140960795 + 2120311 * 2 ^ 59
def prefixEnd_2120311 : Nat := 4983230072969 + 3 ^ 40 * 2120311 * 2
def baseEnd_2120311 : Nat := 1088738680015359007161373

theorem tailTrace_2120311 : CollatzResearch.WordTrace tailWord_2120311 prefixEnd_2120311 1088738680015359007161373 := by
  unfold tailWord_2120311
  simp only [CollatzResearch.WordTrace]
  refine ⟨77334095421482842134040787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51556063614321894756027191 77334095421482842134040787)
  ·
    refine ⟨116001143132224263201061181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77334095421482842134040787 116001143132224263201061181)
    ·
      refine ⟨43500428674584098700397943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116001143132224263201061181 43500428674584098700397943)
      ·
        refine ⟨65250643011876148050596915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43500428674584098700397943 65250643011876148050596915)
        ·
          refine ⟨97875964517814222075895373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65250643011876148050596915 97875964517814222075895373)
          ·
            refine ⟨36703486694180333278460765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97875964517814222075895373 36703486694180333278460765)
            ·
              refine ⟨13763807510317624979422787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36703486694180333278460765 13763807510317624979422787)
              ·
                refine ⟨20645711265476437469134181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13763807510317624979422787 20645711265476437469134181)
                ·
                  refine ⟨3871070862276832025462659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20645711265476437469134181 3871070862276832025462659)
                  ·
                    refine ⟨5806606293415248038193989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3871070862276832025462659 5806606293415248038193989)
                    ·
                      refine ⟨1088738680015359007161373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5806606293415248038193989 1088738680015359007161373)
                      ·
                        rfl

theorem cell23_2120311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 4, 1, 4].length) (baseStart_2120311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2120311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2120311 prefixEnd_2120311 := by exact prefixLift 2120311
  have htrace : WordTrace (prefixWord ++ tailWord_2120311) baseStart_2120311 baseEnd_2120311 := by
    simpa [prefixWord, tailWord_2120311, baseEnd_2120311] using wordTrace_append hprefix tailTrace_2120311
  have hstable : (prefixWord ++ tailWord_2120311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2120311).length < 2 ^ (prefixWord ++ tailWord_2120311).sum := by decide
  have hdescent : baseEnd_2120311 < baseStart_2120311 := by decide
  rcases family_descends (prefixWord ++ tailWord_2120311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2120331 : List Nat := [1, 1, 1, 1, 4, 1, 2, 4, 1, 4, 3]
def baseStart_2120331 : Nat := 118140960795 + 2120331 * 2 ^ 59
def prefixEnd_2120331 : Nat := 4983230072969 + 3 ^ 40 * 2120331 * 2
def baseEnd_2120331 : Nat := 1088748949628448928911281

theorem tailTrace_2120331 : CollatzResearch.WordTrace tailWord_2120331 prefixEnd_2120331 1088748949628448928911281 := by
  unfold tailWord_2120331
  simp only [CollatzResearch.WordTrace]
  refine ⟨77334824881410385549768847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51556549920940257033179231 77334824881410385549768847)
  ·
    refine ⟨116002237322115578324653271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77334824881410385549768847 116002237322115578324653271)
    ·
      refine ⟨174003355983173367486979907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116002237322115578324653271 174003355983173367486979907)
      ·
        refine ⟨261005033974760051230469861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174003355983173367486979907 261005033974760051230469861)
        ·
          refine ⟨48938443870267509605713099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 261005033974760051230469861 48938443870267509605713099)
          ·
            refine ⟨73407665805401264408569649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48938443870267509605713099 73407665805401264408569649)
            ·
              refine ⟨55055749354050948306427237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73407665805401264408569649 55055749354050948306427237)
              ·
                refine ⟨10322953003884552807455107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55055749354050948306427237 10322953003884552807455107)
                ·
                  refine ⟨15484429505826829211182661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10322953003884552807455107 15484429505826829211182661)
                  ·
                    refine ⟨2903330532342530477096749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15484429505826829211182661 2903330532342530477096749)
                    ·
                      refine ⟨1088748949628448928911281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2903330532342530477096749 1088748949628448928911281)
                      ·
                        rfl

theorem cell23_2120331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 4, 1, 4, 3].length) (baseStart_2120331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2120331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2120331 prefixEnd_2120331 := by exact prefixLift 2120331
  have htrace : WordTrace (prefixWord ++ tailWord_2120331) baseStart_2120331 baseEnd_2120331 := by
    simpa [prefixWord, tailWord_2120331, baseEnd_2120331] using wordTrace_append hprefix tailTrace_2120331
  have hstable : (prefixWord ++ tailWord_2120331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2120331).length < 2 ^ (prefixWord ++ tailWord_2120331).sum := by decide
  have hdescent : baseEnd_2120331 < baseStart_2120331 := by decide
  rcases family_descends (prefixWord ++ tailWord_2120331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2120365 : List Nat := [1, 5, 2, 1, 1, 2, 2, 2, 2, 2, 3]
def baseStart_2120365 : Nat := 118140960795 + 2120365 * 2 ^ 59
def prefixEnd_2120365 : Nat := 4983230072969 + 3 ^ 40 * 2120365 * 2
def baseEnd_2120365 : Nat := 1088766407970701795886125

theorem tailTrace_2120365 : CollatzResearch.WordTrace tailWord_2120365 prefixEnd_2120365 1088766407970701795886125 := by
  unfold tailWord_2120365
  simp only [CollatzResearch.WordTrace]
  refine ⟨77336064963287209356506549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51557376642191472904337699 77336064963287209356506549)
  ·
    refine ⟨7250256090308175877172489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 77336064963287209356506549 7250256090308175877172489)
    ·
      refine ⟨5437692067731131907879367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7250256090308175877172489 5437692067731131907879367)
      ·
        refine ⟨8156538101596697861819051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5437692067731131907879367 8156538101596697861819051)
        ·
          refine ⟨12234807152395046792728577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8156538101596697861819051 12234807152395046792728577)
          ·
            refine ⟨9176105364296285094546433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12234807152395046792728577 9176105364296285094546433)
            ·
              refine ⟨6882079023222213820909825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9176105364296285094546433 6882079023222213820909825)
              ·
                refine ⟨5161559267416660365682369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6882079023222213820909825 5161559267416660365682369)
                ·
                  refine ⟨3871169450562495274261777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5161559267416660365682369 3871169450562495274261777)
                  ·
                    refine ⟨2903377087921871455696333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3871169450562495274261777 2903377087921871455696333)
                    ·
                      refine ⟨1088766407970701795886125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2903377087921871455696333 1088766407970701795886125)
                      ·
                        rfl

theorem cell23_2120365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_2120365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2120365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2120365 prefixEnd_2120365 := by exact prefixLift 2120365
  have htrace : WordTrace (prefixWord ++ tailWord_2120365) baseStart_2120365 baseEnd_2120365 := by
    simpa [prefixWord, tailWord_2120365, baseEnd_2120365] using wordTrace_append hprefix tailTrace_2120365
  have hstable : (prefixWord ++ tailWord_2120365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2120365).length < 2 ^ (prefixWord ++ tailWord_2120365).sum := by decide
  have hdescent : baseEnd_2120365 < baseStart_2120365 := by decide
  rcases family_descends (prefixWord ++ tailWord_2120365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2120398 : List Nat := [4, 1, 1, 1, 3, 2, 2, 1, 3, 5]
def baseStart_2120398 : Nat := 118140960795 + 2120398 * 2 ^ 59
def prefixEnd_2120398 : Nat := 4983230072969 + 3 ^ 40 * 2120398 * 2
def baseEnd_2120398 : Nat := 362927784277433388924491

theorem tailTrace_2120398 : CollatzResearch.WordTrace tailWord_2120398 prefixEnd_2120398 362927784277433388924491 := by
  unfold tailWord_2120398
  simp only [CollatzResearch.WordTrace]
  refine ⟨9667158571520956999057231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51558179048111770661638565 9667158571520956999057231)
  ·
    refine ⟨14500737857281435498585847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9667158571520956999057231 14500737857281435498585847)
    ·
      refine ⟨21751106785922153247878771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14500737857281435498585847 21751106785922153247878771)
      ·
        refine ⟨32626660178883229871818157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21751106785922153247878771 32626660178883229871818157)
        ·
          refine ⟨12234997567081211201931809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32626660178883229871818157 12234997567081211201931809)
          ·
            refine ⟨9176248175310908401448857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12234997567081211201931809 9176248175310908401448857)
            ·
              refine ⟨6882186131483181301086643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9176248175310908401448857 6882186131483181301086643)
              ·
                refine ⟨10323279197224771951629965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6882186131483181301086643 10323279197224771951629965)
                ·
                  refine ⟨3871229698959289481861237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10323279197224771951629965 3871229698959289481861237)
                  ·
                    refine ⟨362927784277433388924491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3871229698959289481861237 362927784277433388924491)
                    ·
                      rfl

theorem cell23_2120398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 1, 3, 5].length) (baseStart_2120398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2120398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2120398 prefixEnd_2120398 := by exact prefixLift 2120398
  have htrace : WordTrace (prefixWord ++ tailWord_2120398) baseStart_2120398 baseEnd_2120398 := by
    simpa [prefixWord, tailWord_2120398, baseEnd_2120398] using wordTrace_append hprefix tailTrace_2120398
  have hstable : (prefixWord ++ tailWord_2120398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2120398).length < 2 ^ (prefixWord ++ tailWord_2120398).sum := by decide
  have hdescent : baseEnd_2120398 < baseStart_2120398 := by decide
  rcases family_descends (prefixWord ++ tailWord_2120398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2120415 : List Nat := [1, 1, 2, 3, 2, 3, 4, 1, 1, 5]
def baseStart_2120415 : Nat := 118140960795 + 2120415 * 2 ^ 59
def prefixEnd_2120415 : Nat := 4983230072969 + 3 ^ 40 * 2120415 * 2
def baseEnd_2120415 : Nat := 362930694001142200086965

theorem tailTrace_2120415 : CollatzResearch.WordTrace tailWord_2120415 prefixEnd_2120415 362930694001142200086965 := by
  unfold tailWord_2120415
  simp only [CollatzResearch.WordTrace]
  refine ⟨77337888613106067895826699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51558592408737378597217799 77337888613106067895826699)
  ·
    refine ⟨116006832919659101843740049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77337888613106067895826699 116006832919659101843740049)
    ·
      refine ⟨87005124689744326382805037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116006832919659101843740049 87005124689744326382805037)
      ·
        refine ⟨32626921758654122393551889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87005124689744326382805037 32626921758654122393551889)
        ·
          refine ⟨24470191318990591795163917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32626921758654122393551889 24470191318990591795163917)
          ·
            refine ⟨9176321744621471923186469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24470191318990591795163917 9176321744621471923186469)
            ·
              refine ⟨1720560327116525985597463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9176321744621471923186469 1720560327116525985597463)
              ·
                refine ⟨2580840490674788978396195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1720560327116525985597463 2580840490674788978396195)
                ·
                  refine ⟨3871260736012183467594293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2580840490674788978396195 3871260736012183467594293)
                  ·
                    refine ⟨362930694001142200086965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3871260736012183467594293 362930694001142200086965)
                    ·
                      rfl

theorem cell23_2120415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 4, 1, 1, 5].length) (baseStart_2120415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2120415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2120415 prefixEnd_2120415 := by exact prefixLift 2120415
  have htrace : WordTrace (prefixWord ++ tailWord_2120415) baseStart_2120415 baseEnd_2120415 := by
    simpa [prefixWord, tailWord_2120415, baseEnd_2120415] using wordTrace_append hprefix tailTrace_2120415
  have hstable : (prefixWord ++ tailWord_2120415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2120415).length < 2 ^ (prefixWord ++ tailWord_2120415).sum := by decide
  have hdescent : baseEnd_2120415 < baseStart_2120415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2120415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2120452 : List Nat := [2, 3, 2, 2, 1, 1, 1, 4, 3, 2, 2]
def baseStart_2120452 : Nat := 118140960795 + 2120452 * 2 ^ 59
def prefixEnd_2120452 : Nat := 4983230072969 + 3 ^ 40 * 2120452 * 2
def baseEnd_2120452 : Nat := 1088811080787642955498225

theorem tailTrace_2120452 : CollatzResearch.WordTrace tailWord_2120452 prefixEnd_2120452 1088811080787642955498225 := by
  unfold tailWord_2120452
  simp only [CollatzResearch.WordTrace]
  refine ⟨38669619056986011607461805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51559492075981348809949073 38669619056986011607461805)
  ·
    refine ⟨14501107146369754352798177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38669619056986011607461805 14501107146369754352798177)
    ·
      refine ⟨10875830359777315764598633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14501107146369754352798177 10875830359777315764598633)
      ·
        refine ⟨8156872769832986823448975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10875830359777315764598633 8156872769832986823448975)
        ·
          refine ⟨12235309154749480235173463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8156872769832986823448975 12235309154749480235173463)
          ·
            refine ⟨18352963732124220352760195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12235309154749480235173463 18352963732124220352760195)
            ·
              refine ⟨27529445598186330529140293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18352963732124220352760195 27529445598186330529140293)
              ·
                refine ⟨5161771049659936974213805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27529445598186330529140293 5161771049659936974213805)
                ·
                  refine ⟨1935664143622476365330177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5161771049659936974213805 1935664143622476365330177)
                  ·
                    refine ⟨1451748107716857273997633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1935664143622476365330177 1451748107716857273997633)
                    ·
                      refine ⟨1088811080787642955498225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1451748107716857273997633 1088811080787642955498225)
                      ·
                        rfl

theorem cell23_2120452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 4, 3, 2, 2].length) (baseStart_2120452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2120452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2120452 prefixEnd_2120452 := by exact prefixLift 2120452
  have htrace : WordTrace (prefixWord ++ tailWord_2120452) baseStart_2120452 baseEnd_2120452 := by
    simpa [prefixWord, tailWord_2120452, baseEnd_2120452] using wordTrace_append hprefix tailTrace_2120452
  have hstable : (prefixWord ++ tailWord_2120452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2120452).length < 2 ^ (prefixWord ++ tailWord_2120452).sum := by decide
  have hdescent : baseEnd_2120452 < baseStart_2120452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2120452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2120485 : List Nat := [1, 3, 1, 2, 3, 1, 1, 3, 4, 1, 3]
def baseStart_2120485 : Nat := 118140960795 + 2120485 * 2 ^ 59
def prefixEnd_2120485 : Nat := 4983230072969 + 3 ^ 40 * 2120485 * 2
def baseEnd_2120485 : Nat := 1088828025649241326385573

theorem tailTrace_2120485 : CollatzResearch.WordTrace tailWord_2120485 prefixEnd_2120485 1088828025649241326385573 := by
  unfold tailWord_2120485
  simp only [CollatzResearch.WordTrace]
  refine ⟨77340441722852469850874909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51560294481901646567249939 77340441722852469850874909)
  ·
    refine ⟨29002665646069676194078091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77340441722852469850874909 29002665646069676194078091)
    ·
      refine ⟨43503998469104514291117137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29002665646069676194078091 43503998469104514291117137)
      ·
        refine ⟨32627998851828385718337853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43503998469104514291117137 32627998851828385718337853)
        ·
          refine ⟨12235499569435644644376695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32627998851828385718337853 12235499569435644644376695)
          ·
            refine ⟨18353249354153466966565043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12235499569435644644376695 18353249354153466966565043)
            ·
              refine ⟨27529874031230200449847565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18353249354153466966565043 27529874031230200449847565)
              ·
                refine ⟨10323702761711325168692837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27529874031230200449847565 10323702761711325168692837)
                ·
                  refine ⟨1935694267820873469129907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10323702761711325168692837 1935694267820873469129907)
                  ·
                    refine ⟨2903541401731310203694861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1935694267820873469129907 2903541401731310203694861)
                    ·
                      refine ⟨1088828025649241326385573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2903541401731310203694861 1088828025649241326385573)
                      ·
                        rfl

theorem cell23_2120485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 3, 4, 1, 3].length) (baseStart_2120485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2120485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2120485 prefixEnd_2120485 := by exact prefixLift 2120485
  have htrace : WordTrace (prefixWord ++ tailWord_2120485) baseStart_2120485 baseEnd_2120485 := by
    simpa [prefixWord, tailWord_2120485, baseEnd_2120485] using wordTrace_append hprefix tailTrace_2120485
  have hstable : (prefixWord ++ tailWord_2120485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2120485).length < 2 ^ (prefixWord ++ tailWord_2120485).sum := by decide
  have hdescent : baseEnd_2120485 < baseStart_2120485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2120485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2120488 : List Nat := [2, 1, 5, 1, 1, 1, 2, 1, 2, 7]
def baseStart_2120488 : Nat := 118140960795 + 2120488 * 2 ^ 59
def prefixEnd_2120488 : Nat := 4983230072969 + 3 ^ 40 * 2120488 * 2
def baseEnd_2120488 : Nat := 362943188697068271549353

theorem tailTrace_2120488 : CollatzResearch.WordTrace tailWord_2120488 prefixEnd_2120488 362943188697068271549353 := by
  unfold tailWord_2120488
  simp only [CollatzResearch.WordTrace]
  refine ⟨38670275570920800681617059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51560367427894400908822745 38670275570920800681617059)
  ·
    refine ⟨58005413356381201022425589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38670275570920800681617059 58005413356381201022425589)
    ·
      refine ⟨5438007502160737595852399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 58005413356381201022425589 5438007502160737595852399)
      ·
        refine ⟨8157011253241106393778599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5438007502160737595852399 8157011253241106393778599)
        ·
          refine ⟨12235516879861659590667899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8157011253241106393778599 12235516879861659590667899)
          ·
            refine ⟨18353275319792489386001849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12235516879861659590667899 18353275319792489386001849)
            ·
              refine ⟨13764956489844367039501387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18353275319792489386001849 13764956489844367039501387)
              ·
                refine ⟨20647434734766550559252081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13764956489844367039501387 20647434734766550559252081)
                ·
                  refine ⟨15485576051074912919439061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20647434734766550559252081 15485576051074912919439061)
                  ·
                    refine ⟨362943188697068271549353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15485576051074912919439061 362943188697068271549353)
                    ·
                      rfl

theorem cell23_2120488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_2120488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2120488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2120488 prefixEnd_2120488 := by exact prefixLift 2120488
  have htrace : WordTrace (prefixWord ++ tailWord_2120488) baseStart_2120488 baseEnd_2120488 := by
    simpa [prefixWord, tailWord_2120488, baseEnd_2120488] using wordTrace_append hprefix tailTrace_2120488
  have hstable : (prefixWord ++ tailWord_2120488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2120488).length < 2 ^ (prefixWord ++ tailWord_2120488).sum := by decide
  have hdescent : baseEnd_2120488 < baseStart_2120488 := by decide
  rcases family_descends (prefixWord ++ tailWord_2120488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2120528 : List Nat := [2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 5]
def baseStart_2120528 : Nat := 118140960795 + 2120528 * 2 ^ 59
def prefixEnd_2120528 : Nat := 4983230072969 + 3 ^ 40 * 2120528 * 2
def baseEnd_2120528 : Nat := 1088850105317384658147875

theorem tailTrace_2120528 : CollatzResearch.WordTrace tailWord_2120528 prefixEnd_2120528 1088850105317384658147875 := by
  unfold tailWord_2120528
  simp only [CollatzResearch.WordTrace]
  refine ⟨38671005030848344097345119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51561340041131125463126825 38671005030848344097345119)
  ·
    refine ⟨58006507546272516146017679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38671005030848344097345119 58006507546272516146017679)
    ·
      refine ⟨87009761319408774219026519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58006507546272516146017679 87009761319408774219026519)
      ·
        refine ⟨130514641979113161328539779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87009761319408774219026519 130514641979113161328539779)
        ·
          refine ⟨195771962968669741992809669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130514641979113161328539779 195771962968669741992809669)
          ·
            refine ⟨36707243056625576623651813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 195771962968669741992809669 36707243056625576623651813)
            ·
              refine ⟨6882608073117295616934715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36707243056625576623651813 6882608073117295616934715)
              ·
                refine ⟨10323912109675943425402073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6882608073117295616934715 10323912109675943425402073)
                ·
                  refine ⟨7742934082256957569051555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10323912109675943425402073 7742934082256957569051555)
                  ·
                    refine ⟨11614401123385436353577333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7742934082256957569051555 11614401123385436353577333)
                    ·
                      refine ⟨1088850105317384658147875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11614401123385436353577333 1088850105317384658147875)
                      ·
                        rfl

theorem cell23_2120528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 5].length) (baseStart_2120528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2120528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2120528 prefixEnd_2120528 := by exact prefixLift 2120528
  have htrace : WordTrace (prefixWord ++ tailWord_2120528) baseStart_2120528 baseEnd_2120528 := by
    simpa [prefixWord, tailWord_2120528, baseEnd_2120528] using wordTrace_append hprefix tailTrace_2120528
  have hstable : (prefixWord ++ tailWord_2120528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2120528).length < 2 ^ (prefixWord ++ tailWord_2120528).sum := by decide
  have hdescent : baseEnd_2120528 < baseStart_2120528 := by decide
  rcases family_descends (prefixWord ++ tailWord_2120528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2120565 : List Nat := [1, 3, 4, 1, 1, 3, 1, 2, 7]
def baseStart_2120565 : Nat := 118140960795 + 2120565 * 2 ^ 59
def prefixEnd_2120565 : Nat := 4983230072969 + 3 ^ 40 * 2120565 * 2
def baseEnd_2120565 : Nat := 120985456011289001487245

theorem tailTrace_2120565 : CollatzResearch.WordTrace tailWord_2120565 prefixEnd_2120565 120985456011289001487245 := by
  unfold tailWord_2120565
  simp only [CollatzResearch.WordTrace]
  refine ⟨77343359562562643513787149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51562239708375095675858099 77343359562562643513787149)
  ·
    refine ⟨29003759835960991317670181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77343359562562643513787149 29003759835960991317670181)
    ·
      refine ⟨5438204969242685872063159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29003759835960991317670181 5438204969242685872063159)
      ·
        refine ⟨8157307453864028808094739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5438204969242685872063159 8157307453864028808094739)
        ·
          refine ⟨12235961180796043212142109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8157307453864028808094739 12235961180796043212142109)
          ·
            refine ⟨4588485442798516204553291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12235961180796043212142109 4588485442798516204553291)
            ·
              refine ⟨6882728164197774306829937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4588485442798516204553291 6882728164197774306829937)
              ·
                refine ⟨5162046123148330730122453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6882728164197774306829937 5162046123148330730122453)
                ·
                  refine ⟨120985456011289001487245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5162046123148330730122453 120985456011289001487245)
                  ·
                    rfl

theorem cell23_2120565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 2, 7].length) (baseStart_2120565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2120565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2120565 prefixEnd_2120565 := by exact prefixLift 2120565
  have htrace : WordTrace (prefixWord ++ tailWord_2120565) baseStart_2120565 baseEnd_2120565 := by
    simpa [prefixWord, tailWord_2120565, baseEnd_2120565] using wordTrace_append hprefix tailTrace_2120565
  have hstable : (prefixWord ++ tailWord_2120565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2120565).length < 2 ^ (prefixWord ++ tailWord_2120565).sum := by decide
  have hdescent : baseEnd_2120565 < baseStart_2120565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2120565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2120588 : List Nat := [2, 2, 1, 2, 1, 2, 2, 1, 3, 2, 5]
def baseStart_2120588 : Nat := 118140960795 + 2120588 * 2 ^ 59
def prefixEnd_2120588 : Nat := 4983230072969 + 3 ^ 40 * 2120588 * 2
def baseEnd_2120588 : Nat := 1088880914156654423397599

theorem tailTrace_2120588 : CollatzResearch.WordTrace tailWord_2120588 prefixEnd_2120588 1088880914156654423397599 := by
  unfold tailWord_2120588
  simp only [CollatzResearch.WordTrace]
  refine ⟨38672099220739659220937209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51562798960986212294582945 38672099220739659220937209)
  ·
    refine ⟨29004074415554744415702907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38672099220739659220937209 29004074415554744415702907)
    ·
      refine ⟨43506111623332116623554361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29004074415554744415702907 43506111623332116623554361)
      ·
        refine ⟨32629583717499087467665771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43506111623332116623554361 32629583717499087467665771)
        ·
          refine ⟨48944375576248631201498657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32629583717499087467665771 48944375576248631201498657)
          ·
            refine ⟨36708281682186473401123993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48944375576248631201498657 36708281682186473401123993)
            ·
              refine ⟨27531211261639855050842995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36708281682186473401123993 27531211261639855050842995)
              ·
                refine ⟨41296816892459782576264493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27531211261639855050842995 41296816892459782576264493)
                ·
                  refine ⟨15486306334672418466099185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41296816892459782576264493 15486306334672418466099185)
                  ·
                    refine ⟨11614729751004313849574389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15486306334672418466099185 11614729751004313849574389)
                    ·
                      refine ⟨1088880914156654423397599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11614729751004313849574389 1088880914156654423397599)
                      ·
                        rfl

theorem cell23_2120588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 3, 2, 5].length) (baseStart_2120588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2120588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2120588 prefixEnd_2120588 := by exact prefixLift 2120588
  have htrace : WordTrace (prefixWord ++ tailWord_2120588) baseStart_2120588 baseEnd_2120588 := by
    simpa [prefixWord, tailWord_2120588, baseEnd_2120588] using wordTrace_append hprefix tailTrace_2120588
  have hstable : (prefixWord ++ tailWord_2120588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2120588).length < 2 ^ (prefixWord ++ tailWord_2120588).sum := by decide
  have hdescent : baseEnd_2120588 < baseStart_2120588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2120588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2120652 : List Nat := [2, 2, 1, 4, 1, 1, 3, 2, 2, 2, 3]
def baseStart_2120652 : Nat := 118140960795 + 2120652 * 2 ^ 59
def prefixEnd_2120652 : Nat := 4983230072969 + 3 ^ 40 * 2120652 * 2
def baseEnd_2120652 : Nat := 1088913776918542172997305

theorem tailTrace_2120652 : CollatzResearch.WordTrace tailWord_2120652 prefixEnd_2120652 1088913776918542172997305 := by
  unfold tailWord_2120652
  simp only [CollatzResearch.WordTrace]
  refine ⟨38673266356623728686102105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51564355142164971581469473 38673266356623728686102105)
  ·
    refine ⟨29004949767467796514576579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38673266356623728686102105 29004949767467796514576579)
    ·
      refine ⟨43507424651201694771864869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29004949767467796514576579 43507424651201694771864869)
      ·
        refine ⟨8157642122100317769724663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43507424651201694771864869 8157642122100317769724663)
        ·
          refine ⟨12236463183150476654586995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8157642122100317769724663 12236463183150476654586995)
          ·
            refine ⟨18354694774725714981880493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12236463183150476654586995 18354694774725714981880493)
            ·
              refine ⟨6883010540522143118205185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18354694774725714981880493 6883010540522143118205185)
              ·
                refine ⟨5162257905391607338653889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6883010540522143118205185 5162257905391607338653889)
                ·
                  refine ⟨3871693429043705503990417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5162257905391607338653889 3871693429043705503990417)
                  ·
                    refine ⟨2903770071782779127992813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3871693429043705503990417 2903770071782779127992813)
                    ·
                      refine ⟨1088913776918542172997305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2903770071782779127992813 1088913776918542172997305)
                      ·
                        rfl

theorem cell23_2120652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_2120652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2120652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2120652 prefixEnd_2120652 := by exact prefixLift 2120652
  have htrace : WordTrace (prefixWord ++ tailWord_2120652) baseStart_2120652 baseEnd_2120652 := by
    simpa [prefixWord, tailWord_2120652, baseEnd_2120652] using wordTrace_append hprefix tailTrace_2120652
  have hstable : (prefixWord ++ tailWord_2120652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2120652).length < 2 ^ (prefixWord ++ tailWord_2120652).sum := by decide
  have hdescent : baseEnd_2120652 < baseStart_2120652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2120652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2120699 : List Nat := [1, 1, 1, 1, 1, 3, 3, 7, 1, 1, 3]
def baseStart_2120699 : Nat := 118140960795 + 2120699 * 2 ^ 59
def prefixEnd_2120699 : Nat := 4983230072969 + 3 ^ 40 * 2120699 * 2
def baseEnd_2120699 : Nat := 1088937910509303489109589

theorem tailTrace_2120699 : CollatzResearch.WordTrace tailWord_2120699 prefixEnd_2120699 1088937910509303489109589 := by
  unfold tailWord_2120699
  simp only [CollatzResearch.WordTrace]
  refine ⟨77348246944077184399165151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51565497962718122932776767 77348246944077184399165151)
  ·
    refine ⟨116022370416115776598747727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77348246944077184399165151 116022370416115776598747727)
    ·
      refine ⟨174033555624173664898121591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116022370416115776598747727 174033555624173664898121591)
      ·
        refine ⟨261050333436260497347182387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174033555624173664898121591 261050333436260497347182387)
        ·
          refine ⟨391575500154390746020773581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 261050333436260497347182387 391575500154390746020773581)
          ·
            refine ⟨146840812557896529757790093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 391575500154390746020773581 146840812557896529757790093)
            ·
              refine ⟨55065304709211198659171285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 146840812557896529757790093 55065304709211198659171285)
              ·
                refine ⟨1290593079122137468574327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 55065304709211198659171285 1290593079122137468574327)
                ·
                  refine ⟨1935889618683206202861491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1290593079122137468574327 1935889618683206202861491)
                  ·
                    refine ⟨2903834428024809304292237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1935889618683206202861491 2903834428024809304292237)
                    ·
                      refine ⟨1088937910509303489109589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2903834428024809304292237 1088937910509303489109589)
                      ·
                        rfl

theorem cell23_2120699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 7, 1, 1, 3].length) (baseStart_2120699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2120699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2120699 prefixEnd_2120699 := by exact prefixLift 2120699
  have htrace : WordTrace (prefixWord ++ tailWord_2120699) baseStart_2120699 baseEnd_2120699 := by
    simpa [prefixWord, tailWord_2120699, baseEnd_2120699] using wordTrace_append hprefix tailTrace_2120699
  have hstable : (prefixWord ++ tailWord_2120699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2120699).length < 2 ^ (prefixWord ++ tailWord_2120699).sum := by decide
  have hdescent : baseEnd_2120699 < baseStart_2120699 := by decide
  rcases family_descends (prefixWord ++ tailWord_2120699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2120706 : List Nat := [3, 4, 1, 3, 1, 1, 2, 2, 6]
def baseStart_2120706 : Nat := 118140960795 + 2120706 * 2 ^ 59
def prefixEnd_2120706 : Nat := 4983230072969 + 3 ^ 40 * 2120706 * 2
def baseEnd_2120706 : Nat := 120993500541542773524673

theorem tailTrace_2120706 : CollatzResearch.WordTrace tailWord_2120706 prefixEnd_2120706 120993500541542773524673 := by
  unfold tailWord_2120706
  simp only [CollatzResearch.WordTrace]
  refine ⟨19337125563762956148667493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51565668170034549729779981 19337125563762956148667493)
  ·
    refine ⟨3625711043205554277875155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19337125563762956148667493 3625711043205554277875155)
    ·
      refine ⟨5438566564808331416812733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3625711043205554277875155 5438566564808331416812733)
      ·
        refine ⟨2039462461803124281304775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5438566564808331416812733 2039462461803124281304775)
        ·
          refine ⟨3059193692704686421957163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2039462461803124281304775 3059193692704686421957163)
          ·
            refine ⟨4588790539057029632935745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3059193692704686421957163 4588790539057029632935745)
            ·
              refine ⟨3441592904292772224701809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4588790539057029632935745 3441592904292772224701809)
              ·
                refine ⟨2581194678219579168526357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3441592904292772224701809 2581194678219579168526357)
                ·
                  refine ⟨120993500541542773524673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2581194678219579168526357 120993500541542773524673)
                  ·
                    rfl

theorem cell23_2120706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 2, 6].length) (baseStart_2120706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2120706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2120706 prefixEnd_2120706 := by exact prefixLift 2120706
  have htrace : WordTrace (prefixWord ++ tailWord_2120706) baseStart_2120706 baseEnd_2120706 := by
    simpa [prefixWord, tailWord_2120706, baseEnd_2120706] using wordTrace_append hprefix tailTrace_2120706
  have hstable : (prefixWord ++ tailWord_2120706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2120706).length < 2 ^ (prefixWord ++ tailWord_2120706).sum := by decide
  have hdescent : baseEnd_2120706 < baseStart_2120706 := by decide
  rcases family_descends (prefixWord ++ tailWord_2120706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2120716 : List Nat := [2, 2, 1, 2, 3, 3, 1, 4, 1, 1, 3]
def baseStart_2120716 : Nat := 118140960795 + 2120716 * 2 ^ 59
def prefixEnd_2120716 : Nat := 4983230072969 + 3 ^ 40 * 2120716 * 2
def baseEnd_2120716 : Nat := 1088946639680429922597011

theorem tailTrace_2120716 : CollatzResearch.WordTrace tailWord_2120716 prefixEnd_2120716 1088946639680429922597011 := by
  unfold tailWord_2120716
  simp only [CollatzResearch.WordTrace]
  refine ⟨38674433492507798151267001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51565911323343730868356001 38674433492507798151267001)
  ·
    refine ⟨29005825119380848613450251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38674433492507798151267001 29005825119380848613450251)
    ·
      refine ⟨43508737679071272920175377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29005825119380848613450251 43508737679071272920175377)
      ·
        refine ⟨32631553259303454690131533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43508737679071272920175377 32631553259303454690131533)
        ·
          refine ⟨12236832472238795508799325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32631553259303454690131533 12236832472238795508799325)
          ·
            refine ⟨4588812177089548315799747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12236832472238795508799325 4588812177089548315799747)
            ·
              refine ⟨6883218265634322473699621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4588812177089548315799747 6883218265634322473699621)
              ·
                refine ⟨1290603424806435463818679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6883218265634322473699621 1290603424806435463818679)
                ·
                  refine ⟨1935905137209653195728019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1290603424806435463818679 1935905137209653195728019)
                  ·
                    refine ⟨2903857705814479793592029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1935905137209653195728019 2903857705814479793592029)
                    ·
                      refine ⟨1088946639680429922597011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2903857705814479793592029 1088946639680429922597011)
                      ·
                        rfl

theorem cell23_2120716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 4, 1, 1, 3].length) (baseStart_2120716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2120716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2120716 prefixEnd_2120716 := by exact prefixLift 2120716
  have htrace : WordTrace (prefixWord ++ tailWord_2120716) baseStart_2120716 baseEnd_2120716 := by
    simpa [prefixWord, tailWord_2120716, baseEnd_2120716] using wordTrace_append hprefix tailTrace_2120716
  have hstable : (prefixWord ++ tailWord_2120716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2120716).length < 2 ^ (prefixWord ++ tailWord_2120716).sum := by decide
  have hdescent : baseEnd_2120716 < baseStart_2120716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2120716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2120739 : List Nat := [1, 1, 1, 4, 3, 2, 1, 1, 5, 2, 2]
def baseStart_2120739 : Nat := 118140960795 + 2120739 * 2 ^ 59
def prefixEnd_2120739 : Nat := 4983230072969 + 3 ^ 40 * 2120739 * 2
def baseEnd_2120739 : Nat := 1088958449735483332609405

theorem tailTrace_2120739 : CollatzResearch.WordTrace tailWord_2120739 prefixEnd_2120739 1088958449735483332609405 := by
  unfold tailWord_2120739
  simp only [CollatzResearch.WordTrace]
  refine ⟨77349705863932271230621271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51566470575954847487080847 77349705863932271230621271)
  ·
    refine ⟨116024558795898406845931907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77349705863932271230621271 116024558795898406845931907)
    ·
      refine ⟨174036838193847610268897861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116024558795898406845931907 174036838193847610268897861)
      ·
        refine ⟨32631907161346426925418349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 174036838193847610268897861 32631907161346426925418349)
        ·
          refine ⟨12236965185504910097031881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32631907161346426925418349 12236965185504910097031881)
          ·
            refine ⟨9177723889128682572773911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12236965185504910097031881 9177723889128682572773911)
            ·
              refine ⟨13766585833693023859160867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9177723889128682572773911 13766585833693023859160867)
              ·
                refine ⟨20649878750539535788741301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13766585833693023859160867 20649878750539535788741301)
                ·
                  refine ⟨1935926132863081480194497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20649878750539535788741301 1935926132863081480194497)
                  ·
                    refine ⟨1451944599647311110145873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1935926132863081480194497 1451944599647311110145873)
                    ·
                      refine ⟨1088958449735483332609405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1451944599647311110145873 1088958449735483332609405)
                      ·
                        rfl

theorem cell23_2120739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 5, 2, 2].length) (baseStart_2120739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2120739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2120739 prefixEnd_2120739 := by exact prefixLift 2120739
  have htrace : WordTrace (prefixWord ++ tailWord_2120739) baseStart_2120739 baseEnd_2120739 := by
    simpa [prefixWord, tailWord_2120739, baseEnd_2120739] using wordTrace_append hprefix tailTrace_2120739
  have hstable : (prefixWord ++ tailWord_2120739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2120739).length < 2 ^ (prefixWord ++ tailWord_2120739).sum := by decide
  have hdescent : baseEnd_2120739 < baseStart_2120739 := by decide
  rcases family_descends (prefixWord ++ tailWord_2120739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2120743 : List Nat := [1, 1, 7, 1, 1, 3, 1, 1, 2, 3, 2]
def baseStart_2120743 : Nat := 118140960795 + 2120743 * 2 ^ 59
def prefixEnd_2120743 : Nat := 4983230072969 + 3 ^ 40 * 2120743 * 2
def baseEnd_2120743 : Nat := 1088960503658101316959387

theorem tailTrace_2120743 : CollatzResearch.WordTrace tailWord_2120743 prefixEnd_2120743 1088960503658101316959387 := by
  unfold tailWord_2120743
  simp only [CollatzResearch.WordTrace]
  refine ⟨77349851755917779913766883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51566567837278519942511255 77349851755917779913766883)
  ·
    refine ⟨116024777633876669870650325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77349851755917779913766883 116024777633876669870650325)
    ·
      refine ⟨2719330725793984450093367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 116024777633876669870650325 2719330725793984450093367)
      ·
        refine ⟨4078996088690976675140051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2719330725793984450093367 4078996088690976675140051)
        ·
          refine ⟨6118494133036465012710077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4078996088690976675140051 6118494133036465012710077)
          ·
            refine ⟨2294435299888674379766279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6118494133036465012710077 2294435299888674379766279)
            ·
              refine ⟨3441652949833011569649419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2294435299888674379766279 3441652949833011569649419)
              ·
                refine ⟨5162479424749517354474129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3441652949833011569649419 5162479424749517354474129)
                ·
                  refine ⟨3871859568562138015855597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5162479424749517354474129 3871859568562138015855597)
                  ·
                    refine ⟨1451947338210801755945849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3871859568562138015855597 1451947338210801755945849)
                    ·
                      refine ⟨1088960503658101316959387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1451947338210801755945849 1088960503658101316959387)
                      ·
                        rfl

theorem cell23_2120743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_2120743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2120743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2120743 prefixEnd_2120743 := by exact prefixLift 2120743
  have htrace : WordTrace (prefixWord ++ tailWord_2120743) baseStart_2120743 baseEnd_2120743 := by
    simpa [prefixWord, tailWord_2120743, baseEnd_2120743] using wordTrace_append hprefix tailTrace_2120743
  have hstable : (prefixWord ++ tailWord_2120743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2120743).length < 2 ^ (prefixWord ++ tailWord_2120743).sum := by decide
  have hdescent : baseEnd_2120743 < baseStart_2120743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2120743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2120756 : List Nat := [2, 5, 1, 2, 1, 2, 1, 3, 1, 1, 4]
def baseStart_2120756 : Nat := 118140960795 + 2120756 * 2 ^ 59
def prefixEnd_2120756 : Nat := 4983230072969 + 3 ^ 40 * 2120756 * 2
def baseEnd_2120756 : Nat := 1088967178906609766096827

theorem tailTrace_2120756 : CollatzResearch.WordTrace tailWord_2120756 prefixEnd_2120756 1088967178906609766096827 := by
  unfold tailWord_2120756
  simp only [CollatzResearch.WordTrace]
  refine ⟨38675162952435341566995061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51566883936580455422660081 38675162952435341566995061)
  ·
    refine ⟨3625796526790813271905787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38675162952435341566995061 3625796526790813271905787)
    ·
      refine ⟨5438694790186219907858681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3625796526790813271905787 5438694790186219907858681)
      ·
        refine ⟨4079021092639664930894011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5438694790186219907858681 4079021092639664930894011)
        ·
          refine ⟨6118531638959497396341017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4079021092639664930894011 6118531638959497396341017)
          ·
            refine ⟨4588898729219623047255763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6118531638959497396341017 4588898729219623047255763)
            ·
              refine ⟨6883348093829434570883645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4588898729219623047255763 6883348093829434570883645)
              ·
                refine ⟨2581255535186037964081367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6883348093829434570883645 2581255535186037964081367)
                ·
                  refine ⟨3871883302779056946122051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2581255535186037964081367 3871883302779056946122051)
                  ·
                    refine ⟨5807824954168585419183077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3871883302779056946122051 5807824954168585419183077)
                    ·
                      refine ⟨1088967178906609766096827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5807824954168585419183077 1088967178906609766096827)
                      ·
                        rfl

theorem cell23_2120756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_2120756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2120756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2120756 prefixEnd_2120756 := by exact prefixLift 2120756
  have htrace : WordTrace (prefixWord ++ tailWord_2120756) baseStart_2120756 baseEnd_2120756 := by
    simpa [prefixWord, tailWord_2120756, baseEnd_2120756] using wordTrace_append hprefix tailTrace_2120756
  have hstable : (prefixWord ++ tailWord_2120756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2120756).length < 2 ^ (prefixWord ++ tailWord_2120756).sum := by decide
  have hdescent : baseEnd_2120756 < baseStart_2120756 := by decide
  rcases family_descends (prefixWord ++ tailWord_2120756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2120766 : List Nat := [4, 2, 1, 3, 1, 1, 3, 2, 2, 4]
def baseStart_2120766 : Nat := 118140960795 + 2120766 * 2 ^ 59
def prefixEnd_2120766 : Nat := 4983230072969 + 3 ^ 40 * 2120766 * 2
def baseEnd_2120766 : Nat := 362990771237718242323927

theorem tailTrace_2120766 : CollatzResearch.WordTrace tailWord_2120766 prefixEnd_2120766 362990771237718242323927 := by
  unfold tailWord_2120766
  simp only [CollatzResearch.WordTrace]
  refine ⟨9668836329354306855231769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51567127089889636561236101 9668836329354306855231769)
  ·
    refine ⟨7251627247015730141423827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9668836329354306855231769 7251627247015730141423827)
    ·
      refine ⟨10877440870523595212135741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7251627247015730141423827 10877440870523595212135741)
      ·
        refine ⟨4079040326446348204550903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10877440870523595212135741 4079040326446348204550903)
        ·
          refine ⟨6118560489669522306826355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4079040326446348204550903 6118560489669522306826355)
          ·
            refine ⟨9177840734504283460239533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6118560489669522306826355 9177840734504283460239533)
            ·
              refine ⟨3441690275439106297589825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9177840734504283460239533 3441690275439106297589825)
              ·
                refine ⟨2581267706579329723192369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3441690275439106297589825 2581267706579329723192369)
                ·
                  refine ⟨1935950779934497292394277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2581267706579329723192369 1935950779934497292394277)
                  ·
                    refine ⟨362990771237718242323927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1935950779934497292394277 362990771237718242323927)
                    ·
                      rfl

theorem cell23_2120766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 2, 2, 4].length) (baseStart_2120766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2120766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2120766 prefixEnd_2120766 := by exact prefixLift 2120766
  have htrace : WordTrace (prefixWord ++ tailWord_2120766) baseStart_2120766 baseEnd_2120766 := by
    simpa [prefixWord, tailWord_2120766, baseEnd_2120766] using wordTrace_append hprefix tailTrace_2120766
  have hstable : (prefixWord ++ tailWord_2120766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2120766).length < 2 ^ (prefixWord ++ tailWord_2120766).sum := by decide
  have hdescent : baseEnd_2120766 < baseStart_2120766 := by decide
  rcases family_descends (prefixWord ++ tailWord_2120766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2120840 : List Nat := [2, 1, 3, 4, 2, 2, 2, 1, 2, 1, 3]
def baseStart_2120840 : Nat := 118140960795 + 2120840 * 2 ^ 59
def prefixEnd_2120840 : Nat := 4983230072969 + 3 ^ 40 * 2120840 * 2
def baseEnd_2120840 : Nat := 1089010311281587437446441

theorem tailTrace_2120840 : CollatzResearch.WordTrace tailWord_2120840 prefixEnd_2120840 1089010311281587437446441 := by
  unfold tailWord_2120840
  simp only [CollatzResearch.WordTrace]
  refine ⟨38676694818283182740023987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51568926424377576986698649 38676694818283182740023987)
  ·
    refine ⟨58015042227424774110035981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38676694818283182740023987 58015042227424774110035981)
    ·
      refine ⟨21755640835284290291263493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58015042227424774110035981 21755640835284290291263493)
      ·
        refine ⟨4079182656615804429611905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21755640835284290291263493 4079182656615804429611905)
        ·
          refine ⟨3059386992461853322208929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4079182656615804429611905 3059386992461853322208929)
          ·
            refine ⟨2294540244346389991656697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3059386992461853322208929 2294540244346389991656697)
            ·
              refine ⟨1720905183259792493742523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2294540244346389991656697 1720905183259792493742523)
              ·
                refine ⟨2581357774889688740613785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1720905183259792493742523 2581357774889688740613785)
                ·
                  refine ⟨1936018331167266555460339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2581357774889688740613785 1936018331167266555460339)
                  ·
                    refine ⟨2904027496750899833190509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1936018331167266555460339 2904027496750899833190509)
                    ·
                      refine ⟨1089010311281587437446441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2904027496750899833190509 1089010311281587437446441)
                      ·
                        rfl

theorem cell23_2120840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_2120840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2120840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2120840 prefixEnd_2120840 := by exact prefixLift 2120840
  have htrace : WordTrace (prefixWord ++ tailWord_2120840) baseStart_2120840 baseEnd_2120840 := by
    simpa [prefixWord, tailWord_2120840, baseEnd_2120840] using wordTrace_append hprefix tailTrace_2120840
  have hstable : (prefixWord ++ tailWord_2120840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2120840).length < 2 ^ (prefixWord ++ tailWord_2120840).sum := by decide
  have hdescent : baseEnd_2120840 < baseStart_2120840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2120840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2120842 : List Nat := [3, 1, 2, 3, 1, 1, 2, 1, 1, 4, 4]
def baseStart_2120842 : Nat := 118140960795 + 2120842 * 2 ^ 59
def prefixEnd_2120842 : Nat := 4983230072969 + 3 ^ 40 * 2120842 * 2
def baseEnd_2120842 : Nat := 1089011338242896429621431

theorem tailTrace_2120842 : CollatzResearch.WordTrace tailWord_2120842 prefixEnd_2120842 1089011338242896429621431 := by
  unfold tailWord_2120842
  simp only [CollatzResearch.WordTrace]
  refine ⟨19338365645639779955405195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51568975055039413214413853 19338365645639779955405195)
  ·
    refine ⟨29007548468459669933107793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19338365645639779955405195 29007548468459669933107793)
    ·
      refine ⟨21755661351344752449830845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29007548468459669933107793 21755661351344752449830845)
      ·
        refine ⟨8158373006754282168686567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21755661351344752449830845 8158373006754282168686567)
        ·
          refine ⟨12237559510131423253029851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8158373006754282168686567 12237559510131423253029851)
          ·
            refine ⟨18356339265197134879544777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12237559510131423253029851 18356339265197134879544777)
            ·
              refine ⟨13767254448897851159658583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18356339265197134879544777 13767254448897851159658583)
              ·
                refine ⟨20650881673346776739487875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13767254448897851159658583 20650881673346776739487875)
                ·
                  refine ⟨30976322510020165109231813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20650881673346776739487875 30976322510020165109231813)
                  ·
                    refine ⟨5808060470628780957980965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30976322510020165109231813 5808060470628780957980965)
                    ·
                      refine ⟨1089011338242896429621431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5808060470628780957980965 1089011338242896429621431)
                      ·
                        rfl

theorem cell23_2120842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_2120842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2120842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2120842 prefixEnd_2120842 := by exact prefixLift 2120842
  have htrace : WordTrace (prefixWord ++ tailWord_2120842) baseStart_2120842 baseEnd_2120842 := by
    simpa [prefixWord, tailWord_2120842, baseEnd_2120842] using wordTrace_append hprefix tailTrace_2120842
  have hstable : (prefixWord ++ tailWord_2120842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2120842).length < 2 ^ (prefixWord ++ tailWord_2120842).sum := by decide
  have hdescent : baseEnd_2120842 < baseStart_2120842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2120842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2120875 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 7]
def baseStart_2120875 : Nat := 118140960795 + 2120875 * 2 ^ 59
def prefixEnd_2120875 : Nat := 4983230072969 + 3 ^ 40 * 2120875 * 2
def baseEnd_2120875 : Nat := 1089028283104494800508779

theorem tailTrace_2120875 : CollatzResearch.WordTrace tailWord_2120875 prefixEnd_2120875 1089028283104494800508779 := by
  unfold tailWord_2120875
  simp only [CollatzResearch.WordTrace]
  refine ⟨77354666191439566457572079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51569777460959710971714719 77354666191439566457572079)
  ·
    refine ⟨116031999287159349686358119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77354666191439566457572079 116031999287159349686358119)
    ·
      refine ⟨174047998930739024529537179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116031999287159349686358119 174047998930739024529537179)
      ·
        refine ⟨261071998396108536794305769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174047998930739024529537179 261071998396108536794305769)
        ·
          refine ⟨195803998797081402595729327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 261071998396108536794305769 195803998797081402595729327)
          ·
            refine ⟨293705998195622103893593991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 195803998797081402595729327 293705998195622103893593991)
            ·
              refine ⟨440558997293433155840390987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 293705998195622103893593991 440558997293433155840390987)
              ·
                refine ⟨660838495940149733760586481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 440558997293433155840390987 660838495940149733760586481)
                ·
                  refine ⟨495628871955112300320439861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 660838495940149733760586481 495628871955112300320439861)
                  ·
                    refine ⟨46465206745791778155041237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 495628871955112300320439861 46465206745791778155041237)
                    ·
                      refine ⟨1089028283104494800508779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 46465206745791778155041237 1089028283104494800508779)
                      ·
                        rfl

theorem cell23_2120875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 7].length) (baseStart_2120875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2120875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2120875 prefixEnd_2120875 := by exact prefixLift 2120875
  have htrace : WordTrace (prefixWord ++ tailWord_2120875) baseStart_2120875 baseEnd_2120875 := by
    simpa [prefixWord, tailWord_2120875, baseEnd_2120875] using wordTrace_append hprefix tailTrace_2120875
  have hstable : (prefixWord ++ tailWord_2120875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2120875).length < 2 ^ (prefixWord ++ tailWord_2120875).sum := by decide
  have hdescent : baseEnd_2120875 < baseStart_2120875 := by decide
  rcases family_descends (prefixWord ++ tailWord_2120875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2120889 : List Nat := [1, 2, 1, 4, 1, 3, 1, 1, 2, 5, 2]
def baseStart_2120889 : Nat := 118140960795 + 2120889 * 2 ^ 59
def prefixEnd_2120889 : Nat := 4983230072969 + 3 ^ 40 * 2120889 * 2
def baseEnd_2120889 : Nat := 1089035471833657745733715

theorem tailTrace_2120889 : CollatzResearch.WordTrace tailWord_2120889 prefixEnd_2120889 1089035471833657745733715 := by
  unfold tailWord_2120889
  simp only [CollatzResearch.WordTrace]
  refine ⟨77355176813388846848581721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51570117875592564565721147 77355176813388846848581721)
  ·
    refine ⟨58016382610041635136436291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77355176813388846848581721 58016382610041635136436291)
    ·
      refine ⟨87024573915062452704654437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58016382610041635136436291 87024573915062452704654437)
      ·
        refine ⟨16317107609074209882122707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 87024573915062452704654437 16317107609074209882122707)
        ·
          refine ⟨24475661413611314823184061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16317107609074209882122707 24475661413611314823184061)
          ·
            refine ⟨9178373030104243058694023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24475661413611314823184061 9178373030104243058694023)
            ·
              refine ⟨13767559545156364588041035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9178373030104243058694023 13767559545156364588041035)
              ·
                refine ⟨20651339317734546882061553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13767559545156364588041035 20651339317734546882061553)
                ·
                  refine ⟨15488504488300910161546165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20651339317734546882061553 15488504488300910161546165)
                  ·
                    refine ⟨1452047295778210327644953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15488504488300910161546165 1452047295778210327644953)
                    ·
                      refine ⟨1089035471833657745733715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1452047295778210327644953 1089035471833657745733715)
                      ·
                        rfl

theorem cell23_2120889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 2, 5, 2].length) (baseStart_2120889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2120889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2120889 prefixEnd_2120889 := by exact prefixLift 2120889
  have htrace : WordTrace (prefixWord ++ tailWord_2120889) baseStart_2120889 baseEnd_2120889 := by
    simpa [prefixWord, tailWord_2120889, baseEnd_2120889] using wordTrace_append hprefix tailTrace_2120889
  have hstable : (prefixWord ++ tailWord_2120889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2120889).length < 2 ^ (prefixWord ++ tailWord_2120889).sum := by decide
  have hdescent : baseEnd_2120889 < baseStart_2120889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2120889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2120916 : List Nat := [2, 4, 1, 4, 1, 1, 1, 1, 1, 7]
def baseStart_2120916 : Nat := 118140960795 + 2120916 * 2 ^ 59
def prefixEnd_2120916 : Nat := 4983230072969 + 3 ^ 40 * 2120916 * 2
def baseEnd_2120916 : Nat := 363016445270443046698697

theorem tailTrace_2120916 : CollatzResearch.WordTrace tailWord_2120916 prefixEnd_2120916 363016445270443046698697 := by
  unfold tailWord_2120916
  simp only [CollatzResearch.WordTrace]
  refine ⟨38678080792145515229907301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51570774389527353639876401 38678080792145515229907301)
  ·
    refine ⟨7252140148527284105607619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38678080792145515229907301 7252140148527284105607619)
    ·
      refine ⟨10878210222790926158411429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7252140148527284105607619 10878210222790926158411429)
      ·
        refine ⟨2039664416773298654702143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10878210222790926158411429 2039664416773298654702143)
        ·
          refine ⟨3059496625159947982053215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2039664416773298654702143 3059496625159947982053215)
          ·
            refine ⟨4589244937739921973079823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3059496625159947982053215 4589244937739921973079823)
            ·
              refine ⟨6883867406609882959619735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4589244937739921973079823 6883867406609882959619735)
              ·
                refine ⟨10325801109914824439429603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6883867406609882959619735 10325801109914824439429603)
                ·
                  refine ⟨15488701664872236659144405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10325801109914824439429603 15488701664872236659144405)
                  ·
                    refine ⟨363016445270443046698697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15488701664872236659144405 363016445270443046698697)
                    ·
                      rfl

theorem cell23_2120916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 1, 1, 7].length) (baseStart_2120916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2120916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2120916 prefixEnd_2120916 := by exact prefixLift 2120916
  have htrace : WordTrace (prefixWord ++ tailWord_2120916) baseStart_2120916 baseEnd_2120916 := by
    simpa [prefixWord, tailWord_2120916, baseEnd_2120916] using wordTrace_append hprefix tailTrace_2120916
  have hstable : (prefixWord ++ tailWord_2120916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2120916).length < 2 ^ (prefixWord ++ tailWord_2120916).sum := by decide
  have hdescent : baseEnd_2120916 < baseStart_2120916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2120916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2120919 : List Nat := [1, 1, 3, 2, 1, 2, 5, 1, 2, 1, 4]
def baseStart_2120919 : Nat := 118140960795 + 2120919 * 2 ^ 59
def prefixEnd_2120919 : Nat := 4983230072969 + 3 ^ 40 * 2120919 * 2
def baseEnd_2120919 : Nat := 1089050876253292628358577

theorem tailTrace_2120919 : CollatzResearch.WordTrace tailWord_2120919 prefixEnd_2120919 1089050876253292628358577 := by
  unfold tailWord_2120919
  simp only [CollatzResearch.WordTrace]
  refine ⟨77356271003280161972173811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51570847335520107981449207 77356271003280161972173811)
  ·
    refine ⟨116034406504920242958260717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77356271003280161972173811 116034406504920242958260717)
    ·
      refine ⟨43512902439345091109347769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116034406504920242958260717 43512902439345091109347769)
      ·
        refine ⟨32634676829508818332010827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43512902439345091109347769 32634676829508818332010827)
        ·
          refine ⟨48952015244263227498016241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32634676829508818332010827 48952015244263227498016241)
          ·
            refine ⟨36714011433197420623512181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48952015244263227498016241 36714011433197420623512181)
            ·
              refine ⟨3441938571862258183454267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36714011433197420623512181 3441938571862258183454267)
              ·
                refine ⟨5162907857793387275181401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3441938571862258183454267 5162907857793387275181401)
                ·
                  refine ⟨3872180893345040456386051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5162907857793387275181401 3872180893345040456386051)
                  ·
                    refine ⟨5808271340017560684579077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3872180893345040456386051 5808271340017560684579077)
                    ·
                      refine ⟨1089050876253292628358577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5808271340017560684579077 1089050876253292628358577)
                      ·
                        rfl

theorem cell23_2120919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 1, 2, 1, 4].length) (baseStart_2120919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2120919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2120919 prefixEnd_2120919 := by exact prefixLift 2120919
  have htrace : WordTrace (prefixWord ++ tailWord_2120919) baseStart_2120919 baseEnd_2120919 := by
    simpa [prefixWord, tailWord_2120919, baseEnd_2120919] using wordTrace_append hprefix tailTrace_2120919
  have hstable : (prefixWord ++ tailWord_2120919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2120919).length < 2 ^ (prefixWord ++ tailWord_2120919).sum := by decide
  have hdescent : baseEnd_2120919 < baseStart_2120919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2120919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2120932 : List Nat := [2, 3, 1, 1, 1, 2, 3, 1, 2, 1, 6]
def baseStart_2120932 : Nat := 118140960795 + 2120932 * 2 ^ 59
def prefixEnd_2120932 : Nat := 4983230072969 + 3 ^ 40 * 2120932 * 2
def baseEnd_2120932 : Nat := 1089057551501801077496017

theorem tailTrace_2120932 : CollatzResearch.WordTrace tailWord_2120932 prefixEnd_2120932 1089057551501801077496017 := by
  unfold tailWord_2120932
  simp only [CollatzResearch.WordTrace]
  refine ⟨38678372576116532596198525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51571163434822043461598033 38678372576116532596198525)
  ·
    refine ⟨14504389716043699723574447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38678372576116532596198525 14504389716043699723574447)
    ·
      refine ⟨21756584574065549585361671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14504389716043699723574447 21756584574065549585361671)
      ·
        refine ⟨32634876861098324378042507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21756584574065549585361671 32634876861098324378042507)
        ·
          refine ⟨48952315291647486567063761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32634876861098324378042507 48952315291647486567063761)
          ·
            refine ⟨36714236468735614925297821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48952315291647486567063761 36714236468735614925297821)
            ·
              refine ⟨13767838675775855596986683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36714236468735614925297821 13767838675775855596986683)
              ·
                refine ⟨20651758013663783395480025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13767838675775855596986683 20651758013663783395480025)
                ·
                  refine ⟨15488818510247837546610019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20651758013663783395480025 15488818510247837546610019)
                  ·
                    refine ⟨23233227765371756319915029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15488818510247837546610019 23233227765371756319915029)
                    ·
                      refine ⟨1089057551501801077496017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23233227765371756319915029 1089057551501801077496017)
                      ·
                        rfl

theorem cell23_2120932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 2, 1, 6].length) (baseStart_2120932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2120932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2120932 prefixEnd_2120932 := by exact prefixLift 2120932
  have htrace : WordTrace (prefixWord ++ tailWord_2120932) baseStart_2120932 baseEnd_2120932 := by
    simpa [prefixWord, tailWord_2120932, baseEnd_2120932] using wordTrace_append hprefix tailTrace_2120932
  have hstable : (prefixWord ++ tailWord_2120932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2120932).length < 2 ^ (prefixWord ++ tailWord_2120932).sum := by decide
  have hdescent : baseEnd_2120932 < baseStart_2120932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2120932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2120990 : List Nat := [4, 3, 2, 1, 2, 1, 1, 2, 2, 2, 3]
def baseStart_2120990 : Nat := 118140960795 + 2120990 * 2 ^ 59
def prefixEnd_2120990 : Nat := 4983230072969 + 3 ^ 40 * 2120990 * 2
def baseEnd_2120990 : Nat := 1089087333379761850570751

theorem tailTrace_2120990 : CollatzResearch.WordTrace tailWord_2120990 prefixEnd_2120990 1089087333379761850570751 := by
  unfold tailWord_2120990
  simp only [CollatzResearch.WordTrace]
  refine ⟨9669857573252867637251053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51572573724015294065338949 9669857573252867637251053)
  ·
    refine ⟨3626196589969825363969145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9669857573252867637251053 3626196589969825363969145)
    ·
      refine ⟨2719647442477369022976859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3626196589969825363969145 2719647442477369022976859)
      ·
        refine ⟨4079471163716053534465289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2719647442477369022976859 4079471163716053534465289)
        ·
          refine ⟨3059603372787040150848967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4079471163716053534465289 3059603372787040150848967)
          ·
            refine ⟨4589405059180560226273451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3059603372787040150848967 4589405059180560226273451)
            ·
              refine ⟨6884107588770840339410177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4589405059180560226273451 6884107588770840339410177)
              ·
                refine ⟨5163080691578130254557633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6884107588770840339410177 5163080691578130254557633)
                ·
                  refine ⟨3872310518683597690918225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5163080691578130254557633 3872310518683597690918225)
                  ·
                    refine ⟨2904232889012698268188669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3872310518683597690918225 2904232889012698268188669)
                    ·
                      refine ⟨1089087333379761850570751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2904232889012698268188669 1089087333379761850570751)
                      ·
                        rfl

theorem cell23_2120990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_2120990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2120990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2120990 prefixEnd_2120990 := by exact prefixLift 2120990
  have htrace : WordTrace (prefixWord ++ tailWord_2120990) baseStart_2120990 baseEnd_2120990 := by
    simpa [prefixWord, tailWord_2120990, baseEnd_2120990] using wordTrace_append hprefix tailTrace_2120990
  have hstable : (prefixWord ++ tailWord_2120990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2120990).length < 2 ^ (prefixWord ++ tailWord_2120990).sum := by decide
  have hdescent : baseEnd_2120990 < baseStart_2120990 := by decide
  rcases family_descends (prefixWord ++ tailWord_2120990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2121097 : List Nat := [1, 2, 1, 1, 8, 1, 2, 1, 1, 2, 3]
def baseStart_2121097 : Nat := 118140960795 + 2121097 * 2 ^ 59
def prefixEnd_2121097 : Nat := 4983230072969 + 3 ^ 40 * 2121097 * 2
def baseEnd_2121097 : Nat := 1089142275809792931932759

theorem tailTrace_2121097 : CollatzResearch.WordTrace tailWord_2121097 prefixEnd_2121097 1089142275809792931932759 := by
  unfold tailWord_2121097
  simp only [CollatzResearch.WordTrace]
  refine ⟨77362763196635298372153545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51575175464423532248102363 77362763196635298372153545)
  ·
    refine ⟨58022072397476473779115159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77362763196635298372153545 58022072397476473779115159)
    ·
      refine ⟨87033108596214710668672739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58022072397476473779115159 87033108596214710668672739)
      ·
        refine ⟨130549662894322066003009109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87033108596214710668672739 130549662894322066003009109)
        ·
          refine ⟨1529878862042836710972763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 130549662894322066003009109 1529878862042836710972763)
          ·
            refine ⟨2294818293064255066459145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1529878862042836710972763 2294818293064255066459145)
            ·
              refine ⟨1721113719798191299844359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2294818293064255066459145 1721113719798191299844359)
              ·
                refine ⟨2581670579697286949766539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1721113719798191299844359 2581670579697286949766539)
                ·
                  refine ⟨3872505869545930424649809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2581670579697286949766539 3872505869545930424649809)
                  ·
                    refine ⟨2904379402159447818487357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3872505869545930424649809 2904379402159447818487357)
                    ·
                      refine ⟨1089142275809792931932759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2904379402159447818487357 1089142275809792931932759)
                      ·
                        rfl

theorem cell23_2121097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 2, 1, 1, 2, 3].length) (baseStart_2121097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2121097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2121097 prefixEnd_2121097 := by exact prefixLift 2121097
  have htrace : WordTrace (prefixWord ++ tailWord_2121097) baseStart_2121097 baseEnd_2121097 := by
    simpa [prefixWord, tailWord_2121097, baseEnd_2121097] using wordTrace_append hprefix tailTrace_2121097
  have hstable : (prefixWord ++ tailWord_2121097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2121097).length < 2 ^ (prefixWord ++ tailWord_2121097).sum := by decide
  have hdescent : baseEnd_2121097 < baseStart_2121097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2121097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2121109 : List Nat := [1, 3, 2, 1, 1, 2, 3, 2, 2, 6]
def baseStart_2121109 : Nat := 118140960795 + 2121109 * 2 ^ 59
def prefixEnd_2121109 : Nat := 4983230072969 + 3 ^ 40 * 2121109 * 2
def baseEnd_2121109 : Nat := 363049479192548961660901

theorem tailTrace_2121109 : CollatzResearch.WordTrace tailWord_2121109 prefixEnd_2121109 363049479192548961660901 := by
  unfold tailWord_2121109
  simp only [CollatzResearch.WordTrace]
  refine ⟨77363200872591824421590381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51575467248394549614393587 77363200872591824421590381)
  ·
    refine ⟨29011200327221934158096393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77363200872591824421590381 29011200327221934158096393)
    ·
      refine ⟨21758400245416450618572295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29011200327221934158096393 21758400245416450618572295)
      ·
        refine ⟨32637600368124675927858443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21758400245416450618572295 32637600368124675927858443)
        ·
          refine ⟨48956400552187013891787665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32637600368124675927858443 48956400552187013891787665)
          ·
            refine ⟨36717300414140260418840749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48956400552187013891787665 36717300414140260418840749)
            ·
              refine ⟨13768987655302597657065281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36717300414140260418840749 13768987655302597657065281)
              ·
                refine ⟨10326740741476948242798961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13768987655302597657065281 10326740741476948242798961)
                ·
                  refine ⟨7745055556107711182099221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10326740741476948242798961 7745055556107711182099221)
                  ·
                    refine ⟨363049479192548961660901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7745055556107711182099221 363049479192548961660901)
                    ·
                      rfl

theorem cell23_2121109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 2, 2, 6].length) (baseStart_2121109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2121109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2121109 prefixEnd_2121109 := by exact prefixLift 2121109
  have htrace : WordTrace (prefixWord ++ tailWord_2121109) baseStart_2121109 baseEnd_2121109 := by
    simpa [prefixWord, tailWord_2121109, baseEnd_2121109] using wordTrace_append hprefix tailTrace_2121109
  have hstable : (prefixWord ++ tailWord_2121109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2121109).length < 2 ^ (prefixWord ++ tailWord_2121109).sum := by decide
  have hdescent : baseEnd_2121109 < baseStart_2121109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2121109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2121166 : List Nat := [4, 1, 1, 1, 2, 1, 2, 1, 4, 3, 3]
def baseStart_2121166 : Nat := 118140960795 + 2121166 * 2 ^ 59
def prefixEnd_2121166 : Nat := 4983230072969 + 3 ^ 40 * 2121166 * 2
def baseEnd_2121166 : Nat := 1089177705974953161969941

theorem tailTrace_2121166 : CollatzResearch.WordTrace tailWord_2121166 prefixEnd_2121166 1089177705974953161969941 := by
  unfold tailWord_2121166
  simp only [CollatzResearch.WordTrace]
  refine ⟨9670659979173165394551919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51576853222256882104276901 9670659979173165394551919)
  ·
    refine ⟨14505989968759748091827879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9670659979173165394551919 14505989968759748091827879)
    ·
      refine ⟨21758984953139622137741819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14505989968759748091827879 21758984953139622137741819)
      ·
        refine ⟨32638477429709433206612729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21758984953139622137741819 32638477429709433206612729)
        ·
          refine ⟨24478858072282074904959547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32638477429709433206612729 24478858072282074904959547)
          ·
            refine ⟨36718287108423112357439321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24478858072282074904959547 36718287108423112357439321)
            ·
              refine ⟨27538715331317334268079491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36718287108423112357439321 27538715331317334268079491)
              ·
                refine ⟨41308072996976001402119237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27538715331317334268079491 41308072996976001402119237)
                ·
                  refine ⟨7745263686933000262897357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41308072996976001402119237 7745263686933000262897357)
                  ·
                    refine ⟨2904473882599875098586509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7745263686933000262897357 2904473882599875098586509)
                    ·
                      refine ⟨1089177705974953161969941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2904473882599875098586509 1089177705974953161969941)
                      ·
                        rfl

theorem cell23_2121166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 4, 3, 3].length) (baseStart_2121166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2121166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2121166 prefixEnd_2121166 := by exact prefixLift 2121166
  have htrace : WordTrace (prefixWord ++ tailWord_2121166) baseStart_2121166 baseEnd_2121166 := by
    simpa [prefixWord, tailWord_2121166, baseEnd_2121166] using wordTrace_append hprefix tailTrace_2121166
  have hstable : (prefixWord ++ tailWord_2121166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2121166).length < 2 ^ (prefixWord ++ tailWord_2121166).sum := by decide
  have hdescent : baseEnd_2121166 < baseStart_2121166 := by decide
  rcases family_descends (prefixWord ++ tailWord_2121166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2121199 : List Nat := [1, 1, 2, 1, 4, 1, 2, 1, 2, 8]
def baseStart_2121199 : Nat := 118140960795 + 2121199 * 2 ^ 59
def prefixEnd_2121199 : Nat := 4983230072969 + 3 ^ 40 * 2121199 * 2
def baseEnd_2121199 : Nat := 363064883612183844285763

theorem tailTrace_2121199 : CollatzResearch.WordTrace tailWord_2121199 prefixEnd_2121199 363064883612183844285763 := by
  unfold tailWord_2121199
  simp only [CollatzResearch.WordTrace]
  refine ⟨77366483442265769792366651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51577655628177179861577767 77366483442265769792366651)
  ·
    refine ⟨116049725163398654688549977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77366483442265769792366651 116049725163398654688549977)
    ·
      refine ⟨87037293872548991016412483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116049725163398654688549977 87037293872548991016412483)
      ·
        refine ⟨130555940808823486524618725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87037293872548991016412483 130555940808823486524618725)
        ·
          refine ⟨24479238901654403723366011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 130555940808823486524618725 24479238901654403723366011)
          ·
            refine ⟨36718858352481605585049017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24479238901654403723366011 36718858352481605585049017)
            ·
              refine ⟨27539143764361204188786763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36718858352481605585049017 27539143764361204188786763)
              ·
                refine ⟨41308715646541806283180145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27539143764361204188786763 41308715646541806283180145)
                ·
                  refine ⟨30981536734906354712385109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41308715646541806283180145 30981536734906354712385109)
                  ·
                    refine ⟨363064883612183844285763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 30981536734906354712385109 363064883612183844285763)
                    ·
                      rfl

theorem cell23_2121199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 8].length) (baseStart_2121199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2121199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2121199 prefixEnd_2121199 := by exact prefixLift 2121199
  have htrace : WordTrace (prefixWord ++ tailWord_2121199) baseStart_2121199 baseEnd_2121199 := by
    simpa [prefixWord, tailWord_2121199, baseEnd_2121199] using wordTrace_append hprefix tailTrace_2121199
  have hstable : (prefixWord ++ tailWord_2121199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2121199).length < 2 ^ (prefixWord ++ tailWord_2121199).sum := by decide
  have hdescent : baseEnd_2121199 < baseStart_2121199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2121199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2121223 : List Nat := [1, 1, 4, 3, 2, 1, 2, 2, 2, 1, 4]
def baseStart_2121223 : Nat := 118140960795 + 2121223 * 2 ^ 59
def prefixEnd_2121223 : Nat := 4983230072969 + 3 ^ 40 * 2121223 * 2
def baseEnd_2121223 : Nat := 1089206974372259438957179

theorem tailTrace_2121223 : CollatzResearch.WordTrace tailWord_2121223 prefixEnd_2121223 1089206974372259438957179 := by
  unfold tailWord_2121223
  simp only [CollatzResearch.WordTrace]
  refine ⟨77367358794178821891240323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51578239196119214594160215 77367358794178821891240323)
  ·
    refine ⟨116051038191268232836860485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77367358794178821891240323 116051038191268232836860485)
    ·
      refine ⟨21759569660862793656911341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 116051038191268232836860485 21759569660862793656911341)
      ·
        refine ⟨8159838622823547621341753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21759569660862793656911341 8159838622823547621341753)
        ·
          refine ⟨6119878967117660716006315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8159838622823547621341753 6119878967117660716006315)
          ·
            refine ⟨9179818450676491074009473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6119878967117660716006315 9179818450676491074009473)
            ·
              refine ⟨6884863838007368305507105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9179818450676491074009473 6884863838007368305507105)
              ·
                refine ⟨5163647878505526229130329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6884863838007368305507105 5163647878505526229130329)
                ·
                  refine ⟨3872735908879144671847747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5163647878505526229130329 3872735908879144671847747)
                  ·
                    refine ⟨5809103863318717007771621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3872735908879144671847747 5809103863318717007771621)
                    ·
                      refine ⟨1089206974372259438957179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5809103863318717007771621 1089206974372259438957179)
                      ·
                        rfl

theorem cell23_2121223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_2121223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2121223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2121223 prefixEnd_2121223 := by exact prefixLift 2121223
  have htrace : WordTrace (prefixWord ++ tailWord_2121223) baseStart_2121223 baseEnd_2121223 := by
    simpa [prefixWord, tailWord_2121223, baseEnd_2121223] using wordTrace_append hprefix tailTrace_2121223
  have hstable : (prefixWord ++ tailWord_2121223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2121223).length < 2 ^ (prefixWord ++ tailWord_2121223).sum := by decide
  have hdescent : baseEnd_2121223 < baseStart_2121223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2121223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2121240 : List Nat := [2, 1, 2, 3, 4, 1, 1, 1, 2, 4, 2]
def baseStart_2121240 : Nat := 118140960795 + 2121240 * 2 ^ 59
def prefixEnd_2121240 : Nat := 4983230072969 + 3 ^ 40 * 2121240 * 2
def baseEnd_2121240 : Nat := 1089215703543385872444601

theorem tailTrace_2121240 : CollatzResearch.WordTrace tailWord_2121240 prefixEnd_2121240 1089215703543385872444601 := by
  unfold tailWord_2121240
  simp only [CollatzResearch.WordTrace]
  refine ⟨38683989417558616897304587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51578652556744822529739449 38683989417558616897304587)
  ·
    refine ⟨58025984126337925345956881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38683989417558616897304587 58025984126337925345956881)
    ·
      refine ⟨43519488094753444009467661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58025984126337925345956881 43519488094753444009467661)
      ·
        refine ⟨16319808035532541503550373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43519488094753444009467661 16319808035532541503550373)
        ·
          refine ⟨3059964006662351531915695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16319808035532541503550373 3059964006662351531915695)
          ·
            refine ⟨4589946009993527297873543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3059964006662351531915695 4589946009993527297873543)
            ·
              refine ⟨6884919014990290946810315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4589946009993527297873543 6884919014990290946810315)
              ·
                refine ⟨10327378522485436420215473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6884919014990290946810315 10327378522485436420215473)
                ·
                  refine ⟨7745533891864077315161605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10327378522485436420215473 7745533891864077315161605)
                  ·
                    refine ⟨1452287604724514496592801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7745533891864077315161605 1452287604724514496592801)
                    ·
                      refine ⟨1089215703543385872444601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1452287604724514496592801 1089215703543385872444601)
                      ·
                        rfl

theorem cell23_2121240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 1, 2, 4, 2].length) (baseStart_2121240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2121240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2121240 prefixEnd_2121240 := by exact prefixLift 2121240
  have htrace : WordTrace (prefixWord ++ tailWord_2121240) baseStart_2121240 baseEnd_2121240 := by
    simpa [prefixWord, tailWord_2121240, baseEnd_2121240] using wordTrace_append hprefix tailTrace_2121240
  have hstable : (prefixWord ++ tailWord_2121240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2121240).length < 2 ^ (prefixWord ++ tailWord_2121240).sum := by decide
  have hdescent : baseEnd_2121240 < baseStart_2121240 := by decide
  rcases family_descends (prefixWord ++ tailWord_2121240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2121290 : List Nat := [3, 1, 2, 1, 1, 3, 4, 1, 3, 1, 3]
def baseStart_2121290 : Nat := 118140960795 + 2121290 * 2 ^ 59
def prefixEnd_2121290 : Nat := 4983230072969 + 3 ^ 40 * 2121290 * 2
def baseEnd_2121290 : Nat := 1089241377576110676819371

theorem tailTrace_2121290 : CollatzResearch.WordTrace tailWord_2121290 prefixEnd_2121290 1089241377576110676819371 := by
  unfold tailWord_2121290
  simp only [CollatzResearch.WordTrace]
  refine ⟨19342450621234023083482331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51579868323290728222619549 19342450621234023083482331)
  ·
    refine ⟨29013675931851034625223497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19342450621234023083482331 29013675931851034625223497)
    ·
      refine ⟨21760256948888275968917623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29013675931851034625223497 21760256948888275968917623)
      ·
        refine ⟨32640385423332413953376435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21760256948888275968917623 32640385423332413953376435)
        ·
          refine ⟨48960578134998620930064653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32640385423332413953376435 48960578134998620930064653)
          ·
            refine ⟨18360216800624482848774245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48960578134998620930064653 18360216800624482848774245)
            ·
              refine ⟨3442540650117090534145171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18360216800624482848774245 3442540650117090534145171)
              ·
                refine ⟨5163810975175635801217757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3442540650117090534145171 5163810975175635801217757)
                ·
                  refine ⟨1936429115690863425456659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5163810975175635801217757 1936429115690863425456659)
                  ·
                    refine ⟨2904643673536295138184989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1936429115690863425456659 2904643673536295138184989)
                    ·
                      refine ⟨1089241377576110676819371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2904643673536295138184989 1089241377576110676819371)
                      ·
                        rfl

theorem cell23_2121290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 1, 3, 1, 3].length) (baseStart_2121290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2121290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2121290 prefixEnd_2121290 := by exact prefixLift 2121290
  have htrace : WordTrace (prefixWord ++ tailWord_2121290) baseStart_2121290 baseEnd_2121290 := by
    simpa [prefixWord, tailWord_2121290, baseEnd_2121290] using wordTrace_append hprefix tailTrace_2121290
  have hstable : (prefixWord ++ tailWord_2121290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2121290).length < 2 ^ (prefixWord ++ tailWord_2121290).sum := by decide
  have hdescent : baseEnd_2121290 < baseStart_2121290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2121290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2121313 : List Nat := [1, 2, 3, 1, 1, 3, 1, 1, 2, 6, 2]
def baseStart_2121313 : Nat := 118140960795 + 2121313 * 2 ^ 59
def prefixEnd_2121313 : Nat := 4983230072969 + 3 ^ 40 * 2121313 * 2
def baseEnd_2121313 : Nat := 1089253187631164086831765

theorem tailTrace_2121313 : CollatzResearch.WordTrace tailWord_2121313 prefixEnd_2121313 1089253187631164086831765 := by
  unfold tailWord_2121313
  simp only [CollatzResearch.WordTrace]
  refine ⟨77370641363852767262016593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51580427575901844841344395 77370641363852767262016593)
  ·
    refine ⟨58027981022889575446512445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77370641363852767262016593 58027981022889575446512445)
    ·
      refine ⟨21760492883583590792442167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58027981022889575446512445 21760492883583590792442167)
      ·
        refine ⟨32640739325375386188663251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21760492883583590792442167 32640739325375386188663251)
        ·
          refine ⟨48961108988063079282994877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32640739325375386188663251 48961108988063079282994877)
          ·
            refine ⟨18360415870523654731123079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48961108988063079282994877 18360415870523654731123079)
            ·
              refine ⟨27540623805785482096684619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18360415870523654731123079 27540623805785482096684619)
              ·
                refine ⟨41310935708678223145026929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27540623805785482096684619 41310935708678223145026929)
                ·
                  refine ⟨30983201781508667358770197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41310935708678223145026929 30983201781508667358770197)
                  ·
                    refine ⟨1452337583508218782442353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30983201781508667358770197 1452337583508218782442353)
                    ·
                      refine ⟨1089253187631164086831765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1452337583508218782442353 1089253187631164086831765)
                      ·
                        rfl

theorem cell23_2121313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 6, 2].length) (baseStart_2121313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2121313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2121313 prefixEnd_2121313 := by exact prefixLift 2121313
  have htrace : WordTrace (prefixWord ++ tailWord_2121313) baseStart_2121313 baseEnd_2121313 := by
    simpa [prefixWord, tailWord_2121313, baseEnd_2121313] using wordTrace_append hprefix tailTrace_2121313
  have hstable : (prefixWord ++ tailWord_2121313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2121313).length < 2 ^ (prefixWord ++ tailWord_2121313).sum := by decide
  have hdescent : baseEnd_2121313 < baseStart_2121313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2121313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2121330 : List Nat := [3, 2, 1, 2, 3, 1, 2, 3, 1, 1, 4]
def baseStart_2121330 : Nat := 118140960795 + 2121330 * 2 ^ 59
def prefixEnd_2121330 : Nat := 4983230072969 + 3 ^ 40 * 2121330 * 2
def baseEnd_2121330 : Nat := 1089261916802290520319187

theorem tailTrace_2121330 : CollatzResearch.WordTrace tailWord_2121330 prefixEnd_2121330 1089261916802290520319187 := by
  unfold tailWord_2121330
  simp only [CollatzResearch.WordTrace]
  refine ⟨19342815351197794791346361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51580840936527452776923629 19342815351197794791346361)
  ·
    refine ⟨14507111513398346093509771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19342815351197794791346361 14507111513398346093509771)
    ·
      refine ⟨21760667270097519140264657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14507111513398346093509771 21760667270097519140264657)
      ·
        refine ⟨16320500452573139355198493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21760667270097519140264657 16320500452573139355198493)
        ·
          refine ⟨6120187669714927258199435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16320500452573139355198493 6120187669714927258199435)
          ·
            refine ⟨9180281504572390887299153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6120187669714927258199435 9180281504572390887299153)
            ·
              refine ⟨6885211128429293165474365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9180281504572390887299153 6885211128429293165474365)
              ·
                refine ⟨2581954173160984937052887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6885211128429293165474365 2581954173160984937052887)
                ·
                  refine ⟨3872931259741477405579331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2581954173160984937052887 3872931259741477405579331)
                  ·
                    refine ⟨5809396889612216108368997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3872931259741477405579331 5809396889612216108368997)
                    ·
                      refine ⟨1089261916802290520319187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5809396889612216108368997 1089261916802290520319187)
                      ·
                        rfl

theorem cell23_2121330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 3, 1, 1, 4].length) (baseStart_2121330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2121330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2121330 prefixEnd_2121330 := by exact prefixLift 2121330
  have htrace : WordTrace (prefixWord ++ tailWord_2121330) baseStart_2121330 baseEnd_2121330 := by
    simpa [prefixWord, tailWord_2121330, baseEnd_2121330] using wordTrace_append hprefix tailTrace_2121330
  have hstable : (prefixWord ++ tailWord_2121330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2121330).length < 2 ^ (prefixWord ++ tailWord_2121330).sum := by decide
  have hdescent : baseEnd_2121330 < baseStart_2121330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2121330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2121356 : List Nat := [2, 2, 1, 2, 1, 1, 3, 1, 2, 2, 6]
def baseStart_2121356 : Nat := 118140960795 + 2121356 * 2 ^ 59
def prefixEnd_2121356 : Nat := 4983230072969 + 3 ^ 40 * 2121356 * 2
def baseEnd_2121356 : Nat := 1089275267299307418594067

theorem tailTrace_2121356 : CollatzResearch.WordTrace tailWord_2121356 prefixEnd_2121356 1089275267299307418594067 := by
  unfold tailWord_2121356
  simp only [CollatzResearch.WordTrace]
  refine ⟨38686104851348492802915961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51581473135131323737221281 38686104851348492802915961)
  ·
    refine ⟨29014578638511369602186971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38686104851348492802915961 29014578638511369602186971)
    ·
      refine ⟨43521867957767054403280457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29014578638511369602186971 43521867957767054403280457)
      ·
        refine ⟨32641400968325290802460343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43521867957767054403280457 32641400968325290802460343)
        ·
          refine ⟨48962101452487936203690515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32641400968325290802460343 48962101452487936203690515)
          ·
            refine ⟨73443152178731904305535773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48962101452487936203690515 73443152178731904305535773)
            ·
              refine ⟨27541182067024464114575915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73443152178731904305535773 27541182067024464114575915)
              ·
                refine ⟨41311773100536696171863873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27541182067024464114575915 41311773100536696171863873)
                ·
                  refine ⟨30983829825402522128897905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41311773100536696171863873 30983829825402522128897905)
                  ·
                    refine ⟨23237872369051891596673429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30983829825402522128897905 23237872369051891596673429)
                    ·
                      refine ⟨1089275267299307418594067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23237872369051891596673429 1089275267299307418594067)
                      ·
                        rfl

theorem cell23_2121356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 2, 2, 6].length) (baseStart_2121356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2121356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2121356 prefixEnd_2121356 := by exact prefixLift 2121356
  have htrace : WordTrace (prefixWord ++ tailWord_2121356) baseStart_2121356 baseEnd_2121356 := by
    simpa [prefixWord, tailWord_2121356, baseEnd_2121356] using wordTrace_append hprefix tailTrace_2121356
  have hstable : (prefixWord ++ tailWord_2121356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2121356).length < 2 ^ (prefixWord ++ tailWord_2121356).sum := by decide
  have hdescent : baseEnd_2121356 < baseStart_2121356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2121356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2121364 : List Nat := [2, 4, 2, 2, 2, 2, 1, 2, 1, 1, 4]
def baseStart_2121364 : Nat := 118140960795 + 2121364 * 2 ^ 59
def prefixEnd_2121364 : Nat := 4983230072969 + 3 ^ 40 * 2121364 * 2
def baseEnd_2121364 : Nat := 1089279375144543387294031

theorem tailTrace_2121364 : CollatzResearch.WordTrace tailWord_2121364 prefixEnd_2121364 1089279375144543387294031 := by
  unfold tailWord_2121364
  simp only [CollatzResearch.WordTrace]
  refine ⟨38686250743334001486061573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51581667657778668648082097 38686250743334001486061573)
  ·
    refine ⟨7253672014375125278636545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38686250743334001486061573 7253672014375125278636545)
    ·
      refine ⟨5440254010781343958977409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7253672014375125278636545 5440254010781343958977409)
      ·
        refine ⟨4080190508086007969233057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5440254010781343958977409 4080190508086007969233057)
        ·
          refine ⟨3060142881064505976924793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4080190508086007969233057 3060142881064505976924793)
          ·
            refine ⟨2295107160798379482693595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3060142881064505976924793 2295107160798379482693595)
            ·
              refine ⟨3442660741197569224040393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2295107160798379482693595 3442660741197569224040393)
              ·
                refine ⟨2581995555898176918030295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3442660741197569224040393 2581995555898176918030295)
                ·
                  refine ⟨3872993333847265377045443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2581995555898176918030295 3872993333847265377045443)
                  ·
                    refine ⟨5809490000770898065568165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3872993333847265377045443 5809490000770898065568165)
                    ·
                      refine ⟨1089279375144543387294031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5809490000770898065568165 1089279375144543387294031)
                      ·
                        rfl

theorem cell23_2121364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_2121364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2121364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2121364 prefixEnd_2121364 := by exact prefixLift 2121364
  have htrace : WordTrace (prefixWord ++ tailWord_2121364) baseStart_2121364 baseEnd_2121364 := by
    simpa [prefixWord, tailWord_2121364, baseEnd_2121364] using wordTrace_append hprefix tailTrace_2121364
  have hstable : (prefixWord ++ tailWord_2121364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2121364).length < 2 ^ (prefixWord ++ tailWord_2121364).sum := by decide
  have hdescent : baseEnd_2121364 < baseStart_2121364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2121364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2121367 : List Nat := [1, 1, 3, 3, 2, 4, 1, 2, 1, 2, 3]
def baseStart_2121367 : Nat := 118140960795 + 2121367 * 2 ^ 59
def prefixEnd_2121367 : Nat := 4983230072969 + 3 ^ 40 * 2121367 * 2
def baseEnd_2121367 : Nat := 1089280915586506875556517

theorem tailTrace_2121367 : CollatzResearch.WordTrace tailWord_2121367 prefixEnd_2121367 1089280915586506875556517 := by
  unfold tailWord_2121367
  simp only [CollatzResearch.WordTrace]
  refine ⟨77372610905657134484482355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51581740603771422989654903 77372610905657134484482355)
  ·
    refine ⟨116058916358485701726723533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77372610905657134484482355 116058916358485701726723533)
    ·
      refine ⟨43522093634432138147521325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116058916358485701726723533 43522093634432138147521325)
      ·
        refine ⟨16320785112912051805320497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43522093634432138147521325 16320785112912051805320497)
        ·
          refine ⟨12240588834684038853990373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16320785112912051805320497 12240588834684038853990373)
          ·
            refine ⟨2295110406503257285123195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12240588834684038853990373 2295110406503257285123195)
            ·
              refine ⟨3442665609754885927684793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2295110406503257285123195 3442665609754885927684793)
              ·
                refine ⟨2581999207316164445763595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3442665609754885927684793 2581999207316164445763595)
                ·
                  refine ⟨3872998810974246668645393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2581999207316164445763595 3872998810974246668645393)
                  ·
                    refine ⟨2904749108230685001484045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3872998810974246668645393 2904749108230685001484045)
                    ·
                      refine ⟨1089280915586506875556517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2904749108230685001484045 1089280915586506875556517)
                      ·
                        rfl

theorem cell23_2121367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 2, 1, 2, 3].length) (baseStart_2121367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2121367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2121367 prefixEnd_2121367 := by exact prefixLift 2121367
  have htrace : WordTrace (prefixWord ++ tailWord_2121367) baseStart_2121367 baseEnd_2121367 := by
    simpa [prefixWord, tailWord_2121367, baseEnd_2121367] using wordTrace_append hprefix tailTrace_2121367
  have hstable : (prefixWord ++ tailWord_2121367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2121367).length < 2 ^ (prefixWord ++ tailWord_2121367).sum := by decide
  have hdescent : baseEnd_2121367 < baseStart_2121367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2121367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2121380 : List Nat := [2, 3, 1, 2, 2, 3, 1, 2, 1, 3, 3]
def baseStart_2121380 : Nat := 118140960795 + 2121380 * 2 ^ 59
def prefixEnd_2121380 : Nat := 4983230072969 + 3 ^ 40 * 2121380 * 2
def baseEnd_2121380 : Nat := 1089287590835015324693957

theorem tailTrace_2121380 : CollatzResearch.WordTrace tailWord_2121380 prefixEnd_2121380 1089287590835015324693957 := by
  unfold tailWord_2121380
  simp only [CollatzResearch.WordTrace]
  refine ⟨38686542527305018852352797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51582056703073358469803729 38686542527305018852352797)
  ·
    refine ⟨14507453447739382069632299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38686542527305018852352797 14507453447739382069632299)
    ·
      refine ⟨21761180171609073104448449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14507453447739382069632299 21761180171609073104448449)
      ·
        refine ⟨16320885128706804828336337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21761180171609073104448449 16320885128706804828336337)
        ·
          refine ⟨12240663846530103621252253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16320885128706804828336337 12240663846530103621252253)
          ·
            refine ⟨4590248942448788857969595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12240663846530103621252253 4590248942448788857969595)
            ·
              refine ⟨6885373413673183286954393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4590248942448788857969595 6885373413673183286954393)
              ·
                refine ⟨5164030060254887465215795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6885373413673183286954393 5164030060254887465215795)
                ·
                  refine ⟨7746045090382331197823693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5164030060254887465215795 7746045090382331197823693)
                  ·
                    refine ⟨2904766908893374199183885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7746045090382331197823693 2904766908893374199183885)
                    ·
                      refine ⟨1089287590835015324693957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2904766908893374199183885 1089287590835015324693957)
                      ·
                        rfl

theorem cell23_2121380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 2, 1, 3, 3].length) (baseStart_2121380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2121380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2121380 prefixEnd_2121380 := by exact prefixLift 2121380
  have htrace : WordTrace (prefixWord ++ tailWord_2121380) baseStart_2121380 baseEnd_2121380 := by
    simpa [prefixWord, tailWord_2121380, baseEnd_2121380] using wordTrace_append hprefix tailTrace_2121380
  have hstable : (prefixWord ++ tailWord_2121380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2121380).length < 2 ^ (prefixWord ++ tailWord_2121380).sum := by decide
  have hdescent : baseEnd_2121380 < baseStart_2121380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2121380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2121398 : List Nat := [5, 1, 3, 1, 1, 2, 1, 4, 1, 2, 2]
def baseStart_2121398 : Nat := 118140960795 + 2121398 * 2 ^ 59
def prefixEnd_2121398 : Nat := 4983230072969 + 3 ^ 40 * 2121398 * 2
def baseEnd_2121398 : Nat := 1089296833486796254268875

theorem tailTrace_2121398 : CollatzResearch.WordTrace tailWord_2121398 prefixEnd_2121398 1089296833486796254268875 := by
  unfold tailWord_2121398
  simp only [CollatzResearch.WordTrace]
  refine ⟨4835858848034051673678803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 51582494379029884519240565 4835858848034051673678803)
  ·
    refine ⟨7253788272051077510518205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4835858848034051673678803 7253788272051077510518205)
    ·
      refine ⟨2720170602019154066444327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7253788272051077510518205 2720170602019154066444327)
      ·
        refine ⟨4080255903028731099666491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2720170602019154066444327 4080255903028731099666491)
        ·
          refine ⟨6120383854543096649499737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4080255903028731099666491 6120383854543096649499737)
          ·
            refine ⟨4590287890907322487124803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6120383854543096649499737 4590287890907322487124803)
            ·
              refine ⟨6885431836360983730687205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4590287890907322487124803 6885431836360983730687205)
              ·
                refine ⟨1291018469317684449503851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6885431836360983730687205 1291018469317684449503851)
                ·
                  refine ⟨1936527703976526674255777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1291018469317684449503851 1936527703976526674255777)
                  ·
                    refine ⟨1452395777982395005691833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1936527703976526674255777 1452395777982395005691833)
                    ·
                      refine ⟨1089296833486796254268875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1452395777982395005691833 1089296833486796254268875)
                      ·
                        rfl

theorem cell23_2121398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_2121398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2121398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2121398 prefixEnd_2121398 := by exact prefixLift 2121398
  have htrace : WordTrace (prefixWord ++ tailWord_2121398) baseStart_2121398 baseEnd_2121398 := by
    simpa [prefixWord, tailWord_2121398, baseEnd_2121398] using wordTrace_append hprefix tailTrace_2121398
  have hstable : (prefixWord ++ tailWord_2121398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2121398).length < 2 ^ (prefixWord ++ tailWord_2121398).sum := by decide
  have hdescent : baseEnd_2121398 < baseStart_2121398 := by decide
  rcases family_descends (prefixWord ++ tailWord_2121398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2121414 : List Nat := [6, 1, 2, 1, 1, 1, 1, 3, 1, 3, 3]
def baseStart_2121414 : Nat := 118140960795 + 2121414 * 2 ^ 59
def prefixEnd_2121414 : Nat := 4983230072969 + 3 ^ 40 * 2121414 * 2
def baseEnd_2121414 : Nat := 1089305049177268191668801

theorem tailTrace_2121414 : CollatzResearch.WordTrace tailWord_2121414 prefixEnd_2121414 1089305049177268191668801 := by
  unfold tailWord_2121414
  simp only [CollatzResearch.WordTrace]
  refine ⟨2417947660515214422232603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 51582883424324574340962197 2417947660515214422232603)
  ·
    refine ⟨3626921490772821633348905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2417947660515214422232603 3626921490772821633348905)
    ·
      refine ⟨2720191118079616225011679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3626921490772821633348905 2720191118079616225011679)
      ·
        refine ⟨4080286677119424337517519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2720191118079616225011679 4080286677119424337517519)
        ·
          refine ⟨6120430015679136506276279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4080286677119424337517519 6120430015679136506276279)
          ·
            refine ⟨9180645023518704759414419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6120430015679136506276279 9180645023518704759414419)
            ·
              refine ⟨13770967535278057139121629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9180645023518704759414419 13770967535278057139121629)
              ·
                refine ⟨5164112825729271427170611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13770967535278057139121629 5164112825729271427170611)
                ·
                  refine ⟨7746169238593907140755917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5164112825729271427170611 7746169238593907140755917)
                  ·
                    refine ⟨2904813464472715177783469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7746169238593907140755917 2904813464472715177783469)
                    ·
                      refine ⟨1089305049177268191668801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2904813464472715177783469 1089305049177268191668801)
                      ·
                        rfl

theorem cell23_2121414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_2121414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2121414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2121414 prefixEnd_2121414 := by exact prefixLift 2121414
  have htrace : WordTrace (prefixWord ++ tailWord_2121414) baseStart_2121414 baseEnd_2121414 := by
    simpa [prefixWord, tailWord_2121414, baseEnd_2121414] using wordTrace_append hprefix tailTrace_2121414
  have hstable : (prefixWord ++ tailWord_2121414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2121414).length < 2 ^ (prefixWord ++ tailWord_2121414).sum := by decide
  have hdescent : baseEnd_2121414 < baseStart_2121414 := by decide
  rcases family_descends (prefixWord ++ tailWord_2121414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2121441 : List Nat := [1, 2, 3, 1, 5, 2, 2, 1, 1, 3, 2]
def baseStart_2121441 : Nat := 118140960795 + 2121441 * 2 ^ 59
def prefixEnd_2121441 : Nat := 4983230072969 + 3 ^ 40 * 2121441 * 2
def baseEnd_2121441 : Nat := 1089318913154939586031177

theorem tailTrace_2121441 : CollatzResearch.WordTrace tailWord_2121441 prefixEnd_2121441 1089318913154939586031177 := by
  unfold tailWord_2121441
  simp only [CollatzResearch.WordTrace]
  refine ⟨77375309907389045122676177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51583539938259363415117451 77375309907389045122676177)
  ·
    refine ⟨58031482430541783842007133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77375309907389045122676177 58031482430541783842007133)
    ·
      refine ⟨21761805911453168940752675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58031482430541783842007133 21761805911453168940752675)
      ·
        refine ⟨32642708867179753411129013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21761805911453168940752675 32642708867179753411129013)
        ·
          refine ⟨3060253956298101882293345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32642708867179753411129013 3060253956298101882293345)
          ·
            refine ⟨2295190467223576411720009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3060253956298101882293345 2295190467223576411720009)
            ·
              refine ⟨1721392850417682308790007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2295190467223576411720009 1721392850417682308790007)
              ·
                refine ⟨2582089275626523463185011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1721392850417682308790007 2582089275626523463185011)
                ·
                  refine ⟨3873133913439785194777517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2582089275626523463185011 3873133913439785194777517)
                  ·
                    refine ⟨1452425217539919448041569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3873133913439785194777517 1452425217539919448041569)
                    ·
                      refine ⟨1089318913154939586031177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1452425217539919448041569 1089318913154939586031177)
                      ·
                        rfl

theorem cell23_2121441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 2, 1, 1, 3, 2].length) (baseStart_2121441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2121441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2121441 prefixEnd_2121441 := by exact prefixLift 2121441
  have htrace : WordTrace (prefixWord ++ tailWord_2121441) baseStart_2121441 baseEnd_2121441 := by
    simpa [prefixWord, tailWord_2121441, baseEnd_2121441] using wordTrace_append hprefix tailTrace_2121441
  have hstable : (prefixWord ++ tailWord_2121441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2121441).length < 2 ^ (prefixWord ++ tailWord_2121441).sum := by decide
  have hdescent : baseEnd_2121441 < baseStart_2121441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2121441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2121473 : List Nat := [1, 2, 4, 1, 1, 1, 3, 2, 1, 7]
def baseStart_2121473 : Nat := 118140960795 + 2121473 * 2 ^ 59
def prefixEnd_2121473 : Nat := 4983230072969 + 3 ^ 40 * 2121473 * 2
def baseEnd_2121473 : Nat := 363111781511961153610343

theorem tailTrace_2121473 : CollatzResearch.WordTrace tailWord_2121473 prefixEnd_2121473 363111781511961153610343 := by
  unfold tailWord_2121473
  simp only [CollatzResearch.WordTrace]
  refine ⟨77376477043273114587841073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51584318028848743058560715 77376477043273114587841073)
  ·
    refine ⟨58032357782454835940880805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77376477043273114587841073 58032357782454835940880805)
    ·
      refine ⟨10881067084210281738915151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58032357782454835940880805 10881067084210281738915151)
      ·
        refine ⟨16321600626315422608372727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10881067084210281738915151 16321600626315422608372727)
        ·
          refine ⟨24482400939473133912559091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16321600626315422608372727 24482400939473133912559091)
          ·
            refine ⟨36723601409209700868838637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24482400939473133912559091 36723601409209700868838637)
            ·
              refine ⟨13771350528453637825814489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36723601409209700868838637 13771350528453637825814489)
              ·
                refine ⟨10328512896340228369360867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13771350528453637825814489 10328512896340228369360867)
                ·
                  refine ⟨15492769344510342554041301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10328512896340228369360867 15492769344510342554041301)
                  ·
                    refine ⟨363111781511961153610343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15492769344510342554041301 363111781511961153610343)
                    ·
                      rfl

theorem cell23_2121473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 2, 1, 7].length) (baseStart_2121473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2121473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2121473 prefixEnd_2121473 := by exact prefixLift 2121473
  have htrace : WordTrace (prefixWord ++ tailWord_2121473) baseStart_2121473 baseEnd_2121473 := by
    simpa [prefixWord, tailWord_2121473, baseEnd_2121473] using wordTrace_append hprefix tailTrace_2121473
  have hstable : (prefixWord ++ tailWord_2121473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2121473).length < 2 ^ (prefixWord ++ tailWord_2121473).sum := by decide
  have hdescent : baseEnd_2121473 < baseStart_2121473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2121473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2121580 : List Nat := [2, 2, 1, 1, 4, 2, 1, 2, 3, 5]
def baseStart_2121580 : Nat := 118140960795 + 2121580 * 2 ^ 59
def prefixEnd_2121580 : Nat := 4983230072969 + 3 ^ 40 * 2121580 * 2
def baseEnd_2121580 : Nat := 363130095655304847397679

theorem tailTrace_2121580 : CollatzResearch.WordTrace tailWord_2121580 prefixEnd_2121580 363130095655304847397679 := by
  unfold tailWord_2121580
  simp only [CollatzResearch.WordTrace]
  refine ⟨38690189826942735930993097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51586919769256981241324129 38690189826942735930993097)
  ·
    refine ⟨29017642370207051948244823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38690189826942735930993097 29017642370207051948244823)
    ·
      refine ⟨43526463555310577922367235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29017642370207051948244823 43526463555310577922367235)
      ·
        refine ⟨65289695332965866883550853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43526463555310577922367235 65289695332965866883550853)
        ·
          refine ⟨12241817874931100040665785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65289695332965866883550853 12241817874931100040665785)
          ·
            refine ⟨9181363406198325030499339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12241817874931100040665785 9181363406198325030499339)
            ·
              refine ⟨13772045109297487545749009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9181363406198325030499339 13772045109297487545749009)
              ·
                refine ⟨10329033831973115659311757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13772045109297487545749009 10329033831973115659311757)
                ·
                  refine ⟨3873387686989918372241909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10329033831973115659311757 3873387686989918372241909)
                  ·
                    refine ⟨363130095655304847397679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3873387686989918372241909 363130095655304847397679)
                    ·
                      rfl

theorem cell23_2121580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 5].length) (baseStart_2121580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2121580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2121580 prefixEnd_2121580 := by exact prefixLift 2121580
  have htrace : WordTrace (prefixWord ++ tailWord_2121580) baseStart_2121580 baseEnd_2121580 := by
    simpa [prefixWord, tailWord_2121580, baseEnd_2121580] using wordTrace_append hprefix tailTrace_2121580
  have hstable : (prefixWord ++ tailWord_2121580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2121580).length < 2 ^ (prefixWord ++ tailWord_2121580).sum := by decide
  have hdescent : baseEnd_2121580 < baseStart_2121580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2121580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2121600 : List Nat := [2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 4]
def baseStart_2121600 : Nat := 118140960795 + 2121600 * 2 ^ 59
def prefixEnd_2121600 : Nat := 4983230072969 + 3 ^ 40 * 2121600 * 2
def baseEnd_2121600 : Nat := 1089400556579004463942945

theorem tailTrace_2121600 : CollatzResearch.WordTrace tailWord_2121600 prefixEnd_2121600 1089400556579004463942945 := by
  unfold tailWord_2121600
  simp only [CollatzResearch.WordTrace]
  refine ⟨38690554556906507638857127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51587406075875343518476169 38690554556906507638857127)
  ·
    refine ⟨58035831835359761458285691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38690554556906507638857127 58035831835359761458285691)
    ·
      refine ⟨87053747753039642187428537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58035831835359761458285691 87053747753039642187428537)
      ·
        refine ⟨65290310814779731640571403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87053747753039642187428537 65290310814779731640571403)
        ·
          refine ⟨97935466222169597460857105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65290310814779731640571403 97935466222169597460857105)
          ·
            refine ⟨73451599666627198095642829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97935466222169597460857105 73451599666627198095642829)
            ·
              refine ⟨27544349874985199285866061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73451599666627198095642829 27544349874985199285866061)
              ·
                refine ⟨10329131203119449732199773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27544349874985199285866061 10329131203119449732199773)
                ·
                  refine ⟨3873424201169793649574915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10329131203119449732199773 3873424201169793649574915)
                  ·
                    refine ⟨5810136301754690474362373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3873424201169793649574915 5810136301754690474362373)
                    ·
                      refine ⟨1089400556579004463942945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5810136301754690474362373 1089400556579004463942945)
                      ·
                        rfl

theorem cell23_2121600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 4].length) (baseStart_2121600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2121600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2121600 prefixEnd_2121600 := by exact prefixLift 2121600
  have htrace : WordTrace (prefixWord ++ tailWord_2121600) baseStart_2121600 baseEnd_2121600 := by
    simpa [prefixWord, tailWord_2121600, baseEnd_2121600] using wordTrace_append hprefix tailTrace_2121600
  have hstable : (prefixWord ++ tailWord_2121600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2121600).length < 2 ^ (prefixWord ++ tailWord_2121600).sum := by decide
  have hdescent : baseEnd_2121600 < baseStart_2121600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2121600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2121604 : List Nat := [2, 3, 2, 1, 1, 1, 5, 1, 2, 3, 2]
def baseStart_2121604 : Nat := 118140960795 + 2121604 * 2 ^ 59
def prefixEnd_2121604 : Nat := 4983230072969 + 3 ^ 40 * 2121604 * 2
def baseEnd_2121604 : Nat := 1089402610501622448292927

theorem tailTrace_2121604 : CollatzResearch.WordTrace tailWord_2121604 prefixEnd_2121604 1089402610501622448292927 := by
  unfold tailWord_2121604
  simp only [CollatzResearch.WordTrace]
  refine ⟨38690627502899261980429933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51587503337199015973906577 38690627502899261980429933)
  ·
    refine ⟨14508985313587223242661225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38690627502899261980429933 14508985313587223242661225)
    ·
      refine ⟨10881738985190417431995919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14508985313587223242661225 10881738985190417431995919)
      ·
        refine ⟨16322608477785626147993879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10881738985190417431995919 16322608477785626147993879)
        ·
          refine ⟨24483912716678439221990819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16322608477785626147993879 24483912716678439221990819)
          ·
            refine ⟨36725869075017658832986229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24483912716678439221990819 36725869075017658832986229)
            ·
              refine ⟨3443050225782905515592459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36725869075017658832986229 3443050225782905515592459)
              ·
                refine ⟨5164575338674358273388689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3443050225782905515592459 5164575338674358273388689)
                ·
                  refine ⟨3873431504005768705041517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5164575338674358273388689 3873431504005768705041517)
                  ·
                    refine ⟨1452536814002163264390569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3873431504005768705041517 1452536814002163264390569)
                    ·
                      refine ⟨1089402610501622448292927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1452536814002163264390569 1089402610501622448292927)
                      ·
                        rfl

theorem cell23_2121604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 1, 2, 3, 2].length) (baseStart_2121604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2121604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2121604 prefixEnd_2121604 := by exact prefixLift 2121604
  have htrace : WordTrace (prefixWord ++ tailWord_2121604) baseStart_2121604 baseEnd_2121604 := by
    simpa [prefixWord, tailWord_2121604, baseEnd_2121604] using wordTrace_append hprefix tailTrace_2121604
  have hstable : (prefixWord ++ tailWord_2121604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2121604).length < 2 ^ (prefixWord ++ tailWord_2121604).sum := by decide
  have hdescent : baseEnd_2121604 < baseStart_2121604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2121604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2121684 : List Nat := [2, 4, 1, 2, 1, 1, 1, 3, 4, 1, 3]
def baseStart_2121684 : Nat := 118140960795 + 2121684 * 2 ^ 59
def prefixEnd_2121684 : Nat := 4983230072969 + 3 ^ 40 * 2121684 * 2
def baseEnd_2121684 : Nat := 1089443688953982135292559

theorem tailTrace_2121684 : CollatzResearch.WordTrace tailWord_2121684 prefixEnd_2121684 1089443688953982135292559 := by
  unfold tailWord_2121684
  simp only [CollatzResearch.WordTrace]
  refine ⟨38692086422754348811886053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51589448563672465082514737 38692086422754348811886053)
  ·
    refine ⟨7254766204266440402228635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38692086422754348811886053 7254766204266440402228635)
    ·
      refine ⟨10882149306399660603342953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7254766204266440402228635 10882149306399660603342953)
      ·
        refine ⟨8161611979799745452507215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10882149306399660603342953 8161611979799745452507215)
        ·
          refine ⟨12242417969699618178760823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8161611979799745452507215 12242417969699618178760823)
          ·
            refine ⟨18363626954549427268141235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12242417969699618178760823 18363626954549427268141235)
            ·
              refine ⟨27545440431824140902211853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18363626954549427268141235 27545440431824140902211853)
              ·
                refine ⟨10329540161934052838329445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27545440431824140902211853 10329540161934052838329445)
                ·
                  refine ⟨1936788780362634907186771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10329540161934052838329445 1936788780362634907186771)
                  ·
                    refine ⟨2905183170543952360780157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1936788780362634907186771 2905183170543952360780157)
                    ·
                      refine ⟨1089443688953982135292559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2905183170543952360780157 1089443688953982135292559)
                      ·
                        rfl

theorem cell23_2121684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_2121684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2121684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2121684 prefixEnd_2121684 := by exact prefixLift 2121684
  have htrace : WordTrace (prefixWord ++ tailWord_2121684) baseStart_2121684 baseEnd_2121684 := by
    simpa [prefixWord, tailWord_2121684, baseEnd_2121684] using wordTrace_append hprefix tailTrace_2121684
  have hstable : (prefixWord ++ tailWord_2121684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2121684).length < 2 ^ (prefixWord ++ tailWord_2121684).sum := by decide
  have hdescent : baseEnd_2121684 < baseStart_2121684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2121684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2121685 : List Nat := [1, 3, 2, 3, 2, 2, 3, 2, 1, 2, 2]
def baseStart_2121685 : Nat := 118140960795 + 2121685 * 2 ^ 59
def prefixEnd_2121685 : Nat := 4983230072969 + 3 ^ 40 * 2121685 * 2
def baseEnd_2121685 : Nat := 1089444202434636631380055

theorem tailTrace_2121685 : CollatzResearch.WordTrace tailWord_2121685 prefixEnd_2121685 1089444202434636631380055 := by
  unfold tailWord_2121685
  simp only [CollatzResearch.WordTrace]
  refine ⟨77384209318505074794558509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51589472879003383196372339 77384209318505074794558509)
  ·
    refine ⟨29019078494439403047959441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77384209318505074794558509 29019078494439403047959441)
    ·
      refine ⟨21764308870829552285969581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29019078494439403047959441 21764308870829552285969581)
      ·
        refine ⟨8161615826561082107238593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21764308870829552285969581 8161615826561082107238593)
        ·
          refine ⟨6121211869920811580428945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8161615826561082107238593 6121211869920811580428945)
          ·
            refine ⟨4590908902440608685321709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6121211869920811580428945 4590908902440608685321709)
            ·
              refine ⟨1721590838415228256995641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4590908902440608685321709 1721590838415228256995641)
              ·
                refine ⟨1291193128811421192746731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1721590838415228256995641 1291193128811421192746731)
                ·
                  refine ⟨1936789693217131789120097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1291193128811421192746731 1936789693217131789120097)
                  ·
                    refine ⟨1452592269912848841840073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1936789693217131789120097 1452592269912848841840073)
                    ·
                      refine ⟨1089444202434636631380055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1452592269912848841840073 1089444202434636631380055)
                      ·
                        rfl

theorem cell23_2121685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 3, 2, 1, 2, 2].length) (baseStart_2121685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2121685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2121685 prefixEnd_2121685 := by exact prefixLift 2121685
  have htrace : WordTrace (prefixWord ++ tailWord_2121685) baseStart_2121685 baseEnd_2121685 := by
    simpa [prefixWord, tailWord_2121685, baseEnd_2121685] using wordTrace_append hprefix tailTrace_2121685
  have hstable : (prefixWord ++ tailWord_2121685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2121685).length < 2 ^ (prefixWord ++ tailWord_2121685).sum := by decide
  have hdescent : baseEnd_2121685 < baseStart_2121685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2121685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2121700 : List Nat := [2, 3, 1, 1, 1, 1, 4, 1, 1, 8]
def baseStart_2121700 : Nat := 118140960795 + 2121700 * 2 ^ 59
def prefixEnd_2121700 : Nat := 4983230072969 + 3 ^ 40 * 2121700 * 2
def baseEnd_2121700 : Nat := 363150634881484690897495

theorem tailTrace_2121700 : CollatzResearch.WordTrace tailWord_2121700 prefixEnd_2121700 363150634881484690897495 := by
  unfold tailWord_2121700
  simp only [CollatzResearch.WordTrace]
  refine ⟨38692378206725366178177277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51589837608967154904236369 38692378206725366178177277)
  ·
    refine ⟨14509641827522012316816479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38692378206725366178177277 14509641827522012316816479)
    ·
      refine ⟨21764462741283018475224719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14509641827522012316816479 21764462741283018475224719)
      ·
        refine ⟨32646694111924527712837079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21764462741283018475224719 32646694111924527712837079)
        ·
          refine ⟨48970041167886791569255619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32646694111924527712837079 48970041167886791569255619)
          ·
            refine ⟨73455061751830187353883429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48970041167886791569255619 73455061751830187353883429)
            ·
              refine ⟨13772824078468160128853143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 73455061751830187353883429 13772824078468160128853143)
              ·
                refine ⟨20659236117702240193279715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13772824078468160128853143 20659236117702240193279715)
                ·
                  refine ⟨30988854176553360289919573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20659236117702240193279715 30988854176553360289919573)
                  ·
                    refine ⟨363150634881484690897495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 30988854176553360289919573 363150634881484690897495)
                    ·
                      rfl

theorem cell23_2121700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 1, 8].length) (baseStart_2121700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2121700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2121700 prefixEnd_2121700 := by exact prefixLift 2121700
  have htrace : WordTrace (prefixWord ++ tailWord_2121700) baseStart_2121700 baseEnd_2121700 := by
    simpa [prefixWord, tailWord_2121700, baseEnd_2121700] using wordTrace_append hprefix tailTrace_2121700
  have hstable : (prefixWord ++ tailWord_2121700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2121700).length < 2 ^ (prefixWord ++ tailWord_2121700).sum := by decide
  have hdescent : baseEnd_2121700 < baseStart_2121700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2121700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2121707 : List Nat := [1, 1, 1, 1, 2, 3, 1, 2, 5, 4, 2]
def baseStart_2121707 : Nat := 118140960795 + 2121707 * 2 ^ 59
def prefixEnd_2121707 : Nat := 4983230072969 + 3 ^ 40 * 2121707 * 2
def baseEnd_2121707 : Nat := 1089455499009035545304953

theorem tailTrace_2121707 : CollatzResearch.WordTrace tailWord_2121707 prefixEnd_2121707 1089455499009035545304953 := by
  unfold tailWord_2121707
  simp only [CollatzResearch.WordTrace]
  refine ⟨77385011724425372551859375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51590007816283581701239583 77385011724425372551859375)
  ·
    refine ⟨116077517586638058827789063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77385011724425372551859375 116077517586638058827789063)
    ·
      refine ⟨174116276379957088241683595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116077517586638058827789063 174116276379957088241683595)
      ·
        refine ⟨261174414569935632362525393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174116276379957088241683595 261174414569935632362525393)
        ·
          refine ⟨195880810927451724271894045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 261174414569935632362525393 195880810927451724271894045)
          ·
            refine ⟨73455304097794396601960267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 195880810927451724271894045 73455304097794396601960267)
            ·
              refine ⟨110182956146691594902940401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73455304097794396601960267 110182956146691594902940401)
              ·
                refine ⟨82637217110018696177205301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 110182956146691594902940401 82637217110018696177205301)
                ·
                  refine ⟨7747239104064252766612997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 82637217110018696177205301 7747239104064252766612997)
                  ·
                    refine ⟨1452607332012047393739937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7747239104064252766612997 1452607332012047393739937)
                    ·
                      refine ⟨1089455499009035545304953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1452607332012047393739937 1089455499009035545304953)
                      ·
                        rfl

theorem cell23_2121707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 5, 4, 2].length) (baseStart_2121707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2121707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2121707 prefixEnd_2121707 := by exact prefixLift 2121707
  have htrace : WordTrace (prefixWord ++ tailWord_2121707) baseStart_2121707 baseEnd_2121707 := by
    simpa [prefixWord, tailWord_2121707, baseEnd_2121707] using wordTrace_append hprefix tailTrace_2121707
  have hstable : (prefixWord ++ tailWord_2121707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2121707).length < 2 ^ (prefixWord ++ tailWord_2121707).sum := by decide
  have hdescent : baseEnd_2121707 < baseStart_2121707 := by decide
  rcases family_descends (prefixWord ++ tailWord_2121707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2121724 : List Nat := [2, 2, 2, 1, 2, 2, 3, 2, 1, 4, 2]
def baseStart_2121724 : Nat := 118140960795 + 2121724 * 2 ^ 59
def prefixEnd_2121724 : Nat := 4983230072969 + 3 ^ 40 * 2121724 * 2
def baseEnd_2121724 : Nat := 1089464228180161978792375

theorem tailTrace_2121724 : CollatzResearch.WordTrace tailWord_2121724 prefixEnd_2121724 1089464228180161978792375 := by
  unfold tailWord_2121724
  simp only [CollatzResearch.WordTrace]
  refine ⟨38692815882681892227614113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51590421176909189636818817 38692815882681892227614113)
  ·
    refine ⟨29019611912011419170710585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38692815882681892227614113 29019611912011419170710585)
    ·
      refine ⟨21764708934008564378032939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29019611912011419170710585 21764708934008564378032939)
      ·
        refine ⟨32647063401012846567049409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21764708934008564378032939 32647063401012846567049409)
        ·
          refine ⟨24485297550759634925287057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32647063401012846567049409 24485297550759634925287057)
          ·
            refine ⟨18363973163069726193965293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24485297550759634925287057 18363973163069726193965293)
            ·
              refine ⟨6886489936151147322736985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18363973163069726193965293 6886489936151147322736985)
              ·
                refine ⟨5164867452113360492052739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6886489936151147322736985 5164867452113360492052739)
                ·
                  refine ⟨7747301178170040738079109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5164867452113360492052739 7747301178170040738079109)
                  ·
                    refine ⟨1452618970906882638389833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7747301178170040738079109 1452618970906882638389833)
                    ·
                      refine ⟨1089464228180161978792375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1452618970906882638389833 1089464228180161978792375)
                      ·
                        rfl

theorem cell23_2121724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 2, 1, 4, 2].length) (baseStart_2121724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2121724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2121724 prefixEnd_2121724 := by exact prefixLift 2121724
  have htrace : WordTrace (prefixWord ++ tailWord_2121724) baseStart_2121724 baseEnd_2121724 := by
    simpa [prefixWord, tailWord_2121724, baseEnd_2121724] using wordTrace_append hprefix tailTrace_2121724
  have hstable : (prefixWord ++ tailWord_2121724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2121724).length < 2 ^ (prefixWord ++ tailWord_2121724).sum := by decide
  have hdescent : baseEnd_2121724 < baseStart_2121724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2121724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2121764 : List Nat := [2, 3, 1, 4, 2, 1, 1, 2, 7]
def baseStart_2121764 : Nat := 118140960795 + 2121764 * 2 ^ 59
def prefixEnd_2121764 : Nat := 4983230072969 + 3 ^ 40 * 2121764 * 2
def baseEnd_2121764 : Nat := 121053863045149091365799

theorem tailTrace_2121764 : CollatzResearch.WordTrace tailWord_2121764 prefixEnd_2121764 121053863045149091365799 := by
  unfold tailWord_2121764
  simp only [CollatzResearch.WordTrace]
  refine ⟨38693545342609435643342173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51591393790145914191122897 38693545342609435643342173)
  ·
    refine ⟨14510079503478538366253315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38693545342609435643342173 14510079503478538366253315)
    ·
      refine ⟨21765119255217807549379973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14510079503478538366253315 21765119255217807549379973)
      ·
        refine ⟨4080959860353338915508745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21765119255217807549379973 4080959860353338915508745)
        ·
          refine ⟨3060719895265004186631559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4080959860353338915508745 3060719895265004186631559)
          ·
            refine ⟨4591079842897506279947339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3060719895265004186631559 4591079842897506279947339)
            ·
              refine ⟨6886619764346259419921009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4591079842897506279947339 6886619764346259419921009)
              ·
                refine ⟨5164964823259694564940757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6886619764346259419921009 5164964823259694564940757)
                ·
                  refine ⟨121053863045149091365799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5164964823259694564940757 121053863045149091365799)
                  ·
                    rfl

theorem cell23_2121764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 2, 7].length) (baseStart_2121764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2121764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2121764 prefixEnd_2121764 := by exact prefixLift 2121764
  have htrace : WordTrace (prefixWord ++ tailWord_2121764) baseStart_2121764 baseEnd_2121764 := by
    simpa [prefixWord, tailWord_2121764, baseEnd_2121764] using wordTrace_append hprefix tailTrace_2121764
  have hstable : (prefixWord ++ tailWord_2121764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2121764).length < 2 ^ (prefixWord ++ tailWord_2121764).sum := by decide
  have hdescent : baseEnd_2121764 < baseStart_2121764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2121764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2121777 : List Nat := [1, 2, 2, 3, 1, 4, 1, 1, 1, 7]
def baseStart_2121777 : Nat := 118140960795 + 2121777 * 2 ^ 59
def prefixEnd_2121777 : Nat := 4983230072969 + 3 ^ 40 * 2121777 * 2
def baseEnd_2121777 : Nat := 363163814218283423809877

theorem tailTrace_2121777 : CollatzResearch.WordTrace tailWord_2121777 prefixEnd_2121777 363163814218283423809877 := by
  unfold tailWord_2121777
  simp only [CollatzResearch.WordTrace]
  refine ⟨77387564834171774506907585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51591709889447849671271723 77387564834171774506907585)
  ·
    refine ⟨58040673625628830880180689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77387564834171774506907585 58040673625628830880180689)
    ·
      refine ⟨43530505219221623160135517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58040673625628830880180689 43530505219221623160135517)
      ·
        refine ⟨16323939457208108685050819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43530505219221623160135517 16323939457208108685050819)
        ·
          refine ⟨24485909185812163027576229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16323939457208108685050819 24485909185812163027576229)
          ·
            refine ⟨4591107972339780567670543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24485909185812163027576229 4591107972339780567670543)
            ·
              refine ⟨6886661958509670851505815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4591107972339780567670543 6886661958509670851505815)
              ·
                refine ⟨10329992937764506277258723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6886661958509670851505815 10329992937764506277258723)
                ·
                  refine ⟨15494989406646759415888085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10329992937764506277258723 15494989406646759415888085)
                  ·
                    refine ⟨363163814218283423809877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15494989406646759415888085 363163814218283423809877)
                    ·
                      rfl

theorem cell23_2121777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 1, 1, 7].length) (baseStart_2121777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2121777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2121777 prefixEnd_2121777 := by exact prefixLift 2121777
  have htrace : WordTrace (prefixWord ++ tailWord_2121777) baseStart_2121777 baseEnd_2121777 := by
    simpa [prefixWord, tailWord_2121777, baseEnd_2121777] using wordTrace_append hprefix tailTrace_2121777
  have hstable : (prefixWord ++ tailWord_2121777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2121777).length < 2 ^ (prefixWord ++ tailWord_2121777).sum := by decide
  have hdescent : baseEnd_2121777 < baseStart_2121777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2121777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2121797 : List Nat := [1, 3, 1, 1, 1, 3, 1, 3, 4, 1, 4]
def baseStart_2121797 : Nat := 118140960795 + 2121797 * 2 ^ 59
def prefixEnd_2121797 : Nat := 4983230072969 + 3 ^ 40 * 2121797 * 2
def baseEnd_2121797 : Nat := 1089501712267940193179539

theorem tailTrace_2121797 : CollatzResearch.WordTrace tailWord_2121797 prefixEnd_2121797 1089501712267940193179539 := by
  unfold tailWord_2121797
  simp only [CollatzResearch.WordTrace]
  refine ⟨77388294294099317922635645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51592196196066211948423763 77388294294099317922635645)
  ·
    refine ⟨29020610360287244220988367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77388294294099317922635645 29020610360287244220988367)
    ·
      refine ⟨43530915540430866331482551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29020610360287244220988367 43530915540430866331482551)
      ·
        refine ⟨65296373310646299497223827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43530915540430866331482551 65296373310646299497223827)
        ·
          refine ⟨97944559965969449245835741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65296373310646299497223827 97944559965969449245835741)
          ·
            refine ⟨36729209987238543467188403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97944559965969449245835741 36729209987238543467188403)
            ·
              refine ⟨55093814980857815200782605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36729209987238543467188403 55093814980857815200782605)
              ·
                refine ⟨20660180617821680700293477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55093814980857815200782605 20660180617821680700293477)
                ·
                  refine ⟨3873783865841565131305027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20660180617821680700293477 3873783865841565131305027)
                  ·
                    refine ⟨5810675798762347696957541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3873783865841565131305027 5810675798762347696957541)
                    ·
                      refine ⟨1089501712267940193179539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5810675798762347696957541 1089501712267940193179539)
                      ·
                        rfl

theorem cell23_2121797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 4, 1, 4].length) (baseStart_2121797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2121797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2121797 prefixEnd_2121797 := by exact prefixLift 2121797
  have htrace : WordTrace (prefixWord ++ tailWord_2121797) baseStart_2121797 baseEnd_2121797 := by
    simpa [prefixWord, tailWord_2121797, baseEnd_2121797] using wordTrace_append hprefix tailTrace_2121797
  have hstable : (prefixWord ++ tailWord_2121797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2121797).length < 2 ^ (prefixWord ++ tailWord_2121797).sum := by decide
  have hdescent : baseEnd_2121797 < baseStart_2121797 := by decide
  rcases family_descends (prefixWord ++ tailWord_2121797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2121807 : List Nat := [1, 1, 2, 1, 1, 2, 2, 2, 7, 4]
def baseStart_2121807 : Nat := 118140960795 + 2121807 * 2 ^ 59
def prefixEnd_2121807 : Nat := 4983230072969 + 3 ^ 40 * 2121807 * 2
def baseEnd_2121807 : Nat := 363168949024828384684831

theorem tailTrace_2121807 : CollatzResearch.WordTrace tailWord_2121807 prefixEnd_2121807 363168949024828384684831 := by
  unfold tailWord_2121807
  simp only [CollatzResearch.WordTrace]
  refine ⟨77388659024063089630499675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51592439349375393086999783 77388659024063089630499675)
  ·
    refine ⟨116082988536094634445749513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77388659024063089630499675 116082988536094634445749513)
    ·
      refine ⟨87062241402070975834312135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116082988536094634445749513 87062241402070975834312135)
      ·
        refine ⟨130593362103106463751468203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87062241402070975834312135 130593362103106463751468203)
        ·
          refine ⟨195890043154659695627202305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130593362103106463751468203 195890043154659695627202305)
          ·
            refine ⟨146917532365994771720401729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 195890043154659695627202305 146917532365994771720401729)
            ·
              refine ⟨110188149274496078790301297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 146917532365994771720401729 110188149274496078790301297)
              ·
                refine ⟨82641111955872059092725973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 110188149274496078790301297 82641111955872059092725973)
                ·
                  refine ⟨1936901061465751384985765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 82641111955872059092725973 1936901061465751384985765)
                  ·
                    refine ⟨363168949024828384684831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1936901061465751384985765 363168949024828384684831)
                    ·
                      rfl

theorem cell23_2121807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 7, 4].length) (baseStart_2121807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2121807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2121807 prefixEnd_2121807 := by exact prefixLift 2121807
  have htrace : WordTrace (prefixWord ++ tailWord_2121807) baseStart_2121807 baseEnd_2121807 := by
    simpa [prefixWord, tailWord_2121807, baseEnd_2121807] using wordTrace_append hprefix tailTrace_2121807
  have hstable : (prefixWord ++ tailWord_2121807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2121807).length < 2 ^ (prefixWord ++ tailWord_2121807).sum := by decide
  have hdescent : baseEnd_2121807 < baseStart_2121807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2121807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2121817 : List Nat := [1, 2, 1, 2, 2, 1, 3, 1, 3, 4, 3]
def baseStart_2121817 : Nat := 118140960795 + 2121817 * 2 ^ 59
def prefixEnd_2121817 : Nat := 4983230072969 + 3 ^ 40 * 2121817 * 2
def baseEnd_2121817 : Nat := 1089511981881030114929447

theorem tailTrace_2121817 : CollatzResearch.WordTrace tailWord_2121817 prefixEnd_2121817 1089511981881030114929447 := by
  unfold tailWord_2121817
  simp only [CollatzResearch.WordTrace]
  refine ⟨77389023754026861338363705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51592682502684574225575803 77389023754026861338363705)
  ·
    refine ⟨58041767815520146003772779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77389023754026861338363705 58041767815520146003772779)
    ·
      refine ⟨87062651723280219005659169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58041767815520146003772779 87062651723280219005659169)
      ·
        refine ⟨65296988792460164254244377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87062651723280219005659169 65296988792460164254244377)
        ·
          refine ⟨48972741594345123190683283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65296988792460164254244377 48972741594345123190683283)
          ·
            refine ⟨73459112391517684786024925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48972741594345123190683283 73459112391517684786024925)
            ·
              refine ⟨27547167146819131794759347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73459112391517684786024925 27547167146819131794759347)
              ·
                refine ⟨41320750720228697692139021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27547167146819131794759347 41320750720228697692139021)
                ·
                  refine ⟨15495281520085761634552133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41320750720228697692139021 15495281520085761634552133)
                  ·
                    refine ⟨2905365285016080306478525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15495281520085761634552133 2905365285016080306478525)
                    ·
                      refine ⟨1089511981881030114929447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2905365285016080306478525 1089511981881030114929447)
                      ·
                        rfl

theorem cell23_2121817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 3, 4, 3].length) (baseStart_2121817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2121817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2121817 prefixEnd_2121817 := by exact prefixLift 2121817
  have htrace : WordTrace (prefixWord ++ tailWord_2121817) baseStart_2121817 baseEnd_2121817 := by
    simpa [prefixWord, tailWord_2121817, baseEnd_2121817] using wordTrace_append hprefix tailTrace_2121817
  have hstable : (prefixWord ++ tailWord_2121817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2121817).length < 2 ^ (prefixWord ++ tailWord_2121817).sum := by decide
  have hdescent : baseEnd_2121817 < baseStart_2121817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2121817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2121824 : List Nat := [2, 1, 1, 3, 2, 3, 2, 2, 3, 4]
def baseStart_2121824 : Nat := 118140960795 + 2121824 * 2 ^ 59
def prefixEnd_2121824 : Nat := 4983230072969 + 3 ^ 40 * 2121824 * 2
def baseEnd_2121824 : Nat := 363171858748537195847305

theorem tailTrace_2121824 : CollatzResearch.WordTrace tailWord_2121824 prefixEnd_2121824 363171858748537195847305 := by
  unfold tailWord_2121824
  simp only [CollatzResearch.WordTrace]
  refine ⟨38694639532500750766934263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51592852710001001022579017 38694639532500750766934263)
  ·
    refine ⟨58041959298751126150401395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38694639532500750766934263 58041959298751126150401395)
    ·
      refine ⟨87062938948126689225602093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58041959298751126150401395 87062938948126689225602093)
      ·
        refine ⟨32648602105547508459600785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87062938948126689225602093 32648602105547508459600785)
        ·
          refine ⟨24486451579160631344700589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32648602105547508459600785 24486451579160631344700589)
          ·
            refine ⟨9182419342185236754262721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24486451579160631344700589 9182419342185236754262721)
            ·
              refine ⟨6886814506638927565697041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9182419342185236754262721 6886814506638927565697041)
              ·
                refine ⟨5165110879979195674272781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6886814506638927565697041 5165110879979195674272781)
                ·
                  refine ⟨1936916579992198377852293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5165110879979195674272781 1936916579992198377852293)
                  ·
                    refine ⟨363171858748537195847305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1936916579992198377852293 363171858748537195847305)
                    ·
                      rfl

theorem cell23_2121824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 2, 3, 4].length) (baseStart_2121824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2121824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2121824 prefixEnd_2121824 := by exact prefixLift 2121824
  have htrace : WordTrace (prefixWord ++ tailWord_2121824) baseStart_2121824 baseEnd_2121824 := by
    simpa [prefixWord, tailWord_2121824, baseEnd_2121824] using wordTrace_append hprefix tailTrace_2121824
  have hstable : (prefixWord ++ tailWord_2121824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2121824).length < 2 ^ (prefixWord ++ tailWord_2121824).sum := by decide
  have hdescent : baseEnd_2121824 < baseStart_2121824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2121824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2121837 : List Nat := [1, 5, 1, 1, 2, 1, 1, 1, 10]
def baseStart_2121837 : Nat := 118140960795 + 2121837 * 2 ^ 59
def prefixEnd_2121837 : Nat := 4983230072969 + 3 ^ 40 * 2121837 * 2
def baseEnd_2121837 : Nat := 121058027943791115186595

theorem tailTrace_2121837 : CollatzResearch.WordTrace tailWord_2121837 prefixEnd_2121837 121058027943791115186595 := by
  unfold tailWord_2121837
  simp only [CollatzResearch.WordTrace]
  refine ⟨77389753213954404754091765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51593168809302936502727843 77389753213954404754091765)
  ·
    refine ⟨7255289363808225445696103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 77389753213954404754091765 7255289363808225445696103)
    ·
      refine ⟨10882934045712338168544155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7255289363808225445696103 10882934045712338168544155)
      ·
        refine ⟨16324401068568507252816233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10882934045712338168544155 16324401068568507252816233)
        ·
          refine ⟨12243300801426380439612175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16324401068568507252816233 12243300801426380439612175)
          ·
            refine ⟨18364951202139570659418263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12243300801426380439612175 18364951202139570659418263)
            ·
              refine ⟨27547426803209355989127395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18364951202139570659418263 27547426803209355989127395)
              ·
                refine ⟨41321140204814033983691093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27547426803209355989127395 41321140204814033983691093)
                ·
                  refine ⟨121058027943791115186595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 41321140204814033983691093 121058027943791115186595)
                  ·
                    rfl

theorem cell23_2121837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 10].length) (baseStart_2121837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2121837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2121837 prefixEnd_2121837 := by exact prefixLift 2121837
  have htrace : WordTrace (prefixWord ++ tailWord_2121837) baseStart_2121837 baseEnd_2121837 := by
    simpa [prefixWord, tailWord_2121837, baseEnd_2121837] using wordTrace_append hprefix tailTrace_2121837
  have hstable : (prefixWord ++ tailWord_2121837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2121837).length < 2 ^ (prefixWord ++ tailWord_2121837).sum := by decide
  have hdescent : baseEnd_2121837 < baseStart_2121837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2121837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2121884 : List Nat := [2, 2, 3, 2, 1, 1, 3, 1, 3, 5]
def baseStart_2121884 : Nat := 118140960795 + 2121884 * 2 ^ 59
def prefixEnd_2121884 : Nat := 4983230072969 + 3 ^ 40 * 2121884 * 2
def baseEnd_2121884 : Nat := 363182128361627117597213

theorem tailTrace_2121884 : CollatzResearch.WordTrace tailWord_2121884 prefixEnd_2121884 363182128361627117597213 := by
  unfold tailWord_2121884
  simp only [CollatzResearch.WordTrace]
  refine ⟨38695733722392065890526353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51594311629856087854035137 38695733722392065890526353)
  ·
    refine ⟨29021800291794049417894765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38695733722392065890526353 29021800291794049417894765)
    ·
      refine ⟨10883175109422768531710537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29021800291794049417894765 10883175109422768531710537)
      ·
        refine ⟨8162381332067076398782903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10883175109422768531710537 8162381332067076398782903)
        ·
          refine ⟨12243571998100614598174355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8162381332067076398782903 12243571998100614598174355)
          ·
            refine ⟨18365357997150921897261533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12243571998100614598174355 18365357997150921897261533)
            ·
              refine ⟨6887009248931595711473075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18365357997150921897261533 6887009248931595711473075)
              ·
                refine ⟨10330513873397393567209613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6887009248931595711473075 10330513873397393567209613)
                ·
                  refine ⟨3873942702524022587703605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10330513873397393567209613 3873942702524022587703605)
                  ·
                    refine ⟨363182128361627117597213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3873942702524022587703605 363182128361627117597213)
                    ·
                      rfl

theorem cell23_2121884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 1, 3, 5].length) (baseStart_2121884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2121884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2121884 prefixEnd_2121884 := by exact prefixLift 2121884
  have htrace : WordTrace (prefixWord ++ tailWord_2121884) baseStart_2121884 baseEnd_2121884 := by
    simpa [prefixWord, tailWord_2121884, baseEnd_2121884] using wordTrace_append hprefix tailTrace_2121884
  have hstable : (prefixWord ++ tailWord_2121884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2121884).length < 2 ^ (prefixWord ++ tailWord_2121884).sum := by decide
  have hdescent : baseEnd_2121884 < baseStart_2121884 := by decide
  rcases family_descends (prefixWord ++ tailWord_2121884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2121909 : List Nat := [1, 3, 3, 4, 2, 1, 2, 2, 1, 4]
def baseStart_2121909 : Nat := 118140960795 + 2121909 * 2 ^ 59
def prefixEnd_2121909 : Nat := 4983230072969 + 3 ^ 40 * 2121909 * 2
def baseEnd_2121909 : Nat := 363186407367081251659675

theorem tailTrace_2121909 : CollatzResearch.WordTrace tailWord_2121909 prefixEnd_2121909 363186407367081251659675 := by
  unfold tailWord_2121909
  simp only [CollatzResearch.WordTrace]
  refine ⟨77392379269693561050712781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51594919513129040700475187 77392379269693561050712781)
  ·
    refine ⟨29022142226135085394017293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77392379269693561050712781 29022142226135085394017293)
    ·
      refine ⟨10883303334800657022756485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29022142226135085394017293 10883303334800657022756485)
      ·
        refine ⟨2040619375275123191766841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10883303334800657022756485 2040619375275123191766841)
        ·
          refine ⟨1530464531456342393825131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2040619375275123191766841 1530464531456342393825131)
          ·
            refine ⟨2295696797184513590737697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1530464531456342393825131 2295696797184513590737697)
            ·
              refine ⟨1721772597888385193053273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2295696797184513590737697 1721772597888385193053273)
              ·
                refine ⟨1291329448416288894789955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1721772597888385193053273 1291329448416288894789955)
                ·
                  refine ⟨1936994172624433342184933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1291329448416288894789955 1936994172624433342184933)
                  ·
                    refine ⟨363186407367081251659675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1936994172624433342184933 363186407367081251659675)
                    ·
                      rfl

theorem cell23_2121909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 2, 2, 1, 4].length) (baseStart_2121909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2121909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2121909 prefixEnd_2121909 := by exact prefixLift 2121909
  have htrace : WordTrace (prefixWord ++ tailWord_2121909) baseStart_2121909 baseEnd_2121909 := by
    simpa [prefixWord, tailWord_2121909, baseEnd_2121909] using wordTrace_append hprefix tailTrace_2121909
  have hstable : (prefixWord ++ tailWord_2121909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2121909).length < 2 ^ (prefixWord ++ tailWord_2121909).sum := by decide
  have hdescent : baseEnd_2121909 < baseStart_2121909 := by decide
  rcases family_descends (prefixWord ++ tailWord_2121909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2121914 : List Nat := [3, 1, 1, 1, 2, 2, 2, 3, 4, 4]
def baseStart_2121914 : Nat := 118140960795 + 2121914 * 2 ^ 59
def prefixEnd_2121914 : Nat := 4983230072969 + 3 ^ 40 * 2121914 * 2
def baseEnd_2121914 : Nat := 363187263168172078472167

theorem tailTrace_2121914 : CollatzResearch.WordTrace tailWord_2121914 prefixEnd_2121914 363187263168172078472167 := by
  unfold tailWord_2121914
  simp only [CollatzResearch.WordTrace]
  refine ⟨19348140408668861726161199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51595041089783631269763197 19348140408668861726161199)
  ·
    refine ⟨29022210613003292589241799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19348140408668861726161199 29022210613003292589241799)
    ·
      refine ⟨43533315919504938883862699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29022210613003292589241799 43533315919504938883862699)
      ·
        refine ⟨65299973879257408325794049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43533315919504938883862699 65299973879257408325794049)
        ·
          refine ⟨48974980409443056244345537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65299973879257408325794049 48974980409443056244345537)
          ·
            refine ⟨36731235307082292183259153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48974980409443056244345537 36731235307082292183259153)
            ·
              refine ⟨27548426480311719137444365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36731235307082292183259153 27548426480311719137444365)
              ·
                refine ⟨10330659930116894676541637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27548426480311719137444365 10330659930116894676541637)
                ·
                  refine ⟨1936998736896917751851557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10330659930116894676541637 1936998736896917751851557)
                  ·
                    refine ⟨363187263168172078472167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1936998736896917751851557 363187263168172078472167)
                    ·
                      rfl

theorem cell23_2121914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 3, 4, 4].length) (baseStart_2121914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2121914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2121914 prefixEnd_2121914 := by exact prefixLift 2121914
  have htrace : WordTrace (prefixWord ++ tailWord_2121914) baseStart_2121914 baseEnd_2121914 := by
    simpa [prefixWord, tailWord_2121914, baseEnd_2121914] using wordTrace_append hprefix tailTrace_2121914
  have hstable : (prefixWord ++ tailWord_2121914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2121914).length < 2 ^ (prefixWord ++ tailWord_2121914).sum := by decide
  have hdescent : baseEnd_2121914 < baseStart_2121914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2121914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2121938 : List Nat := [3, 2, 2, 2, 1, 2, 1, 1, 5, 2, 2]
def baseStart_2121938 : Nat := 118140960795 + 2121938 * 2 ^ 59
def prefixEnd_2121938 : Nat := 4983230072969 + 3 ^ 40 * 2121938 * 2
def baseEnd_2121938 : Nat := 1089574113040224141516391

theorem tailTrace_2121938 : CollatzResearch.WordTrace tailWord_2121938 prefixEnd_2121938 1089574113040224141516391 := by
  unfold tailWord_2121938
  simp only [CollatzResearch.WordTrace]
  refine ⟨19348359246647124750879617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51595624657725666002345645 19348359246647124750879617)
  ·
    refine ⟨14511269434985343563159713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19348359246647124750879617 14511269434985343563159713)
    ·
      refine ⟨10883452076239007672369785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14511269434985343563159713 10883452076239007672369785)
      ·
        refine ⟨8162589057179255754277339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10883452076239007672369785 8162589057179255754277339)
        ·
          refine ⟨12243883585768883631416009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8162589057179255754277339 12243883585768883631416009)
          ·
            refine ⟨9182912689326662723562007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12243883585768883631416009 9182912689326662723562007)
            ·
              refine ⟨13774369033989994085343011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9182912689326662723562007 13774369033989994085343011)
              ·
                refine ⟨20661553550984991128014517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13774369033989994085343011 20661553550984991128014517)
                ·
                  refine ⟨1937020645404842918251361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20661553550984991128014517 1937020645404842918251361)
                  ·
                    refine ⟨1452765484053632188688521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1937020645404842918251361 1452765484053632188688521)
                    ·
                      refine ⟨1089574113040224141516391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1452765484053632188688521 1089574113040224141516391)
                      ·
                        rfl

theorem cell23_2121938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 5, 2, 2].length) (baseStart_2121938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2121938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2121938 prefixEnd_2121938 := by exact prefixLift 2121938
  have htrace : WordTrace (prefixWord ++ tailWord_2121938) baseStart_2121938 baseEnd_2121938 := by
    simpa [prefixWord, tailWord_2121938, baseEnd_2121938] using wordTrace_append hprefix tailTrace_2121938
  have hstable : (prefixWord ++ tailWord_2121938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2121938).length < 2 ^ (prefixWord ++ tailWord_2121938).sum := by decide
  have hdescent : baseEnd_2121938 < baseStart_2121938 := by decide
  rcases family_descends (prefixWord ++ tailWord_2121938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2121942 : List Nat := [5, 2, 1, 2, 1, 3, 1, 1, 2, 3, 2]
def baseStart_2121942 : Nat := 118140960795 + 2121942 * 2 ^ 59
def prefixEnd_2121942 : Nat := 4983230072969 + 3 ^ 40 * 2121942 * 2
def baseEnd_2121942 : Nat := 1089576166962842125866373

theorem tailTrace_2121942 : CollatzResearch.WordTrace tailWord_2121942 prefixEnd_2121942 1089576166962842125866373 := by
  unfold tailWord_2121942
  simp only [CollatzResearch.WordTrace]
  refine ⟨4837098929910875480416505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 51595721919049338457776053 4837098929910875480416505)
  ·
    refine ⟨3627824197433156610312379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4837098929910875480416505 3627824197433156610312379)
    ·
      refine ⟨5441736296149734915468569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3627824197433156610312379 5441736296149734915468569)
      ·
        refine ⟨4081302222112301186601427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5441736296149734915468569 4081302222112301186601427)
        ·
          refine ⟨6121953333168451779902141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4081302222112301186601427 6121953333168451779902141)
          ·
            refine ⟨2295732499938169417463303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6121953333168451779902141 2295732499938169417463303)
            ·
              refine ⟨3443598749907254126194955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2295732499938169417463303 3443598749907254126194955)
              ·
                refine ⟨5165398124860881189292433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3443598749907254126194955 5165398124860881189292433)
                ·
                  refine ⟨3874048593645660891969325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5165398124860881189292433 3874048593645660891969325)
                  ·
                    refine ⟨1452768222617122834488497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3874048593645660891969325 1452768222617122834488497)
                    ·
                      refine ⟨1089576166962842125866373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1452768222617122834488497 1089576166962842125866373)
                      ·
                        rfl

theorem cell23_2121942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_2121942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2121942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2121942 prefixEnd_2121942 := by exact prefixLift 2121942
  have htrace : WordTrace (prefixWord ++ tailWord_2121942) baseStart_2121942 baseEnd_2121942 := by
    simpa [prefixWord, tailWord_2121942, baseEnd_2121942] using wordTrace_append hprefix tailTrace_2121942
  have hstable : (prefixWord ++ tailWord_2121942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2121942).length < 2 ^ (prefixWord ++ tailWord_2121942).sum := by decide
  have hdescent : baseEnd_2121942 < baseStart_2121942 := by decide
  rcases family_descends (prefixWord ++ tailWord_2121942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2121965 : List Nat := [1, 5, 1, 2, 3, 2, 1, 2, 2, 4]
def baseStart_2121965 : Nat := 118140960795 + 2121965 * 2 ^ 59
def prefixEnd_2121965 : Nat := 4983230072969 + 3 ^ 40 * 2121965 * 2
def baseEnd_2121965 : Nat := 363195992339298511959589

theorem tailTrace_2121965 : CollatzResearch.WordTrace tailWord_2121965 prefixEnd_2121965 363195992339298511959589 := by
  unfold tailWord_2121965
  simp only [CollatzResearch.WordTrace]
  refine ⟨77394421757490682614751349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51596281171660455076500899 77394421757490682614751349)
  ·
    refine ⟨7255727039764751495132939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 77394421757490682614751349 7255727039764751495132939)
    ·
      refine ⟨10883590559647127242699409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7255727039764751495132939 10883590559647127242699409)
      ·
        refine ⟨8162692919735345432024557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10883590559647127242699409 8162692919735345432024557)
        ·
          refine ⟨3061009844900754537009209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8162692919735345432024557 3061009844900754537009209)
          ·
            refine ⟨2295757383675565902756907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3061009844900754537009209 2295757383675565902756907)
            ·
              refine ⟨3443636075513348854135361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2295757383675565902756907 3443636075513348854135361)
              ·
                refine ⟨2582727056635011640601521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3443636075513348854135361 2582727056635011640601521)
                ·
                  refine ⟨1937045292476258730451141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2582727056635011640601521 1937045292476258730451141)
                  ·
                    refine ⟨363195992339298511959589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1937045292476258730451141 363195992339298511959589)
                    ·
                      rfl

theorem cell23_2121965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 2, 2, 4].length) (baseStart_2121965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2121965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2121965 prefixEnd_2121965 := by exact prefixLift 2121965
  have htrace : WordTrace (prefixWord ++ tailWord_2121965) baseStart_2121965 baseEnd_2121965 := by
    simpa [prefixWord, tailWord_2121965, baseEnd_2121965] using wordTrace_append hprefix tailTrace_2121965
  have hstable : (prefixWord ++ tailWord_2121965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2121965).length < 2 ^ (prefixWord ++ tailWord_2121965).sum := by decide
  have hdescent : baseEnd_2121965 < baseStart_2121965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2121965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2121971 : List Nat := [1, 1, 1, 2, 2, 4, 3, 1, 4, 1, 3]
def baseStart_2121971 : Nat := 118140960795 + 2121971 * 2 ^ 59
def prefixEnd_2121971 : Nat := 4983230072969 + 3 ^ 40 * 2121971 * 2
def baseEnd_2121971 : Nat := 1089591057901822512403739

theorem tailTrace_2121971 : CollatzResearch.WordTrace tailWord_2121971 prefixEnd_2121971 1089591057901822512403739 := by
  unfold tailWord_2121971
  simp only [CollatzResearch.WordTrace]
  refine ⟨77394640595468945639469767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51596427063645963759646511 77394640595468945639469767)
  ·
    refine ⟨116091960893203418459204651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77394640595468945639469767 116091960893203418459204651)
    ·
      refine ⟨174137941339805127688806977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116091960893203418459204651 174137941339805127688806977)
      ·
        refine ⟨130603456004853845766605233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174137941339805127688806977 130603456004853845766605233)
        ·
          refine ⟨97952592003640384324953925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130603456004853845766605233 97952592003640384324953925)
          ·
            refine ⟨18366111000682572060928861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 97952592003640384324953925 18366111000682572060928861)
            ·
              refine ⟨6887291625255964522848323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18366111000682572060928861 6887291625255964522848323)
              ·
                refine ⟨10330937437883946784272485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6887291625255964522848323 10330937437883946784272485)
                ·
                  refine ⟨1937050769603240022051091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10330937437883946784272485 1937050769603240022051091)
                  ·
                    refine ⟨2905576154404860033076637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1937050769603240022051091 2905576154404860033076637)
                    ·
                      refine ⟨1089591057901822512403739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2905576154404860033076637 1089591057901822512403739)
                      ·
                        rfl

theorem cell23_2121971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 1, 4, 1, 3].length) (baseStart_2121971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2121971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2121971 prefixEnd_2121971 := by exact prefixLift 2121971
  have htrace : WordTrace (prefixWord ++ tailWord_2121971) baseStart_2121971 baseEnd_2121971 := by
    simpa [prefixWord, tailWord_2121971, baseEnd_2121971] using wordTrace_append hprefix tailTrace_2121971
  have hstable : (prefixWord ++ tailWord_2121971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2121971).length < 2 ^ (prefixWord ++ tailWord_2121971).sum := by decide
  have hdescent : baseEnd_2121971 < baseStart_2121971 := by decide
  rcases family_descends (prefixWord ++ tailWord_2121971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2121974 : List Nat := [5, 1, 1, 1, 1, 1, 2, 1, 1, 9]
def baseStart_2121974 : Nat := 118140960795 + 2121974 * 2 ^ 59
def prefixEnd_2121974 : Nat := 4983230072969 + 3 ^ 40 * 2121974 * 2
def baseEnd_2121974 : Nat := 363197532781262000222075

theorem tailTrace_2121974 : CollatzResearch.WordTrace tailWord_2121974 prefixEnd_2121974 363197532781262000222075 := by
  unfold tailWord_2121974
  simp only [CollatzResearch.WordTrace]
  refine ⟨4837171875903629821989311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 51596500009638718101219317 4837171875903629821989311)
  ·
    refine ⟨7255757813855444732983967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4837171875903629821989311 7255757813855444732983967)
    ·
      refine ⟨10883636720783167099475951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7255757813855444732983967 10883636720783167099475951)
      ·
        refine ⟨16325455081174750649213927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10883636720783167099475951 16325455081174750649213927)
        ·
          refine ⟨24488182621762125973820891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16325455081174750649213927 24488182621762125973820891)
          ·
            refine ⟨36732273932643188960731337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24488182621762125973820891 36732273932643188960731337)
            ·
              refine ⟨27549205449482391720548503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36732273932643188960731337 27549205449482391720548503)
              ·
                refine ⟨41323808174223587580822755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27549205449482391720548503 41323808174223587580822755)
                ·
                  refine ⟨61985712261335381371234133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41323808174223587580822755 61985712261335381371234133)
                  ·
                    refine ⟨363197532781262000222075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 61985712261335381371234133 363197532781262000222075)
                    ·
                      rfl

theorem cell23_2121974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 1, 9].length) (baseStart_2121974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2121974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2121974 prefixEnd_2121974 := by exact prefixLift 2121974
  have htrace : WordTrace (prefixWord ++ tailWord_2121974) baseStart_2121974 baseEnd_2121974 := by
    simpa [prefixWord, tailWord_2121974, baseEnd_2121974] using wordTrace_append hprefix tailTrace_2121974
  have hstable : (prefixWord ++ tailWord_2121974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2121974).length < 2 ^ (prefixWord ++ tailWord_2121974).sum := by decide
  have hdescent : baseEnd_2121974 < baseStart_2121974 := by decide
  rcases family_descends (prefixWord ++ tailWord_2121974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2121981 : List Nat := [1, 4, 1, 1, 1, 1, 1, 3, 5, 3, 2]
def baseStart_2121981 : Nat := 118140960795 + 2121981 * 2 ^ 59
def prefixEnd_2121981 : Nat := 4983230072969 + 3 ^ 40 * 2121981 * 2
def baseEnd_2121981 : Nat := 1089596192708367473278693

theorem tailTrace_2121981 : CollatzResearch.WordTrace tailWord_2121981 prefixEnd_2121981 1089596192708367473278693 := by
  unfold tailWord_2121981
  simp only [CollatzResearch.WordTrace]
  refine ⟨77395005325432717347333797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51596670216955144898222531 77395005325432717347333797)
  ·
    refine ⟨14511563498518634502625087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77395005325432717347333797 14511563498518634502625087)
    ·
      refine ⟨21767345247777951753937631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14511563498518634502625087 21767345247777951753937631)
      ·
        refine ⟨32651017871666927630906447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21767345247777951753937631 32651017871666927630906447)
        ·
          refine ⟨48976526807500391446359671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32651017871666927630906447 48976526807500391446359671)
          ·
            refine ⟨73464790211250587169539507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48976526807500391446359671 73464790211250587169539507)
            ·
              refine ⟨110197185316875880754309261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73464790211250587169539507 110197185316875880754309261)
              ·
                refine ⟨41323944493828455282865973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 110197185316875880754309261 41323944493828455282865973)
                ·
                  refine ⟨3874119796296417682768685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41323944493828455282865973 3874119796296417682768685)
                  ·
                    refine ⟨1452794923611156631038257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3874119796296417682768685 1452794923611156631038257)
                    ·
                      refine ⟨1089596192708367473278693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1452794923611156631038257 1089596192708367473278693)
                      ·
                        rfl

theorem cell23_2121981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 5, 3, 2].length) (baseStart_2121981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2121981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2121981 prefixEnd_2121981 := by exact prefixLift 2121981
  have htrace : WordTrace (prefixWord ++ tailWord_2121981) baseStart_2121981 baseEnd_2121981 := by
    simpa [prefixWord, tailWord_2121981, baseEnd_2121981] using wordTrace_append hprefix tailTrace_2121981
  have hstable : (prefixWord ++ tailWord_2121981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2121981).length < 2 ^ (prefixWord ++ tailWord_2121981).sum := by decide
  have hdescent : baseEnd_2121981 < baseStart_2121981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2121981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2121994 : List Nat := [3, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4]
def baseStart_2121994 : Nat := 118140960795 + 2121994 * 2 ^ 59
def prefixEnd_2121994 : Nat := 4983230072969 + 3 ^ 40 * 2121994 * 2
def baseEnd_2121994 : Nat := 1089602867956875922416133

theorem tailTrace_2121994 : CollatzResearch.WordTrace tailWord_2121994 prefixEnd_2121994 1089602867956875922416133 := by
  unfold tailWord_2121994
  simp only [CollatzResearch.WordTrace]
  refine ⟨19348869868596405141889259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51596986316257080378371357 19348869868596405141889259)
  ·
    refine ⟨29023304802894607712833889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19348869868596405141889259 29023304802894607712833889)
    ·
      refine ⟨21767478602170955784625417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29023304802894607712833889 21767478602170955784625417)
      ·
        refine ⟨16325608951628216838469063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21767478602170955784625417 16325608951628216838469063)
        ·
          refine ⟨24488413427442325257703595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16325608951628216838469063 24488413427442325257703595)
          ·
            refine ⟨36732620141163487886555393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24488413427442325257703595 36732620141163487886555393)
            ·
              refine ⟨27549465105872615914916545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36732620141163487886555393 27549465105872615914916545)
              ·
                refine ⟨20662098829404461936187409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27549465105872615914916545 20662098829404461936187409)
                ·
                  refine ⟨15496574122053346452140557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20662098829404461936187409 15496574122053346452140557)
                  ·
                    refine ⟨5811215295770004919552709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15496574122053346452140557 5811215295770004919552709)
                    ·
                      refine ⟨1089602867956875922416133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5811215295770004919552709 1089602867956875922416133)
                      ·
                        rfl

theorem cell23_2121994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_2121994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2121994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2121994 prefixEnd_2121994 := by exact prefixLift 2121994
  have htrace : WordTrace (prefixWord ++ tailWord_2121994) baseStart_2121994 baseEnd_2121994 := by
    simpa [prefixWord, tailWord_2121994, baseEnd_2121994] using wordTrace_append hprefix tailTrace_2121994
  have hstable : (prefixWord ++ tailWord_2121994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2121994).length < 2 ^ (prefixWord ++ tailWord_2121994).sum := by decide
  have hdescent : baseEnd_2121994 < baseStart_2121994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2121994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2122011 : List Nat := [1, 1, 1, 1, 1, 1, 6, 4, 1, 4, 2]
def baseStart_2122011 : Nat := 118140960795 + 2122011 * 2 ^ 59
def prefixEnd_2122011 : Nat := 4983230072969 + 3 ^ 40 * 2122011 * 2
def baseEnd_2122011 : Nat := 1089611597128002355903555

theorem tailTrace_2122011 : CollatzResearch.WordTrace tailWord_2122011 prefixEnd_2122011 1089611597128002355903555 := by
  unfold tailWord_2122011
  simp only [CollatzResearch.WordTrace]
  refine ⟨77396099515324032470925887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51597399676882688313950591 77396099515324032470925887)
  ·
    refine ⟨116094149272986048706388831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77396099515324032470925887 116094149272986048706388831)
    ·
      refine ⟨174141223909479073059583247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116094149272986048706388831 174141223909479073059583247)
      ·
        refine ⟨261211835864218609589374871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174141223909479073059583247 261211835864218609589374871)
        ·
          refine ⟨391817753796327914384062307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 261211835864218609589374871 391817753796327914384062307)
          ·
            refine ⟨587726630694491871576093461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 391817753796327914384062307 587726630694491871576093461)
            ·
              refine ⟨27549685813804306480129381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 587726630694491871576093461 27549685813804306480129381)
              ·
                refine ⟨5165566090088307465024259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27549685813804306480129381 5165566090088307465024259)
                ·
                  refine ⟨7748349135132461197536389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5165566090088307465024259 7748349135132461197536389)
                  ·
                    refine ⟨1452815462837336474538073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7748349135132461197536389 1452815462837336474538073)
                    ·
                      refine ⟨1089611597128002355903555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1452815462837336474538073 1089611597128002355903555)
                      ·
                        rfl

theorem cell23_2122011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 4, 1, 4, 2].length) (baseStart_2122011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2122011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2122011 prefixEnd_2122011 := by exact prefixLift 2122011
  have htrace : WordTrace (prefixWord ++ tailWord_2122011) baseStart_2122011 baseEnd_2122011 := by
    simpa [prefixWord, tailWord_2122011, baseEnd_2122011] using wordTrace_append hprefix tailTrace_2122011
  have hstable : (prefixWord ++ tailWord_2122011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2122011).length < 2 ^ (prefixWord ++ tailWord_2122011).sum := by decide
  have hdescent : baseEnd_2122011 < baseStart_2122011 := by decide
  rcases family_descends (prefixWord ++ tailWord_2122011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2122023 : List Nat := [1, 1, 8, 1, 1, 1, 3, 2, 1, 2, 2]
def baseStart_2122023 : Nat := 118140960795 + 2122023 * 2 ^ 59
def prefixEnd_2122023 : Nat := 4983230072969 + 3 ^ 40 * 2122023 * 2
def baseEnd_2122023 : Nat := 1089617758895856308953501

theorem tailTrace_2122023 : CollatzResearch.WordTrace tailWord_2122023 prefixEnd_2122023 1089617758895856308953501 := by
  unfold tailWord_2122023
  simp only [CollatzResearch.WordTrace]
  refine ⟨77396537191280558520362723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51597691460853705680241815 77396537191280558520362723)
  ·
    refine ⟨116094805786920837780544085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77396537191280558520362723 116094805786920837780544085)
    ·
      refine ⟨1360486005315478567740751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 116094805786920837780544085 1360486005315478567740751)
      ·
        refine ⟨2040729007973217851611127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1360486005315478567740751 2040729007973217851611127)
        ·
          refine ⟨3061093511959826777416691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2040729007973217851611127 3061093511959826777416691)
          ·
            refine ⟨4591640267939740166125037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3061093511959826777416691 4591640267939740166125037)
            ·
              refine ⟨1721865100477402562296889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4591640267939740166125037 1721865100477402562296889)
              ·
                refine ⟨1291398825358051921722667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1721865100477402562296889 1291398825358051921722667)
                ·
                  refine ⟨1937098238037077882584001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1291398825358051921722667 1937098238037077882584001)
                  ·
                    refine ⟨1452823678527808411938001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1937098238037077882584001 1452823678527808411938001)
                    ·
                      refine ⟨1089617758895856308953501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1452823678527808411938001 1089617758895856308953501)
                      ·
                        rfl

theorem cell23_2122023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_2122023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2122023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2122023 prefixEnd_2122023 := by exact prefixLift 2122023
  have htrace : WordTrace (prefixWord ++ tailWord_2122023) baseStart_2122023 baseEnd_2122023 := by
    simpa [prefixWord, tailWord_2122023, baseEnd_2122023] using wordTrace_append hprefix tailTrace_2122023
  have hstable : (prefixWord ++ tailWord_2122023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2122023).length < 2 ^ (prefixWord ++ tailWord_2122023).sum := by decide
  have hdescent : baseEnd_2122023 < baseStart_2122023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2122023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2122028 : List Nat := [2, 2, 1, 1, 1, 3, 4, 1, 4, 2, 2]
def baseStart_2122028 : Nat := 118140960795 + 2122028 * 2 ^ 59
def prefixEnd_2122028 : Nat := 4983230072969 + 3 ^ 40 * 2122028 * 2
def baseEnd_2122028 : Nat := 1089620326299128789390977

theorem tailTrace_2122028 : CollatzResearch.WordTrace tailWord_2122028 prefixEnd_2122028 1089620326299128789390977 := by
  unfold tailWord_2122028
  simp only [CollatzResearch.WordTrace]
  refine ⟨38698359778131222187147369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51597813037508296249529825 38698359778131222187147369)
  ·
    refine ⟨29023769833598416640360527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38698359778131222187147369 29023769833598416640360527)
    ·
      refine ⟨43535654750397624960540791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29023769833598416640360527 43535654750397624960540791)
      ·
        refine ⟨65303482125596437440811187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43535654750397624960540791 65303482125596437440811187)
        ·
          refine ⟨97955223188394656161216781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65303482125596437440811187 97955223188394656161216781)
          ·
            refine ⟨36733208695647996060456293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97955223188394656161216781 36733208695647996060456293)
            ·
              refine ⟨6887476630433999261335555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36733208695647996060456293 6887476630433999261335555)
              ·
                refine ⟨10331214945650998892003333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6887476630433999261335555 10331214945650998892003333)
                ·
                  refine ⟨1937102802309562292250625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10331214945650998892003333 1937102802309562292250625)
                  ·
                    refine ⟨1452827101732171719187969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1937102802309562292250625 1452827101732171719187969)
                    ·
                      refine ⟨1089620326299128789390977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1452827101732171719187969 1089620326299128789390977)
                      ·
                        rfl

theorem cell23_2122028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 2, 2].length) (baseStart_2122028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2122028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2122028 prefixEnd_2122028 := by exact prefixLift 2122028
  have htrace : WordTrace (prefixWord ++ tailWord_2122028) baseStart_2122028 baseEnd_2122028 := by
    simpa [prefixWord, tailWord_2122028, baseEnd_2122028] using wordTrace_append hprefix tailTrace_2122028
  have hstable : (prefixWord ++ tailWord_2122028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2122028).length < 2 ^ (prefixWord ++ tailWord_2122028).sum := by decide
  have hdescent : baseEnd_2122028 < baseStart_2122028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2122028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2122049 : List Nat := [1, 2, 5, 2, 3, 1, 1, 2, 1, 3, 2]
def baseStart_2122049 : Nat := 118140960795 + 2122049 * 2 ^ 59
def prefixEnd_2122049 : Nat := 4983230072969 + 3 ^ 40 * 2122049 * 2
def baseEnd_2122049 : Nat := 1089631109392873207228381

theorem tailTrace_2122049 : CollatzResearch.WordTrace tailWord_2122049 prefixEnd_2122049 1089631109392873207228381 := by
  unfold tailWord_2122049
  simp only [CollatzResearch.WordTrace]
  refine ⟨77397485489186364960809201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51598323659457576640539467 77397485489186364960809201)
  ·
    refine ⟨58048114116889773720606901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77397485489186364960809201 58048114116889773720606901)
    ·
      refine ⟨5442010698458416286306897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 58048114116889773720606901 5442010698458416286306897)
      ·
        refine ⟨4081508023843812214730173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5442010698458416286306897 4081508023843812214730173)
        ·
          refine ⟨1530565508941429580523815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4081508023843812214730173 1530565508941429580523815)
          ·
            refine ⟨2295848263412144370785723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1530565508941429580523815 2295848263412144370785723)
            ·
              refine ⟨3443772395118216556178585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2295848263412144370785723 3443772395118216556178585)
              ·
                refine ⟨2582829296338662417133939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3443772395118216556178585 2582829296338662417133939)
                ·
                  refine ⟨3874243944507993625700909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2582829296338662417133939 3874243944507993625700909)
                  ·
                    refine ⟨1452841479190497609637841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3874243944507993625700909 1452841479190497609637841)
                    ·
                      refine ⟨1089631109392873207228381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1452841479190497609637841 1089631109392873207228381)
                      ·
                        rfl

theorem cell23_2122049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_2122049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2122049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2122049 prefixEnd_2122049 := by exact prefixLift 2122049
  have htrace : WordTrace (prefixWord ++ tailWord_2122049) baseStart_2122049 baseEnd_2122049 := by
    simpa [prefixWord, tailWord_2122049, baseEnd_2122049] using wordTrace_append hprefix tailTrace_2122049
  have hstable : (prefixWord ++ tailWord_2122049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2122049).length < 2 ^ (prefixWord ++ tailWord_2122049).sum := by decide
  have hdescent : baseEnd_2122049 < baseStart_2122049 := by decide
  rcases family_descends (prefixWord ++ tailWord_2122049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2122085 : List Nat := [1, 3, 1, 3, 1, 5, 2, 2, 5]
def baseStart_2122085 : Nat := 118140960795 + 2122085 * 2 ^ 59
def prefixEnd_2122085 : Nat := 4983230072969 + 3 ^ 40 * 2122085 * 2
def baseEnd_2122085 : Nat := 121072177188492785153135

theorem tailTrace_2122085 : CollatzResearch.WordTrace tailWord_2122085 prefixEnd_2122085 121072177188492785153135 := by
  unfold tailWord_2122085
  simp only [CollatzResearch.WordTrace]
  refine ⟨77398798517055943109119709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51599199011370628739413139 77398798517055943109119709)
  ·
    refine ⟨29024549443895978665919891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77398798517055943109119709 29024549443895978665919891)
    ·
      refine ⟨43536824165843967998879837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29024549443895978665919891 43536824165843967998879837)
      ·
        refine ⟨16326309062191487999579939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43536824165843967998879837 16326309062191487999579939)
        ·
          refine ⟨24489463593287231999369909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16326309062191487999579939 24489463593287231999369909)
          ·
            refine ⟨2295887211870677999940929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24489463593287231999369909 2295887211870677999940929)
            ·
              refine ⟨1721915408903008499955697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2295887211870677999940929 1721915408903008499955697)
              ·
                refine ⟨1291436556677256374966773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1721915408903008499955697 1291436556677256374966773)
                ·
                  refine ⟨121072177188492785153135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1291436556677256374966773 121072177188492785153135)
                  ·
                    rfl

theorem cell23_2122085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 2, 2, 5].length) (baseStart_2122085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2122085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2122085 prefixEnd_2122085 := by exact prefixLift 2122085
  have htrace : WordTrace (prefixWord ++ tailWord_2122085) baseStart_2122085 baseEnd_2122085 := by
    simpa [prefixWord, tailWord_2122085, baseEnd_2122085] using wordTrace_append hprefix tailTrace_2122085
  have hstable : (prefixWord ++ tailWord_2122085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2122085).length < 2 ^ (prefixWord ++ tailWord_2122085).sum := by decide
  have hdescent : baseEnd_2122085 < baseStart_2122085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2122085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2122088 : List Nat := [2, 1, 4, 2, 2, 1, 1, 1, 2, 5, 2]
def baseStart_2122088 : Nat := 118140960795 + 2122088 * 2 ^ 59
def prefixEnd_2122088 : Nat := 4983230072969 + 3 ^ 40 * 2122088 * 2
def baseEnd_2122088 : Nat := 1089651135138398554640701

theorem tailTrace_2122088 : CollatzResearch.WordTrace tailWord_2122088 prefixEnd_2122088 1089651135138398554640701 := by
  unfold tailWord_2122088
  simp only [CollatzResearch.WordTrace]
  refine ⟨38699453968022537310739459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51599271957363383080985945 38699453968022537310739459)
  ·
    refine ⟨58049180952033805966109189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38699453968022537310739459 58049180952033805966109189)
    ·
      refine ⟨10884221428506338618645473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58049180952033805966109189 10884221428506338618645473)
      ·
        refine ⟨8163166071379753963984105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10884221428506338618645473 8163166071379753963984105)
        ·
          refine ⟨6122374553534815472988079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8163166071379753963984105 6122374553534815472988079)
          ·
            refine ⟨9183561830302223209482119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6122374553534815472988079 9183561830302223209482119)
            ·
              refine ⟨13775342745453334814223179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9183561830302223209482119 13775342745453334814223179)
              ·
                refine ⟨20663014118180002221334769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13775342745453334814223179 20663014118180002221334769)
                ·
                  refine ⟨15497260588635001666001077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20663014118180002221334769 15497260588635001666001077)
                  ·
                    refine ⟨1452868180184531406187601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15497260588635001666001077 1452868180184531406187601)
                    ·
                      refine ⟨1089651135138398554640701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1452868180184531406187601 1089651135138398554640701)
                      ·
                        rfl

theorem cell23_2122088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 2, 5, 2].length) (baseStart_2122088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2122088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2122088 prefixEnd_2122088 := by exact prefixLift 2122088
  have htrace : WordTrace (prefixWord ++ tailWord_2122088) baseStart_2122088 baseEnd_2122088 := by
    simpa [prefixWord, tailWord_2122088, baseEnd_2122088] using wordTrace_append hprefix tailTrace_2122088
  have hstable : (prefixWord ++ tailWord_2122088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2122088).length < 2 ^ (prefixWord ++ tailWord_2122088).sum := by decide
  have hdescent : baseEnd_2122088 < baseStart_2122088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2122088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2122111 : List Nat := [1, 1, 2, 2, 1, 1, 2, 6, 3, 4]
def baseStart_2122111 : Nat := 118140960795 + 2122111 * 2 ^ 59
def prefixEnd_2122111 : Nat := 4983230072969 + 3 ^ 40 * 2122111 * 2
def baseEnd_2122111 : Nat := 363220981731150654884365

theorem tailTrace_2122111 : CollatzResearch.WordTrace tailWord_2122111 prefixEnd_2122111 363220981731150654884365 := by
  unfold tailWord_2122111
  simp only [CollatzResearch.WordTrace]
  refine ⟨77399746814961749549566187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51599831209974499699710791 77399746814961749549566187)
  ·
    refine ⟨116099620222442624324349281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77399746814961749549566187 116099620222442624324349281)
    ·
      refine ⟨87074715166831968243261961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116099620222442624324349281 87074715166831968243261961)
      ·
        refine ⟨65306036375123976182446471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87074715166831968243261961 65306036375123976182446471)
        ·
          refine ⟨97959054562685964273669707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65306036375123976182446471 97959054562685964273669707)
          ·
            refine ⟨146938581844028946410504561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97959054562685964273669707 146938581844028946410504561)
            ·
              refine ⟨110203936383021709807878421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 146938581844028946410504561 110203936383021709807878421)
              ·
                refine ⟨5165809517954142647244301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 110203936383021709807878421 5165809517954142647244301)
                ·
                  refine ⟨1937178569232803492716613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5165809517954142647244301 1937178569232803492716613)
                  ·
                    refine ⟨363220981731150654884365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1937178569232803492716613 363220981731150654884365)
                    ·
                      rfl

theorem cell23_2122111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 6, 3, 4].length) (baseStart_2122111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2122111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2122111 prefixEnd_2122111 := by exact prefixLift 2122111
  have htrace : WordTrace (prefixWord ++ tailWord_2122111) baseStart_2122111 baseEnd_2122111 := by
    simpa [prefixWord, tailWord_2122111, baseEnd_2122111] using wordTrace_append hprefix tailTrace_2122111
  have hstable : (prefixWord ++ tailWord_2122111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2122111).length < 2 ^ (prefixWord ++ tailWord_2122111).sum := by decide
  have hdescent : baseEnd_2122111 < baseStart_2122111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2122111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2122115 : List Nat := [1, 1, 1, 3, 7, 1, 1, 1, 2, 5]
def baseStart_2122115 : Nat := 118140960795 + 2122115 * 2 ^ 59
def prefixEnd_2122115 : Nat := 4983230072969 + 3 ^ 40 * 2122115 * 2
def baseEnd_2122115 : Nat := 363221666372023316334359

theorem tailTrace_2122115 : CollatzResearch.WordTrace tailWord_2122115 prefixEnd_2122115 363221666372023316334359 := by
  unfold tailWord_2122115
  simp only [CollatzResearch.WordTrace]
  refine ⟨77399892706947258232711799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51599928471298172155141199 77399892706947258232711799)
  ·
    refine ⟨116099839060420887349067699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77399892706947258232711799 116099839060420887349067699)
    ·
      refine ⟨174149758590631331023601549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116099839060420887349067699 174149758590631331023601549)
      ·
        refine ⟨65306159471486749133850581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 174149758590631331023601549 65306159471486749133850581)
        ·
          refine ⟨1530613112612970682824623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 65306159471486749133850581 1530613112612970682824623)
          ·
            refine ⟨2295919668919456024236935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1530613112612970682824623 2295919668919456024236935)
            ·
              refine ⟨3443879503379184036355403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2295919668919456024236935 3443879503379184036355403)
              ·
                refine ⟨5165819255068776054533105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3443879503379184036355403 5165819255068776054533105)
                ·
                  refine ⟨3874364441301582040899829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5165819255068776054533105 3874364441301582040899829)
                  ·
                    refine ⟨363221666372023316334359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3874364441301582040899829 363221666372023316334359)
                    ·
                      rfl

theorem cell23_2122115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 1, 2, 5].length) (baseStart_2122115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2122115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2122115 prefixEnd_2122115 := by exact prefixLift 2122115
  have htrace : WordTrace (prefixWord ++ tailWord_2122115) baseStart_2122115 baseEnd_2122115 := by
    simpa [prefixWord, tailWord_2122115, baseEnd_2122115] using wordTrace_append hprefix tailTrace_2122115
  have hstable : (prefixWord ++ tailWord_2122115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2122115).length < 2 ^ (prefixWord ++ tailWord_2122115).sum := by decide
  have hdescent : baseEnd_2122115 < baseStart_2122115 := by decide
  rcases family_descends (prefixWord ++ tailWord_2122115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2122191 : List Nat := [1, 1, 2, 1, 1, 4, 1, 2, 5, 1, 4]
def baseStart_2122191 : Nat := 118140960795 + 2122191 * 2 ^ 59
def prefixEnd_2122191 : Nat := 4983230072969 + 3 ^ 40 * 2122191 * 2
def baseEnd_2122191 : Nat := 1089704023645811651652727

theorem tailTrace_2122191 : CollatzResearch.WordTrace tailWord_2122191 prefixEnd_2122191 1089704023645811651652727 := by
  unfold tailWord_2122191
  simp only [CollatzResearch.WordTrace]
  refine ⟨77402664654671923212478427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51601776436447948808318951 77402664654671923212478427)
  ·
    refine ⟨116103996982007884818717641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77402664654671923212478427 116103996982007884818717641)
    ·
      refine ⟨87077997736505913614038231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116103996982007884818717641 87077997736505913614038231)
      ·
        refine ⟨130616996604758870421057347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87077997736505913614038231 130616996604758870421057347)
        ·
          refine ⟨195925494907138305631586021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130616996604758870421057347 195925494907138305631586021)
          ·
            refine ⟨36736030295088432305922379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 195925494907138305631586021 36736030295088432305922379)
            ·
              refine ⟨55104045442632648458883569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36736030295088432305922379 55104045442632648458883569)
              ·
                refine ⟨41328034081974486344162677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55104045442632648458883569 41328034081974486344162677)
                ·
                  refine ⟨3874503195185108094765251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41328034081974486344162677 3874503195185108094765251)
                  ·
                    refine ⟨5811754792777662142147877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3874503195185108094765251 5811754792777662142147877)
                    ·
                      refine ⟨1089704023645811651652727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5811754792777662142147877 1089704023645811651652727)
                      ·
                        rfl

theorem cell23_2122191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 5, 1, 4].length) (baseStart_2122191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2122191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2122191 prefixEnd_2122191 := by exact prefixLift 2122191
  have htrace : WordTrace (prefixWord ++ tailWord_2122191) baseStart_2122191 baseEnd_2122191 := by
    simpa [prefixWord, tailWord_2122191, baseEnd_2122191] using wordTrace_append hprefix tailTrace_2122191
  have hstable : (prefixWord ++ tailWord_2122191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2122191).length < 2 ^ (prefixWord ++ tailWord_2122191).sum := by decide
  have hdescent : baseEnd_2122191 < baseStart_2122191 := by decide
  rcases family_descends (prefixWord ++ tailWord_2122191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2122225 : List Nat := [1, 2, 2, 2, 3, 1, 2, 1, 5, 2, 2]
def baseStart_2122225 : Nat := 118140960795 + 2122225 * 2 ^ 59
def prefixEnd_2122225 : Nat := 4983230072969 + 3 ^ 40 * 2122225 * 2
def baseEnd_2122225 : Nat := 1089721481988064518627571

theorem tailTrace_2122225 : CollatzResearch.WordTrace tailWord_2122225 prefixEnd_2122225 1089721481988064518627571 := by
  unfold tailWord_2122225
  simp only [CollatzResearch.WordTrace]
  refine ⟨77403904736548747019216129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51602603157699164679477419 77403904736548747019216129)
  ·
    refine ⟨58052928552411560264412097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77403904736548747019216129 58052928552411560264412097)
    ·
      refine ⟨43539696414308670198309073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58052928552411560264412097 43539696414308670198309073)
      ·
        refine ⟨32654772310731502648731805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43539696414308670198309073 32654772310731502648731805)
        ·
          refine ⟨12245539616524313493274427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32654772310731502648731805 12245539616524313493274427)
          ·
            refine ⟨18368309424786470239911641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12245539616524313493274427 18368309424786470239911641)
            ·
              refine ⟨13776232068589852679933731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18368309424786470239911641 13776232068589852679933731)
              ·
                refine ⟨20664348102884779019900597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13776232068589852679933731 20664348102884779019900597)
                ·
                  refine ⟨1937282634645448033115681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20664348102884779019900597 1937282634645448033115681)
                  ·
                    refine ⟨1452961975984086024836761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1937282634645448033115681 1452961975984086024836761)
                    ·
                      refine ⟨1089721481988064518627571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1452961975984086024836761 1089721481988064518627571)
                      ·
                        rfl

theorem cell23_2122225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 5, 2, 2].length) (baseStart_2122225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2122225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2122225 prefixEnd_2122225 := by exact prefixLift 2122225
  have htrace : WordTrace (prefixWord ++ tailWord_2122225) baseStart_2122225 baseEnd_2122225 := by
    simpa [prefixWord, tailWord_2122225, baseEnd_2122225] using wordTrace_append hprefix tailTrace_2122225
  have hstable : (prefixWord ++ tailWord_2122225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2122225).length < 2 ^ (prefixWord ++ tailWord_2122225).sum := by decide
  have hdescent : baseEnd_2122225 < baseStart_2122225 := by decide
  rcases family_descends (prefixWord ++ tailWord_2122225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2122229 : List Nat := [1, 3, 5, 1, 2, 1, 2, 1, 2, 3, 2]
def baseStart_2122229 : Nat := 118140960795 + 2122229 * 2 ^ 59
def prefixEnd_2122229 : Nat := 4983230072969 + 3 ^ 40 * 2122229 * 2
def baseEnd_2122229 : Nat := 1089723535910682502977553

theorem tailTrace_2122229 : CollatzResearch.WordTrace tailWord_2122229 prefixEnd_2122229 1089723535910682502977553 := by
  unfold tailWord_2122229
  simp only [CollatzResearch.WordTrace]
  refine ⟨77404050628534255702361741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51602700419022837134907827 77404050628534255702361741)
  ·
    refine ⟨29026518985700345888385653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77404050628534255702361741 29026518985700345888385653)
    ·
      refine ⟨2721236154909407427036155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29026518985700345888385653 2721236154909407427036155)
      ·
        refine ⟨4081854232364111140554233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2721236154909407427036155 4081854232364111140554233)
        ·
          refine ⟨3061390674273083355415675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4081854232364111140554233 3061390674273083355415675)
          ·
            refine ⟨4592086011409625033123513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3061390674273083355415675 4592086011409625033123513)
            ·
              refine ⟨3444064508557218774842635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4592086011409625033123513 3444064508557218774842635)
              ·
                refine ⟨5166096762835828162263953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3444064508557218774842635 5166096762835828162263953)
                ·
                  refine ⟨3874572572126871121697965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5166096762835828162263953 3874572572126871121697965)
                  ·
                    refine ⟨1452964714547576670636737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3874572572126871121697965 1452964714547576670636737)
                    ·
                      refine ⟨1089723535910682502977553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1452964714547576670636737 1089723535910682502977553)
                      ·
                        rfl

theorem cell23_2122229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_2122229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2122229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2122229 prefixEnd_2122229 := by exact prefixLift 2122229
  have htrace : WordTrace (prefixWord ++ tailWord_2122229) baseStart_2122229 baseEnd_2122229 := by
    simpa [prefixWord, tailWord_2122229, baseEnd_2122229] using wordTrace_append hprefix tailTrace_2122229
  have hstable : (prefixWord ++ tailWord_2122229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2122229).length < 2 ^ (prefixWord ++ tailWord_2122229).sum := by decide
  have hdescent : baseEnd_2122229 < baseStart_2122229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2122229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2122246 : List Nat := [6, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2]
def baseStart_2122246 : Nat := 118140960795 + 2122246 * 2 ^ 59
def prefixEnd_2122246 : Nat := 4983230072969 + 3 ^ 40 * 2122246 * 2
def baseEnd_2122246 : Nat := 1089732265081808936464975

theorem tailTrace_2122246 : CollatzResearch.WordTrace tailWord_2122246 prefixEnd_2122246 1089732265081808936464975 := by
  unfold tailWord_2122246
  simp only [CollatzResearch.WordTrace]
  refine ⟨2418895958421020862679081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 51603113779648445070487061 2418895958421020862679081)
  ·
    refine ⟨1814171968815765647009311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2418895958421020862679081 1814171968815765647009311)
    ·
      refine ⟨2721257953223648470513967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1814171968815765647009311 2721257953223648470513967)
      ·
        refine ⟨4081886929835472705770951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2721257953223648470513967 4081886929835472705770951)
        ·
          refine ⟨6122830394753209058656427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4081886929835472705770951 6122830394753209058656427)
          ·
            refine ⟨9184245592129813587984641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6122830394753209058656427 9184245592129813587984641)
            ·
              refine ⟨6888184194097360190988481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9184245592129813587984641 6888184194097360190988481)
              ·
                refine ⟨5166138145573020143241361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6888184194097360190988481 5166138145573020143241361)
                ·
                  refine ⟨3874603609179765107431021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5166138145573020143241361 3874603609179765107431021)
                  ·
                    refine ⟨1452976353442411915286633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3874603609179765107431021 1452976353442411915286633)
                    ·
                      refine ⟨1089732265081808936464975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1452976353442411915286633 1089732265081808936464975)
                      ·
                        rfl

theorem cell23_2122246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_2122246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2122246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2122246 prefixEnd_2122246 := by exact prefixLift 2122246
  have htrace : WordTrace (prefixWord ++ tailWord_2122246) baseStart_2122246 baseEnd_2122246 := by
    simpa [prefixWord, tailWord_2122246, baseEnd_2122246] using wordTrace_append hprefix tailTrace_2122246
  have hstable : (prefixWord ++ tailWord_2122246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2122246).length < 2 ^ (prefixWord ++ tailWord_2122246).sum := by decide
  have hdescent : baseEnd_2122246 < baseStart_2122246 := by decide
  rcases family_descends (prefixWord ++ tailWord_2122246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2122253 : List Nat := [1, 7, 1, 1, 1, 1, 4, 2, 1, 1, 3]
def baseStart_2122253 : Nat := 118140960795 + 2122253 * 2 ^ 59
def prefixEnd_2122253 : Nat := 4983230072969 + 3 ^ 40 * 2122253 * 2
def baseEnd_2122253 : Nat := 1089735859446390409077443

theorem tailTrace_2122253 : CollatzResearch.WordTrace tailWord_2122253 prefixEnd_2122253 1089735859446390409077443 := by
  unfold tailWord_2122253
  simp only [CollatzResearch.WordTrace]
  refine ⟨77404925980447307801235413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51603283986964871867490275 77404925980447307801235413)
  ·
    refine ⟨1814177952666733776591455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 77404925980447307801235413 1814177952666733776591455)
    ·
      refine ⟨2721266929000100664887183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1814177952666733776591455 2721266929000100664887183)
      ·
        refine ⟨4081900393500150997330775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2721266929000100664887183 4081900393500150997330775)
        ·
          refine ⟨6122850590250226495996163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4081900393500150997330775 6122850590250226495996163)
          ·
            refine ⟨9184275885375339743994245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6122850590250226495996163 9184275885375339743994245)
            ·
              refine ⟨1722051728507876201998921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9184275885375339743994245 1722051728507876201998921)
              ·
                refine ⟨1291538796380907151499191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1722051728507876201998921 1291538796380907151499191)
                ·
                  refine ⟨1937308194571360727248787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1291538796380907151499191 1937308194571360727248787)
                  ·
                    refine ⟨2905962291857041090873181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1937308194571360727248787 2905962291857041090873181)
                    ·
                      refine ⟨1089735859446390409077443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2905962291857041090873181 1089735859446390409077443)
                      ·
                        rfl

theorem cell23_2122253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_2122253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2122253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2122253 prefixEnd_2122253 := by exact prefixLift 2122253
  have htrace : WordTrace (prefixWord ++ tailWord_2122253) baseStart_2122253 baseEnd_2122253 := by
    simpa [prefixWord, tailWord_2122253, baseEnd_2122253] using wordTrace_append hprefix tailTrace_2122253
  have hstable : (prefixWord ++ tailWord_2122253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2122253).length < 2 ^ (prefixWord ++ tailWord_2122253).sum := by decide
  have hdescent : baseEnd_2122253 < baseStart_2122253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2122253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2122261 : List Nat := [1, 3, 2, 1, 3, 1, 1, 1, 1, 9]
def baseStart_2122261 : Nat := 118140960795 + 2122261 * 2 ^ 59
def prefixEnd_2122261 : Nat := 4983230072969 + 3 ^ 40 * 2122261 * 2
def baseEnd_2122261 : Nat := 363246655763875459259135

theorem tailTrace_2122261 : CollatzResearch.WordTrace tailWord_2122261 prefixEnd_2122261 363246655763875459259135 := by
  unfold tailWord_2122261
  simp only [CollatzResearch.WordTrace]
  refine ⟨77405217764418325167526637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51603478509612216778351091 77405217764418325167526637)
  ·
    refine ⟨29026956661656871937822489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77405217764418325167526637 29026956661656871937822489)
    ·
      refine ⟨21770217496242653953366867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29026956661656871937822489 21770217496242653953366867)
      ·
        refine ⟨32655326244363980930050301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21770217496242653953366867 32655326244363980930050301)
        ·
          refine ⟨12245747341636492848768863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32655326244363980930050301 12245747341636492848768863)
          ·
            refine ⟨18368621012454739273153295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12245747341636492848768863 18368621012454739273153295)
            ·
              refine ⟨27552931518682108909729943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18368621012454739273153295 27552931518682108909729943)
              ·
                refine ⟨41329397278023163364594915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27552931518682108909729943 41329397278023163364594915)
                ·
                  refine ⟨61994095917034745046892373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41329397278023163364594915 61994095917034745046892373)
                  ·
                    refine ⟨363246655763875459259135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 61994095917034745046892373 363246655763875459259135)
                    ·
                      rfl

theorem cell23_2122261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 9].length) (baseStart_2122261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2122261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2122261 prefixEnd_2122261 := by exact prefixLift 2122261
  have htrace : WordTrace (prefixWord ++ tailWord_2122261) baseStart_2122261 baseEnd_2122261 := by
    simpa [prefixWord, tailWord_2122261, baseEnd_2122261] using wordTrace_append hprefix tailTrace_2122261
  have hstable : (prefixWord ++ tailWord_2122261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2122261).length < 2 ^ (prefixWord ++ tailWord_2122261).sum := by decide
  have hdescent : baseEnd_2122261 < baseStart_2122261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2122261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2122271 : List Nat := [1, 1, 2, 4, 1, 1, 1, 2, 1, 4, 5]
def baseStart_2122271 : Nat := 118140960795 + 2122271 * 2 ^ 59
def prefixEnd_2122271 : Nat := 4983230072969 + 3 ^ 40 * 2122271 * 2
def baseEnd_2122271 : Nat := 1089745102098171338652359

theorem tailTrace_2122271 : CollatzResearch.WordTrace tailWord_2122271 prefixEnd_2122271 1089745102098171338652359 := by
  unfold tailWord_2122271
  simp only [CollatzResearch.WordTrace]
  refine ⟨77405582494382096875390667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51603721662921397916927111 77405582494382096875390667)
  ·
    refine ⟨116108373741573145313086001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77405582494382096875390667 116108373741573145313086001)
    ·
      refine ⟨87081280306179858984814501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116108373741573145313086001 87081280306179858984814501)
      ·
        refine ⟨16327740057408723559652719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 87081280306179858984814501 16327740057408723559652719)
        ·
          refine ⟨24491610086113085339479079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16327740057408723559652719 24491610086113085339479079)
          ·
            refine ⟨36737415129169628009218619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24491610086113085339479079 36737415129169628009218619)
            ·
              refine ⟨55106122693754442013827929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36737415129169628009218619 55106122693754442013827929)
              ·
                refine ⟨41329592020315831510370947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55106122693754442013827929 41329592020315831510370947)
                ·
                  refine ⟨61994388030473747265556421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41329592020315831510370947 61994388030473747265556421)
                  ·
                    refine ⟨11623947755713827612291829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 61994388030473747265556421 11623947755713827612291829)
                    ·
                      refine ⟨1089745102098171338652359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11623947755713827612291829 1089745102098171338652359)
                      ·
                        rfl

theorem cell23_2122271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_2122271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2122271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2122271 prefixEnd_2122271 := by exact prefixLift 2122271
  have htrace : WordTrace (prefixWord ++ tailWord_2122271) baseStart_2122271 baseEnd_2122271 := by
    simpa [prefixWord, tailWord_2122271, baseEnd_2122271] using wordTrace_append hprefix tailTrace_2122271
  have hstable : (prefixWord ++ tailWord_2122271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2122271).length < 2 ^ (prefixWord ++ tailWord_2122271).sum := by decide
  have hdescent : baseEnd_2122271 < baseStart_2122271 := by decide
  rcases family_descends (prefixWord ++ tailWord_2122271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2122275 : List Nat := [1, 1, 1, 4, 4, 2, 2, 1, 1, 3, 3]
def baseStart_2122275 : Nat := 118140960795 + 2122275 * 2 ^ 59
def prefixEnd_2122275 : Nat := 4983230072969 + 3 ^ 40 * 2122275 * 2
def baseEnd_2122275 : Nat := 1089747156020789323002341

theorem tailTrace_2122275 : CollatzResearch.WordTrace tailWord_2122275 prefixEnd_2122275 1089747156020789323002341 := by
  unfold tailWord_2122275
  simp only [CollatzResearch.WordTrace]
  refine ⟨77405728386367605558536279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51603818924245070372357519 77405728386367605558536279)
  ·
    refine ⟨116108592579551408337804419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77405728386367605558536279 116108592579551408337804419)
    ·
      refine ⟨174162888869327112506706629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116108592579551408337804419 174162888869327112506706629)
      ·
        refine ⟨32655541662998833595007493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 174162888869327112506706629 32655541662998833595007493)
        ·
          refine ⟨6122914061812281299063905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32655541662998833595007493 6122914061812281299063905)
          ·
            refine ⟨4592185546359210974297929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6122914061812281299063905 4592185546359210974297929)
            ·
              refine ⟨3444139159769408230723447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4592185546359210974297929 3444139159769408230723447)
              ·
                refine ⟨5166208739654112346085171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3444139159769408230723447 5166208739654112346085171)
                ·
                  refine ⟨7749313109481168519127757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5166208739654112346085171 7749313109481168519127757)
                  ·
                    refine ⟨2905992416055438194672909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7749313109481168519127757 2905992416055438194672909)
                    ·
                      refine ⟨1089747156020789323002341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2905992416055438194672909 1089747156020789323002341)
                      ·
                        rfl

theorem cell23_2122275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 1, 1, 3, 3].length) (baseStart_2122275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2122275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2122275 prefixEnd_2122275 := by exact prefixLift 2122275
  have htrace : WordTrace (prefixWord ++ tailWord_2122275) baseStart_2122275 baseEnd_2122275 := by
    simpa [prefixWord, tailWord_2122275, baseEnd_2122275] using wordTrace_append hprefix tailTrace_2122275
  have hstable : (prefixWord ++ tailWord_2122275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2122275).length < 2 ^ (prefixWord ++ tailWord_2122275).sum := by decide
  have hdescent : baseEnd_2122275 < baseStart_2122275 := by decide
  rcases family_descends (prefixWord ++ tailWord_2122275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2122291 : List Nat := [1, 1, 1, 2, 4, 2, 1, 2, 1, 8]
def baseStart_2122291 : Nat := 118140960795 + 2122291 * 2 ^ 59
def prefixEnd_2122291 : Nat := 4983230072969 + 3 ^ 40 * 2122291 * 2
def baseEnd_2122291 : Nat := 363251790570420420134089

theorem tailTrace_2122291 : CollatzResearch.WordTrace tailWord_2122291 prefixEnd_2122291 363251790570420420134089 := by
  unfold tailWord_2122291
  simp only [CollatzResearch.WordTrace]
  refine ⟨77406311954309640291118727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51604207969539760194079151 77406311954309640291118727)
  ·
    refine ⟨116109467931464460436678091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77406311954309640291118727 116109467931464460436678091)
    ·
      refine ⟨174164201897196690655017137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116109467931464460436678091 174164201897196690655017137)
      ·
        refine ⟨130623151422897517991262853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174164201897196690655017137 130623151422897517991262853)
        ·
          refine ⟨24491840891793284623361785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 130623151422897517991262853 24491840891793284623361785)
          ·
            refine ⟨18368880668844963467521339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24491840891793284623361785 18368880668844963467521339)
            ·
              refine ⟨27553321003267445201282009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18368880668844963467521339 27553321003267445201282009)
              ·
                refine ⟨20664990752450583900961507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27553321003267445201282009 20664990752450583900961507)
                ·
                  refine ⟨30997486128675875851442261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20664990752450583900961507 30997486128675875851442261)
                  ·
                    refine ⟨363251790570420420134089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 30997486128675875851442261 363251790570420420134089)
                    ·
                      rfl

theorem cell23_2122291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 8].length) (baseStart_2122291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2122291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2122291 prefixEnd_2122291 := by exact prefixLift 2122291
  have htrace : WordTrace (prefixWord ++ tailWord_2122291) baseStart_2122291 baseEnd_2122291 := by
    simpa [prefixWord, tailWord_2122291, baseEnd_2122291] using wordTrace_append hprefix tailTrace_2122291
  have hstable : (prefixWord ++ tailWord_2122291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2122291).length < 2 ^ (prefixWord ++ tailWord_2122291).sum := by decide
  have hdescent : baseEnd_2122291 < baseStart_2122291 := by decide
  rcases family_descends (prefixWord ++ tailWord_2122291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2122318 : List Nat := [4, 1, 1, 1, 1, 2, 2, 1, 1, 6, 3]
def baseStart_2122318 : Nat := 118140960795 + 2122318 * 2 ^ 59
def prefixEnd_2122318 : Nat := 4983230072969 + 3 ^ 40 * 2122318 * 2
def baseEnd_2122318 : Nat := 1089769235688932654764643

theorem tailTrace_2122318 : CollatzResearch.WordTrace tailWord_2122318 prefixEnd_2122318 1089769235688932654764643 := by
  unfold tailWord_2122318
  simp only [CollatzResearch.WordTrace]
  refine ⟨9675912090651477987793951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51604864483474549268234405 9675912090651477987793951)
  ·
    refine ⟨14513868135977216981690927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9675912090651477987793951 14513868135977216981690927)
    ·
      refine ⟨21770802203965825472536391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14513868135977216981690927 21770802203965825472536391)
      ·
        refine ⟨32656203305948738208804587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21770802203965825472536391 32656203305948738208804587)
        ·
          refine ⟨48984304958923107313206881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32656203305948738208804587 48984304958923107313206881)
          ·
            refine ⟨36738228719192330484905161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48984304958923107313206881 36738228719192330484905161)
            ·
              refine ⟨27553671539394247863678871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36738228719192330484905161 27553671539394247863678871)
              ·
                refine ⟨41330507309091371795518307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27553671539394247863678871 41330507309091371795518307)
                ·
                  refine ⟨61995760963637057693277461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41330507309091371795518307 61995760963637057693277461)
                  ·
                    refine ⟨2906051295170487079372381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 61995760963637057693277461 2906051295170487079372381)
                    ·
                      refine ⟨1089769235688932654764643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2906051295170487079372381 1089769235688932654764643)
                      ·
                        rfl

theorem cell23_2122318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 1, 6, 3].length) (baseStart_2122318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2122318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2122318 prefixEnd_2122318 := by exact prefixLift 2122318
  have htrace : WordTrace (prefixWord ++ tailWord_2122318) baseStart_2122318 baseEnd_2122318 := by
    simpa [prefixWord, tailWord_2122318, baseEnd_2122318] using wordTrace_append hprefix tailTrace_2122318
  have hstable : (prefixWord ++ tailWord_2122318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2122318).length < 2 ^ (prefixWord ++ tailWord_2122318).sum := by decide
  have hdescent : baseEnd_2122318 < baseStart_2122318 := by decide
  rcases family_descends (prefixWord ++ tailWord_2122318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2122328 : List Nat := [2, 1, 2, 2, 1, 2, 4, 1, 2, 2, 4]
def baseStart_2122328 : Nat := 118140960795 + 2122328 * 2 ^ 59
def prefixEnd_2122328 : Nat := 4983230072969 + 3 ^ 40 * 2122328 * 2
def baseEnd_2122328 : Nat := 1089774370495477615639597

theorem tailTrace_2122328 : CollatzResearch.WordTrace tailWord_2122328 prefixEnd_2122328 1089774370495477615639597 := by
  unfold tailWord_2122328
  simp only [CollatzResearch.WordTrace]
  refine ⟨38703830727587797805107819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51605107636783730406810425 38703830727587797805107819)
  ·
    refine ⟨58055746091381696707661729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38703830727587797805107819 58055746091381696707661729)
    ·
      refine ⟨43541809568536272530746297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58055746091381696707661729 43541809568536272530746297)
      ·
        refine ⟨32656357176402204398059723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43541809568536272530746297 32656357176402204398059723)
        ·
          refine ⟨48984535764603306597089585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32656357176402204398059723 48984535764603306597089585)
          ·
            refine ⟨36738401823452479947817189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48984535764603306597089585 36738401823452479947817189)
            ·
              refine ⟨6888450341897339990215723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36738401823452479947817189 6888450341897339990215723)
              ·
                refine ⟨10332675512846009985323585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6888450341897339990215723 10332675512846009985323585)
                ·
                  refine ⟨7749506634634507488992689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10332675512846009985323585 7749506634634507488992689)
                  ·
                    refine ⟨5812129975975880616744517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7749506634634507488992689 5812129975975880616744517)
                    ·
                      refine ⟨1089774370495477615639597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5812129975975880616744517 1089774370495477615639597)
                      ·
                        rfl

theorem cell23_2122328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 1, 2, 2, 4].length) (baseStart_2122328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2122328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2122328 prefixEnd_2122328 := by exact prefixLift 2122328
  have htrace : WordTrace (prefixWord ++ tailWord_2122328) baseStart_2122328 baseEnd_2122328 := by
    simpa [prefixWord, tailWord_2122328, baseEnd_2122328] using wordTrace_append hprefix tailTrace_2122328
  have hstable : (prefixWord ++ tailWord_2122328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2122328).length < 2 ^ (prefixWord ++ tailWord_2122328).sum := by decide
  have hdescent : baseEnd_2122328 < baseStart_2122328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2122328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2122348 : List Nat := [2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 3]
def baseStart_2122348 : Nat := 118140960795 + 2122348 * 2 ^ 59
def prefixEnd_2122348 : Nat := 4983230072969 + 3 ^ 40 * 2122348 * 2
def baseEnd_2122348 : Nat := 1089784640108567537389505

theorem tailTrace_2122348 : CollatzResearch.WordTrace tailWord_2122348 prefixEnd_2122348 1089784640108567537389505 := by
  unfold tailWord_2122348
  simp only [CollatzResearch.WordTrace]
  refine ⟨38704195457551569512971849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51605593943402092683962465 38704195457551569512971849)
  ·
    refine ⟨29028146593163677134728887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38704195457551569512971849 29028146593163677134728887)
    ·
      refine ⟨43542219889745515702093331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29028146593163677134728887 43542219889745515702093331)
      ·
        refine ⟨65313329834618273553139997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43542219889745515702093331 65313329834618273553139997)
        ·
          refine ⟨24492498687981852582427499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65313329834618273553139997 24492498687981852582427499)
          ·
            refine ⟨36738748031972778873641249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24492498687981852582427499 36738748031972778873641249)
            ·
              refine ⟨27554061023979584155230937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36738748031972778873641249 27554061023979584155230937)
              ·
                refine ⟨20665545767984688116423203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27554061023979584155230937 20665545767984688116423203)
                ·
                  refine ⟨30998318651977032174634805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20665545767984688116423203 30998318651977032174634805)
                  ·
                    refine ⟨2906092373622846766372013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30998318651977032174634805 2906092373622846766372013)
                    ·
                      refine ⟨1089784640108567537389505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2906092373622846766372013 1089784640108567537389505)
                      ·
                        rfl

theorem cell23_2122348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 3].length) (baseStart_2122348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2122348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2122348 prefixEnd_2122348 := by exact prefixLift 2122348
  have htrace : WordTrace (prefixWord ++ tailWord_2122348) baseStart_2122348 baseEnd_2122348 := by
    simpa [prefixWord, tailWord_2122348, baseEnd_2122348] using wordTrace_append hprefix tailTrace_2122348
  have hstable : (prefixWord ++ tailWord_2122348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2122348).length < 2 ^ (prefixWord ++ tailWord_2122348).sum := by decide
  have hdescent : baseEnd_2122348 < baseStart_2122348 := by decide
  rcases family_descends (prefixWord ++ tailWord_2122348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2122368 : List Nat := [2, 1, 1, 2, 1, 5, 1, 1, 4, 5]
def baseStart_2122368 : Nat := 118140960795 + 2122368 * 2 ^ 59
def prefixEnd_2122368 : Nat := 4983230072969 + 3 ^ 40 * 2122368 * 2
def baseEnd_2122368 : Nat := 363264969907219153046471

theorem tailTrace_2122368 : CollatzResearch.WordTrace tailWord_2122368 prefixEnd_2122368 363264969907219153046471 := by
  unfold tailWord_2122368
  simp only [CollatzResearch.WordTrace]
  refine ⟨38704560187515341220835879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51606080250020454961114505 38704560187515341220835879)
  ·
    refine ⟨58056840281273011831253819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38704560187515341220835879 58056840281273011831253819)
    ·
      refine ⟨87085260421909517746880729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58056840281273011831253819 87085260421909517746880729)
      ·
        refine ⟨65313945316432138310160547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87085260421909517746880729 65313945316432138310160547)
        ·
          refine ⟨97970917974648207465240821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65313945316432138310160547 97970917974648207465240821)
          ·
            refine ⟨9184773560123269449866327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 97970917974648207465240821 9184773560123269449866327)
            ·
              refine ⟨13777160340184904174799491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9184773560123269449866327 13777160340184904174799491)
              ·
                refine ⟨20665740510277356262199237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13777160340184904174799491 20665740510277356262199237)
                ·
                  refine ⟨3874826345677004299162357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20665740510277356262199237 3874826345677004299162357)
                  ·
                    refine ⟨363264969907219153046471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3874826345677004299162357 363264969907219153046471)
                    ·
                      rfl

theorem cell23_2122368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 4, 5].length) (baseStart_2122368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2122368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2122368 prefixEnd_2122368 := by exact prefixLift 2122368
  have htrace : WordTrace (prefixWord ++ tailWord_2122368) baseStart_2122368 baseEnd_2122368 := by
    simpa [prefixWord, tailWord_2122368, baseEnd_2122368] using wordTrace_append hprefix tailTrace_2122368
  have hstable : (prefixWord ++ tailWord_2122368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2122368).length < 2 ^ (prefixWord ++ tailWord_2122368).sum := by decide
  have hdescent : baseEnd_2122368 < baseStart_2122368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2122368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2122375 : List Nat := [1, 1, 4, 2, 1, 2, 2, 1, 2, 5, 2]
def baseStart_2122375 : Nat := 118140960795 + 2122375 * 2 ^ 59
def prefixEnd_2122375 : Nat := 4983230072969 + 3 ^ 40 * 2122375 * 2
def baseEnd_2122375 : Nat := 1089798504086238931751881

theorem tailTrace_2122375 : CollatzResearch.WordTrace tailWord_2122375 prefixEnd_2122375 1089798504086238931751881 := by
  unfold tailWord_2122375
  simp only [CollatzResearch.WordTrace]
  refine ⟨77409375686005322637176579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51606250457336881758117719 77409375686005322637176579)
  ·
    refine ⟨116114063529007983955764869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77409375686005322637176579 116114063529007983955764869)
    ·
      refine ⟨21771386911688996991705913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 116114063529007983955764869 21771386911688996991705913)
      ·
        refine ⟨16328540183766747743779435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21771386911688996991705913 16328540183766747743779435)
        ·
          refine ⟨24492810275650121615669153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16328540183766747743779435 24492810275650121615669153)
          ·
            refine ⟨18369607706737591211751865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24492810275650121615669153 18369607706737591211751865)
            ·
              refine ⟨13777205780053193408813899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18369607706737591211751865 13777205780053193408813899)
              ·
                refine ⟨20665808670079790113220849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13777205780053193408813899 20665808670079790113220849)
                ·
                  refine ⟨15499356502559842584915637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20665808670079790113220849 15499356502559842584915637)
                  ·
                    refine ⟨1453064672114985242335841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15499356502559842584915637 1453064672114985242335841)
                    ·
                      refine ⟨1089798504086238931751881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1453064672114985242335841 1089798504086238931751881)
                      ·
                        rfl

theorem cell23_2122375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 2, 5, 2].length) (baseStart_2122375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2122375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2122375 prefixEnd_2122375 := by exact prefixLift 2122375
  have htrace : WordTrace (prefixWord ++ tailWord_2122375) baseStart_2122375 baseEnd_2122375 := by
    simpa [prefixWord, tailWord_2122375, baseEnd_2122375] using wordTrace_append hprefix tailTrace_2122375
  have hstable : (prefixWord ++ tailWord_2122375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2122375).length < 2 ^ (prefixWord ++ tailWord_2122375).sum := by decide
  have hdescent : baseEnd_2122375 < baseStart_2122375 := by decide
  rcases family_descends (prefixWord ++ tailWord_2122375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2122405 : List Nat := [1, 3, 1, 2, 1, 2, 1, 2, 4, 4, 2]
def baseStart_2122405 : Nat := 118140960795 + 2122405 * 2 ^ 59
def prefixEnd_2122405 : Nat := 4983230072969 + 3 ^ 40 * 2122405 * 2
def baseEnd_2122405 : Nat := 1089813908505873814376743

theorem tailTrace_2122405 : CollatzResearch.WordTrace tailWord_2122405 prefixEnd_2122405 1089813908505873814376743 := by
  unfold tailWord_2122405
  simp only [CollatzResearch.WordTrace]
  refine ⟨77410469875896637760768669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51606979917264425173845779 77410469875896637760768669)
  ·
    refine ⟨29028926203461239160288251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77410469875896637760768669 29028926203461239160288251)
    ·
      refine ⟨43543389305191858740432377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29028926203461239160288251 43543389305191858740432377)
      ·
        refine ⟨32657541978893894055324283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43543389305191858740432377 32657541978893894055324283)
        ·
          refine ⟨48986312968340841082986425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32657541978893894055324283 48986312968340841082986425)
          ·
            refine ⟨36739734726255630812239819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48986312968340841082986425 36739734726255630812239819)
            ·
              refine ⟨55109602089383446218359729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36739734726255630812239819 55109602089383446218359729)
              ·
                refine ⟨41332201567037584663769797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55109602089383446218359729 41332201567037584663769797)
                ·
                  refine ⟨7749787793819547124456837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41332201567037584663769797 7749787793819547124456837)
                  ·
                    refine ⟨1453085211341165085835657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7749787793819547124456837 1453085211341165085835657)
                    ·
                      refine ⟨1089813908505873814376743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1453085211341165085835657 1089813908505873814376743)
                      ·
                        rfl

theorem cell23_2122405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 4, 4, 2].length) (baseStart_2122405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2122405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2122405 prefixEnd_2122405 := by exact prefixLift 2122405
  have htrace : WordTrace (prefixWord ++ tailWord_2122405) baseStart_2122405 baseEnd_2122405 := by
    simpa [prefixWord, tailWord_2122405, baseEnd_2122405] using wordTrace_append hprefix tailTrace_2122405
  have hstable : (prefixWord ++ tailWord_2122405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2122405).length < 2 ^ (prefixWord ++ tailWord_2122405).sum := by decide
  have hdescent : baseEnd_2122405 < baseStart_2122405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2122405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2122418 : List Nat := [3, 2, 1, 1, 1, 2, 1, 3, 2, 1, 6]
def baseStart_2122418 : Nat := 118140960795 + 2122418 * 2 ^ 59
def prefixEnd_2122418 : Nat := 4983230072969 + 3 ^ 40 * 2122418 * 2
def baseEnd_2122418 : Nat := 1089820583754382263514183

theorem tailTrace_2122418 : CollatzResearch.WordTrace tailWord_2122418 prefixEnd_2122418 1089820583754382263514183 := by
  unfold tailWord_2122418
  simp only [CollatzResearch.WordTrace]
  refine ⟨19352736006212385245247977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51607296016566360653994605 19352736006212385245247977)
  ·
    refine ⟨14514552004659288933935983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19352736006212385245247977 14514552004659288933935983)
    ·
      refine ⟨21771828006988933400903975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14514552004659288933935983 21771828006988933400903975)
      ·
        refine ⟨32657742010483400101355963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21771828006988933400903975 32657742010483400101355963)
        ·
          refine ⟨48986613015725100152033945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32657742010483400101355963 48986613015725100152033945)
          ·
            refine ⟨36739959761793825114025459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48986613015725100152033945 36739959761793825114025459)
            ·
              refine ⟨55109939642690737671038189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36739959761793825114025459 55109939642690737671038189)
              ·
                refine ⟨20666227366009026626639321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55109939642690737671038189 20666227366009026626639321)
                ·
                  refine ⟨15499670524506769969979491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20666227366009026626639321 15499670524506769969979491)
                  ·
                    refine ⟨23249505786760154954969237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15499670524506769969979491 23249505786760154954969237)
                    ·
                      refine ⟨1089820583754382263514183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23249505786760154954969237 1089820583754382263514183)
                      ·
                        rfl

theorem cell23_2122418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 2, 1, 6].length) (baseStart_2122418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2122418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2122418 prefixEnd_2122418 := by exact prefixLift 2122418
  have htrace : WordTrace (prefixWord ++ tailWord_2122418) baseStart_2122418 baseEnd_2122418 := by
    simpa [prefixWord, tailWord_2122418, baseEnd_2122418] using wordTrace_append hprefix tailTrace_2122418
  have hstable : (prefixWord ++ tailWord_2122418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2122418).length < 2 ^ (prefixWord ++ tailWord_2122418).sum := by decide
  have hdescent : baseEnd_2122418 < baseStart_2122418 := by decide
  rcases family_descends (prefixWord ++ tailWord_2122418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2122505 : List Nat := [1, 2, 1, 1, 3, 2, 5, 1, 1, 6]
def baseStart_2122505 : Nat := 118140960795 + 2122505 * 2 ^ 59
def prefixEnd_2122505 : Nat := 4983230072969 + 3 ^ 40 * 2122505 * 2
def baseEnd_2122505 : Nat := 363288418857107807708761

theorem tailTrace_2122505 : CollatzResearch.WordTrace tailWord_2122505 prefixEnd_2122505 363288418857107807708761 := by
  unfold tailWord_2122505
  simp only [CollatzResearch.WordTrace]
  refine ⟨77414117175534354839408969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51609411450356236559605979 77414117175534354839408969)
  ·
    refine ⟨58060587881650766129556727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77414117175534354839408969 58060587881650766129556727)
    ·
      refine ⟨87090881822476149194335091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58060587881650766129556727 87090881822476149194335091)
      ·
        refine ⟨130636322733714223791502637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87090881822476149194335091 130636322733714223791502637)
        ·
          refine ⟨48988621025142833921813489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 130636322733714223791502637 48988621025142833921813489)
          ·
            refine ⟨36741465768857125441360117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48988621025142833921813489 36741465768857125441360117)
            ·
              refine ⟨3444512415830355510127511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36741465768857125441360117 3444512415830355510127511)
              ·
                refine ⟨5166768623745533265191267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3444512415830355510127511 5166768623745533265191267)
                ·
                  refine ⟨7750152935618299897786901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5166768623745533265191267 7750152935618299897786901)
                  ·
                    refine ⟨363288418857107807708761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7750152935618299897786901 363288418857107807708761)
                    ·
                      rfl

theorem cell23_2122505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 1, 1, 6].length) (baseStart_2122505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2122505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2122505 prefixEnd_2122505 := by exact prefixLift 2122505
  have htrace : WordTrace (prefixWord ++ tailWord_2122505) baseStart_2122505 baseEnd_2122505 := by
    simpa [prefixWord, tailWord_2122505, baseEnd_2122505] using wordTrace_append hprefix tailTrace_2122505
  have hstable : (prefixWord ++ tailWord_2122505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2122505).length < 2 ^ (prefixWord ++ tailWord_2122505).sum := by decide
  have hdescent : baseEnd_2122505 < baseStart_2122505 := by decide
  rcases family_descends (prefixWord ++ tailWord_2122505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2122542 : List Nat := [4, 1, 3, 2, 1, 1, 1, 2, 1, 1, 6]
def baseStart_2122542 : Nat := 118140960795 + 2122542 * 2 ^ 59
def prefixEnd_2122542 : Nat := 4983230072969 + 3 ^ 40 * 2122542 * 2
def baseEnd_2122542 : Nat := 1089884255355539778363613

theorem tailTrace_2122542 : CollatzResearch.WordTrace tailWord_2122542 prefixEnd_2122542 1089884255355539778363613 := by
  unfold tailWord_2122542
  simp only [CollatzResearch.WordTrace]
  refine ⟨9676933334550038769813235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51610311117600206772337253 9676933334550038769813235)
  ·
    refine ⟨14515400001825058154719853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9676933334550038769813235 14515400001825058154719853)
    ·
      refine ⟨5443275000684396808019945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14515400001825058154719853 5443275000684396808019945)
      ·
        refine ⟨4082456250513297606014959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5443275000684396808019945 4082456250513297606014959)
        ·
          refine ⟨6123684375769946409022439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4082456250513297606014959 6123684375769946409022439)
          ·
            refine ⟨9185526563654919613533659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6123684375769946409022439 9185526563654919613533659)
            ·
              refine ⟨13778289845482379420300489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9185526563654919613533659 13778289845482379420300489)
              ·
                refine ⟨10333717384111784565225367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13778289845482379420300489 10333717384111784565225367)
                ·
                  refine ⟨15500576076167676847838051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10333717384111784565225367 15500576076167676847838051)
                  ·
                    refine ⟨23250864114251515271757077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15500576076167676847838051 23250864114251515271757077)
                    ·
                      refine ⟨1089884255355539778363613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23250864114251515271757077 1089884255355539778363613)
                      ·
                        rfl

theorem cell23_2122542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_2122542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2122542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2122542 prefixEnd_2122542 := by exact prefixLift 2122542
  have htrace : WordTrace (prefixWord ++ tailWord_2122542) baseStart_2122542 baseEnd_2122542 := by
    simpa [prefixWord, tailWord_2122542, baseEnd_2122542] using wordTrace_append hprefix tailTrace_2122542
  have hstable : (prefixWord ++ tailWord_2122542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2122542).length < 2 ^ (prefixWord ++ tailWord_2122542).sum := by decide
  have hdescent : baseEnd_2122542 < baseStart_2122542 := by decide
  rcases family_descends (prefixWord ++ tailWord_2122542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2122596 : List Nat := [2, 3, 1, 1, 4, 2, 2, 2, 2, 1, 3]
def baseStart_2122596 : Nat := 118140960795 + 2122596 * 2 ^ 59
def prefixEnd_2122596 : Nat := 4983230072969 + 3 ^ 40 * 2122596 * 2
def baseEnd_2122596 : Nat := 1089911983310882567088365

theorem tailTrace_2122596 : CollatzResearch.WordTrace tailWord_2122596 prefixEnd_2122596 1089911983310882567088365 := by
  unfold tailWord_2122596
  simp only [CollatzResearch.WordTrace]
  refine ⟨38708718109102338690485821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51611624145469784920647761 38708718109102338690485821)
  ·
    refine ⟨14515769290913377008932183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38708718109102338690485821 14515769290913377008932183)
    ·
      refine ⟨21773653936370065513398275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14515769290913377008932183 21773653936370065513398275)
      ·
        refine ⟨32660480904555098270097413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21773653936370065513398275 32660480904555098270097413)
        ·
          refine ⟨6123840169604080925643265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32660480904555098270097413 6123840169604080925643265)
          ·
            refine ⟨4592880127203060694232449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6123840169604080925643265 4592880127203060694232449)
            ·
              refine ⟨3444660095402295520674337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4592880127203060694232449 3444660095402295520674337)
              ·
                refine ⟨2583495071551721640505753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3444660095402295520674337 2583495071551721640505753)
                ·
                  refine ⟨1937621303663791230379315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2583495071551721640505753 1937621303663791230379315)
                  ·
                    refine ⟨2906431955495686845568973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1937621303663791230379315 2906431955495686845568973)
                    ·
                      refine ⟨1089911983310882567088365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2906431955495686845568973 1089911983310882567088365)
                      ·
                        rfl

theorem cell23_2122596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 2, 2, 1, 3].length) (baseStart_2122596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2122596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2122596 prefixEnd_2122596 := by exact prefixLift 2122596
  have htrace : WordTrace (prefixWord ++ tailWord_2122596) baseStart_2122596 baseEnd_2122596 := by
    simpa [prefixWord, tailWord_2122596, baseEnd_2122596] using wordTrace_append hprefix tailTrace_2122596
  have hstable : (prefixWord ++ tailWord_2122596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2122596).length < 2 ^ (prefixWord ++ tailWord_2122596).sum := by decide
  have hdescent : baseEnd_2122596 < baseStart_2122596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2122596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2122646 : List Nat := [5, 3, 1, 1, 1, 1, 1, 2, 2, 6]
def baseStart_2122646 : Nat := 118140960795 + 2122646 * 2 ^ 59
def prefixEnd_2122646 : Nat := 4983230072969 + 3 ^ 40 * 2122646 * 2
def baseEnd_2122646 : Nat := 363312552447869123821045

theorem tailTrace_2122646 : CollatzResearch.WordTrace tailWord_2122646 prefixEnd_2122646 363312552447869123821045 := by
  unfold tailWord_2122646
  simp only [CollatzResearch.WordTrace]
  refine ⟨4838703741751470995018237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 51612839912015690613527861 4838703741751470995018237)
  ·
    refine ⟨1814513903156801623131839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4838703741751470995018237 1814513903156801623131839)
    ·
      refine ⟨2721770854735202434697759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1814513903156801623131839 2721770854735202434697759)
      ·
        refine ⟨4082656282102803652046639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2721770854735202434697759 4082656282102803652046639)
        ·
          refine ⟨6123984423154205478069959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4082656282102803652046639 6123984423154205478069959)
          ·
            refine ⟨9185976634731308217104939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6123984423154205478069959 9185976634731308217104939)
            ·
              refine ⟨13778964952096962325657409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9185976634731308217104939 13778964952096962325657409)
              ·
                refine ⟨10334223714072721744243057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13778964952096962325657409 10334223714072721744243057)
                ·
                  refine ⟨7750667785554541308182293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10334223714072721744243057 7750667785554541308182293)
                  ·
                    refine ⟨363312552447869123821045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7750667785554541308182293 363312552447869123821045)
                    ·
                      rfl

theorem cell23_2122646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_2122646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2122646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2122646 prefixEnd_2122646 := by exact prefixLift 2122646
  have htrace : WordTrace (prefixWord ++ tailWord_2122646) baseStart_2122646 baseEnd_2122646 := by
    simpa [prefixWord, tailWord_2122646, baseEnd_2122646] using wordTrace_append hprefix tailTrace_2122646
  have hstable : (prefixWord ++ tailWord_2122646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2122646).length < 2 ^ (prefixWord ++ tailWord_2122646).sum := by decide
  have hdescent : baseEnd_2122646 < baseStart_2122646 := by decide
  rcases family_descends (prefixWord ++ tailWord_2122646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2122665 : List Nat := [1, 2, 1, 1, 1, 1, 6, 1, 1, 1, 7]
def baseStart_2122665 : Nat := 118140960795 + 2122665 * 2 ^ 59
def prefixEnd_2122665 : Nat := 4983230072969 + 3 ^ 40 * 2122665 * 2
def baseEnd_2122665 : Nat := 1089947413476042797125547

theorem tailTrace_2122665 : CollatzResearch.WordTrace tailWord_2122665 prefixEnd_2122665 1089947413476042797125547 := by
  unfold tailWord_2122665
  simp only [CollatzResearch.WordTrace]
  refine ⟨77419952854954702165233449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51613301903303134776822299 77419952854954702165233449)
  ·
    refine ⟨58064964641216026623925087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77419952854954702165233449 58064964641216026623925087)
    ·
      refine ⟨87097446961824039935887631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58064964641216026623925087 87097446961824039935887631)
      ·
        refine ⟨130646170442736059903831447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87097446961824039935887631 130646170442736059903831447)
        ·
          refine ⟨195969255664104089855747171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130646170442736059903831447 195969255664104089855747171)
          ·
            refine ⟨293953883496156134783620757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 195969255664104089855747171 293953883496156134783620757)
            ·
              refine ⟨13779088288882318817982223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 293953883496156134783620757 13779088288882318817982223)
              ·
                refine ⟨20668632433323478226973335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13779088288882318817982223 20668632433323478226973335)
                ·
                  refine ⟨31002948649985217340460003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20668632433323478226973335 31002948649985217340460003)
                  ·
                    refine ⟨46504422974977826010690005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31002948649985217340460003 46504422974977826010690005)
                    ·
                      refine ⟨1089947413476042797125547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 46504422974977826010690005 1089947413476042797125547)
                      ·
                        rfl

theorem cell23_2122665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 1, 7].length) (baseStart_2122665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2122665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2122665 prefixEnd_2122665 := by exact prefixLift 2122665
  have htrace : WordTrace (prefixWord ++ tailWord_2122665) baseStart_2122665 baseEnd_2122665 := by
    simpa [prefixWord, tailWord_2122665, baseEnd_2122665] using wordTrace_append hprefix tailTrace_2122665
  have hstable : (prefixWord ++ tailWord_2122665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2122665).length < 2 ^ (prefixWord ++ tailWord_2122665).sum := by decide
  have hdescent : baseEnd_2122665 < baseStart_2122665 := by decide
  rcases family_descends (prefixWord ++ tailWord_2122665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2122809 : List Nat := [1, 2, 1, 5, 2, 1, 2, 2, 1, 6]
def baseStart_2122809 : Nat := 118140960795 + 2122809 * 2 ^ 59
def prefixEnd_2122809 : Nat := 4983230072969 + 3 ^ 40 * 2122809 * 2
def baseEnd_2122809 : Nat := 363340451563430077908295

theorem tailTrace_2122809 : CollatzResearch.WordTrace tailWord_2122809 prefixEnd_2122809 363340451563430077908295 := by
  unfold tailWord_2122809
  simp only [CollatzResearch.WordTrace]
  refine ⟨77425204966433014758475481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51616803310955343172316987 77425204966433014758475481)
  ·
    refine ⟨58068903724824761068856611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77425204966433014758475481 58068903724824761068856611)
    ·
      refine ⟨87103355587237141603284917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58068903724824761068856611 87103355587237141603284917)
      ·
        refine ⟨8165939586303482025307961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 87103355587237141603284917 8165939586303482025307961)
        ·
          refine ⟨6124454689727611518980971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8165939586303482025307961 6124454689727611518980971)
          ·
            refine ⟨9186682034591417278471457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6124454689727611518980971 9186682034591417278471457)
            ·
              refine ⟨6890011525943562958853593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9186682034591417278471457 6890011525943562958853593)
              ·
                refine ⟨5167508644457672219140195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6890011525943562958853593 5167508644457672219140195)
                ·
                  refine ⟨7751262966686508328710293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5167508644457672219140195 7751262966686508328710293)
                  ·
                    refine ⟨363340451563430077908295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7751262966686508328710293 363340451563430077908295)
                    ·
                      rfl

theorem cell23_2122809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 2, 1, 6].length) (baseStart_2122809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2122809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2122809 prefixEnd_2122809 := by exact prefixLift 2122809
  have htrace : WordTrace (prefixWord ++ tailWord_2122809) baseStart_2122809 baseEnd_2122809 := by
    simpa [prefixWord, tailWord_2122809, baseEnd_2122809] using wordTrace_append hprefix tailTrace_2122809
  have hstable : (prefixWord ++ tailWord_2122809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2122809).length < 2 ^ (prefixWord ++ tailWord_2122809).sum := by decide
  have hdescent : baseEnd_2122809 < baseStart_2122809 := by decide
  rcases family_descends (prefixWord ++ tailWord_2122809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2122813 : List Nat := [1, 4, 1, 3, 1, 4, 2, 1, 1, 5]
def baseStart_2122813 : Nat := 118140960795 + 2122813 * 2 ^ 59
def prefixEnd_2122813 : Nat := 4983230072969 + 3 ^ 40 * 2122813 * 2
def baseEnd_2122813 : Nat := 363341136204302739358289

theorem tailTrace_2122813 : CollatzResearch.WordTrace tailWord_2122813 prefixEnd_2122813 363341136204302739358289 := by
  unfold tailWord_2122813
  simp only [CollatzResearch.WordTrace]
  refine ⟨77425350858418523441621093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51616900572279015627747395 77425350858418523441621093)
  ·
    refine ⟨14517253285953473145303955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77425350858418523441621093 14517253285953473145303955)
    ·
      refine ⟨21775879928930209717955933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14517253285953473145303955 21775879928930209717955933)
      ·
        refine ⟨8165954973348828644233475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21775879928930209717955933 8165954973348828644233475)
        ·
          refine ⟨12248932460023242966350213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8165954973348828644233475 12248932460023242966350213)
          ·
            refine ⟨2296674836254358056190665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12248932460023242966350213 2296674836254358056190665)
            ·
              refine ⟨1722506127190768542142999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2296674836254358056190665 1722506127190768542142999)
              ·
                refine ⟨2583759190786152813214499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1722506127190768542142999 2583759190786152813214499)
                ·
                  refine ⟨3875638786179229219821749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2583759190786152813214499 3875638786179229219821749)
                  ·
                    refine ⟨363341136204302739358289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3875638786179229219821749 363341136204302739358289)
                    ·
                      rfl

theorem cell23_2122813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 2, 1, 1, 5].length) (baseStart_2122813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2122813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2122813 prefixEnd_2122813 := by exact prefixLift 2122813
  have htrace : WordTrace (prefixWord ++ tailWord_2122813) baseStart_2122813 baseEnd_2122813 := by
    simpa [prefixWord, tailWord_2122813, baseEnd_2122813] using wordTrace_append hprefix tailTrace_2122813
  have hstable : (prefixWord ++ tailWord_2122813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2122813).length < 2 ^ (prefixWord ++ tailWord_2122813).sum := by decide
  have hdescent : baseEnd_2122813 < baseStart_2122813 := by decide
  rcases family_descends (prefixWord ++ tailWord_2122813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2122816 : List Nat := [2, 1, 1, 2, 2, 3, 1, 2, 5, 2, 2]
def baseStart_2122816 : Nat := 118140960795 + 2122816 * 2 ^ 59
def prefixEnd_2122816 : Nat := 4983230072969 + 3 ^ 40 * 2122816 * 2
def baseEnd_2122816 : Nat := 1090024949054871706337353

theorem tailTrace_2122816 : CollatzResearch.WordTrace tailWord_2122816 prefixEnd_2122816 1090024949054871706337353 := by
  unfold tailWord_2122816
  simp only [CollatzResearch.WordTrace]
  refine ⟨38712730138703827476990151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51616973518271769969320201 38712730138703827476990151)
  ·
    refine ⟨58069095208055741215485227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38712730138703827476990151 58069095208055741215485227)
    ·
      refine ⟨87103642812083611823227841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58069095208055741215485227 87103642812083611823227841)
      ·
        refine ⟨65327732109062708867420881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87103642812083611823227841 65327732109062708867420881)
        ·
          refine ⟨48995799081797031650565661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65327732109062708867420881 48995799081797031650565661)
          ·
            refine ⟨18373424655673886868962123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48995799081797031650565661 18373424655673886868962123)
            ·
              refine ⟨27560136983510830303443185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18373424655673886868962123 27560136983510830303443185)
              ·
                refine ⟨20670102737633122727582389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27560136983510830303443185 20670102737633122727582389)
                ·
                  refine ⟨1937822131653105255710849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20670102737633122727582389 1937822131653105255710849)
                  ·
                    refine ⟨1453366598739828941783137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1937822131653105255710849 1453366598739828941783137)
                    ·
                      refine ⟨1090024949054871706337353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1453366598739828941783137 1090024949054871706337353)
                      ·
                        rfl

theorem cell23_2122816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 5, 2, 2].length) (baseStart_2122816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2122816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2122816 prefixEnd_2122816 := by exact prefixLift 2122816
  have htrace : WordTrace (prefixWord ++ tailWord_2122816) baseStart_2122816 baseEnd_2122816 := by
    simpa [prefixWord, tailWord_2122816, baseEnd_2122816] using wordTrace_append hprefix tailTrace_2122816
  have hstable : (prefixWord ++ tailWord_2122816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2122816).length < 2 ^ (prefixWord ++ tailWord_2122816).sum := by decide
  have hdescent : baseEnd_2122816 < baseStart_2122816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2122816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2122826 : List Nat := [3, 1, 2, 1, 1, 2, 5, 2, 2, 4]
def baseStart_2122826 : Nat := 118140960795 + 2122826 * 2 ^ 59
def prefixEnd_2122826 : Nat := 4983230072969 + 3 ^ 40 * 2122826 * 2
def baseEnd_2122826 : Nat := 363343361287138889070769

theorem tailTrace_2122826 : CollatzResearch.WordTrace tailWord_2122826 prefixEnd_2122826 363343361287138889070769 := by
  unfold tailWord_2122826
  simp only [CollatzResearch.WordTrace]
  refine ⟨19356456251842856665461083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51617216671580951107896221 19356456251842856665461083)
  ·
    refine ⟨29034684377764284998191625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19356456251842856665461083 29034684377764284998191625)
    ·
      refine ⟨21776013283323213748643719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29034684377764284998191625 21776013283323213748643719)
      ·
        refine ⟨32664019924984820622965579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21776013283323213748643719 32664019924984820622965579)
        ·
          refine ⟨48996029887477230934448369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32664019924984820622965579 48996029887477230934448369)
          ·
            refine ⟨36747022415607923200836277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48996029887477230934448369 36747022415607923200836277)
            ·
              refine ⟨3445033351463242800078401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36747022415607923200836277 3445033351463242800078401)
              ·
                refine ⟨2583775013597432100058801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3445033351463242800078401 2583775013597432100058801)
                ·
                  refine ⟨1937831260198074075044101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2583775013597432100058801 1937831260198074075044101)
                  ·
                    refine ⟨363343361287138889070769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1937831260198074075044101 363343361287138889070769)
                    ·
                      rfl

theorem cell23_2122826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 2, 2, 4].length) (baseStart_2122826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2122826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2122826 prefixEnd_2122826 := by exact prefixLift 2122826
  have htrace : WordTrace (prefixWord ++ tailWord_2122826) baseStart_2122826 baseEnd_2122826 := by
    simpa [prefixWord, tailWord_2122826, baseEnd_2122826] using wordTrace_append hprefix tailTrace_2122826
  have hstable : (prefixWord ++ tailWord_2122826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2122826).length < 2 ^ (prefixWord ++ tailWord_2122826).sum := by decide
  have hdescent : baseEnd_2122826 < baseStart_2122826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2122826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2122842 : List Nat := [3, 1, 1, 2, 1, 1, 2, 1, 1, 4, 6]
def baseStart_2122842 : Nat := 118140960795 + 2122842 * 2 ^ 59
def prefixEnd_2122842 : Nat := 4983230072969 + 3 ^ 40 * 2122842 * 2
def baseEnd_2122842 : Nat := 1090038299551888604612233

theorem tailTrace_2122842 : CollatzResearch.WordTrace tailWord_2122842 prefixEnd_2122842 1090038299551888604612233 := by
  unfold tailWord_2122842
  simp only [CollatzResearch.WordTrace]
  refine ⟨19356602143828365348606695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51617605716875640929617853 19356602143828365348606695)
  ·
    refine ⟨29034903215742548022910043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19356602143828365348606695 29034903215742548022910043)
    ·
      refine ⟨43552354823613822034365065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29034903215742548022910043 43552354823613822034365065)
      ·
        refine ⟨32664266117710366525773799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43552354823613822034365065 32664266117710366525773799)
        ·
          refine ⟨48996399176565549788660699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32664266117710366525773799 48996399176565549788660699)
          ·
            refine ⟨73494598764848324682991049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48996399176565549788660699 73494598764848324682991049)
            ·
              refine ⟨55120949073636243512243287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73494598764848324682991049 55120949073636243512243287)
              ·
                refine ⟨82681423610454365268364931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55120949073636243512243287 82681423610454365268364931)
                ·
                  refine ⟨124022135415681547902547397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82681423610454365268364931 124022135415681547902547397)
                  ·
                    refine ⟨23254150390440290231727637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 124022135415681547902547397 23254150390440290231727637)
                    ·
                      refine ⟨1090038299551888604612233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23254150390440290231727637 1090038299551888604612233)
                      ·
                        rfl

theorem cell23_2122842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 1, 4, 6].length) (baseStart_2122842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2122842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2122842 prefixEnd_2122842 := by exact prefixLift 2122842
  have htrace : WordTrace (prefixWord ++ tailWord_2122842) baseStart_2122842 baseEnd_2122842 := by
    simpa [prefixWord, tailWord_2122842, baseEnd_2122842] using wordTrace_append hprefix tailTrace_2122842
  have hstable : (prefixWord ++ tailWord_2122842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2122842).length < 2 ^ (prefixWord ++ tailWord_2122842).sum := by decide
  have hdescent : baseEnd_2122842 < baseStart_2122842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2122842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2122850 : List Nat := [3, 3, 2, 2, 1, 1, 2, 2, 3, 2, 2]
def baseStart_2122850 : Nat := 118140960795 + 2122850 * 2 ^ 59
def prefixEnd_2122850 : Nat := 4983230072969 + 3 ^ 40 * 2122850 * 2
def baseEnd_2122850 : Nat := 1090042407397124573312197

theorem tailTrace_2122850 : CollatzResearch.WordTrace tailWord_2122850 prefixEnd_2122850 1090042407397124573312197 := by
  unfold tailWord_2122850
  simp only [CollatzResearch.WordTrace]
  refine ⟨19356675089821119690179501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51617800239522985840478669 19356675089821119690179501)
  ·
    refine ⟨7258753158682919883817313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19356675089821119690179501 7258753158682919883817313)
    ·
      refine ⟨5444064869012189912862985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7258753158682919883817313 5444064869012189912862985)
      ·
        refine ⟨4083048651759142434647239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5444064869012189912862985 4083048651759142434647239)
        ·
          refine ⟨6124572977638713651970859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4083048651759142434647239 6124572977638713651970859)
          ·
            refine ⟨9186859466458070477956289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6124572977638713651970859 9186859466458070477956289)
            ·
              refine ⟨6890144599843552858467217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9186859466458070477956289 6890144599843552858467217)
              ·
                refine ⟨5167608449882664643850413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6890144599843552858467217 5167608449882664643850413)
                ·
                  refine ⟨1937853168705999241443905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5167608449882664643850413 1937853168705999241443905)
                  ·
                    refine ⟨1453389876529499431082929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1937853168705999241443905 1453389876529499431082929)
                    ·
                      refine ⟨1090042407397124573312197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1453389876529499431082929 1090042407397124573312197)
                      ·
                        rfl

theorem cell23_2122850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_2122850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2122850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2122850 prefixEnd_2122850 := by exact prefixLift 2122850
  have htrace : WordTrace (prefixWord ++ tailWord_2122850) baseStart_2122850 baseEnd_2122850 := by
    simpa [prefixWord, tailWord_2122850, baseEnd_2122850] using wordTrace_append hprefix tailTrace_2122850
  have hstable : (prefixWord ++ tailWord_2122850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2122850).length < 2 ^ (prefixWord ++ tailWord_2122850).sum := by decide
  have hdescent : baseEnd_2122850 < baseStart_2122850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2122850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2122856 : List Nat := [2, 1, 4, 4, 1, 1, 1, 9]
def baseStart_2122856 : Nat := 118140960795 + 2122856 * 2 ^ 59
def prefixEnd_2122856 : Nat := 4983230072969 + 3 ^ 40 * 2122856 * 2
def baseEnd_2122856 : Nat := 40372055121520427771747

theorem tailTrace_2122856 : CollatzResearch.WordTrace tailWord_2122856 prefixEnd_2122856 40372055121520427771747 := by
  unfold tailWord_2122856
  simp only [CollatzResearch.WordTrace]
  refine ⟨38713459598631370892718211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51617946131508494523624281 38713459598631370892718211)
  ·
    refine ⟨58070189397947056339077317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38713459598631370892718211 58070189397947056339077317)
    ·
      refine ⟨10888160512115073063576997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58070189397947056339077317 10888160512115073063576997)
      ·
        refine ⟨2041530096021576199420687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10888160512115073063576997 2041530096021576199420687)
        ·
          refine ⟨3062295144032364299131031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2041530096021576199420687 3062295144032364299131031)
          ·
            refine ⟨4593442716048546448696547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3062295144032364299131031 4593442716048546448696547)
            ·
              refine ⟨6890164074072819673044821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4593442716048546448696547 6890164074072819673044821)
              ·
                refine ⟨40372055121520427771747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6890164074072819673044821 40372055121520427771747)
                ·
                  rfl

theorem cell23_2122856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 9].length) (baseStart_2122856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2122856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2122856 prefixEnd_2122856 := by exact prefixLift 2122856
  have htrace : WordTrace (prefixWord ++ tailWord_2122856) baseStart_2122856 baseEnd_2122856 := by
    simpa [prefixWord, tailWord_2122856, baseEnd_2122856] using wordTrace_append hprefix tailTrace_2122856
  have hstable : (prefixWord ++ tailWord_2122856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2122856).length < 2 ^ (prefixWord ++ tailWord_2122856).sum := by decide
  have hdescent : baseEnd_2122856 < baseStart_2122856 := by decide
  rcases family_descends (prefixWord ++ tailWord_2122856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2122859 : List Nat := [1, 1, 1, 1, 2, 2, 1, 1, 4, 7, 2]
def baseStart_2122859 : Nat := 118140960795 + 2122859 * 2 ^ 59
def prefixEnd_2122859 : Nat := 4983230072969 + 3 ^ 40 * 2122859 * 2
def baseEnd_2122859 : Nat := 1090047028723015038099655

theorem tailTrace_2122859 : CollatzResearch.WordTrace tailWord_2122859 prefixEnd_2122859 1090047028723015038099655 := by
  unfold tailWord_2122859
  simp only [CollatzResearch.WordTrace]
  refine ⟨77427028616251873297795631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51618019077501248865197087 77427028616251873297795631)
  ·
    refine ⟨116140542924377809946693447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77427028616251873297795631 116140542924377809946693447)
    ·
      refine ⟨174210814386566714920040171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116140542924377809946693447 174210814386566714920040171)
      ·
        refine ⟨261316221579850072380060257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174210814386566714920040171 261316221579850072380060257)
        ·
          refine ⟨195987166184887554285045193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 261316221579850072380060257 195987166184887554285045193)
          ·
            refine ⟨146990374638665665713783895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 195987166184887554285045193 146990374638665665713783895)
            ·
              refine ⟨220485561957998498570675843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146990374638665665713783895 220485561957998498570675843)
              ·
                refine ⟨330728342936997747856013765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 220485561957998498570675843 330728342936997747856013765)
                ·
                  refine ⟨62011564300687077723002581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 330728342936997747856013765 62011564300687077723002581)
                  ·
                    refine ⟨1453396038297353384132873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 62011564300687077723002581 1453396038297353384132873)
                    ·
                      refine ⟨1090047028723015038099655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1453396038297353384132873 1090047028723015038099655)
                      ·
                        rfl

theorem cell23_2122859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 7, 2].length) (baseStart_2122859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2122859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2122859 prefixEnd_2122859 := by exact prefixLift 2122859
  have htrace : WordTrace (prefixWord ++ tailWord_2122859) baseStart_2122859 baseEnd_2122859 := by
    simpa [prefixWord, tailWord_2122859, baseEnd_2122859] using wordTrace_append hprefix tailTrace_2122859
  have hstable : (prefixWord ++ tailWord_2122859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2122859).length < 2 ^ (prefixWord ++ tailWord_2122859).sum := by decide
  have hdescent : baseEnd_2122859 < baseStart_2122859 := by decide
  rcases family_descends (prefixWord ++ tailWord_2122859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2122866 : List Nat := [3, 2, 1, 2, 2, 1, 1, 1, 6, 1, 3]
def baseStart_2122866 : Nat := 118140960795 + 2122866 * 2 ^ 59
def prefixEnd_2122866 : Nat := 4983230072969 + 3 ^ 40 * 2122866 * 2
def baseEnd_2122866 : Nat := 1090050623087596510712123

theorem tailTrace_2122866 : CollatzResearch.WordTrace tailWord_2122866 prefixEnd_2122866 1090050623087596510712123 := by
  unfold tailWord_2122866
  simp only [CollatzResearch.WordTrace]
  refine ⟨19356820981806628373325113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51618189284817675662200301 19356820981806628373325113)
  ·
    refine ⟨14517615736354971279993835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19356820981806628373325113 14517615736354971279993835)
    ·
      refine ⟨21776423604532456919990753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14517615736354971279993835 21776423604532456919990753)
      ·
        refine ⟨16332317703399342689993065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21776423604532456919990753 16332317703399342689993065)
        ·
          refine ⟨12249238277549507017494799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16332317703399342689993065 12249238277549507017494799)
          ·
            refine ⟨18373857416324260526242199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12249238277549507017494799 18373857416324260526242199)
            ·
              refine ⟨27560786124486390789363299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18373857416324260526242199 27560786124486390789363299)
              ·
                refine ⟨41341179186729586184044949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27560786124486390789363299 41341179186729586184044949)
                ·
                  refine ⟨1937867774377949352377107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 41341179186729586184044949 1937867774377949352377107)
                  ·
                    refine ⟨2906801661566924028565661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1937867774377949352377107 2906801661566924028565661)
                    ·
                      refine ⟨1090050623087596510712123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2906801661566924028565661 1090050623087596510712123)
                      ·
                        rfl

theorem cell23_2122866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 6, 1, 3].length) (baseStart_2122866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2122866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2122866 prefixEnd_2122866 := by exact prefixLift 2122866
  have htrace : WordTrace (prefixWord ++ tailWord_2122866) baseStart_2122866 baseEnd_2122866 := by
    simpa [prefixWord, tailWord_2122866, baseEnd_2122866] using wordTrace_append hprefix tailTrace_2122866
  have hstable : (prefixWord ++ tailWord_2122866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2122866).length < 2 ^ (prefixWord ++ tailWord_2122866).sum := by decide
  have hdescent : baseEnd_2122866 < baseStart_2122866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2122866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2122909 : List Nat := [1, 4, 2, 1, 1, 2, 1, 1, 4, 1, 5]
def baseStart_2122909 : Nat := 118140960795 + 2122909 * 2 ^ 59
def prefixEnd_2122909 : Nat := 4983230072969 + 3 ^ 40 * 2122909 * 2
def baseEnd_2122909 : Nat := 1090072702755739842474425

theorem tailTrace_2122909 : CollatzResearch.WordTrace tailWord_2122909 prefixEnd_2122909 1090072702755739842474425 := by
  unfold tailWord_2122909
  simp only [CollatzResearch.WordTrace]
  refine ⟨77428852266070731837115781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51619234844047154558077187 77428852266070731837115781)
  ·
    refine ⟨14517909799888262219459209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77428852266070731837115781 14517909799888262219459209)
    ·
      refine ⟨10888432349916196664594407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14517909799888262219459209 10888432349916196664594407)
      ·
        refine ⟨16332648524874294996891611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10888432349916196664594407 16332648524874294996891611)
        ·
          refine ⟨24498972787311442495337417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16332648524874294996891611 24498972787311442495337417)
          ·
            refine ⟨18374229590483581871503063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24498972787311442495337417 18374229590483581871503063)
            ·
              refine ⟨27561344385725372807254595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18374229590483581871503063 27561344385725372807254595)
              ·
                refine ⟨41342016578588059210881893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27561344385725372807254595 41342016578588059210881893)
                ·
                  refine ⟨7751628108485261102040355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41342016578588059210881893 7751628108485261102040355)
                  ·
                    refine ⟨11627442162727891653060533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7751628108485261102040355 11627442162727891653060533)
                    ·
                      refine ⟨1090072702755739842474425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11627442162727891653060533 1090072702755739842474425)
                      ·
                        rfl

theorem cell23_2122909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_2122909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2122909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2122909 prefixEnd_2122909 := by exact prefixLift 2122909
  have htrace : WordTrace (prefixWord ++ tailWord_2122909) baseStart_2122909 baseEnd_2122909 := by
    simpa [prefixWord, tailWord_2122909, baseEnd_2122909] using wordTrace_append hprefix tailTrace_2122909
  have hstable : (prefixWord ++ tailWord_2122909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2122909).length < 2 ^ (prefixWord ++ tailWord_2122909).sum := by decide
  have hdescent : baseEnd_2122909 < baseStart_2122909 := by decide
  rcases family_descends (prefixWord ++ tailWord_2122909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2122910 : List Nat := [4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2]
def baseStart_2122910 : Nat := 118140960795 + 2122910 * 2 ^ 59
def prefixEnd_2122910 : Nat := 4983230072969 + 3 ^ 40 * 2122910 * 2
def baseEnd_2122910 : Nat := 1090073216236394338561921

theorem tailTrace_2122910 : CollatzResearch.WordTrace tailWord_2122910 prefixEnd_2122910 1090073216236394338561921 := by
  unfold tailWord_2122910
  simp only [CollatzResearch.WordTrace]
  refine ⟨9678611092383388625987773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51619259159378072671934789 9678611092383388625987773)
  ·
    refine ⟨3629479159643770734745415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9678611092383388625987773 3629479159643770734745415)
    ·
      refine ⟨5444218739465656102118123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3629479159643770734745415 5444218739465656102118123)
      ·
        refine ⟨8166328109198484153177185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5444218739465656102118123 8166328109198484153177185)
        ·
          refine ⟨6124746081898863114882889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8166328109198484153177185 6124746081898863114882889)
          ·
            refine ⟨4593559561424147336162167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6124746081898863114882889 4593559561424147336162167)
            ·
              refine ⟨6890339342136221004243251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4593559561424147336162167 6890339342136221004243251)
              ·
                refine ⟨10335509013204331506364877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6890339342136221004243251 10335509013204331506364877)
                ·
                  refine ⟨3875815879951624314886829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10335509013204331506364877 3875815879951624314886829)
                  ·
                    refine ⟨1453430954981859118082561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3875815879951624314886829 1453430954981859118082561)
                    ·
                      refine ⟨1090073216236394338561921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1453430954981859118082561 1090073216236394338561921)
                      ·
                        rfl

theorem cell23_2122910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2].length) (baseStart_2122910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2122910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2122910 prefixEnd_2122910 := by exact prefixLift 2122910
  have htrace : WordTrace (prefixWord ++ tailWord_2122910) baseStart_2122910 baseEnd_2122910 := by
    simpa [prefixWord, tailWord_2122910, baseEnd_2122910] using wordTrace_append hprefix tailTrace_2122910
  have hstable : (prefixWord ++ tailWord_2122910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2122910).length < 2 ^ (prefixWord ++ tailWord_2122910).sum := by decide
  have hdescent : baseEnd_2122910 < baseStart_2122910 := by decide
  rcases family_descends (prefixWord ++ tailWord_2122910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2122934 : List Nat := [5, 1, 3, 2, 1, 1, 2, 2, 2, 1, 3]
def baseStart_2122934 : Nat := 118140960795 + 2122934 * 2 ^ 59
def prefixEnd_2122934 : Nat := 4983230072969 + 3 ^ 40 * 2122934 * 2
def baseEnd_2122934 : Nat := 1090085539772102244661811

theorem tailTrace_2122934 : CollatzResearch.WordTrace tailWord_2122934 prefixEnd_2122934 1090085539772102244661811 := by
  unfold tailWord_2122934
  simp only [CollatzResearch.WordTrace]
  refine ⟨4839360255686260069173491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 51619842727320107404517237 4839360255686260069173491)
  ·
    refine ⟨7259040383529390103760237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4839360255686260069173491 7259040383529390103760237)
    ·
      refine ⟨2722140143823521288910089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7259040383529390103760237 2722140143823521288910089)
      ·
        refine ⟨2041605107867640966682567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2722140143823521288910089 2041605107867640966682567)
        ·
          refine ⟨3062407661801461450023851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2041605107867640966682567 3062407661801461450023851)
          ·
            refine ⟨4593611492702192175035777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3062407661801461450023851 4593611492702192175035777)
            ·
              refine ⟨3445208619526644131276833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4593611492702192175035777 3445208619526644131276833)
              ·
                refine ⟨2583906464644983098457625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3445208619526644131276833 2583906464644983098457625)
                ·
                  refine ⟨1937929848483737323843219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2583906464644983098457625 1937929848483737323843219)
                  ·
                    refine ⟨2906894772725605985764829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1937929848483737323843219 2906894772725605985764829)
                    ·
                      refine ⟨1090085539772102244661811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2906894772725605985764829 1090085539772102244661811)
                      ·
                        rfl

theorem cell23_2122934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_2122934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2122934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2122934 prefixEnd_2122934 := by exact prefixLift 2122934
  have htrace : WordTrace (prefixWord ++ tailWord_2122934) baseStart_2122934 baseEnd_2122934 := by
    simpa [prefixWord, tailWord_2122934, baseEnd_2122934] using wordTrace_append hprefix tailTrace_2122934
  have hstable : (prefixWord ++ tailWord_2122934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2122934).length < 2 ^ (prefixWord ++ tailWord_2122934).sum := by decide
  have hdescent : baseEnd_2122934 < baseStart_2122934 := by decide
  rcases family_descends (prefixWord ++ tailWord_2122934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2122940 : List Nat := [2, 2, 2, 3, 2, 1, 1, 4, 2, 2, 2]
def baseStart_2122940 : Nat := 118140960795 + 2122940 * 2 ^ 59
def prefixEnd_2122940 : Nat := 4983230072969 + 3 ^ 40 * 2122940 * 2
def baseEnd_2122940 : Nat := 1090088620656029221186783

theorem tailTrace_2122940 : CollatzResearch.WordTrace tailWord_2122940 prefixEnd_2122940 1090088620656029221186783 := by
  unfold tailWord_2122940
  simp only [CollatzResearch.WordTrace]
  refine ⟨38714991464479212065747137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51619988619305616087662849 38714991464479212065747137)
  ·
    refine ⟨29036243598359409049310353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38714991464479212065747137 29036243598359409049310353)
    ·
      refine ⟨21777182698769556786982765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29036243598359409049310353 21777182698769556786982765)
      ·
        refine ⟨8166443512038583795118537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21777182698769556786982765 8166443512038583795118537)
        ·
          refine ⟨6124832634028937846338903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8166443512038583795118537 6124832634028937846338903)
          ·
            refine ⟨9187248951043406769508355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6124832634028937846338903 9187248951043406769508355)
            ·
              refine ⟨13780873426565110154262533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9187248951043406769508355 13780873426565110154262533)
              ·
                refine ⟨2583913767480958153924225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13780873426565110154262533 2583913767480958153924225)
                ·
                  refine ⟨1937935325610718615443169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2583913767480958153924225 1937935325610718615443169)
                  ·
                    refine ⟨1453451494208038961582377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1937935325610718615443169 1453451494208038961582377)
                    ·
                      refine ⟨1090088620656029221186783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1453451494208038961582377 1090088620656029221186783)
                      ·
                        rfl

theorem cell23_2122940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 4, 2, 2, 2].length) (baseStart_2122940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2122940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2122940 prefixEnd_2122940 := by exact prefixLift 2122940
  have htrace : WordTrace (prefixWord ++ tailWord_2122940) baseStart_2122940 baseEnd_2122940 := by
    simpa [prefixWord, tailWord_2122940, baseEnd_2122940] using wordTrace_append hprefix tailTrace_2122940
  have hstable : (prefixWord ++ tailWord_2122940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2122940).length < 2 ^ (prefixWord ++ tailWord_2122940).sum := by decide
  have hdescent : baseEnd_2122940 < baseStart_2122940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2122940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2122976 : List Nat := [2, 1, 1, 3, 1, 4, 3, 1, 2, 5]
def baseStart_2122976 : Nat := 118140960795 + 2122976 * 2 ^ 59
def prefixEnd_2122976 : Nat := 4983230072969 + 3 ^ 40 * 2122976 * 2
def baseEnd_2122976 : Nat := 363369035319863693445539

theorem tailTrace_2122976 : CollatzResearch.WordTrace tailWord_2122976 prefixEnd_2122976 363369035319863693445539 := by
  unfold tailWord_2122976
  simp only [CollatzResearch.WordTrace]
  refine ⟨38715647978414001139902391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51620863971218668186536521 38715647978414001139902391)
  ·
    refine ⟨58073471967621001709853587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38715647978414001139902391 58073471967621001709853587)
    ·
      refine ⟨87110207951431502564780381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58073471967621001709853587 87110207951431502564780381)
      ·
        refine ⟨32666327981786813461792643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87110207951431502564780381 32666327981786813461792643)
        ·
          refine ⟨48999491972680220192688965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32666327981786813461792643 48999491972680220192688965)
          ·
            refine ⟨9187404744877541286129181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48999491972680220192688965 9187404744877541286129181)
            ·
              refine ⟨3445276779329077982298443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9187404744877541286129181 3445276779329077982298443)
              ·
                refine ⟨5167915168993616973447665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3445276779329077982298443 5167915168993616973447665)
                ·
                  refine ⟨3875936376745212730085749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5167915168993616973447665 3875936376745212730085749)
                  ·
                    refine ⟨363369035319863693445539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3875936376745212730085749 363369035319863693445539)
                    ·
                      rfl

theorem cell23_2122976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 1, 2, 5].length) (baseStart_2122976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2122976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2122976 prefixEnd_2122976 := by exact prefixLift 2122976
  have htrace : WordTrace (prefixWord ++ tailWord_2122976) baseStart_2122976 baseEnd_2122976 := by
    simpa [prefixWord, tailWord_2122976, baseEnd_2122976] using wordTrace_append hprefix tailTrace_2122976
  have hstable : (prefixWord ++ tailWord_2122976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2122976).length < 2 ^ (prefixWord ++ tailWord_2122976).sum := by decide
  have hdescent : baseEnd_2122976 < baseStart_2122976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2122976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2123050 : List Nat := [3, 1, 4, 2, 1, 2, 1, 2, 2, 2, 3]
def baseStart_2123050 : Nat := 118140960795 + 2123050 * 2 ^ 59
def prefixEnd_2123050 : Nat := 4983230072969 + 3 ^ 40 * 2123050 * 2
def baseEnd_2123050 : Nat := 1090145103528023790811277

theorem tailTrace_2123050 : CollatzResearch.WordTrace tailWord_2123050 prefixEnd_2123050 1090145103528023790811277 := by
  unfold tailWord_2123050
  simp only [CollatzResearch.WordTrace]
  refine ⟨19358498739639978229499651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51622663305706608611999069 19358498739639978229499651)
  ·
    refine ⟨29037748109459967344249477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19358498739639978229499651 29037748109459967344249477)
    ·
      refine ⟨5444577770523743877046777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29037748109459967344249477 5444577770523743877046777)
      ·
        refine ⟨4083433327892807907785083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5444577770523743877046777 4083433327892807907785083)
        ·
          refine ⟨6125149991839211861677625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4083433327892807907785083 6125149991839211861677625)
          ·
            refine ⟨4593862493879408896258219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6125149991839211861677625 4593862493879408896258219)
            ·
              refine ⟨6890793740819113344387329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4593862493879408896258219 6890793740819113344387329)
              ·
                refine ⟨5168095305614335008290497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6890793740819113344387329 5168095305614335008290497)
                ·
                  refine ⟨3876071479210751256217873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5168095305614335008290497 3876071479210751256217873)
                  ·
                    refine ⟨2907053609408063442163405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3876071479210751256217873 2907053609408063442163405)
                    ·
                      refine ⟨1090145103528023790811277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2907053609408063442163405 1090145103528023790811277)
                      ·
                        rfl

theorem cell23_2123050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_2123050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2123050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2123050 prefixEnd_2123050 := by exact prefixLift 2123050
  have htrace : WordTrace (prefixWord ++ tailWord_2123050) baseStart_2123050 baseEnd_2123050 := by
    simpa [prefixWord, tailWord_2123050, baseEnd_2123050] using wordTrace_append hprefix tailTrace_2123050
  have hstable : (prefixWord ++ tailWord_2123050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2123050).length < 2 ^ (prefixWord ++ tailWord_2123050).sum := by decide
  have hdescent : baseEnd_2123050 < baseStart_2123050 := by decide
  rcases family_descends (prefixWord ++ tailWord_2123050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2123053 : List Nat := [1, 5, 3, 1, 1, 1, 2, 1, 8]
def baseStart_2123053 : Nat := 118140960795 + 2123053 * 2 ^ 59
def prefixEnd_2123053 : Nat := 4983230072969 + 3 ^ 40 * 2123053 * 2
def baseEnd_2123053 : Nat := 121127404885554142119307

theorem tailTrace_2123053 : CollatzResearch.WordTrace tailWord_2123053 prefixEnd_2123053 121127404885554142119307 := by
  unfold tailWord_2123053
  simp only [CollatzResearch.WordTrace]
  refine ⟨77434104377549044430357813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51622736251699362953571875 77434104377549044430357813)
  ·
    refine ⟨7259447285395222915346045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 77434104377549044430357813 7259447285395222915346045)
    ·
      refine ⟨2722292732023208593254767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7259447285395222915346045 2722292732023208593254767)
      ·
        refine ⟨4083439098034812889882151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2722292732023208593254767 4083439098034812889882151)
        ·
          refine ⟨6125158647052219334823227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4083439098034812889882151 6125158647052219334823227)
          ·
            refine ⟨9187737970578329002234841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6125158647052219334823227 9187737970578329002234841)
            ·
              refine ⟨6890803477933746751676131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9187737970578329002234841 6890803477933746751676131)
              ·
                refine ⟨10336205216900620127514197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6890803477933746751676131 10336205216900620127514197)
                ·
                  refine ⟨121127404885554142119307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10336205216900620127514197 121127404885554142119307)
                  ·
                    rfl

theorem cell23_2123053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 1, 8].length) (baseStart_2123053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2123053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2123053 prefixEnd_2123053 := by exact prefixLift 2123053
  have htrace : WordTrace (prefixWord ++ tailWord_2123053) baseStart_2123053 baseEnd_2123053 := by
    simpa [prefixWord, tailWord_2123053, baseEnd_2123053] using wordTrace_append hprefix tailTrace_2123053
  have hstable : (prefixWord ++ tailWord_2123053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2123053).length < 2 ^ (prefixWord ++ tailWord_2123053).sum := by decide
  have hdescent : baseEnd_2123053 < baseStart_2123053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2123053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2123057 : List Nat := [1, 2, 2, 3, 3, 2, 3, 2, 1, 4]
def baseStart_2123057 : Nat := 118140960795 + 2123057 * 2 ^ 59
def prefixEnd_2123057 : Nat := 4983230072969 + 3 ^ 40 * 2123057 * 2
def baseEnd_2123057 : Nat := 363382899297535087807915

theorem tailTrace_2123057 : CollatzResearch.WordTrace tailWord_2123057 prefixEnd_2123057 363382899297535087807915 := by
  unfold tailWord_2123057
  simp only [CollatzResearch.WordTrace]
  refine ⟨77434250269534553113503425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51622833513023035409002283 77434250269534553113503425)
  ·
    refine ⟨58075687702150914835127569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77434250269534553113503425 58075687702150914835127569)
    ·
      refine ⟨43556765776613186126345677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58075687702150914835127569 43556765776613186126345677)
      ·
        refine ⟨16333787166229944797379629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43556765776613186126345677 16333787166229944797379629)
        ·
          refine ⟨6125170187336229299017361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16333787166229944797379629 6125170187336229299017361)
          ·
            refine ⟨4593877640502171974263021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6125170187336229299017361 4593877640502171974263021)
            ·
              refine ⟨1722704115188314490348633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4593877640502171974263021 1722704115188314490348633)
              ·
                refine ⟨1292028086391235867761475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1722704115188314490348633 1292028086391235867761475)
                ·
                  refine ⟨1938042129586853801642213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1292028086391235867761475 1938042129586853801642213)
                  ·
                    refine ⟨363382899297535087807915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1938042129586853801642213 363382899297535087807915)
                    ·
                      rfl

theorem cell23_2123057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 3, 2, 1, 4].length) (baseStart_2123057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2123057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2123057 prefixEnd_2123057 := by exact prefixLift 2123057
  have htrace : WordTrace (prefixWord ++ tailWord_2123057) baseStart_2123057 baseEnd_2123057 := by
    simpa [prefixWord, tailWord_2123057, baseEnd_2123057] using wordTrace_append hprefix tailTrace_2123057
  have hstable : (prefixWord ++ tailWord_2123057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2123057).length < 2 ^ (prefixWord ++ tailWord_2123057).sum := by decide
  have hdescent : baseEnd_2123057 < baseStart_2123057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2123057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2123066 : List Nat := [3, 1, 1, 1, 4, 1, 2, 2, 3, 5]
def baseStart_2123066 : Nat := 118140960795 + 2123066 * 2 ^ 59
def prefixEnd_2123066 : Nat := 4983230072969 + 3 ^ 40 * 2123066 * 2
def baseEnd_2123066 : Nat := 363384439739498576070401

theorem tailTrace_2123066 : CollatzResearch.WordTrace tailWord_2123066 prefixEnd_2123066 363384439739498576070401 := by
  unfold tailWord_2123066
  simp only [CollatzResearch.WordTrace]
  refine ⟨19358644631625486912645263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51623052351001298433720701 19358644631625486912645263)
  ·
    refine ⟨29037966947438230368967895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19358644631625486912645263 29037966947438230368967895)
    ·
      refine ⟨43556950421157345553451843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29037966947438230368967895 43556950421157345553451843)
      ·
        refine ⟨65335425631736018330177765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43556950421157345553451843 65335425631736018330177765)
        ·
          refine ⟨12250392305950503436908331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65335425631736018330177765 12250392305950503436908331)
          ·
            refine ⟨18375588458925755155362497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12250392305950503436908331 18375588458925755155362497)
            ·
              refine ⟨13781691344194316366521873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18375588458925755155362497 13781691344194316366521873)
              ·
                refine ⟨10336268508145737274891405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13781691344194316366521873 10336268508145737274891405)
                ·
                  refine ⟨3876100690554651478084277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10336268508145737274891405 3876100690554651478084277)
                  ·
                    refine ⟨363384439739498576070401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3876100690554651478084277 363384439739498576070401)
                    ·
                      rfl

theorem cell23_2123066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 2, 3, 5].length) (baseStart_2123066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2123066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2123066 prefixEnd_2123066 := by exact prefixLift 2123066
  have htrace : WordTrace (prefixWord ++ tailWord_2123066) baseStart_2123066 baseEnd_2123066 := by
    simpa [prefixWord, tailWord_2123066, baseEnd_2123066] using wordTrace_append hprefix tailTrace_2123066
  have hstable : (prefixWord ++ tailWord_2123066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2123066).length < 2 ^ (prefixWord ++ tailWord_2123066).sum := by decide
  have hdescent : baseEnd_2123066 < baseStart_2123066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2123066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2123096 : List Nat := [2, 1, 2, 2, 1, 1, 5, 2, 1, 6]
def baseStart_2123096 : Nat := 118140960795 + 2123096 * 2 ^ 59
def prefixEnd_2123096 : Nat := 4983230072969 + 3 ^ 40 * 2123096 * 2
def baseEnd_2123096 : Nat := 363389574546043536945355

theorem tailTrace_2123096 : CollatzResearch.WordTrace tailWord_2123096 prefixEnd_2123096 363389574546043536945355 := by
  unfold tailWord_2123096
  simp only [CollatzResearch.WordTrace]
  refine ⟨38717836358196631387086571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51623781810928841849448761 38717836358196631387086571)
  ·
    refine ⟨58076754537294947080629857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38717836358196631387086571 58076754537294947080629857)
    ·
      refine ⟨43557565902971210310472393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58076754537294947080629857 43557565902971210310472393)
      ·
        refine ⟨32668174427228407732854295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43557565902971210310472393 32668174427228407732854295)
        ·
          refine ⟨49002261640842611599281443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32668174427228407732854295 49002261640842611599281443)
          ·
            refine ⟨73503392461263917398922165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49002261640842611599281443 73503392461263917398922165)
            ·
              refine ⟨6890943043243492256148953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 73503392461263917398922165 6890943043243492256148953)
              ·
                refine ⟨5168207282432619192111715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6890943043243492256148953 5168207282432619192111715)
                ·
                  refine ⟨7752310923648928788167573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5168207282432619192111715 7752310923648928788167573)
                  ·
                    refine ⟨363389574546043536945355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7752310923648928788167573 363389574546043536945355)
                    ·
                      rfl

theorem cell23_2123096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 2, 1, 6].length) (baseStart_2123096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2123096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2123096 prefixEnd_2123096 := by exact prefixLift 2123096
  have htrace : WordTrace (prefixWord ++ tailWord_2123096) baseStart_2123096 baseEnd_2123096 := by
    simpa [prefixWord, tailWord_2123096, baseEnd_2123096] using wordTrace_append hprefix tailTrace_2123096
  have hstable : (prefixWord ++ tailWord_2123096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2123096).length < 2 ^ (prefixWord ++ tailWord_2123096).sum := by decide
  have hdescent : baseEnd_2123096 < baseStart_2123096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2123096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2123099 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 12]
def baseStart_2123099 : Nat := 118140960795 + 2123099 * 2 ^ 59
def prefixEnd_2123099 : Nat := 4983230072969 + 3 ^ 40 * 2123099 * 2
def baseEnd_2123099 : Nat := 1090170264080094099098551

theorem tailTrace_2123099 : CollatzResearch.WordTrace tailWord_2123099 prefixEnd_2123099 1090170264080094099098551 := by
  unfold tailWord_2123099
  simp only [CollatzResearch.WordTrace]
  refine ⟨77435782135382394286532351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51623854756921596191021567 77435782135382394286532351)
  ·
    refine ⟨116153673203073591429798527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77435782135382394286532351 116153673203073591429798527)
    ·
      refine ⟨174230509804610387144697791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116153673203073591429798527 174230509804610387144697791)
      ·
        refine ⟨261345764706915580717046687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174230509804610387144697791 261345764706915580717046687)
        ·
          refine ⟨392018647060373371075570031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 261345764706915580717046687 392018647060373371075570031)
          ·
            refine ⟨588027970590560056613355047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 392018647060373371075570031 588027970590560056613355047)
            ·
              refine ⟨882041955885840084920032571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 588027970590560056613355047 882041955885840084920032571)
              ·
                refine ⟨1323062933828760127380048857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 882041955885840084920032571 1323062933828760127380048857)
                ·
                  refine ⟨992297200371570095535036643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1323062933828760127380048857 992297200371570095535036643)
                  ·
                    refine ⟨1488445800557355143302554965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 992297200371570095535036643 1488445800557355143302554965)
                    ·
                      refine ⟨1090170264080094099098551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 12 1488445800557355143302554965 1090170264080094099098551)
                      ·
                        rfl

theorem cell23_2123099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 12].length) (baseStart_2123099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2123099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2123099 prefixEnd_2123099 := by exact prefixLift 2123099
  have htrace : WordTrace (prefixWord ++ tailWord_2123099) baseStart_2123099 baseEnd_2123099 := by
    simpa [prefixWord, tailWord_2123099, baseEnd_2123099] using wordTrace_append hprefix tailTrace_2123099
  have hstable : (prefixWord ++ tailWord_2123099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2123099).length < 2 ^ (prefixWord ++ tailWord_2123099).sum := by decide
  have hdescent : baseEnd_2123099 < baseStart_2123099 := by decide
  rcases family_descends (prefixWord ++ tailWord_2123099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2123114 : List Nat := [3, 1, 3, 3, 2, 1, 1, 4, 1, 1, 3]
def baseStart_2123114 : Nat := 118140960795 + 2123114 * 2 ^ 59
def prefixEnd_2123114 : Nat := 4983230072969 + 3 ^ 40 * 2123114 * 2
def baseEnd_2123114 : Nat := 1090177966289911540410983

theorem tailTrace_2123114 : CollatzResearch.WordTrace tailWord_2123114 prefixEnd_2123114 1090177966289911540410983 := by
  unfold tailWord_2123114
  simp only [CollatzResearch.WordTrace]
  refine ⟨19359082307582012962082099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51624219486885367898885597 19359082307582012962082099)
  ·
    refine ⟨29038623461373019443123149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19359082307582012962082099 29038623461373019443123149)
    ·
      refine ⟨10889483798014882291171181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29038623461373019443123149 10889483798014882291171181)
      ·
        refine ⟨4083556424255580859189193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10889483798014882291171181 4083556424255580859189193)
        ·
          refine ⟨3062667318191685644391895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4083556424255580859189193 3062667318191685644391895)
          ·
            refine ⟨4594000977287528466587843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3062667318191685644391895 4594000977287528466587843)
            ·
              refine ⟨6891001465931292699881765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4594000977287528466587843 6891001465931292699881765)
              ·
                refine ⟨1292062774862117381227831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6891001465931292699881765 1292062774862117381227831)
                ·
                  refine ⟨1938094162293176071841747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1292062774862117381227831 1938094162293176071841747)
                  ·
                    refine ⟨2907141243439764107762621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1938094162293176071841747 2907141243439764107762621)
                    ·
                      refine ⟨1090177966289911540410983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2907141243439764107762621 1090177966289911540410983)
                      ·
                        rfl

theorem cell23_2123114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_2123114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2123114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2123114 prefixEnd_2123114 := by exact prefixLift 2123114
  have htrace : WordTrace (prefixWord ++ tailWord_2123114) baseStart_2123114 baseEnd_2123114 := by
    simpa [prefixWord, tailWord_2123114, baseEnd_2123114] using wordTrace_append hprefix tailTrace_2123114
  have hstable : (prefixWord ++ tailWord_2123114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2123114).length < 2 ^ (prefixWord ++ tailWord_2123114).sum := by decide
  have hdescent : baseEnd_2123114 < baseStart_2123114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2123114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2123120 : List Nat := [2, 1, 1, 1, 4, 2, 2, 3, 3, 2, 2]
def baseStart_2123120 : Nat := 118140960795 + 2123120 * 2 ^ 59
def prefixEnd_2123120 : Nat := 4983230072969 + 3 ^ 40 * 2123120 * 2
def baseEnd_2123120 : Nat := 1090181047173838516935955

theorem tailTrace_2123120 : CollatzResearch.WordTrace tailWord_2123120 prefixEnd_2123120 1090181047173838516935955 := by
  unfold tailWord_2123120
  simp only [CollatzResearch.WordTrace]
  refine ⟨38718274034153157436523407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51624365378870876582031209 38718274034153157436523407)
  ·
    refine ⟨58077411051229736154785111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38718274034153157436523407 58077411051229736154785111)
    ·
      refine ⟨87116116576844604232177667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58077411051229736154785111 87116116576844604232177667)
      ·
        refine ⟨130674174865266906348266501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87116116576844604232177667 130674174865266906348266501)
        ·
          refine ⟨24501407787237544940299969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 130674174865266906348266501 24501407787237544940299969)
          ·
            refine ⟨18376055840428158705224977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24501407787237544940299969 18376055840428158705224977)
            ·
              refine ⟨13782041880321119028918733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18376055840428158705224977 13782041880321119028918733)
              ·
                refine ⟨5168265705120419635844525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13782041880321119028918733 5168265705120419635844525)
                ·
                  refine ⟨1938099639420157363441697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5168265705120419635844525 1938099639420157363441697)
                  ·
                    refine ⟨1453574729565118022581273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1938099639420157363441697 1453574729565118022581273)
                    ·
                      refine ⟨1090181047173838516935955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1453574729565118022581273 1090181047173838516935955)
                      ·
                        rfl

theorem cell23_2123120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 3, 3, 2, 2].length) (baseStart_2123120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2123120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2123120 prefixEnd_2123120 := by exact prefixLift 2123120
  have htrace : WordTrace (prefixWord ++ tailWord_2123120) baseStart_2123120 baseEnd_2123120 := by
    simpa [prefixWord, tailWord_2123120, baseEnd_2123120] using wordTrace_append hprefix tailTrace_2123120
  have hstable : (prefixWord ++ tailWord_2123120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2123120).length < 2 ^ (prefixWord ++ tailWord_2123120).sum := by decide
  have hdescent : baseEnd_2123120 < baseStart_2123120 := by decide
  rcases family_descends (prefixWord ++ tailWord_2123120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2123133 : List Nat := [1, 4, 1, 1, 2, 2, 4, 1, 1, 2, 4]
def baseStart_2123133 : Nat := 118140960795 + 2123133 * 2 ^ 59
def prefixEnd_2123133 : Nat := 4983230072969 + 3 ^ 40 * 2123133 * 2
def baseEnd_2123133 : Nat := 1090187722422346966073395

theorem tailTrace_2123133 : CollatzResearch.WordTrace tailWord_2123133 prefixEnd_2123133 1090187722422346966073395 := by
  unfold tailWord_2123133
  simp only [CollatzResearch.WordTrace]
  refine ⟨77437022217259218093270053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51624681478172812062180035 77437022217259218093270053)
  ·
    refine ⟨14519441665736103392488135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77437022217259218093270053 14519441665736103392488135)
    ·
      refine ⟨21779162498604155088732203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14519441665736103392488135 21779162498604155088732203)
      ·
        refine ⟨32668743747906232633098305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21779162498604155088732203 32668743747906232633098305)
        ·
          refine ⟨24501557810929674474823729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32668743747906232633098305 24501557810929674474823729)
          ·
            refine ⟨18376168358197255856117797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24501557810929674474823729 18376168358197255856117797)
            ·
              refine ⟨3445531567161985473022087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18376168358197255856117797 3445531567161985473022087)
              ·
                refine ⟨5168297350742978209533131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3445531567161985473022087 5168297350742978209533131)
                ·
                  refine ⟨7752446026114467314299697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5168297350742978209533131 7752446026114467314299697)
                  ·
                    refine ⟨5814334519585850485724773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7752446026114467314299697 5814334519585850485724773)
                    ·
                      refine ⟨1090187722422346966073395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5814334519585850485724773 1090187722422346966073395)
                      ·
                        rfl

theorem cell23_2123133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 1, 1, 2, 4].length) (baseStart_2123133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2123133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2123133 prefixEnd_2123133 := by exact prefixLift 2123133
  have htrace : WordTrace (prefixWord ++ tailWord_2123133) baseStart_2123133 baseEnd_2123133 := by
    simpa [prefixWord, tailWord_2123133, baseEnd_2123133] using wordTrace_append hprefix tailTrace_2123133
  have hstable : (prefixWord ++ tailWord_2123133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2123133).length < 2 ^ (prefixWord ++ tailWord_2123133).sum := by decide
  have hdescent : baseEnd_2123133 < baseStart_2123133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2123133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2123143 : List Nat := [1, 1, 4, 2, 2, 3, 3, 7]
def baseStart_2123143 : Nat := 118140960795 + 2123143 * 2 ^ 59
def prefixEnd_2123143 : Nat := 4983230072969 + 3 ^ 40 * 2123143 * 2
def baseEnd_2123143 : Nat := 40377513230699700998087

theorem tailTrace_2123143 : CollatzResearch.WordTrace tailWord_2123143 prefixEnd_2123143 40377513230699700998087 := by
  unfold tailWord_2123143
  simp only [CollatzResearch.WordTrace]
  refine ⟨77437386947222989801134083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51624924631481993200756055 77437386947222989801134083)
  ·
    refine ⟨116156080420834484701701125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77437386947222989801134083 116156080420834484701701125)
    ·
      refine ⟨21779265078906465881568961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 116156080420834484701701125 21779265078906465881568961)
      ·
        refine ⟨16334448809179849411176721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21779265078906465881568961 16334448809179849411176721)
        ·
          refine ⟨12250836606884887058382541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16334448809179849411176721 12250836606884887058382541)
          ·
            refine ⟨4594063727581832646893453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12250836606884887058382541 4594063727581832646893453)
            ·
              refine ⟨1722773897843187242585045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4594063727581832646893453 1722773897843187242585045)
              ·
                refine ⟨40377513230699700998087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1722773897843187242585045 40377513230699700998087)
                ·
                  rfl

theorem cell23_2123143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 3, 7].length) (baseStart_2123143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2123143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2123143 prefixEnd_2123143 := by exact prefixLift 2123143
  have htrace : WordTrace (prefixWord ++ tailWord_2123143) baseStart_2123143 baseEnd_2123143 := by
    simpa [prefixWord, tailWord_2123143, baseEnd_2123143] using wordTrace_append hprefix tailTrace_2123143
  have hstable : (prefixWord ++ tailWord_2123143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2123143).length < 2 ^ (prefixWord ++ tailWord_2123143).sum := by decide
  have hdescent : baseEnd_2123143 < baseStart_2123143 := by decide
  rcases family_descends (prefixWord ++ tailWord_2123143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2123153 : List Nat := [1, 2, 2, 1, 1, 1, 2, 3, 6, 1, 3]
def baseStart_2123153 : Nat := 118140960795 + 2123153 * 2 ^ 59
def prefixEnd_2123153 : Nat := 4983230072969 + 3 ^ 40 * 2123153 * 2
def baseEnd_2123153 : Nat := 1090197992035436887823303

theorem tailTrace_2123153 : CollatzResearch.WordTrace tailWord_2123153 prefixEnd_2123153 1090197992035436887823303 := by
  unfold tailWord_2123153
  simp only [CollatzResearch.WordTrace]
  refine ⟨77437751677186761508998113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51625167784791174339332075 77437751677186761508998113)
  ·
    refine ⟨58078313757890071131748585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77437751677186761508998113 58078313757890071131748585)
    ·
      refine ⟨43558735318417553348811439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58078313757890071131748585 43558735318417553348811439)
      ·
        refine ⟨65338102977626330023217159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43558735318417553348811439 65338102977626330023217159)
        ·
          refine ⟨98007154466439495034825739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65338102977626330023217159 98007154466439495034825739)
          ·
            refine ⟨147010731699659242552238609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98007154466439495034825739 147010731699659242552238609)
            ·
              refine ⟨110258048774744431914178957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 147010731699659242552238609 110258048774744431914178957)
              ·
                refine ⟨41346768290529161967817109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 110258048774744431914178957 41346768290529161967817109)
                ·
                  refine ⟨1938129763618554467241427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 41346768290529161967817109 1938129763618554467241427)
                  ·
                    refine ⟨2907194645427831700862141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1938129763618554467241427 2907194645427831700862141)
                    ·
                      refine ⟨1090197992035436887823303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2907194645427831700862141 1090197992035436887823303)
                      ·
                        rfl

theorem cell23_2123153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 6, 1, 3].length) (baseStart_2123153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2123153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2123153 prefixEnd_2123153 := by exact prefixLift 2123153
  have htrace : WordTrace (prefixWord ++ tailWord_2123153) baseStart_2123153 baseEnd_2123153 := by
    simpa [prefixWord, tailWord_2123153, baseEnd_2123153] using wordTrace_append hprefix tailTrace_2123153
  have hstable : (prefixWord ++ tailWord_2123153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2123153).length < 2 ^ (prefixWord ++ tailWord_2123153).sum := by decide
  have hdescent : baseEnd_2123153 < baseStart_2123153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2123153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2123164 : List Nat := [2, 2, 3, 4, 1, 2, 1, 2, 2, 4]
def baseStart_2123164 : Nat := 118140960795 + 2123164 * 2 ^ 59
def prefixEnd_2123164 : Nat := 4983230072969 + 3 ^ 40 * 2123164 * 2
def baseEnd_2123164 : Nat := 363401213440878781595251

theorem tailTrace_2123164 : CollatzResearch.WordTrace tailWord_2123164 prefixEnd_2123164 363401213440878781595251 := by
  unfold tailWord_2123164
  simp only [CollatzResearch.WordTrace]
  refine ⟨38719076440073455193824273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51625435253431273591765697 38719076440073455193824273)
  ·
    refine ⟨29039307330055091395368205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38719076440073455193824273 29039307330055091395368205)
    ·
      refine ⟨10889740248770659273263077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29039307330055091395368205 10889740248770659273263077)
      ·
        refine ⟨2041826296644498613736827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10889740248770659273263077 2041826296644498613736827)
        ·
          refine ⟨3062739444966747920605241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2041826296644498613736827 3062739444966747920605241)
          ·
            refine ⟨2297054583725060940453931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3062739444966747920605241 2297054583725060940453931)
            ·
              refine ⟨3445581875587591410680897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2297054583725060940453931 3445581875587591410680897)
              ·
                refine ⟨2584186406690693558010673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3445581875587591410680897 2584186406690693558010673)
                ·
                  refine ⟨1938139805018020168508005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2584186406690693558010673 1938139805018020168508005)
                  ·
                    refine ⟨363401213440878781595251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1938139805018020168508005 363401213440878781595251)
                    ·
                      rfl

theorem cell23_2123164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 2, 2, 4].length) (baseStart_2123164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2123164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2123164 prefixEnd_2123164 := by exact prefixLift 2123164
  have htrace : WordTrace (prefixWord ++ tailWord_2123164) baseStart_2123164 baseEnd_2123164 := by
    simpa [prefixWord, tailWord_2123164, baseEnd_2123164] using wordTrace_append hprefix tailTrace_2123164
  have hstable : (prefixWord ++ tailWord_2123164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2123164).length < 2 ^ (prefixWord ++ tailWord_2123164).sum := by decide
  have hdescent : baseEnd_2123164 < baseStart_2123164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2123164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2123186 : List Nat := [3, 2, 1, 1, 1, 1, 2, 3, 1, 8]
def baseStart_2123186 : Nat := 118140960795 + 2123186 * 2 ^ 59
def prefixEnd_2123186 : Nat := 4983230072969 + 3 ^ 40 * 2123186 * 2
def baseEnd_2123186 : Nat := 363404978965678419570217

theorem tailTrace_2123186 : CollatzResearch.WordTrace tailWord_2123186 prefixEnd_2123186 363404978965678419570217 := by
  unfold tailWord_2123186
  simp only [CollatzResearch.WordTrace]
  refine ⟨19359738821516802036237353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51625970190711472096632941 19359738821516802036237353)
  ·
    refine ⟨14519804116137601527178015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19359738821516802036237353 14519804116137601527178015)
    ·
      refine ⟨21779706174206402290767023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14519804116137601527178015 21779706174206402290767023)
      ·
        refine ⟨32669559261309603436150535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21779706174206402290767023 32669559261309603436150535)
        ·
          refine ⟨49004338891964405154225803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32669559261309603436150535 49004338891964405154225803)
          ·
            refine ⟨73506508337946607731338705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49004338891964405154225803 73506508337946607731338705)
            ·
              refine ⟨55129881253459955798504029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73506508337946607731338705 55129881253459955798504029)
              ·
                refine ⟨20673705470047483424439011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55129881253459955798504029 20673705470047483424439011)
                ·
                  refine ⟨31010558205071225136658517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20673705470047483424439011 31010558205071225136658517)
                  ·
                    refine ⟨363404978965678419570217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 31010558205071225136658517 363404978965678419570217)
                    ·
                      rfl

theorem cell23_2123186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 1, 8].length) (baseStart_2123186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2123186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2123186 prefixEnd_2123186 := by exact prefixLift 2123186
  have htrace : WordTrace (prefixWord ++ tailWord_2123186) baseStart_2123186 baseEnd_2123186 := by
    simpa [prefixWord, tailWord_2123186, baseEnd_2123186] using wordTrace_append hprefix tailTrace_2123186
  have hstable : (prefixWord ++ tailWord_2123186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2123186).length < 2 ^ (prefixWord ++ tailWord_2123186).sum := by decide
  have hdescent : baseEnd_2123186 < baseStart_2123186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2123186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2123197 : List Nat := [1, 4, 1, 2, 2, 1, 4, 2, 1, 3, 2]
def baseStart_2123197 : Nat := 118140960795 + 2123197 * 2 ^ 59
def prefixEnd_2123197 : Nat := 4983230072969 + 3 ^ 40 * 2123197 * 2
def baseEnd_2123197 : Nat := 1090220585184234715673101

theorem tailTrace_2123197 : CollatzResearch.WordTrace tailWord_2123197 prefixEnd_2123197 1090220585184234715673101 := by
  unfold tailWord_2123197
  simp only [CollatzResearch.WordTrace]
  refine ⟨77439356489027357023599845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51626237659351571349066563 77439356489027357023599845)
  ·
    refine ⟨14519879341692629441924971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77439356489027357023599845 14519879341692629441924971)
    ·
      refine ⟨21779819012538944162887457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14519879341692629441924971 21779819012538944162887457)
      ·
        refine ⟨16334864259404208122165593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21779819012538944162887457 16334864259404208122165593)
        ·
          refine ⟨12251148194553156091624195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16334864259404208122165593 12251148194553156091624195)
          ·
            refine ⟨18376722291829734137436293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12251148194553156091624195 18376722291829734137436293)
            ·
              refine ⟨3445635429718075150769305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18376722291829734137436293 3445635429718075150769305)
              ·
                refine ⟨2584226572288556363076979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3445635429718075150769305 2584226572288556363076979)
                ·
                  refine ⟨3876339858432834544615469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2584226572288556363076979 3876339858432834544615469)
                  ·
                    refine ⟨1453627446912312954230801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3876339858432834544615469 1453627446912312954230801)
                    ·
                      refine ⟨1090220585184234715673101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1453627446912312954230801 1090220585184234715673101)
                      ·
                        rfl

theorem cell23_2123197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 2, 1, 3, 2].length) (baseStart_2123197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2123197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2123197 prefixEnd_2123197 := by exact prefixLift 2123197
  have htrace : WordTrace (prefixWord ++ tailWord_2123197) baseStart_2123197 baseEnd_2123197 := by
    simpa [prefixWord, tailWord_2123197, baseEnd_2123197] using wordTrace_append hprefix tailTrace_2123197
  have hstable : (prefixWord ++ tailWord_2123197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2123197).length < 2 ^ (prefixWord ++ tailWord_2123197).sum := by decide
  have hdescent : baseEnd_2123197 < baseStart_2123197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2123197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2123233 : List Nat := [1, 2, 3, 1, 2, 3, 3, 1, 7]
def baseStart_2123233 : Nat := 118140960795 + 2123233 * 2 ^ 59
def prefixEnd_2123233 : Nat := 4983230072969 + 3 ^ 40 * 2123233 * 2
def baseEnd_2123233 : Nat := 121137674498644063869215

theorem tailTrace_2123233 : CollatzResearch.WordTrace tailWord_2123233 prefixEnd_2123233 121137674498644063869215 := by
  unfold tailWord_2123233
  simp only [CollatzResearch.WordTrace]
  refine ⟨77440669516896935171910353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51627113011264623447940235 77440669516896935171910353)
  ·
    refine ⟨58080502137672701378932765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77440669516896935171910353 58080502137672701378932765)
    ·
      refine ⟨21780188301627263017099787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58080502137672701378932765 21780188301627263017099787)
      ·
        refine ⟨32670282452440894525649681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21780188301627263017099787 32670282452440894525649681)
        ·
          refine ⟨24502711839330670894237261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32670282452440894525649681 24502711839330670894237261)
          ·
            refine ⟨9188516939749001585338973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24502711839330670894237261 9188516939749001585338973)
            ·
              refine ⟨3445693852405875594502115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9188516939749001585338973 3445693852405875594502115)
              ·
                refine ⟨5168540778608813391753173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3445693852405875594502115 5168540778608813391753173)
                ·
                  refine ⟨121137674498644063869215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5168540778608813391753173 121137674498644063869215)
                  ·
                    rfl

theorem cell23_2123233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 1, 7].length) (baseStart_2123233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2123233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2123233 prefixEnd_2123233 := by exact prefixLift 2123233
  have htrace : WordTrace (prefixWord ++ tailWord_2123233) baseStart_2123233 baseEnd_2123233 := by
    simpa [prefixWord, tailWord_2123233, baseEnd_2123233] using wordTrace_append hprefix tailTrace_2123233
  have hstable : (prefixWord ++ tailWord_2123233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2123233).length < 2 ^ (prefixWord ++ tailWord_2123233).sum := by decide
  have hdescent : baseEnd_2123233 < baseStart_2123233 := by decide
  rcases family_descends (prefixWord ++ tailWord_2123233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2123284 : List Nat := [2, 4, 3, 1, 2, 1, 1, 4, 5]
def baseStart_2123284 : Nat := 118140960795 + 2123284 * 2 ^ 59
def prefixEnd_2123284 : Nat := 4983230072969 + 3 ^ 40 * 2123284 * 2
def baseEnd_2123284 : Nat := 121140584222352875031689

theorem tailTrace_2123284 : CollatzResearch.WordTrace tailWord_2123284 prefixEnd_2123284 121140584222352875031689 := by
  unfold tailWord_2123284
  simp only [CollatzResearch.WordTrace]
  refine ⟨38721264819856085441008453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51628353093141447254677937 38721264819856085441008453)
  ·
    refine ⟨7260237153723016020189085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38721264819856085441008453 7260237153723016020189085)
    ·
      refine ⟨2722588932646131007570907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7260237153723016020189085 2722588932646131007570907)
      ·
        refine ⟨4083883398969196511356361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2722588932646131007570907 4083883398969196511356361)
        ·
          refine ⟨3062912549226897383517271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4083883398969196511356361 3062912549226897383517271)
          ·
            refine ⟨4594368823840346075275907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3062912549226897383517271 4594368823840346075275907)
            ·
              refine ⟨6891553235760519112913861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4594368823840346075275907 6891553235760519112913861)
              ·
                refine ⟨1292166231705097333671349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6891553235760519112913861 1292166231705097333671349)
                ·
                  refine ⟨121140584222352875031689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1292166231705097333671349 121140584222352875031689)
                  ·
                    rfl

theorem cell23_2123284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 4, 5].length) (baseStart_2123284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2123284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2123284 prefixEnd_2123284 := by exact prefixLift 2123284
  have htrace : WordTrace (prefixWord ++ tailWord_2123284) baseStart_2123284 baseEnd_2123284 := by
    simpa [prefixWord, tailWord_2123284, baseEnd_2123284] using wordTrace_append hprefix tailTrace_2123284
  have hstable : (prefixWord ++ tailWord_2123284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2123284).length < 2 ^ (prefixWord ++ tailWord_2123284).sum := by decide
  have hdescent : baseEnd_2123284 < baseStart_2123284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2123284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2123317 : List Nat := [1, 3, 3, 1, 1, 5, 1, 1, 2, 1, 4]
def baseStart_2123317 : Nat := 118140960795 + 2123317 * 2 ^ 59
def prefixEnd_2123317 : Nat := 4983230072969 + 3 ^ 40 * 2123317 * 2
def baseEnd_2123317 : Nat := 1090282202862774246172549

theorem tailTrace_2123317 : CollatzResearch.WordTrace tailWord_2123317 prefixEnd_2123317 1090282202862774246172549 := by
  unfold tailWord_2123317
  simp only [CollatzResearch.WordTrace]
  refine ⟨77443733248592617517968205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51629155499061745011978803 77443733248592617517968205)
  ·
    refine ⟨29041399968222231569238077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77443733248592617517968205 29041399968222231569238077)
    ·
      refine ⟨10890524988083336838464279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29041399968222231569238077 10890524988083336838464279)
      ·
        refine ⟨16335787482125005257696419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10890524988083336838464279 16335787482125005257696419)
        ·
          refine ⟨24503681223187507886544629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16335787482125005257696419 24503681223187507886544629)
          ·
            refine ⟨2297220114673828864363559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24503681223187507886544629 2297220114673828864363559)
            ·
              refine ⟨3445830172010743296545339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2297220114673828864363559 3445830172010743296545339)
              ·
                refine ⟨5168745258016114944818009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3445830172010743296545339 5168745258016114944818009)
                ·
                  refine ⟨3876558943512086208613507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5168745258016114944818009 3876558943512086208613507)
                  ·
                    refine ⟨5814838415268129312920261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3876558943512086208613507 5814838415268129312920261)
                    ·
                      refine ⟨1090282202862774246172549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5814838415268129312920261 1090282202862774246172549)
                      ·
                        rfl

theorem cell23_2123317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 1, 2, 1, 4].length) (baseStart_2123317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2123317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2123317 prefixEnd_2123317 := by exact prefixLift 2123317
  have htrace : WordTrace (prefixWord ++ tailWord_2123317) baseStart_2123317 baseEnd_2123317 := by
    simpa [prefixWord, tailWord_2123317, baseEnd_2123317] using wordTrace_append hprefix tailTrace_2123317
  have hstable : (prefixWord ++ tailWord_2123317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2123317).length < 2 ^ (prefixWord ++ tailWord_2123317).sum := by decide
  have hdescent : baseEnd_2123317 < baseStart_2123317 := by decide
  rcases family_descends (prefixWord ++ tailWord_2123317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2123320 : List Nat := [2, 1, 2, 1, 4, 3, 1, 1, 1, 4, 3]
def baseStart_2123320 : Nat := 118140960795 + 2123320 * 2 ^ 59
def prefixEnd_2123320 : Nat := 4983230072969 + 3 ^ 40 * 2123320 * 2
def baseEnd_2123320 : Nat := 1090283743304737734435035

theorem tailTrace_2123320 : CollatzResearch.WordTrace tailWord_2123320 prefixEnd_2123320 1090283743304737734435035 := by
  unfold tailWord_2123320
  simp only [CollatzResearch.WordTrace]
  refine ⟨38721921333790874515163707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51629228445054499353551609 38721921333790874515163707)
  ·
    refine ⟨58082882000686311772745561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38721921333790874515163707 58082882000686311772745561)
    ·
      refine ⟨43562161500514733829559171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58082882000686311772745561 43562161500514733829559171)
      ·
        refine ⟨65343242250772100744338757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43562161500514733829559171 65343242250772100744338757)
        ·
          refine ⟨12251857922019768889563517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65343242250772100744338757 12251857922019768889563517)
          ·
            refine ⟨4594446720757413333586319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12251857922019768889563517 4594446720757413333586319)
            ·
              refine ⟨6891670081136120000379479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4594446720757413333586319 6891670081136120000379479)
              ·
                refine ⟨10337505121704180000569219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6891670081136120000379479 10337505121704180000569219)
                ·
                  refine ⟨15506257682556270000853829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10337505121704180000569219 15506257682556270000853829)
                  ·
                    refine ⟨2907423315479300625160093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15506257682556270000853829 2907423315479300625160093)
                    ·
                      refine ⟨1090283743304737734435035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2907423315479300625160093 1090283743304737734435035)
                      ·
                        rfl

theorem cell23_2123320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 1, 1, 4, 3].length) (baseStart_2123320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2123320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2123320 prefixEnd_2123320 := by exact prefixLift 2123320
  have htrace : WordTrace (prefixWord ++ tailWord_2123320) baseStart_2123320 baseEnd_2123320 := by
    simpa [prefixWord, tailWord_2123320, baseEnd_2123320] using wordTrace_append hprefix tailTrace_2123320
  have hstable : (prefixWord ++ tailWord_2123320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2123320).length < 2 ^ (prefixWord ++ tailWord_2123320).sum := by decide
  have hdescent : baseEnd_2123320 < baseStart_2123320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2123320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2123327 : List Nat := [1, 1, 2, 2, 3, 3, 1, 5, 1, 4]
def baseStart_2123327 : Nat := 118140960795 + 2123327 * 2 ^ 59
def prefixEnd_2123327 : Nat := 4983230072969 + 3 ^ 40 * 2123327 * 2
def baseEnd_2123327 : Nat := 363429112556439735682501

theorem tailTrace_2123327 : CollatzResearch.WordTrace tailWord_2123327 prefixEnd_2123327 363429112556439735682501 := by
  unfold tailWord_2123327
  simp only [CollatzResearch.WordTrace]
  refine ⟨77444097978556389225832235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51629398652370926150554823 77444097978556389225832235)
  ·
    refine ⟨116166146967834583838748353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77444097978556389225832235 116166146967834583838748353)
    ·
      refine ⟨87124610225875937879061265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116166146967834583838748353 87124610225875937879061265)
      ·
        refine ⟨65343457669406953409295949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87124610225875937879061265 65343457669406953409295949)
        ·
          refine ⟨24503796626027607528485981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65343457669406953409295949 24503796626027607528485981)
          ·
            refine ⟨9188923734760352823182243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24503796626027607528485981 9188923734760352823182243)
            ·
              refine ⟨13783385602140529234773365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9188923734760352823182243 13783385602140529234773365)
              ·
                refine ⟨1292192400200674615760003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13783385602140529234773365 1292192400200674615760003)
                ·
                  refine ⟨1938288600301011923640005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1292192400200674615760003 1938288600301011923640005)
                  ·
                    refine ⟨363429112556439735682501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1938288600301011923640005 363429112556439735682501)
                    ·
                      rfl

theorem cell23_2123327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 5, 1, 4].length) (baseStart_2123327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2123327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2123327 prefixEnd_2123327 := by exact prefixLift 2123327
  have htrace : WordTrace (prefixWord ++ tailWord_2123327) baseStart_2123327 baseEnd_2123327 := by
    simpa [prefixWord, tailWord_2123327, baseEnd_2123327] using wordTrace_append hprefix tailTrace_2123327
  have hstable : (prefixWord ++ tailWord_2123327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2123327).length < 2 ^ (prefixWord ++ tailWord_2123327).sum := by decide
  have hdescent : baseEnd_2123327 < baseStart_2123327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2123327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2123340 : List Nat := [2, 2, 1, 3, 1, 3, 3, 2, 6]
def baseStart_2123340 : Nat := 118140960795 + 2123340 * 2 ^ 59
def prefixEnd_2123340 : Nat := 4983230072969 + 3 ^ 40 * 2123340 * 2
def baseEnd_2123340 : Nat := 121143779213091961798327

theorem tailTrace_2123340 : CollatzResearch.WordTrace tailWord_2123340 prefixEnd_2123340 121143779213091961798327 := by
  unfold tailWord_2123340
  simp only [CollatzResearch.WordTrace]
  refine ⟨38722286063754646223027737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51629714751672861630703649 38722286063754646223027737)
  ·
    refine ⟨29041714547815984667270803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38722286063754646223027737 29041714547815984667270803)
    ·
      refine ⟨43562571821723977000906205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29041714547815984667270803 43562571821723977000906205)
      ·
        refine ⟨16335964433146491375339827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43562571821723977000906205 16335964433146491375339827)
        ·
          refine ⟨24503946649719737063009741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16335964433146491375339827 24503946649719737063009741)
          ·
            refine ⟨9188979993644901398628653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24503946649719737063009741 9188979993644901398628653)
            ·
              refine ⟨3445867497616838024485745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9188979993644901398628653 3445867497616838024485745)
              ·
                refine ⟨2584400623212628518364309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3445867497616838024485745 2584400623212628518364309)
                ·
                  refine ⟨121143779213091961798327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2584400623212628518364309 121143779213091961798327)
                  ·
                    rfl

theorem cell23_2123340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 2, 6].length) (baseStart_2123340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2123340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2123340 prefixEnd_2123340 := by exact prefixLift 2123340
  have htrace : WordTrace (prefixWord ++ tailWord_2123340) baseStart_2123340 baseEnd_2123340 := by
    simpa [prefixWord, tailWord_2123340, baseEnd_2123340] using wordTrace_append hprefix tailTrace_2123340
  have hstable : (prefixWord ++ tailWord_2123340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2123340).length < 2 ^ (prefixWord ++ tailWord_2123340).sum := by decide
  have hdescent : baseEnd_2123340 < baseStart_2123340 := by decide
  rcases family_descends (prefixWord ++ tailWord_2123340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2123353 : List Nat := [1, 2, 1, 2, 2, 1, 1, 3, 5, 5]
def baseStart_2123353 : Nat := 118140960795 + 2123353 * 2 ^ 59
def prefixEnd_2123353 : Nat := 4983230072969 + 3 ^ 40 * 2123353 * 2
def baseEnd_2123353 : Nat := 363433562722112035107461

theorem tailTrace_2123353 : CollatzResearch.WordTrace tailWord_2123353 prefixEnd_2123353 363433562722112035107461 := by
  unfold tailWord_2123353
  simp only [CollatzResearch.WordTrace]
  refine ⟨77445046276462195666278713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51630030850974797110852475 77445046276462195666278713)
  ·
    refine ⟨58083784707346646749709035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77445046276462195666278713 58083784707346646749709035)
    ·
      refine ⟨87125677061019970124563553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58083784707346646749709035 87125677061019970124563553)
      ·
        refine ⟨65344257795764977593422665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87125677061019970124563553 65344257795764977593422665)
        ·
          refine ⟨49008193346823733195066999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65344257795764977593422665 49008193346823733195066999)
          ·
            refine ⟨73512290020235599792600499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49008193346823733195066999 73512290020235599792600499)
            ·
              refine ⟨110268435030353399688900749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73512290020235599792600499 110268435030353399688900749)
              ·
                refine ⟨41350663136382524883337781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 110268435030353399688900749 41350663136382524883337781)
                ·
                  refine ⟨3876624669035861707812917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41350663136382524883337781 3876624669035861707812917)
                  ·
                    refine ⟨363433562722112035107461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3876624669035861707812917 363433562722112035107461)
                    ·
                      rfl

theorem cell23_2123353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 5, 5].length) (baseStart_2123353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2123353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2123353 prefixEnd_2123353 := by exact prefixLift 2123353
  have htrace : WordTrace (prefixWord ++ tailWord_2123353) baseStart_2123353 baseEnd_2123353 := by
    simpa [prefixWord, tailWord_2123353, baseEnd_2123353] using wordTrace_append hprefix tailTrace_2123353
  have hstable : (prefixWord ++ tailWord_2123353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2123353).length < 2 ^ (prefixWord ++ tailWord_2123353).sum := by decide
  have hdescent : baseEnd_2123353 < baseStart_2123353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2123353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2123367 : List Nat := [1, 1, 5, 1, 1, 1, 4, 2, 3, 1, 3]
def baseStart_2123367 : Nat := 118140960795 + 2123367 * 2 ^ 59
def prefixEnd_2123367 : Nat := 4983230072969 + 3 ^ 40 * 2123367 * 2
def baseEnd_2123367 : Nat := 1090307876895499050547319

theorem tailTrace_2123367 : CollatzResearch.WordTrace tailWord_2123367 prefixEnd_2123367 1090307876895499050547319 := by
  unfold tailWord_2123367
  simp only [CollatzResearch.WordTrace]
  refine ⟨77445556898411476057288355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51630371265607650704858903 77445556898411476057288355)
  ·
    refine ⟨116168335347617214085932533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77445556898411476057288355 116168335347617214085932533)
    ·
      refine ⟨10890781438839113820556175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 116168335347617214085932533 10890781438839113820556175)
      ·
        refine ⟨16336172158258670730834263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10890781438839113820556175 16336172158258670730834263)
        ·
          refine ⟨24504258237388006096251395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16336172158258670730834263 24504258237388006096251395)
          ·
            refine ⟨36756387356082009144377093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24504258237388006096251395 36756387356082009144377093)
            ·
              refine ⟨6891822629265376714570705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36756387356082009144377093 6891822629265376714570705)
              ·
                refine ⟨5168866971949032535928029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6891822629265376714570705 5168866971949032535928029)
                ·
                  refine ⟨1938325114480887200973011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5168866971949032535928029 1938325114480887200973011)
                  ·
                    refine ⟨2907487671721330801459517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1938325114480887200973011 2907487671721330801459517)
                    ·
                      refine ⟨1090307876895499050547319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2907487671721330801459517 1090307876895499050547319)
                      ·
                        rfl

theorem cell23_2123367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 2, 3, 1, 3].length) (baseStart_2123367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2123367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2123367 prefixEnd_2123367 := by exact prefixLift 2123367
  have htrace : WordTrace (prefixWord ++ tailWord_2123367) baseStart_2123367 baseEnd_2123367 := by
    simpa [prefixWord, tailWord_2123367, baseEnd_2123367] using wordTrace_append hprefix tailTrace_2123367
  have hstable : (prefixWord ++ tailWord_2123367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2123367).length < 2 ^ (prefixWord ++ tailWord_2123367).sum := by decide
  have hdescent : baseEnd_2123367 < baseStart_2123367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2123367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2123383 : List Nat := [1, 1, 3, 1, 1, 3, 1, 3, 3, 6]
def baseStart_2123383 : Nat := 118140960795 + 2123383 * 2 ^ 59
def prefixEnd_2123383 : Nat := 4983230072969 + 3 ^ 40 * 2123383 * 2
def baseEnd_2123383 : Nat := 363438697528656995982415

theorem tailTrace_2123383 : CollatzResearch.WordTrace tailWord_2123383 prefixEnd_2123383 363438697528656995982415 := by
  unfold tailWord_2123383
  simp only [CollatzResearch.WordTrace]
  refine ⟨77446140466353510789870803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51630760310902340526580535 77446140466353510789870803)
  ·
    refine ⟨116169210699530266184806205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77446140466353510789870803 116169210699530266184806205)
    ·
      refine ⟨43563454012323849819302327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116169210699530266184806205 43563454012323849819302327)
      ·
        refine ⟨65345181018485774728953491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43563454012323849819302327 65345181018485774728953491)
        ·
          refine ⟨98017771527728662093430237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65345181018485774728953491 98017771527728662093430237)
          ·
            refine ⟨36756664322898248285036339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98017771527728662093430237 36756664322898248285036339)
            ·
              refine ⟨55134996484347372427554509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36756664322898248285036339 55134996484347372427554509)
              ·
                refine ⟨20675623681630264660332941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55134996484347372427554509 20675623681630264660332941)
                ·
                  refine ⟨7753358880611349247624853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20675623681630264660332941 7753358880611349247624853)
                  ·
                    refine ⟨363438697528656995982415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7753358880611349247624853 363438697528656995982415)
                    ·
                      rfl

theorem cell23_2123383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 3, 6].length) (baseStart_2123383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2123383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2123383 prefixEnd_2123383 := by exact prefixLift 2123383
  have htrace : WordTrace (prefixWord ++ tailWord_2123383) baseStart_2123383 baseEnd_2123383 := by
    simpa [prefixWord, tailWord_2123383, baseEnd_2123383] using wordTrace_append hprefix tailTrace_2123383
  have hstable : (prefixWord ++ tailWord_2123383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2123383).length < 2 ^ (prefixWord ++ tailWord_2123383).sum := by decide
  have hdescent : baseEnd_2123383 < baseStart_2123383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2123383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2123403 : List Nat := [1, 1, 1, 1, 4, 1, 3, 1, 3, 1, 6]
def baseStart_2123403 : Nat := 118140960795 + 2123403 * 2 ^ 59
def prefixEnd_2123403 : Nat := 4983230072969 + 3 ^ 40 * 2123403 * 2
def baseEnd_2123403 : Nat := 1090326362199060909697153

theorem tailTrace_2123403 : CollatzResearch.WordTrace tailWord_2123403 prefixEnd_2123403 1090326362199060909697153 := by
  unfold tailWord_2123403
  simp only [CollatzResearch.WordTrace]
  refine ⟨77446869926281054205598863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51631246617520702803732575 77446869926281054205598863)
  ·
    refine ⟨116170304889421581308398295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77446869926281054205598863 116170304889421581308398295)
    ·
      refine ⟨174255457334132371962597443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116170304889421581308398295 174255457334132371962597443)
      ·
        refine ⟨261383186001198557943896165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174255457334132371962597443 261383186001198557943896165)
        ·
          refine ⟨49009347375224729614480531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 261383186001198557943896165 49009347375224729614480531)
          ·
            refine ⟨73514021062837094421720797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49009347375224729614480531 73514021062837094421720797)
            ·
              refine ⟨27567757898563910408145299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73514021062837094421720797 27567757898563910408145299)
              ·
                refine ⟨41351636847845865612217949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27567757898563910408145299 41351636847845865612217949)
                ·
                  refine ⟨15506863817942199604581731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41351636847845865612217949 15506863817942199604581731)
                  ·
                    refine ⟨23260295726913299406872597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15506863817942199604581731 23260295726913299406872597)
                    ·
                      refine ⟨1090326362199060909697153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23260295726913299406872597 1090326362199060909697153)
                      ·
                        rfl

theorem cell23_2123403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 3, 1, 6].length) (baseStart_2123403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2123403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2123403 prefixEnd_2123403 := by exact prefixLift 2123403
  have htrace : WordTrace (prefixWord ++ tailWord_2123403) baseStart_2123403 baseEnd_2123403 := by
    simpa [prefixWord, tailWord_2123403, baseEnd_2123403] using wordTrace_append hprefix tailTrace_2123403
  have hstable : (prefixWord ++ tailWord_2123403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2123403).length < 2 ^ (prefixWord ++ tailWord_2123403).sum := by decide
  have hdescent : baseEnd_2123403 < baseStart_2123403 := by decide
  rcases family_descends (prefixWord ++ tailWord_2123403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2123424 : List Nat := [2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 4]
def baseStart_2123424 : Nat := 118140960795 + 2123424 * 2 ^ 59
def prefixEnd_2123424 : Nat := 4983230072969 + 3 ^ 40 * 2123424 * 2
def baseEnd_2123424 : Nat := 1090337145292805327534557

theorem tailTrace_2123424 : CollatzResearch.WordTrace tailWord_2123424 prefixEnd_2123424 1090337145292805327534557 := by
  unfold tailWord_2123424
  simp only [CollatzResearch.WordTrace]
  refine ⟨38723817929602487396056663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51631757239469983194742217 38723817929602487396056663)
  ·
    refine ⟨58085726894403731094084995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38723817929602487396056663 58085726894403731094084995)
    ·
      refine ⟨87128590341605596641127493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58085726894403731094084995 87128590341605596641127493)
      ·
        refine ⟨16336610689051049370211405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 87128590341605596641127493 16336610689051049370211405)
        ·
          refine ⟨6126229008394143513829277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16336610689051049370211405 6126229008394143513829277)
          ·
            refine ⟨2297335878147803817685979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6126229008394143513829277 2297335878147803817685979)
            ·
              refine ⟨3446003817221705726528969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2297335878147803817685979 3446003817221705726528969)
              ·
                refine ⟨2584502862916279294896727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3446003817221705726528969 2584502862916279294896727)
                ·
                  refine ⟨3876754294374418942345091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2584502862916279294896727 3876754294374418942345091)
                  ·
                    refine ⟨5815131441561628413517637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3876754294374418942345091 5815131441561628413517637)
                    ·
                      refine ⟨1090337145292805327534557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5815131441561628413517637 1090337145292805327534557)
                      ·
                        rfl

theorem cell23_2123424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 4].length) (baseStart_2123424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2123424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2123424 prefixEnd_2123424 := by exact prefixLift 2123424
  have htrace : WordTrace (prefixWord ++ tailWord_2123424) baseStart_2123424 baseEnd_2123424 := by
    simpa [prefixWord, tailWord_2123424, baseEnd_2123424] using wordTrace_append hprefix tailTrace_2123424
  have hstable : (prefixWord ++ tailWord_2123424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2123424).length < 2 ^ (prefixWord ++ tailWord_2123424).sum := by decide
  have hdescent : baseEnd_2123424 < baseStart_2123424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2123424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2123433 : List Nat := [1, 2, 1, 1, 1, 1, 2, 2, 4, 2, 6]
def baseStart_2123433 : Nat := 118140960795 + 2123433 * 2 ^ 59
def prefixEnd_2123433 : Nat := 4983230072969 + 3 ^ 40 * 2123433 * 2
def baseEnd_2123433 : Nat := 1090341766618695792322015

theorem tailTrace_2123433 : CollatzResearch.WordTrace tailWord_2123433 prefixEnd_2123433 1090341766618695792322015 := by
  unfold tailWord_2123433
  simp only [CollatzResearch.WordTrace]
  refine ⟨77447964116172369329190953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51631976077448246219460635 77447964116172369329190953)
  ·
    refine ⟨58085973087129276996893215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77447964116172369329190953 58085973087129276996893215)
    ·
      refine ⟨87128959630693915495339823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58085973087129276996893215 87128959630693915495339823)
      ·
        refine ⟨130693439446040873243009735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87128959630693915495339823 130693439446040873243009735)
        ·
          refine ⟨196040159169061309864514603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130693439446040873243009735 196040159169061309864514603)
          ·
            refine ⟨294060238753591964796771905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196040159169061309864514603 294060238753591964796771905)
            ·
              refine ⟨220545179065193973597578929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 294060238753591964796771905 220545179065193973597578929)
              ·
                refine ⟨165408884298895480198184197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 220545179065193973597578929 165408884298895480198184197)
                ·
                  refine ⟨31014165806042902537159537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 165408884298895480198184197 31014165806042902537159537)
                  ·
                    refine ⟨23260624354532176902869653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31014165806042902537159537 23260624354532176902869653)
                    ·
                      refine ⟨1090341766618695792322015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23260624354532176902869653 1090341766618695792322015)
                      ·
                        rfl

theorem cell23_2123433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 2, 6].length) (baseStart_2123433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2123433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2123433 prefixEnd_2123433 := by exact prefixLift 2123433
  have htrace : WordTrace (prefixWord ++ tailWord_2123433) baseStart_2123433 baseEnd_2123433 := by
    simpa [prefixWord, tailWord_2123433, baseEnd_2123433] using wordTrace_append hprefix tailTrace_2123433
  have hstable : (prefixWord ++ tailWord_2123433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2123433).length < 2 ^ (prefixWord ++ tailWord_2123433).sum := by decide
  have hdescent : baseEnd_2123433 < baseStart_2123433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2123433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2123437 : List Nat := [1, 5, 2, 1, 1, 1, 3, 2, 1, 2, 4]
def baseStart_2123437 : Nat := 118140960795 + 2123437 * 2 ^ 59
def prefixEnd_2123437 : Nat := 4983230072969 + 3 ^ 40 * 2123437 * 2
def baseEnd_2123437 : Nat := 1090343820541313776671997

theorem tailTrace_2123437 : CollatzResearch.WordTrace tailWord_2123437 prefixEnd_2123437 1090343820541313776671997 := by
  unfold tailWord_2123437
  simp only [CollatzResearch.WordTrace]
  refine ⟨77448110008157878012336565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51632073338771918674891043 77448110008157878012336565)
  ·
    refine ⟨7260760313264801063656553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 77448110008157878012336565 7260760313264801063656553)
    ·
      refine ⟨5445570234948600797742415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7260760313264801063656553 5445570234948600797742415)
      ·
        refine ⟨8168355352422901196613623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5445570234948600797742415 8168355352422901196613623)
        ·
          refine ⟨12252533028634351794920435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8168355352422901196613623 12252533028634351794920435)
          ·
            refine ⟨18378799542951527692380653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12252533028634351794920435 18378799542951527692380653)
            ·
              refine ⟨6892049828606822884642745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18378799542951527692380653 6892049828606822884642745)
              ·
                refine ⟨5169037371455117163482059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6892049828606822884642745 5169037371455117163482059)
                ·
                  refine ⟨7753556057182675745223089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5169037371455117163482059 7753556057182675745223089)
                  ·
                    refine ⟨5815167042887006808917317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7753556057182675745223089 5815167042887006808917317)
                    ·
                      refine ⟨1090343820541313776671997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5815167042887006808917317 1090343820541313776671997)
                      ·
                        rfl

theorem cell23_2123437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_2123437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2123437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2123437 prefixEnd_2123437 := by exact prefixLift 2123437
  have htrace : WordTrace (prefixWord ++ tailWord_2123437) baseStart_2123437 baseEnd_2123437 := by
    simpa [prefixWord, tailWord_2123437, baseEnd_2123437] using wordTrace_append hprefix tailTrace_2123437
  have hstable : (prefixWord ++ tailWord_2123437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2123437).length < 2 ^ (prefixWord ++ tailWord_2123437).sum := by decide
  have hdescent : baseEnd_2123437 < baseStart_2123437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2123437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2123440 : List Nat := [2, 1, 1, 1, 2, 1, 5, 1, 3, 3, 3]
def baseStart_2123440 : Nat := 118140960795 + 2123440 * 2 ^ 59
def prefixEnd_2123440 : Nat := 4983230072969 + 3 ^ 40 * 2123440 * 2
def baseEnd_2123440 : Nat := 1090345360983277264934483

theorem tailTrace_2123440 : CollatzResearch.WordTrace tailWord_2123440 prefixEnd_2123440 1090345360983277264934483 := by
  unfold tailWord_2123440
  simp only [CollatzResearch.WordTrace]
  refine ⟨38724109713573504762347887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51632146284764673016463849 38724109713573504762347887)
  ·
    refine ⟨58086164570360257143521831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38724109713573504762347887 58086164570360257143521831)
    ·
      refine ⟨87129246855540385715282747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58086164570360257143521831 87129246855540385715282747)
      ·
        refine ⟨130693870283310578572924121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87129246855540385715282747 130693870283310578572924121)
        ·
          refine ⟨98020402712482933929693091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130693870283310578572924121 98020402712482933929693091)
          ·
            refine ⟨147030604068724400894539637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98020402712482933929693091 147030604068724400894539637)
            ·
              refine ⟨13784119131442912583863091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 147030604068724400894539637 13784119131442912583863091)
              ·
                refine ⟨20676178697164368875794637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13784119131442912583863091 20676178697164368875794637)
                ·
                  refine ⟨7753567011436638328422989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20676178697164368875794637 7753567011436638328422989)
                  ·
                    refine ⟨2907587629288739373158621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7753567011436638328422989 2907587629288739373158621)
                    ·
                      refine ⟨1090345360983277264934483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2907587629288739373158621 1090345360983277264934483)
                      ·
                        rfl

theorem cell23_2123440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 3, 3, 3].length) (baseStart_2123440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2123440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2123440 prefixEnd_2123440 := by exact prefixLift 2123440
  have htrace : WordTrace (prefixWord ++ tailWord_2123440) baseStart_2123440 baseEnd_2123440 := by
    simpa [prefixWord, tailWord_2123440, baseEnd_2123440] using wordTrace_append hprefix tailTrace_2123440
  have hstable : (prefixWord ++ tailWord_2123440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2123440).length < 2 ^ (prefixWord ++ tailWord_2123440).sum := by decide
  have hdescent : baseEnd_2123440 < baseStart_2123440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2123440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
