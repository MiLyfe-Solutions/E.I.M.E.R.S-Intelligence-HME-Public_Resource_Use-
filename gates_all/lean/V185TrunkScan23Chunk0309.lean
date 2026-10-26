import V185TrunkScan23Chunk0308

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1827950 : List Nat := [4, 1, 2, 2, 1, 2, 2, 1, 2, 3, 3]
def baseStart_1827950 : Nat := 118140960795 + 1827950 * 2 ^ 59
def prefixEnd_1827950 : Nat := 4983230072969 + 3 ^ 40 * 1827950 * 2
def baseEnd_1827950 : Nat := 938616962386228370918417

theorem tailTrace_1827950 : CollatzResearch.WordTrace tailWord_1827950 prefixEnd_1827950 938616962386228370918417 := by
  unfold tailWord_1827950
  simp only [CollatzResearch.WordTrace]
  refine ⟨8333851715957101731309163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44447209151771209233648869 8333851715957101731309163)
  ·
    refine ⟨12500777573935652596963745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8333851715957101731309163 12500777573935652596963745)
    ·
      refine ⟨9375583180451739447722809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12500777573935652596963745 9375583180451739447722809)
      ·
        refine ⟨7031687385338804585792107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9375583180451739447722809 7031687385338804585792107)
        ·
          refine ⟨10547531078008206878688161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7031687385338804585792107 10547531078008206878688161)
          ·
            refine ⟨7910648308506155159016121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10547531078008206878688161 7910648308506155159016121)
            ·
              refine ⟨5932986231379616369262091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7910648308506155159016121 5932986231379616369262091)
              ·
                refine ⟨8899479347069424553893137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5932986231379616369262091 8899479347069424553893137)
                ·
                  refine ⟨6674609510302068415419853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8899479347069424553893137 6674609510302068415419853)
                  ·
                    refine ⟨2502978566363275655782445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6674609510302068415419853 2502978566363275655782445)
                    ·
                      refine ⟨938616962386228370918417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2502978566363275655782445 938616962386228370918417)
                      ·
                        rfl

theorem cell23_1827950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_1827950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1827950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1827950 prefixEnd_1827950 := by exact prefixLift 1827950
  have htrace : WordTrace (prefixWord ++ tailWord_1827950) baseStart_1827950 baseEnd_1827950 := by
    simpa [prefixWord, tailWord_1827950, baseEnd_1827950] using wordTrace_append hprefix tailTrace_1827950
  have hstable : (prefixWord ++ tailWord_1827950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827950).length < 2 ^ (prefixWord ++ tailWord_1827950).sum := by decide
  have hdescent : baseEnd_1827950 < baseStart_1827950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828090 : List Nat := [3, 1, 1, 1, 1, 4, 2, 2, 4, 4]
def baseStart_1828090 : Nat := 118140960795 + 1828090 * 2 ^ 59
def prefixEnd_1828090 : Nat := 4983230072969 + 3 ^ 40 * 1828090 * 2
def baseEnd_1828090 : Nat := 312896283225952607722591

theorem tailTrace_1828090 : CollatzResearch.WordTrace tailWord_1828090 prefixEnd_1828090 312896283225952607722591 := by
  unfold tailWord_1828090
  simp only [CollatzResearch.WordTrace]
  refine ⟨16668979986787404440142431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44450613298099745173713149 16668979986787404440142431)
  ·
    refine ⟨25003469980181106660213647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16668979986787404440142431 25003469980181106660213647)
    ·
      refine ⟨37505204970271659990320471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25003469980181106660213647 37505204970271659990320471)
      ·
        refine ⟨56257807455407489985480707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37505204970271659990320471 56257807455407489985480707)
        ·
          refine ⟨84386711183111234978221061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56257807455407489985480707 84386711183111234978221061)
          ·
            refine ⟨15822508346833356558416449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84386711183111234978221061 15822508346833356558416449)
            ·
              refine ⟨11866881260125017418812337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15822508346833356558416449 11866881260125017418812337)
              ·
                refine ⟨8900160945093763064109253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11866881260125017418812337 8900160945093763064109253)
                ·
                  refine ⟨1668780177205080574520485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8900160945093763064109253 1668780177205080574520485)
                  ·
                    refine ⟨312896283225952607722591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1668780177205080574520485 312896283225952607722591)
                    ·
                      rfl

theorem cell23_1828090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 2, 4, 4].length) (baseStart_1828090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1828090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1828090 prefixEnd_1828090 := by exact prefixLift 1828090
  have htrace : WordTrace (prefixWord ++ tailWord_1828090) baseStart_1828090 baseEnd_1828090 := by
    simpa [prefixWord, tailWord_1828090, baseEnd_1828090] using wordTrace_append hprefix tailTrace_1828090
  have hstable : (prefixWord ++ tailWord_1828090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828090).length < 2 ^ (prefixWord ++ tailWord_1828090).sum := by decide
  have hdescent : baseEnd_1828090 < baseStart_1828090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828093 : List Nat := [1, 4, 1, 1, 1, 1, 1, 1, 5, 1, 6]
def baseStart_1828093 : Nat := 118140960795 + 1828093 * 2 ^ 59
def prefixEnd_1828093 : Nat := 4983230072969 + 3 ^ 40 * 1828093 * 2
def baseEnd_1828093 : Nat := 938690390119821311430259

theorem tailTrace_1828093 : CollatzResearch.WordTrace tailWord_1828093 prefixEnd_1828093 938690390119821311430259 := by
  unfold tailWord_1828093
  simp only [CollatzResearch.WordTrace]
  refine ⟨66676029366138749272928933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44450686244092499515285955 66676029366138749272928933)
  ·
    refine ⟨12501755506151015488674175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66676029366138749272928933 12501755506151015488674175)
    ·
      refine ⟨18752633259226523233011263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12501755506151015488674175 18752633259226523233011263)
      ·
        refine ⟨28128949888839784849516895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18752633259226523233011263 28128949888839784849516895)
        ·
          refine ⟨42193424833259677274275343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28128949888839784849516895 42193424833259677274275343)
          ·
            refine ⟨63290137249889515911413015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42193424833259677274275343 63290137249889515911413015)
            ·
              refine ⟨94935205874834273867119523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63290137249889515911413015 94935205874834273867119523)
              ·
                refine ⟨142402808812251410800679285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94935205874834273867119523 142402808812251410800679285)
                ·
                  refine ⟨13350263326148569762563683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 142402808812251410800679285 13350263326148569762563683)
                  ·
                    refine ⟨20025394989222854643845525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13350263326148569762563683 20025394989222854643845525)
                    ·
                      refine ⟨938690390119821311430259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20025394989222854643845525 938690390119821311430259)
                      ·
                        rfl

theorem cell23_1828093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 5, 1, 6].length) (baseStart_1828093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1828093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1828093 prefixEnd_1828093 := by exact prefixLift 1828093
  have htrace : WordTrace (prefixWord ++ tailWord_1828093) baseStart_1828093 baseEnd_1828093 := by
    simpa [prefixWord, tailWord_1828093, baseEnd_1828093] using wordTrace_append hprefix tailTrace_1828093
  have hstable : (prefixWord ++ tailWord_1828093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828093).length < 2 ^ (prefixWord ++ tailWord_1828093).sum := by decide
  have hdescent : baseEnd_1828093 < baseStart_1828093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828094 : List Nat := [4, 2, 2, 1, 1, 2, 4, 1, 1, 5]
def baseStart_1828094 : Nat := 118140960795 + 1828094 * 2 ^ 59
def prefixEnd_1828094 : Nat := 4983230072969 + 3 ^ 40 * 1828094 * 2
def baseEnd_1828094 : Nat := 312896967866825269172585

theorem tailTrace_1828094 : CollatzResearch.WordTrace tailWord_1828094 prefixEnd_1828094 312896967866825269172585 := by
  unfold tailWord_1828094
  simp only [CollatzResearch.WordTrace]
  refine ⟨8334508229891890805464417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44450710559423417629143557 8334508229891890805464417)
  ·
    refine ⟨6250881172418918104098313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8334508229891890805464417 6250881172418918104098313)
    ·
      refine ⟨4688160879314188578073735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6250881172418918104098313 4688160879314188578073735)
      ·
        refine ⟨7032241318971282867110603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4688160879314188578073735 7032241318971282867110603)
        ·
          refine ⟨10548361978456924300665905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7032241318971282867110603 10548361978456924300665905)
          ·
            refine ⟨7911271483842693225499429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10548361978456924300665905 7911271483842693225499429)
            ·
              refine ⟨1483363403220504979781143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7911271483842693225499429 1483363403220504979781143)
              ·
                refine ⟨2225045104830757469671715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1483363403220504979781143 2225045104830757469671715)
                ·
                  refine ⟨3337567657246136204507573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2225045104830757469671715 3337567657246136204507573)
                  ·
                    refine ⟨312896967866825269172585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3337567657246136204507573 312896967866825269172585)
                    ·
                      rfl

theorem cell23_1828094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_1828094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1828094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1828094 prefixEnd_1828094 := by exact prefixLift 1828094
  have htrace : WordTrace (prefixWord ++ tailWord_1828094) baseStart_1828094 baseEnd_1828094 := by
    simpa [prefixWord, tailWord_1828094, baseEnd_1828094] using wordTrace_append hprefix tailTrace_1828094
  have hstable : (prefixWord ++ tailWord_1828094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828094).length < 2 ^ (prefixWord ++ tailWord_1828094).sum := by decide
  have hdescent : baseEnd_1828094 < baseStart_1828094 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828097 : List Nat := [1, 2, 4, 1, 1, 4, 1, 3, 1, 1, 4]
def baseStart_1828097 : Nat := 118140960795 + 1828097 * 2 ^ 59
def prefixEnd_1828097 : Nat := 4983230072969 + 3 ^ 40 * 1828097 * 2
def baseEnd_1828097 : Nat := 938692444042439295780241

theorem tailTrace_1828097 : CollatzResearch.WordTrace tailWord_1828097 prefixEnd_1828097 938692444042439295780241 := by
  unfold tailWord_1828097
  simp only [CollatzResearch.WordTrace]
  refine ⟨66676175258124257956074545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44450783505416171970716363 66676175258124257956074545)
  ·
    refine ⟨50007131443593193467055909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66676175258124257956074545 50007131443593193467055909)
    ·
      refine ⟨9376337145673723775072983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50007131443593193467055909 9376337145673723775072983)
      ·
        refine ⟨14064505718510585662609475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9376337145673723775072983 14064505718510585662609475)
        ·
          refine ⟨21096758577765878493914213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14064505718510585662609475 21096758577765878493914213)
          ·
            refine ⟨3955642233331102217608915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21096758577765878493914213 3955642233331102217608915)
            ·
              refine ⟨5933463349996653326413373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3955642233331102217608915 5933463349996653326413373)
              ·
                refine ⟨2225048756248744997405015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5933463349996653326413373 2225048756248744997405015)
                ·
                  refine ⟨3337573134373117496107523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2225048756248744997405015 3337573134373117496107523)
                  ·
                    refine ⟨5006359701559676244161285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3337573134373117496107523 5006359701559676244161285)
                    ·
                      refine ⟨938692444042439295780241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5006359701559676244161285 938692444042439295780241)
                      ·
                        rfl

theorem cell23_1828097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 3, 1, 1, 4].length) (baseStart_1828097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1828097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1828097 prefixEnd_1828097 := by exact prefixLift 1828097
  have htrace : WordTrace (prefixWord ++ tailWord_1828097) baseStart_1828097 baseEnd_1828097 := by
    simpa [prefixWord, tailWord_1828097, baseEnd_1828097] using wordTrace_append hprefix tailTrace_1828097
  have hstable : (prefixWord ++ tailWord_1828097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828097).length < 2 ^ (prefixWord ++ tailWord_1828097).sum := by decide
  have hdescent : baseEnd_1828097 < baseStart_1828097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828107 : List Nat := [1, 1, 1, 1, 5, 3, 3, 2, 2, 4]
def baseStart_1828107 : Nat := 118140960795 + 1828107 * 2 ^ 59
def prefixEnd_1828107 : Nat := 4983230072969 + 3 ^ 40 * 1828107 * 2
def baseEnd_1828107 : Nat := 312899192949661418885065

theorem tailTrace_1828107 : CollatzResearch.WordTrace tailWord_1828107 prefixEnd_1828107 312899192949661418885065 := by
  unfold tailWord_1828107
  simp only [CollatzResearch.WordTrace]
  refine ⟨66676539988088029663938575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44451026658725353109292383 66676539988088029663938575)
  ·
    refine ⟨100014809982132044495907863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66676539988088029663938575 100014809982132044495907863)
    ·
      refine ⟨150022214973198066743861795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100014809982132044495907863 150022214973198066743861795)
      ·
        refine ⟨225033322459797100115792693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150022214973198066743861795 225033322459797100115792693)
        ·
          refine ⟨21096873980605978135855565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 225033322459797100115792693 21096873980605978135855565)
          ·
            refine ⟨7911327742727241800945837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21096873980605978135855565 7911327742727241800945837)
            ·
              refine ⟨2966747903522715675354689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7911327742727241800945837 2966747903522715675354689)
              ·
                refine ⟨2225060927642036756516017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2966747903522715675354689 2225060927642036756516017)
                ·
                  refine ⟨1668795695731527567387013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2225060927642036756516017 1668795695731527567387013)
                  ·
                    refine ⟨312899192949661418885065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1668795695731527567387013 312899192949661418885065)
                    ·
                      rfl

theorem cell23_1828107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 2, 2, 4].length) (baseStart_1828107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1828107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1828107 prefixEnd_1828107 := by exact prefixLift 1828107
  have htrace : WordTrace (prefixWord ++ tailWord_1828107) baseStart_1828107 baseEnd_1828107 := by
    simpa [prefixWord, tailWord_1828107, baseEnd_1828107] using wordTrace_append hprefix tailTrace_1828107
  have hstable : (prefixWord ++ tailWord_1828107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828107).length < 2 ^ (prefixWord ++ tailWord_1828107).sum := by decide
  have hdescent : baseEnd_1828107 < baseStart_1828107 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828147 : List Nat := [1, 1, 1, 2, 5, 2, 1, 2, 4, 1, 3]
def baseStart_1828147 : Nat := 118140960795 + 1828147 * 2 ^ 59
def prefixEnd_1828147 : Nat := 4983230072969 + 3 ^ 40 * 1828147 * 2
def baseEnd_1828147 : Nat := 938718118075164100155011

theorem tailTrace_1828147 : CollatzResearch.WordTrace tailWord_1828147 prefixEnd_1828147 938718118075164100155011 := by
  unfold tailWord_1828147
  simp only [CollatzResearch.WordTrace]
  refine ⟨66677998907943116495394695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44451999271962077663596463 66677998907943116495394695)
  ·
    refine ⟨100016998361914674743092043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66677998907943116495394695 100016998361914674743092043)
    ·
      refine ⟨150025497542872012114638065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100016998361914674743092043 150025497542872012114638065)
      ·
        refine ⟨112519123157154009085978549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150025497542872012114638065 112519123157154009085978549)
        ·
          refine ⟨10548667795983188351810489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 112519123157154009085978549 10548667795983188351810489)
          ·
            refine ⟨7911500846987391263857867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10548667795983188351810489 7911500846987391263857867)
            ·
              refine ⟨11867251270481086895786801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7911500846987391263857867 11867251270481086895786801)
              ·
                refine ⟨8900438452860815171840101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11867251270481086895786801 8900438452860815171840101)
                ·
                  refine ⟨1668832209911402844720019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8900438452860815171840101 1668832209911402844720019)
                  ·
                    refine ⟨2503248314867104267080029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1668832209911402844720019 2503248314867104267080029)
                    ·
                      refine ⟨938718118075164100155011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2503248314867104267080029 938718118075164100155011)
                      ·
                        rfl

theorem cell23_1828147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 2, 4, 1, 3].length) (baseStart_1828147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1828147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1828147 prefixEnd_1828147 := by exact prefixLift 1828147
  have htrace : WordTrace (prefixWord ++ tailWord_1828147) baseStart_1828147 baseEnd_1828147 := by
    simpa [prefixWord, tailWord_1828147, baseEnd_1828147] using wordTrace_append hprefix tailTrace_1828147
  have hstable : (prefixWord ++ tailWord_1828147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828147).length < 2 ^ (prefixWord ++ tailWord_1828147).sum := by decide
  have hdescent : baseEnd_1828147 < baseStart_1828147 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828180 : List Nat := [2, 4, 1, 1, 2, 1, 2, 1, 1, 8]
def baseStart_1828180 : Nat := 118140960795 + 1828180 * 2 ^ 59
def prefixEnd_1828180 : Nat := 4983230072969 + 3 ^ 40 * 1828180 * 2
def baseEnd_1828180 : Nat := 312911687645587490347453

theorem tailTrace_1828180 : CollatzResearch.WordTrace tailWord_1828180 prefixEnd_1828180 312911687645587490347453 := by
  unfold tailWord_1828180
  simp only [CollatzResearch.WordTrace]
  refine ⟨33339601258411781565672997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44452801677882375420897329 33339601258411781565672997)
  ·
    refine ⟨6251175235952209043563687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33339601258411781565672997 6251175235952209043563687)
    ·
      refine ⟨9376762853928313565345531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6251175235952209043563687 9376762853928313565345531)
      ·
        refine ⟨14065144280892470348018297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9376762853928313565345531 14065144280892470348018297)
        ·
          refine ⟨10548858210669352761013723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14065144280892470348018297 10548858210669352761013723)
          ·
            refine ⟨15823287316004029141520585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10548858210669352761013723 15823287316004029141520585)
            ·
              refine ⟨11867465487003021856140439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15823287316004029141520585 11867465487003021856140439)
              ·
                refine ⟨17801198230504532784210659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11867465487003021856140439 17801198230504532784210659)
                ·
                  refine ⟨26701797345756799176315989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17801198230504532784210659 26701797345756799176315989)
                  ·
                    refine ⟨312911687645587490347453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 26701797345756799176315989 312911687645587490347453)
                    ·
                      rfl

theorem cell23_1828180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 1, 8].length) (baseStart_1828180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1828180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1828180 prefixEnd_1828180 := by exact prefixLift 1828180
  have htrace : WordTrace (prefixWord ++ tailWord_1828180) baseStart_1828180 baseEnd_1828180 := by
    simpa [prefixWord, tailWord_1828180, baseEnd_1828180] using wordTrace_append hprefix tailTrace_1828180
  have hstable : (prefixWord ++ tailWord_1828180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828180).length < 2 ^ (prefixWord ++ tailWord_1828180).sum := by decide
  have hdescent : baseEnd_1828180 < baseStart_1828180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828181 : List Nat := [1, 3, 2, 2, 3, 1, 4, 1, 2, 1, 3]
def baseStart_1828181 : Nat := 118140960795 + 1828181 * 2 ^ 59
def prefixEnd_1828181 : Nat := 4983230072969 + 3 ^ 40 * 1828181 * 2
def baseEnd_1828181 : Nat := 938735576417416967129855

theorem tailTrace_1828181 : CollatzResearch.WordTrace tailWord_1828181 prefixEnd_1828181 938735576417416967129855 := by
  unfold tailWord_1828181
  simp only [CollatzResearch.WordTrace]
  refine ⟨66679238989819940302132397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44452825993213293534754931 66679238989819940302132397)
  ·
    refine ⟨25004714621182477613299649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66679238989819940302132397 25004714621182477613299649)
    ·
      refine ⟨18753535965886858209974737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25004714621182477613299649 18753535965886858209974737)
      ·
        refine ⟨14065151974415143657481053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18753535965886858209974737 14065151974415143657481053)
        ·
          refine ⟨5274431990405678871555395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14065151974415143657481053 5274431990405678871555395)
          ·
            refine ⟨7911647985608518307333093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5274431990405678871555395 7911647985608518307333093)
            ·
              refine ⟨1483433997301597182624955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7911647985608518307333093 1483433997301597182624955)
              ·
                refine ⟨2225150995952395773937433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1483433997301597182624955 2225150995952395773937433)
                ·
                  refine ⟨1668863246964296830453075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2225150995952395773937433 1668863246964296830453075)
                  ·
                    refine ⟨2503294870446445245679613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1668863246964296830453075 2503294870446445245679613)
                    ·
                      refine ⟨938735576417416967129855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2503294870446445245679613 938735576417416967129855)
                      ·
                        rfl

theorem cell23_1828181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 4, 1, 2, 1, 3].length) (baseStart_1828181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1828181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1828181 prefixEnd_1828181 := by exact prefixLift 1828181
  have htrace : WordTrace (prefixWord ++ tailWord_1828181) baseStart_1828181 baseEnd_1828181 := by
    simpa [prefixWord, tailWord_1828181, baseEnd_1828181] using wordTrace_append hprefix tailTrace_1828181
  have hstable : (prefixWord ++ tailWord_1828181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828181).length < 2 ^ (prefixWord ++ tailWord_1828181).sum := by decide
  have hdescent : baseEnd_1828181 < baseStart_1828181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828182 : List Nat := [5, 2, 3, 1, 2, 1, 1, 2, 1, 1, 4]
def baseStart_1828182 : Nat := 118140960795 + 1828182 * 2 ^ 59
def prefixEnd_1828182 : Nat := 4983230072969 + 3 ^ 40 * 1828182 * 2
def baseEnd_1828182 : Nat := 938736089898071463217351

theorem tailTrace_1828182 : CollatzResearch.WordTrace tailWord_1828182 prefixEnd_1828182 938736089898071463217351 := by
  unfold tailWord_1828182
  simp only [CollatzResearch.WordTrace]
  refine ⟨4167454716426019842057425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44452850308544211648612533 4167454716426019842057425)
  ·
    refine ⟨3125591037319514881543069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4167454716426019842057425 3125591037319514881543069)
    ·
      refine ⟨1172096638994818080578651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3125591037319514881543069 1172096638994818080578651)
      ·
        refine ⟨1758144958492227120867977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1172096638994818080578651 1758144958492227120867977)
        ·
          refine ⟨1318608718869170340650983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1758144958492227120867977 1318608718869170340650983)
          ·
            refine ⟨1977913078303755510976475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1318608718869170340650983 1977913078303755510976475)
            ·
              refine ⟨2966869617455633266464713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1977913078303755510976475 2966869617455633266464713)
              ·
                refine ⟨2225152213091724949848535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2966869617455633266464713 2225152213091724949848535)
                ·
                  refine ⟨3337728319637587424772803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2225152213091724949848535 3337728319637587424772803)
                  ·
                    refine ⟨5006592479456381137159205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3337728319637587424772803 5006592479456381137159205)
                    ·
                      refine ⟨938736089898071463217351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5006592479456381137159205 938736089898071463217351)
                      ·
                        rfl

theorem cell23_1828182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_1828182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1828182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1828182 prefixEnd_1828182 := by exact prefixLift 1828182
  have htrace : WordTrace (prefixWord ++ tailWord_1828182) baseStart_1828182 baseEnd_1828182 := by
    simpa [prefixWord, tailWord_1828182, baseEnd_1828182] using wordTrace_append hprefix tailTrace_1828182
  have hstable : (prefixWord ++ tailWord_1828182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828182).length < 2 ^ (prefixWord ++ tailWord_1828182).sum := by decide
  have hdescent : baseEnd_1828182 < baseStart_1828182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828204 : List Nat := [2, 2, 1, 1, 5, 2, 1, 2, 1, 4, 2]
def baseStart_1828204 : Nat := 118140960795 + 1828204 * 2 ^ 59
def prefixEnd_1828204 : Nat := 4983230072969 + 3 ^ 40 * 1828204 * 2
def baseEnd_1828204 : Nat := 938747386472470377142249

theorem tailTrace_1828204 : CollatzResearch.WordTrace tailWord_1828204 prefixEnd_1828204 938747386472470377142249 := by
  unfold tailWord_1828204
  simp only [CollatzResearch.WordTrace]
  refine ⟨33340038934368307615109833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44453385245824410153479777 33340038934368307615109833)
  ·
    refine ⟨25005029200776230711332375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33340038934368307615109833 25005029200776230711332375)
    ·
      refine ⟨37507543801164346066998563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25005029200776230711332375 37507543801164346066998563)
      ·
        refine ⟨56261315701746519100497845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37507543801164346066998563 56261315701746519100497845)
        ·
          refine ⟨5274498347038736165671673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56261315701746519100497845 5274498347038736165671673)
          ·
            refine ⟨3955873760279052124253755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5274498347038736165671673 3955873760279052124253755)
            ·
              refine ⟨5933810640418578186380633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3955873760279052124253755 5933810640418578186380633)
              ·
                refine ⟨4450357980313933639785475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5933810640418578186380633 4450357980313933639785475)
                ·
                  refine ⟨6675536970470900459678213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4450357980313933639785475 6675536970470900459678213)
                  ·
                    refine ⟨1251663181963293836189665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6675536970470900459678213 1251663181963293836189665)
                    ·
                      refine ⟨938747386472470377142249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1251663181963293836189665 938747386472470377142249)
                      ·
                        rfl

theorem cell23_1828204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 4, 2].length) (baseStart_1828204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1828204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1828204 prefixEnd_1828204 := by exact prefixLift 1828204
  have htrace : WordTrace (prefixWord ++ tailWord_1828204) baseStart_1828204 baseEnd_1828204 := by
    simpa [prefixWord, tailWord_1828204, baseEnd_1828204] using wordTrace_append hprefix tailTrace_1828204
  have hstable : (prefixWord ++ tailWord_1828204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828204).length < 2 ^ (prefixWord ++ tailWord_1828204).sum := by decide
  have hdescent : baseEnd_1828204 < baseStart_1828204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828221 : List Nat := [1, 4, 1, 1, 2, 2, 4, 2, 2, 2, 2]
def baseStart_1828221 : Nat := 118140960795 + 1828221 * 2 ^ 59
def prefixEnd_1828221 : Nat := 4983230072969 + 3 ^ 40 * 1828221 * 2
def baseEnd_1828221 : Nat := 938756115643596810629671

theorem tailTrace_1828221 : CollatzResearch.WordTrace tailWord_1828221 prefixEnd_1828221 938756115643596810629671 := by
  unfold tailWord_1828221
  simp only [CollatzResearch.WordTrace]
  refine ⟨66680697909675027133588517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44453798606450018089059011 66680697909675027133588517)
  ·
    refine ⟨12502630858064067587547847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66680697909675027133588517 12502630858064067587547847)
    ·
      refine ⟨18753946287096101381321771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12502630858064067587547847 18753946287096101381321771)
      ·
        refine ⟨28130919430644152071982657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18753946287096101381321771 28130919430644152071982657)
        ·
          refine ⟨21098189572983114053986993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28130919430644152071982657 21098189572983114053986993)
          ·
            refine ⟨15823642179737335540490245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21098189572983114053986993 15823642179737335540490245)
            ·
              refine ⟨2966932908700750413841921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15823642179737335540490245 2966932908700750413841921)
              ·
                refine ⟨2225199681525562810381441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2966932908700750413841921 2225199681525562810381441)
                ·
                  refine ⟨1668899761144172107786081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2225199681525562810381441 1668899761144172107786081)
                  ·
                    refine ⟨1251674820858129080839561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1668899761144172107786081 1251674820858129080839561)
                    ·
                      refine ⟨938756115643596810629671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1251674820858129080839561 938756115643596810629671)
                      ·
                        rfl

theorem cell23_1828221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 2, 2, 2, 2].length) (baseStart_1828221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1828221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1828221 prefixEnd_1828221 := by exact prefixLift 1828221
  have htrace : WordTrace (prefixWord ++ tailWord_1828221) baseStart_1828221 baseEnd_1828221 := by
    simpa [prefixWord, tailWord_1828221, baseEnd_1828221] using wordTrace_append hprefix tailTrace_1828221
  have hstable : (prefixWord ++ tailWord_1828221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828221).length < 2 ^ (prefixWord ++ tailWord_1828221).sum := by decide
  have hdescent : baseEnd_1828221 < baseStart_1828221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828247 : List Nat := [1, 1, 3, 3, 1, 1, 1, 1, 4, 5, 2]
def baseStart_1828247 : Nat := 118140960795 + 1828247 * 2 ^ 59
def prefixEnd_1828247 : Nat := 4983230072969 + 3 ^ 40 * 1828247 * 2
def baseEnd_1828247 : Nat := 938769466140613708904551

theorem tailTrace_1828247 : CollatzResearch.WordTrace tailWord_1828247 prefixEnd_1828247 938769466140613708904551 := by
  unfold tailWord_1828247
  simp only [CollatzResearch.WordTrace]
  refine ⟨66681646207580833574034995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44454430805053889049356663 66681646207580833574034995)
  ·
    refine ⟨100022469311371250361052493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66681646207580833574034995 100022469311371250361052493)
    ·
      refine ⟨37508425991764218885394685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100022469311371250361052493 37508425991764218885394685)
      ·
        refine ⟨14065659746911582082023007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37508425991764218885394685 14065659746911582082023007)
        ·
          refine ⟨21098489620367373123034511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14065659746911582082023007 21098489620367373123034511)
          ·
            refine ⟨31647734430551059684551767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21098489620367373123034511 31647734430551059684551767)
            ·
              refine ⟨47471601645826589526827651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31647734430551059684551767 47471601645826589526827651)
              ·
                refine ⟨71207402468739884290241477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47471601645826589526827651 71207402468739884290241477)
                ·
                  refine ⟨13351387962888728304420277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71207402468739884290241477 13351387962888728304420277)
                  ·
                    refine ⟨1251692621520818278539401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13351387962888728304420277 1251692621520818278539401)
                    ·
                      refine ⟨938769466140613708904551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1251692621520818278539401 938769466140613708904551)
                      ·
                        rfl

theorem cell23_1828247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 4, 5, 2].length) (baseStart_1828247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1828247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1828247 prefixEnd_1828247 := by exact prefixLift 1828247
  have htrace : WordTrace (prefixWord ++ tailWord_1828247) baseStart_1828247 baseEnd_1828247 := by
    simpa [prefixWord, tailWord_1828247, baseEnd_1828247] using wordTrace_append hprefix tailTrace_1828247
  have hstable : (prefixWord ++ tailWord_1828247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828247).length < 2 ^ (prefixWord ++ tailWord_1828247).sum := by decide
  have hdescent : baseEnd_1828247 < baseStart_1828247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828280 : List Nat := [2, 1, 2, 1, 2, 2, 2, 1, 2, 3, 5]
def baseStart_1828280 : Nat := 118140960795 + 1828280 * 2 ^ 59
def prefixEnd_1828280 : Nat := 4983230072969 + 3 ^ 40 * 1828280 * 2
def baseEnd_1828280 : Nat := 938786411002212079791899

theorem tailTrace_1828280 : CollatzResearch.WordTrace tailWord_1828280 prefixEnd_1828280 938786411002212079791899 := by
  unfold tailWord_1828280
  simp only [CollatzResearch.WordTrace]
  refine ⟨33341424908230640104993147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44455233210974186806657529 33341424908230640104993147)
  ·
    refine ⟨50012137362345960157489721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33341424908230640104993147 50012137362345960157489721)
    ·
      refine ⟨37509103021759470118117291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50012137362345960157489721 37509103021759470118117291)
      ·
        refine ⟨56263654532639205177175937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37509103021759470118117291 56263654532639205177175937)
        ·
          refine ⟨42197740899479403882881953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56263654532639205177175937 42197740899479403882881953)
          ·
            refine ⟨31648305674609552912161465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42197740899479403882881953 31648305674609552912161465)
            ·
              refine ⟨23736229255957164684121099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31648305674609552912161465 23736229255957164684121099)
              ·
                refine ⟨35604343883935747026181649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23736229255957164684121099 35604343883935747026181649)
                ·
                  refine ⟨26703257912951810269636237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35604343883935747026181649 26703257912951810269636237)
                  ·
                    refine ⟨10013721717356928851113589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26703257912951810269636237 10013721717356928851113589)
                    ·
                      refine ⟨938786411002212079791899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10013721717356928851113589 938786411002212079791899)
                      ·
                        rfl

theorem cell23_1828280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 2, 3, 5].length) (baseStart_1828280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1828280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1828280 prefixEnd_1828280 := by exact prefixLift 1828280
  have htrace : WordTrace (prefixWord ++ tailWord_1828280) baseStart_1828280 baseEnd_1828280 := by
    simpa [prefixWord, tailWord_1828280, baseEnd_1828280] using wordTrace_append hprefix tailTrace_1828280
  have hstable : (prefixWord ++ tailWord_1828280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828280).length < 2 ^ (prefixWord ++ tailWord_1828280).sum := by decide
  have hdescent : baseEnd_1828280 < baseStart_1828280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828317 : List Nat := [1, 4, 3, 1, 1, 2, 1, 2, 8]
def baseStart_1828317 : Nat := 118140960795 + 1828317 * 2 ^ 59
def prefixEnd_1828317 : Nat := 4983230072969 + 3 ^ 40 * 1828317 * 2
def baseEnd_1828317 : Nat := 104311712198492048336581

theorem tailTrace_1828317 : CollatzResearch.WordTrace tailWord_1828317 prefixEnd_1828317 104311712198492048336581 := by
  unfold tailWord_1828317
  simp only [CollatzResearch.WordTrace]
  refine ⟨66684199317327235529083205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44456132878218157019388803 66684199317327235529083205)
  ·
    refine ⟨12503287371998856661703101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66684199317327235529083205 12503287371998856661703101)
    ·
      refine ⟨4688732764499571248138663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12503287371998856661703101 4688732764499571248138663)
      ·
        refine ⟨7033099146749356872207995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4688732764499571248138663 7033099146749356872207995)
        ·
          refine ⟨10549648720124035308311993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7033099146749356872207995 10549648720124035308311993)
          ·
            refine ⟨7912236540093026481233995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10549648720124035308311993 7912236540093026481233995)
            ·
              refine ⟨11868354810139539721850993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7912236540093026481233995 11868354810139539721850993)
              ·
                refine ⟨8901266107604654791388245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11868354810139539721850993 8901266107604654791388245)
                ·
                  refine ⟨104311712198492048336581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8901266107604654791388245 104311712198492048336581)
                  ·
                    rfl

theorem cell23_1828317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 2, 8].length) (baseStart_1828317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1828317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1828317 prefixEnd_1828317 := by exact prefixLift 1828317
  have htrace : WordTrace (prefixWord ++ tailWord_1828317) baseStart_1828317 baseEnd_1828317 := by
    simpa [prefixWord, tailWord_1828317, baseEnd_1828317] using wordTrace_append hprefix tailTrace_1828317
  have hstable : (prefixWord ++ tailWord_1828317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828317).length < 2 ^ (prefixWord ++ tailWord_1828317).sum := by decide
  have hdescent : baseEnd_1828317 < baseStart_1828317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828320 : List Nat := [2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 8]
def baseStart_1828320 : Nat := 118140960795 + 1828320 * 2 ^ 59
def prefixEnd_1828320 : Nat := 4983230072969 + 3 ^ 40 * 1828320 * 2
def baseEnd_1828320 : Nat := 938806950228391923291715

theorem tailTrace_1828320 : CollatzResearch.WordTrace tailWord_1828320 prefixEnd_1828320 938806950228391923291715 := by
  unfold tailWord_1828320
  simp only [CollatzResearch.WordTrace]
  refine ⟨33342154368158183520721207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44456205824210911360961609 33342154368158183520721207)
  ·
    refine ⟨50013231552237275281081811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33342154368158183520721207 50013231552237275281081811)
    ·
      refine ⟨75019847328355912921622717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50013231552237275281081811 75019847328355912921622717)
      ·
        refine ⟨28132442748133467345608519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75019847328355912921622717 28132442748133467345608519)
        ·
          refine ⟨42198664122200201018412779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28132442748133467345608519 42198664122200201018412779)
          ·
            refine ⟨63297996183300301527619169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42198664122200201018412779 63297996183300301527619169)
            ·
              refine ⟨47473497137475226145714377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63297996183300301527619169 47473497137475226145714377)
              ·
                refine ⟨35605122853106419609285783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47473497137475226145714377 35605122853106419609285783)
                ·
                  refine ⟨53407684279659629413928675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35605122853106419609285783 53407684279659629413928675)
                  ·
                    refine ⟨80111526419489444120893013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53407684279659629413928675 80111526419489444120893013)
                    ·
                      refine ⟨938806950228391923291715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 80111526419489444120893013 938806950228391923291715)
                      ·
                        rfl

theorem cell23_1828320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_1828320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1828320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1828320 prefixEnd_1828320 := by exact prefixLift 1828320
  have htrace : WordTrace (prefixWord ++ tailWord_1828320) baseStart_1828320 baseEnd_1828320 := by
    simpa [prefixWord, tailWord_1828320, baseEnd_1828320] using wordTrace_append hprefix tailTrace_1828320
  have hstable : (prefixWord ++ tailWord_1828320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828320).length < 2 ^ (prefixWord ++ tailWord_1828320).sum := by decide
  have hdescent : baseEnd_1828320 < baseStart_1828320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828321 : List Nat := [1, 2, 3, 1, 2, 3, 3, 3, 1, 4]
def baseStart_1828321 : Nat := 118140960795 + 1828321 * 2 ^ 59
def prefixEnd_1828321 : Nat := 4983230072969 + 3 ^ 40 * 1828321 * 2
def baseEnd_1828321 : Nat := 312935821236348806459737

theorem tailTrace_1828321 : CollatzResearch.WordTrace tailWord_1828321 prefixEnd_1828321 312935821236348806459737 := by
  unfold tailWord_1828321
  simp only [CollatzResearch.WordTrace]
  refine ⟨66684345209312744212228817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44456230139541829474819211 66684345209312744212228817)
  ·
    refine ⟨50013258906984558159171613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66684345209312744212228817 50013258906984558159171613)
    ·
      refine ⟨18754972090119209309689355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50013258906984558159171613 18754972090119209309689355)
      ·
        refine ⟨28132458135178813964534033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18754972090119209309689355 28132458135178813964534033)
        ·
          refine ⟨21099343601384110473400525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28132458135178813964534033 21099343601384110473400525)
          ·
            refine ⟨7912253850519041427525197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21099343601384110473400525 7912253850519041427525197)
            ·
              refine ⟨2967095193944640535321949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7912253850519041427525197 2967095193944640535321949)
              ·
                refine ⟨1112660697729240200745731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2967095193944640535321949 1112660697729240200745731)
                ·
                  refine ⟨1668991046593860301118597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1112660697729240200745731 1668991046593860301118597)
                  ·
                    refine ⟨312935821236348806459737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1668991046593860301118597 312935821236348806459737)
                    ·
                      rfl

theorem cell23_1828321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 3, 1, 4].length) (baseStart_1828321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1828321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1828321 prefixEnd_1828321 := by exact prefixLift 1828321
  have htrace : WordTrace (prefixWord ++ tailWord_1828321) baseStart_1828321 baseEnd_1828321 := by
    simpa [prefixWord, tailWord_1828321, baseEnd_1828321] using wordTrace_append hprefix tailTrace_1828321
  have hstable : (prefixWord ++ tailWord_1828321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828321).length < 2 ^ (prefixWord ++ tailWord_1828321).sum := by decide
  have hdescent : baseEnd_1828321 < baseStart_1828321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828364 : List Nat := [2, 2, 1, 2, 5, 1, 1, 1, 3, 5]
def baseStart_1828364 : Nat := 118140960795 + 1828364 * 2 ^ 59
def prefixEnd_1828364 : Nat := 4983230072969 + 3 ^ 40 * 1828364 * 2
def baseEnd_1828364 : Nat := 312943181125729917047171

theorem tailTrace_1828364 : CollatzResearch.WordTrace tailWord_1828364 prefixEnd_1828364 312943181125729917047171 := by
  unfold tailWord_1828364
  simp only [CollatzResearch.WordTrace]
  refine ⟨33342956774078481278022073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44457275698771308370696097 33342956774078481278022073)
  ·
    refine ⟨25007217580558860958516555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33342956774078481278022073 25007217580558860958516555)
    ·
      refine ⟨37510826370838291437774833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25007217580558860958516555 37510826370838291437774833)
      ·
        refine ⟨28133119778128718578331125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37510826370838291437774833 28133119778128718578331125)
        ·
          refine ⟨2637479979199567366718543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28133119778128718578331125 2637479979199567366718543)
          ·
            refine ⟨3956219968799351050077815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2637479979199567366718543 3956219968799351050077815)
            ·
              refine ⟨5934329953199026575116723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3956219968799351050077815 5934329953199026575116723)
              ·
                refine ⟨8901494929798539862675085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5934329953199026575116723 8901494929798539862675085)
                ·
                  refine ⟨3338060598674452448503157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8901494929798539862675085 3338060598674452448503157)
                  ·
                    refine ⟨312943181125729917047171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3338060598674452448503157 312943181125729917047171)
                    ·
                      rfl

theorem cell23_1828364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 1, 3, 5].length) (baseStart_1828364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1828364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1828364 prefixEnd_1828364 := by exact prefixLift 1828364
  have htrace : WordTrace (prefixWord ++ tailWord_1828364) baseStart_1828364 baseEnd_1828364 := by
    simpa [prefixWord, tailWord_1828364, baseEnd_1828364] using wordTrace_append hprefix tailTrace_1828364
  have hstable : (prefixWord ++ tailWord_1828364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828364).length < 2 ^ (prefixWord ++ tailWord_1828364).sum := by decide
  have hdescent : baseEnd_1828364 < baseStart_1828364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828365 : List Nat := [1, 7, 1, 1, 2, 1, 2, 1, 2, 2, 3]
def baseStart_1828365 : Nat := 118140960795 + 1828365 * 2 ^ 59
def prefixEnd_1828365 : Nat := 4983230072969 + 3 ^ 40 * 1828365 * 2
def baseEnd_1828365 : Nat := 938830056857844247229009

theorem tailTrace_1828365 : CollatzResearch.WordTrace tailWord_1828365 prefixEnd_1828365 938830056857844247229009 := by
  unfold tailWord_1828365
  simp only [CollatzResearch.WordTrace]
  refine ⟨66685950021153339726830549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44457300014102226484553699 66685950021153339726830549)
  ·
    refine ⟨1562951953620781399847591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 66685950021153339726830549 1562951953620781399847591)
    ·
      refine ⟨2344427930431172099771387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1562951953620781399847591 2344427930431172099771387)
      ·
        refine ⟨3516641895646758149657081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2344427930431172099771387 3516641895646758149657081)
        ·
          refine ⟨2637481421735068612242811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3516641895646758149657081 2637481421735068612242811)
          ·
            refine ⟨3956222132602602918364217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2637481421735068612242811 3956222132602602918364217)
            ·
              refine ⟨2967166599451952188773163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3956222132602602918364217 2967166599451952188773163)
              ·
                refine ⟨4450749899177928283159745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2967166599451952188773163 4450749899177928283159745)
                ·
                  refine ⟨3338062424383446212369809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4450749899177928283159745 3338062424383446212369809)
                  ·
                    refine ⟨2503546818287584659277357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3338062424383446212369809 2503546818287584659277357)
                    ·
                      refine ⟨938830056857844247229009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2503546818287584659277357 938830056857844247229009)
                      ·
                        rfl

theorem cell23_1828365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_1828365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1828365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1828365 prefixEnd_1828365 := by exact prefixLift 1828365
  have htrace : WordTrace (prefixWord ++ tailWord_1828365) baseStart_1828365 baseEnd_1828365 := by
    simpa [prefixWord, tailWord_1828365, baseEnd_1828365] using wordTrace_append hprefix tailTrace_1828365
  have hstable : (prefixWord ++ tailWord_1828365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828365).length < 2 ^ (prefixWord ++ tailWord_1828365).sum := by decide
  have hdescent : baseEnd_1828365 < baseStart_1828365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828371 : List Nat := [1, 1, 1, 2, 1, 7, 2, 1, 2, 3, 2]
def baseStart_1828371 : Nat := 118140960795 + 1828371 * 2 ^ 59
def prefixEnd_1828371 : Nat := 4983230072969 + 3 ^ 40 * 1828371 * 2
def baseEnd_1828371 : Nat := 938833137741771223753981

theorem tailTrace_1828371 : CollatzResearch.WordTrace tailWord_1828371 prefixEnd_1828371 938833137741771223753981 := by
  unfold tailWord_1828371
  simp only [CollatzResearch.WordTrace]
  refine ⟨66686168859131602751548967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44457445906087735167699311 66686168859131602751548967)
  ·
    refine ⟨100029253288697404127323451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66686168859131602751548967 100029253288697404127323451)
    ·
      refine ⟨150043879933046106190985177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100029253288697404127323451 150043879933046106190985177)
      ·
        refine ⟨112532909949784579643238883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150043879933046106190985177 112532909949784579643238883)
        ·
          refine ⟨168799364924676869464858325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112532909949784579643238883 168799364924676869464858325)
          ·
            refine ⟨3956235115422114128082617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 168799364924676869464858325 3956235115422114128082617)
            ·
              refine ⟨2967176336566585596061963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3956235115422114128082617 2967176336566585596061963)
              ·
                refine ⟨4450764504849878394092945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2967176336566585596061963 4450764504849878394092945)
                ·
                  refine ⟨3338073378637408795569709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4450764504849878394092945 3338073378637408795569709)
                  ·
                    refine ⟨1251777516989028298338641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3338073378637408795569709 1251777516989028298338641)
                    ·
                      refine ⟨938833137741771223753981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1251777516989028298338641 938833137741771223753981)
                      ·
                        rfl

theorem cell23_1828371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 1, 2, 3, 2].length) (baseStart_1828371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1828371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1828371 prefixEnd_1828371 := by exact prefixLift 1828371
  have htrace : WordTrace (prefixWord ++ tailWord_1828371) baseStart_1828371 baseEnd_1828371 := by
    simpa [prefixWord, tailWord_1828371, baseEnd_1828371] using wordTrace_append hprefix tailTrace_1828371
  have hstable : (prefixWord ++ tailWord_1828371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828371).length < 2 ^ (prefixWord ++ tailWord_1828371).sum := by decide
  have hdescent : baseEnd_1828371 < baseStart_1828371 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828381 : List Nat := [1, 4, 2, 2, 1, 1, 5, 1, 1, 5]
def baseStart_1828381 : Nat := 118140960795 + 1828381 * 2 ^ 59
def prefixEnd_1828381 : Nat := 4983230072969 + 3 ^ 40 * 1828381 * 2
def baseEnd_1828381 : Nat := 312946090849438728209645

theorem tailTrace_1828381 : CollatzResearch.WordTrace tailWord_1828381 prefixEnd_1828381 312946090849438728209645 := by
  unfold tailWord_1828381
  simp only [CollatzResearch.WordTrace]
  refine ⟨66686533589095374459412997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44457689059396916306275331 66686533589095374459412997)
  ·
    refine ⟨12503725047955382711139937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66686533589095374459412997 12503725047955382711139937)
    ·
      refine ⟨9377793785966537033354953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12503725047955382711139937 9377793785966537033354953)
      ·
        refine ⟨7033345339474902775016215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9377793785966537033354953 7033345339474902775016215)
        ·
          refine ⟨10550018009212354162524323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7033345339474902775016215 10550018009212354162524323)
          ·
            refine ⟨15825027013818531243786485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10550018009212354162524323 15825027013818531243786485)
            ·
              refine ⟨1483596282545487304104983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15825027013818531243786485 1483596282545487304104983)
              ·
                refine ⟨2225394423818230956157475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1483596282545487304104983 2225394423818230956157475)
                ·
                  refine ⟨3338091635727346434236213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2225394423818230956157475 3338091635727346434236213)
                  ·
                    refine ⟨312946090849438728209645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3338091635727346434236213 312946090849438728209645)
                    ·
                      rfl

theorem cell23_1828381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 5, 1, 1, 5].length) (baseStart_1828381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1828381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1828381 prefixEnd_1828381 := by exact prefixLift 1828381
  have htrace : WordTrace (prefixWord ++ tailWord_1828381) baseStart_1828381 baseEnd_1828381 := by
    simpa [prefixWord, tailWord_1828381, baseEnd_1828381] using wordTrace_append hprefix tailTrace_1828381
  have hstable : (prefixWord ++ tailWord_1828381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828381).length < 2 ^ (prefixWord ++ tailWord_1828381).sum := by decide
  have hdescent : baseEnd_1828381 < baseStart_1828381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828401 : List Nat := [1, 2, 2, 3, 1, 1, 1, 5, 3, 2, 2]
def baseStart_1828401 : Nat := 118140960795 + 1828401 * 2 ^ 59
def prefixEnd_1828401 : Nat := 4983230072969 + 3 ^ 40 * 1828401 * 2
def baseEnd_1828401 : Nat := 938848542161406106378843

theorem tailTrace_1828401 : CollatzResearch.WordTrace tailWord_1828401 prefixEnd_1828401 938848542161406106378843 := by
  unfold tailWord_1828401
  simp only [CollatzResearch.WordTrace]
  refine ⟨66687263049022917875141057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44458175366015278583427371 66687263049022917875141057)
  ·
    refine ⟨50015447286767188406355793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66687263049022917875141057 50015447286767188406355793)
    ·
      refine ⟨37511585465075391304766845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50015447286767188406355793 37511585465075391304766845)
      ·
        refine ⟨14066844549403271739287567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37511585465075391304766845 14066844549403271739287567)
        ·
          refine ⟨21100266824104907608931351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14066844549403271739287567 21100266824104907608931351)
          ·
            refine ⟨31650400236157361413397027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21100266824104907608931351 31650400236157361413397027)
            ·
              refine ⟨47475600354236042120095541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31650400236157361413397027 47475600354236042120095541)
              ·
                refine ⟨4450837533209628948758957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47475600354236042120095541 4450837533209628948758957)
                ·
                  refine ⟨1669064074953610855784609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4450837533209628948758957 1669064074953610855784609)
                  ·
                    refine ⟨1251798056215208141838457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1669064074953610855784609 1251798056215208141838457)
                    ·
                      refine ⟨938848542161406106378843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1251798056215208141838457 938848542161406106378843)
                      ·
                        rfl

theorem cell23_1828401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 5, 3, 2, 2].length) (baseStart_1828401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1828401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1828401 prefixEnd_1828401 := by exact prefixLift 1828401
  have htrace : WordTrace (prefixWord ++ tailWord_1828401) baseStart_1828401 baseEnd_1828401 := by
    simpa [prefixWord, tailWord_1828401, baseEnd_1828401] using wordTrace_append hprefix tailTrace_1828401
  have hstable : (prefixWord ++ tailWord_1828401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828401).length < 2 ^ (prefixWord ++ tailWord_1828401).sum := by decide
  have hdescent : baseEnd_1828401 < baseStart_1828401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828407 : List Nat := [1, 1, 3, 1, 2, 4, 3, 8]
def baseStart_1828407 : Nat := 118140960795 + 1828407 * 2 ^ 59
def prefixEnd_1828407 : Nat := 4983230072969 + 3 ^ 40 * 1828407 * 2
def baseEnd_1828407 : Nat := 34772282335012336403845

theorem tailTrace_1828407 : CollatzResearch.WordTrace tailWord_1828407 prefixEnd_1828407 34772282335012336403845 := by
  unfold tailWord_1828407
  simp only [CollatzResearch.WordTrace]
  refine ⟨66687481887001180899859475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44458321258000787266572983 66687481887001180899859475)
  ·
    refine ⟨100031222830501771349789213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66687481887001180899859475 100031222830501771349789213)
    ·
      refine ⟨37511708561438164256170955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100031222830501771349789213 37511708561438164256170955)
      ·
        refine ⟨56267562842157246384256433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37511708561438164256170955 56267562842157246384256433)
        ·
          refine ⟨42200672131617934788192325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56267562842157246384256433 42200672131617934788192325)
          ·
            refine ⟨7912626024678362772786061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42200672131617934788192325 7912626024678362772786061)
            ·
              refine ⟨2967234759254386039794773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7912626024678362772786061 2967234759254386039794773)
              ·
                refine ⟨34772282335012336403845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2967234759254386039794773 34772282335012336403845)
                ·
                  rfl

theorem cell23_1828407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 8].length) (baseStart_1828407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1828407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1828407 prefixEnd_1828407 := by exact prefixLift 1828407
  have htrace : WordTrace (prefixWord ++ tailWord_1828407) baseStart_1828407 baseEnd_1828407 := by
    simpa [prefixWord, tailWord_1828407, baseEnd_1828407] using wordTrace_append hprefix tailTrace_1828407
  have hstable : (prefixWord ++ tailWord_1828407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828407).length < 2 ^ (prefixWord ++ tailWord_1828407).sum := by decide
  have hdescent : baseEnd_1828407 < baseStart_1828407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828422 : List Nat := [6, 1, 1, 1, 3, 2, 1, 1, 2, 3, 2]
def baseStart_1828422 : Nat := 118140960795 + 1828422 * 2 ^ 59
def prefixEnd_1828422 : Nat := 4983230072969 + 3 ^ 40 * 1828422 * 2
def baseEnd_1828422 : Nat := 938859325255150524216247

theorem tailTrace_1828422 : CollatzResearch.WordTrace tailWord_1828422 prefixEnd_1828422 938859325255150524216247 := by
  unfold tailWord_1828422
  simp only [CollatzResearch.WordTrace]
  refine ⟨2084000905685838701926735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 44458685987964558974437013 2084000905685838701926735)
  ·
    refine ⟨3126001358528758052890103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2084000905685838701926735 3126001358528758052890103)
    ·
      refine ⟨4689002037793137079335155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3126001358528758052890103 4689002037793137079335155)
      ·
        refine ⟨7033503056689705619002733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4689002037793137079335155 7033503056689705619002733)
        ·
          refine ⟨2637563646258639607126025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7033503056689705619002733 2637563646258639607126025)
          ·
            refine ⟨1978172734693979705344519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2637563646258639607126025 1978172734693979705344519)
            ·
              refine ⟨2967259102040969558016779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1978172734693979705344519 2967259102040969558016779)
              ·
                refine ⟨4450888653061454337025169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2967259102040969558016779 4450888653061454337025169)
                ·
                  refine ⟨3338166489796090752768877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4450888653061454337025169 3338166489796090752768877)
                  ·
                    refine ⟨1251812433673534032288329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3338166489796090752768877 1251812433673534032288329)
                    ·
                      refine ⟨938859325255150524216247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1251812433673534032288329 938859325255150524216247)
                      ·
                        rfl

theorem cell23_1828422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 1, 2, 3, 2].length) (baseStart_1828422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1828422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1828422 prefixEnd_1828422 := by exact prefixLift 1828422
  have htrace : WordTrace (prefixWord ++ tailWord_1828422) baseStart_1828422 baseEnd_1828422 := by
    simpa [prefixWord, tailWord_1828422, baseEnd_1828422] using wordTrace_append hprefix tailTrace_1828422
  have hstable : (prefixWord ++ tailWord_1828422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828422).length < 2 ^ (prefixWord ++ tailWord_1828422).sum := by decide
  have hdescent : baseEnd_1828422 < baseStart_1828422 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828451 : List Nat := [1, 1, 1, 5, 1, 4, 1, 1, 4, 1, 3]
def baseStart_1828451 : Nat := 118140960795 + 1828451 * 2 ^ 59
def prefixEnd_1828451 : Nat := 4983230072969 + 3 ^ 40 * 1828451 * 2
def baseEnd_1828451 : Nat := 938874216194130910753613

theorem tailTrace_1828451 : CollatzResearch.WordTrace tailWord_1828451 prefixEnd_1828451 938874216194130910753613 := by
  unfold tailWord_1828451
  simp only [CollatzResearch.WordTrace]
  refine ⟨66689086698841776414461207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44459391132561184276307471 66689086698841776414461207)
  ·
    refine ⟨100033630048262664621691811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66689086698841776414461207 100033630048262664621691811)
    ·
      refine ⟨150050445072393996932537717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100033630048262664621691811 150050445072393996932537717)
      ·
        refine ⟨14067229225536937212425411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 150050445072393996932537717 14067229225536937212425411)
        ·
          refine ⟨21100843838305405818638117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14067229225536937212425411 21100843838305405818638117)
          ·
            refine ⟨3956408219682263590994647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21100843838305405818638117 3956408219682263590994647)
            ·
              refine ⟨5934612329523395386491971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3956408219682263590994647 5934612329523395386491971)
              ·
                refine ⟨8901918494285093079737957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5934612329523395386491971 8901918494285093079737957)
                ·
                  refine ⟨1669109717678454952450867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8901918494285093079737957 1669109717678454952450867)
                  ·
                    refine ⟨2503664576517682428676301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1669109717678454952450867 2503664576517682428676301)
                    ·
                      refine ⟨938874216194130910753613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2503664576517682428676301 938874216194130910753613)
                      ·
                        rfl

theorem cell23_1828451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 1, 4, 1, 3].length) (baseStart_1828451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1828451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1828451 prefixEnd_1828451 := by exact prefixLift 1828451
  have htrace : WordTrace (prefixWord ++ tailWord_1828451) baseStart_1828451 baseEnd_1828451 := by
    simpa [prefixWord, tailWord_1828451, baseEnd_1828451] using wordTrace_append hprefix tailTrace_1828451
  have hstable : (prefixWord ++ tailWord_1828451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828451).length < 2 ^ (prefixWord ++ tailWord_1828451).sum := by decide
  have hdescent : baseEnd_1828451 < baseStart_1828451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828457 : List Nat := [1, 2, 1, 1, 1, 4, 2, 1, 1, 5, 4]
def baseStart_1828457 : Nat := 118140960795 + 1828457 * 2 ^ 59
def prefixEnd_1828457 : Nat := 4983230072969 + 3 ^ 40 * 1828457 * 2
def baseEnd_1828457 : Nat := 938877297078057887278585

theorem tailTrace_1828457 : CollatzResearch.WordTrace tailWord_1828457 prefixEnd_1828457 938877297078057887278585 := by
  unfold tailWord_1828457
  simp only [CollatzResearch.WordTrace]
  refine ⟨66689305536820039439179625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44459537024546692959453083 66689305536820039439179625)
  ·
    refine ⟨50016979152615029579384719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66689305536820039439179625 50016979152615029579384719)
    ·
      refine ⟨75025468728922544369077079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50016979152615029579384719 75025468728922544369077079)
      ·
        refine ⟨112538203093383816553615619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75025468728922544369077079 112538203093383816553615619)
        ·
          refine ⟨168807304640075724830423429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112538203093383816553615619 168807304640075724830423429)
          ·
            refine ⟨31651369620014198405704393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 168807304640075724830423429 31651369620014198405704393)
            ·
              refine ⟨23738527215010648804278295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31651369620014198405704393 23738527215010648804278295)
              ·
                refine ⟨35607790822515973206417443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23738527215010648804278295 35607790822515973206417443)
                ·
                  refine ⟨53411686233773959809626165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35607790822515973206417443 53411686233773959809626165)
                  ·
                    refine ⟨5007345584416308732152453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53411686233773959809626165 5007345584416308732152453)
                    ·
                      refine ⟨938877297078057887278585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5007345584416308732152453 938877297078057887278585)
                      ·
                        rfl

theorem cell23_1828457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 5, 4].length) (baseStart_1828457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1828457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1828457 prefixEnd_1828457 := by exact prefixLift 1828457
  have htrace : WordTrace (prefixWord ++ tailWord_1828457) baseStart_1828457 baseEnd_1828457 := by
    simpa [prefixWord, tailWord_1828457, baseEnd_1828457] using wordTrace_append hprefix tailTrace_1828457
  have hstable : (prefixWord ++ tailWord_1828457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828457).length < 2 ^ (prefixWord ++ tailWord_1828457).sum := by decide
  have hdescent : baseEnd_1828457 < baseStart_1828457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828491 : List Nat := [1, 1, 1, 1, 4, 1, 3, 1, 6, 2, 2]
def baseStart_1828491 : Nat := 118140960795 + 1828491 * 2 ^ 59
def prefixEnd_1828491 : Nat := 4983230072969 + 3 ^ 40 * 1828491 * 2
def baseEnd_1828491 : Nat := 938894755420310754253429

theorem tailTrace_1828491 : CollatzResearch.WordTrace tailWord_1828491 prefixEnd_1828491 938894755420310754253429 := by
  unfold tailWord_1828491
  simp only [CollatzResearch.WordTrace]
  refine ⟨66690545618696863245917327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44460363745797908830611551 66690545618696863245917327)
  ·
    refine ⟨100035818428045294868875991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66690545618696863245917327 100035818428045294868875991)
    ·
      refine ⟨150053727642067942303313987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100035818428045294868875991 150053727642067942303313987)
      ·
        refine ⟨225080591463101913454970981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150053727642067942303313987 225080591463101913454970981)
        ·
          refine ⟨42202610899331608772807059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 225080591463101913454970981 42202610899331608772807059)
          ·
            refine ⟨63303916348997413159210589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42202610899331608772807059 63303916348997413159210589)
            ·
              refine ⟨23738968630874029934703971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63303916348997413159210589 23738968630874029934703971)
              ·
                refine ⟨35608452946311044902055957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23738968630874029934703971 35608452946311044902055957)
                ·
                  refine ⟨1669146231858330229783873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 35608452946311044902055957 1669146231858330229783873)
                  ·
                    refine ⟨1251859673893747672337905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1669146231858330229783873 1251859673893747672337905)
                    ·
                      refine ⟨938894755420310754253429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1251859673893747672337905 938894755420310754253429)
                      ·
                        rfl

theorem cell23_1828491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 6, 2, 2].length) (baseStart_1828491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1828491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1828491 prefixEnd_1828491 := by exact prefixLift 1828491
  have htrace : WordTrace (prefixWord ++ tailWord_1828491) baseStart_1828491 baseEnd_1828491 := by
    simpa [prefixWord, tailWord_1828491, baseEnd_1828491] using wordTrace_append hprefix tailTrace_1828491
  have hstable : (prefixWord ++ tailWord_1828491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828491).length < 2 ^ (prefixWord ++ tailWord_1828491).sum := by decide
  have hdescent : baseEnd_1828491 < baseStart_1828491 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828494 : List Nat := [4, 1, 1, 3, 1, 2, 1, 1, 1, 3, 5]
def baseStart_1828494 : Nat := 118140960795 + 1828494 * 2 ^ 59
def prefixEnd_1828494 : Nat := 4983230072969 + 3 ^ 40 * 1828494 * 2
def baseEnd_1828494 : Nat := 938896295862274242515915

theorem tailTrace_1828494 : CollatzResearch.WordTrace tailWord_1828494 prefixEnd_1828494 938896295862274242515915 := by
  unfold tailWord_1828494
  simp only [CollatzResearch.WordTrace]
  refine ⟨8336331879710749344784567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44460436691790663172184357 8336331879710749344784567)
  ·
    refine ⟨12504497819566124017176851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8336331879710749344784567 12504497819566124017176851)
    ·
      refine ⟨18756746729349186025765277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12504497819566124017176851 18756746729349186025765277)
      ·
        refine ⟨7033780023505944759661979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18756746729349186025765277 7033780023505944759661979)
        ·
          refine ⟨10550670035258917139492969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7033780023505944759661979 10550670035258917139492969)
          ·
            refine ⟨7913002526444187854619727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10550670035258917139492969 7913002526444187854619727)
            ·
              refine ⟨11869503789666281781929591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7913002526444187854619727 11869503789666281781929591)
              ·
                refine ⟨17804255684499422672894387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11869503789666281781929591 17804255684499422672894387)
                ·
                  refine ⟨26706383526749134009341581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17804255684499422672894387 26706383526749134009341581)
                  ·
                    refine ⟨10014893822530925253503093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26706383526749134009341581 10014893822530925253503093)
                    ·
                      refine ⟨938896295862274242515915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10014893822530925253503093 938896295862274242515915)
                      ·
                        rfl

theorem cell23_1828494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_1828494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1828494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1828494 prefixEnd_1828494 := by exact prefixLift 1828494
  have htrace : WordTrace (prefixWord ++ tailWord_1828494) baseStart_1828494 baseEnd_1828494 := by
    simpa [prefixWord, tailWord_1828494, baseEnd_1828494] using wordTrace_append hprefix tailTrace_1828494
  have hstable : (prefixWord ++ tailWord_1828494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828494).length < 2 ^ (prefixWord ++ tailWord_1828494).sum := by decide
  have hdescent : baseEnd_1828494 < baseStart_1828494 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828525 : List Nat := [1, 5, 2, 1, 1, 1, 3, 3, 2, 2, 2]
def baseStart_1828525 : Nat := 118140960795 + 1828525 * 2 ^ 59
def prefixEnd_1828525 : Nat := 4983230072969 + 3 ^ 40 * 1828525 * 2
def baseEnd_1828525 : Nat := 938912213762563621228273

theorem tailTrace_1828525 : CollatzResearch.WordTrace tailWord_1828525 prefixEnd_1828525 938912213762563621228273 := by
  unfold tailWord_1828525
  simp only [CollatzResearch.WordTrace]
  refine ⟨66691785700573687052655029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44461190467049124701770019 66691785700573687052655029)
  ·
    refine ⟨6252354909428783161186409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66691785700573687052655029 6252354909428783161186409)
    ·
      refine ⟨4689266182071587370889807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6252354909428783161186409 4689266182071587370889807)
      ·
        refine ⟨7033899273107381056334711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4689266182071587370889807 7033899273107381056334711)
        ·
          refine ⟨10550848909661071584502067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7033899273107381056334711 10550848909661071584502067)
          ·
            refine ⟨15826273364491607376753101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10550848909661071584502067 15826273364491607376753101)
            ·
              refine ⟨5934852511684352766282413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15826273364491607376753101 5934852511684352766282413)
              ·
                refine ⟨2225569691881632287355905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5934852511684352766282413 2225569691881632287355905)
                ·
                  refine ⟨1669177268911224215516929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2225569691881632287355905 1669177268911224215516929)
                  ·
                    refine ⟨1251882951683418161637697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1669177268911224215516929 1251882951683418161637697)
                    ·
                      refine ⟨938912213762563621228273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1251882951683418161637697 938912213762563621228273)
                      ·
                        rfl

theorem cell23_1828525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 3, 2, 2, 2].length) (baseStart_1828525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1828525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1828525 prefixEnd_1828525 := by exact prefixLift 1828525
  have htrace : WordTrace (prefixWord ++ tailWord_1828525) baseStart_1828525 baseEnd_1828525 := by
    simpa [prefixWord, tailWord_1828525, baseEnd_1828525] using wordTrace_append hprefix tailTrace_1828525
  have hstable : (prefixWord ++ tailWord_1828525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828525).length < 2 ^ (prefixWord ++ tailWord_1828525).sum := by decide
  have hdescent : baseEnd_1828525 < baseStart_1828525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828546 : List Nat := [3, 5, 1, 2, 1, 1, 3, 1, 1, 3, 2]
def baseStart_1828546 : Nat := 118140960795 + 1828546 * 2 ^ 59
def prefixEnd_1828546 : Nat := 4983230072969 + 3 ^ 40 * 1828546 * 2
def baseEnd_1828546 : Nat := 938922996856308039065677

theorem tailTrace_1828546 : CollatzResearch.WordTrace tailWord_1828546 prefixEnd_1828546 938922996856308039065677 := by
  unfold tailWord_1828546
  simp only [CollatzResearch.WordTrace]
  refine ⟨16673137908374401909792373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44461701088998405092779661 16673137908374401909792373)
  ·
    refine ⟨1563106678910100179043035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16673137908374401909792373 1563106678910100179043035)
    ·
      refine ⟨2344660018365150268564553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1563106678910100179043035 2344660018365150268564553)
      ·
        refine ⟨1758495013773862701423415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2344660018365150268564553 1758495013773862701423415)
        ·
          refine ⟨2637742520660794052135123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1758495013773862701423415 2637742520660794052135123)
          ·
            refine ⟨3956613780991191078202685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2637742520660794052135123 3956613780991191078202685)
            ·
              refine ⟨1483730167871696654326007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3956613780991191078202685 1483730167871696654326007)
              ·
                refine ⟨2225595251807544981489011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1483730167871696654326007 2225595251807544981489011)
                ·
                  refine ⟨3338392877711317472233517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2225595251807544981489011 3338392877711317472233517)
                  ·
                    refine ⟨1251897329141744052087569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3338392877711317472233517 1251897329141744052087569)
                    ·
                      refine ⟨938922996856308039065677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1251897329141744052087569 938922996856308039065677)
                      ·
                        rfl

theorem cell23_1828546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_1828546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1828546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1828546 prefixEnd_1828546 := by exact prefixLift 1828546
  have htrace : WordTrace (prefixWord ++ tailWord_1828546) baseStart_1828546 baseEnd_1828546 := by
    simpa [prefixWord, tailWord_1828546, baseEnd_1828546] using wordTrace_append hprefix tailTrace_1828546
  have hstable : (prefixWord ++ tailWord_1828546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828546).length < 2 ^ (prefixWord ++ tailWord_1828546).sum := by decide
  have hdescent : baseEnd_1828546 < baseStart_1828546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828591 : List Nat := [1, 1, 2, 1, 5, 1, 3, 2, 3, 4]
def baseStart_1828591 : Nat := 118140960795 + 1828591 * 2 ^ 59
def prefixEnd_1828591 : Nat := 4983230072969 + 3 ^ 40 * 1828591 * 2
def baseEnd_1828591 : Nat := 312982034495253454334323

theorem tailTrace_1828591 : CollatzResearch.WordTrace tailWord_1828591 prefixEnd_1828591 312982034495253454334323 := by
  unfold tailWord_1828591
  simp only [CollatzResearch.WordTrace]
  refine ⟨66694192918334580324557627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44462795278889720216371751 66694192918334580324557627)
  ·
    refine ⟨100041289377501870486836441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66694192918334580324557627 100041289377501870486836441)
    ·
      refine ⟨75030967033126402865127331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100041289377501870486836441 75030967033126402865127331)
      ·
        refine ⟨112546450549689604297690997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75030967033126402865127331 112546450549689604297690997)
        ·
          refine ⟨10551229739033400402908531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 112546450549689604297690997 10551229739033400402908531)
          ·
            refine ⟨15826844608550100604362797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10551229739033400402908531 15826844608550100604362797)
            ·
              refine ⟨5935066728206287726636049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15826844608550100604362797 5935066728206287726636049)
              ·
                refine ⟨4451300046154715794977037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5935066728206287726636049 4451300046154715794977037)
                ·
                  refine ⟨1669237517308018423116389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4451300046154715794977037 1669237517308018423116389)
                  ·
                    refine ⟨312982034495253454334323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1669237517308018423116389 312982034495253454334323)
                    ·
                      rfl

theorem cell23_1828591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 2, 3, 4].length) (baseStart_1828591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1828591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1828591 prefixEnd_1828591 := by exact prefixLift 1828591
  have htrace : WordTrace (prefixWord ++ tailWord_1828591) baseStart_1828591 baseEnd_1828591 := by
    simpa [prefixWord, tailWord_1828591, baseEnd_1828591] using wordTrace_append hprefix tailTrace_1828591
  have hstable : (prefixWord ++ tailWord_1828591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828591).length < 2 ^ (prefixWord ++ tailWord_1828591).sum := by decide
  have hdescent : baseEnd_1828591 < baseStart_1828591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828598 : List Nat := [5, 1, 1, 1, 1, 3, 3, 1, 2, 1, 4]
def baseStart_1828598 : Nat := 118140960795 + 1828598 * 2 ^ 59
def prefixEnd_1828598 : Nat := 4983230072969 + 3 ^ 40 * 1828598 * 2
def baseEnd_1828598 : Nat := 938949697850341835615437

theorem tailTrace_1828598 : CollatzResearch.WordTrace tailWord_1828598 prefixEnd_1828598 938949697850341835615437 := by
  unfold tailWord_1828598
  simp only [CollatzResearch.WordTrace]
  refine ⟨4168403014331826282503903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44462965486206147013374965 4168403014331826282503903)
  ·
    refine ⟨6252604521497739423755855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4168403014331826282503903 6252604521497739423755855)
    ·
      refine ⟨9378906782246609135633783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6252604521497739423755855 9378906782246609135633783)
      ·
        refine ⟨14068360173369913703450675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9378906782246609135633783 14068360173369913703450675)
        ·
          refine ⟨21102540260054870555176013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14068360173369913703450675 21102540260054870555176013)
          ·
            refine ⟨7913452597520576458191005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21102540260054870555176013 7913452597520576458191005)
            ·
              refine ⟨2967544724070216171821627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7913452597520576458191005 2967544724070216171821627)
              ·
                refine ⟨4451317086105324257732441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2967544724070216171821627 4451317086105324257732441)
                ·
                  refine ⟨3338487814578993193299331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4451317086105324257732441 3338487814578993193299331)
                  ·
                    refine ⟨5007731721868489789948997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3338487814578993193299331 5007731721868489789948997)
                    ·
                      refine ⟨938949697850341835615437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5007731721868489789948997 938949697850341835615437)
                      ·
                        rfl

theorem cell23_1828598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 1, 2, 1, 4].length) (baseStart_1828598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1828598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1828598 prefixEnd_1828598 := by exact prefixLift 1828598
  have htrace : WordTrace (prefixWord ++ tailWord_1828598) baseStart_1828598 baseEnd_1828598 := by
    simpa [prefixWord, tailWord_1828598, baseEnd_1828598] using wordTrace_append hprefix tailTrace_1828598
  have hstable : (prefixWord ++ tailWord_1828598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828598).length < 2 ^ (prefixWord ++ tailWord_1828598).sum := by decide
  have hdescent : baseEnd_1828598 < baseStart_1828598 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828604 : List Nat := [2, 2, 2, 1, 3, 1, 2, 2, 8]
def baseStart_1828604 : Nat := 118140960795 + 1828604 * 2 ^ 59
def prefixEnd_1828604 : Nat := 4983230072969 + 3 ^ 40 * 1828604 * 2
def baseEnd_1828604 : Nat := 104328086526029868015601

theorem tailTrace_1828604 : CollatzResearch.WordTrace tailWord_1828604 prefixEnd_1828604 104328086526029868015601 := by
  unfold tailWord_1828604
  simp only [CollatzResearch.WordTrace]
  refine ⟨33347333533643741772390433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44463111378191655696520577 33347333533643741772390433)
  ·
    refine ⟨25010500150232806329292825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33347333533643741772390433 25010500150232806329292825)
    ·
      refine ⟨18757875112674604746969619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25010500150232806329292825 18757875112674604746969619)
      ·
        refine ⟨28136812669011907120454429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18757875112674604746969619 28136812669011907120454429)
        ·
          refine ⟨10551304750879465170170411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28136812669011907120454429 10551304750879465170170411)
          ·
            refine ⟨15826957126319197755255617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10551304750879465170170411 15826957126319197755255617)
            ·
              refine ⟨11870217844739398316441713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15826957126319197755255617 11870217844739398316441713)
              ·
                refine ⟨8902663383554548737331285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11870217844739398316441713 8902663383554548737331285)
                ·
                  refine ⟨104328086526029868015601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8902663383554548737331285 104328086526029868015601)
                  ·
                    rfl

theorem cell23_1828604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 2, 8].length) (baseStart_1828604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1828604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1828604 prefixEnd_1828604 := by exact prefixLift 1828604
  have htrace : WordTrace (prefixWord ++ tailWord_1828604) baseStart_1828604 baseEnd_1828604 := by
    simpa [prefixWord, tailWord_1828604, baseEnd_1828604] using wordTrace_append hprefix tailTrace_1828604
  have hstable : (prefixWord ++ tailWord_1828604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828604).length < 2 ^ (prefixWord ++ tailWord_1828604).sum := by decide
  have hdescent : baseEnd_1828604 < baseStart_1828604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828658 : List Nat := [3, 2, 1, 1, 3, 2, 2, 1, 1, 5, 2]
def baseStart_1828658 : Nat := 118140960795 + 1828658 * 2 ^ 59
def prefixEnd_1828658 : Nat := 4983230072969 + 3 ^ 40 * 1828658 * 2
def baseEnd_1828658 : Nat := 938980506689611600865161

theorem tailTrace_1828658 : CollatzResearch.WordTrace tailWord_1828658 prefixEnd_1828658 938980506689611600865161 := by
  unfold tailWord_1828658
  simp only [CollatzResearch.WordTrace]
  refine ⟨16674159152272962691811657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44464424406061233844831085 16674159152272962691811657)
  ·
    refine ⟨12505619364204722018858743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16674159152272962691811657 12505619364204722018858743)
    ·
      refine ⟨18758429046307083028288115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12505619364204722018858743 18758429046307083028288115)
      ·
        refine ⟨28137643569460624542432173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18758429046307083028288115 28137643569460624542432173)
        ·
          refine ⟨10551616338547734203412065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28137643569460624542432173 10551616338547734203412065)
          ·
            refine ⟨7913712253910800652559049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10551616338547734203412065 7913712253910800652559049)
            ·
              refine ⟨5935284190433100489419287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7913712253910800652559049 5935284190433100489419287)
              ·
                refine ⟨8902926285649650734128931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5935284190433100489419287 8902926285649650734128931)
                ·
                  refine ⟨13354389428474476101193397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8902926285649650734128931 13354389428474476101193397)
                  ·
                    refine ⟨1251974008919482134486881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13354389428474476101193397 1251974008919482134486881)
                    ·
                      refine ⟨938980506689611600865161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1251974008919482134486881 938980506689611600865161)
                      ·
                        rfl

theorem cell23_1828658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 1, 1, 5, 2].length) (baseStart_1828658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1828658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1828658 prefixEnd_1828658 := by exact prefixLift 1828658
  have htrace : WordTrace (prefixWord ++ tailWord_1828658) baseStart_1828658 baseEnd_1828658 := by
    simpa [prefixWord, tailWord_1828658, baseEnd_1828658] using wordTrace_append hprefix tailTrace_1828658
  have hstable : (prefixWord ++ tailWord_1828658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828658).length < 2 ^ (prefixWord ++ tailWord_1828658).sum := by decide
  have hdescent : baseEnd_1828658 < baseStart_1828658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828681 : List Nat := [1, 2, 1, 1, 2, 4, 1, 3, 4, 4]
def baseStart_1828681 : Nat := 118140960795 + 1828681 * 2 ^ 59
def prefixEnd_1828681 : Nat := 4983230072969 + 3 ^ 40 * 1828681 * 2
def baseEnd_1828681 : Nat := 312997438914888336959185

theorem tailTrace_1828681 : CollatzResearch.WordTrace tailWord_1828681 prefixEnd_1828681 312997438914888336959185 := by
  unfold tailWord_1828681
  simp only [CollatzResearch.WordTrace]
  refine ⟨66697475488008525695333897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44464983658672350463555931 66697475488008525695333897)
  ·
    refine ⟨50023106616006394271500423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66697475488008525695333897 50023106616006394271500423)
    ·
      refine ⟨75034659924009591407250635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50023106616006394271500423 75034659924009591407250635)
      ·
        refine ⟨112551989886014387110875953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75034659924009591407250635 112551989886014387110875953)
        ·
          refine ⟨84413992414510790333156965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112551989886014387110875953 84413992414510790333156965)
          ·
            refine ⟨15827623577720773187466931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84413992414510790333156965 15827623577720773187466931)
            ·
              refine ⟨23741435366581159781200397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15827623577720773187466931 23741435366581159781200397)
              ·
                refine ⟨8903038262467934917950149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23741435366581159781200397 8903038262467934917950149)
                ·
                  refine ⟨1669319674212737797115653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8903038262467934917950149 1669319674212737797115653)
                  ·
                    refine ⟨312997438914888336959185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1669319674212737797115653 312997438914888336959185)
                    ·
                      rfl

theorem cell23_1828681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 3, 4, 4].length) (baseStart_1828681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1828681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1828681 prefixEnd_1828681 := by exact prefixLift 1828681
  have htrace : WordTrace (prefixWord ++ tailWord_1828681) baseStart_1828681 baseEnd_1828681 := by
    simpa [prefixWord, tailWord_1828681, baseEnd_1828681] using wordTrace_append hprefix tailTrace_1828681
  have hstable : (prefixWord ++ tailWord_1828681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828681).length < 2 ^ (prefixWord ++ tailWord_1828681).sum := by decide
  have hdescent : baseEnd_1828681 < baseStart_1828681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828682 : List Nat := [3, 1, 2, 1, 1, 1, 7, 2, 1, 1, 3]
def baseStart_1828682 : Nat := 118140960795 + 1828682 * 2 ^ 59
def prefixEnd_1828682 : Nat := 4983230072969 + 3 ^ 40 * 1828682 * 2
def baseEnd_1828682 : Nat := 938992830225319506965051

theorem tailTrace_1828682 : CollatzResearch.WordTrace tailWord_1828682 prefixEnd_1828682 938992830225319506965051 := by
  unfold tailWord_1828682
  simp only [CollatzResearch.WordTrace]
  refine ⟨16674377990251225716530075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44465007974003268577413533 16674377990251225716530075)
  ·
    refine ⟨25011566985376838574795113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16674377990251225716530075 25011566985376838574795113)
    ·
      refine ⟨18758675239032628931096335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25011566985376838574795113 18758675239032628931096335)
      ·
        refine ⟨28138012858548943396644503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18758675239032628931096335 28138012858548943396644503)
        ·
          refine ⟨42207019287823415094966755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28138012858548943396644503 42207019287823415094966755)
          ·
            refine ⟨63310528931735122642450133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42207019287823415094966755 63310528931735122642450133)
            ·
              refine ⟨1483840521837541936932425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 63310528931735122642450133 1483840521837541936932425)
              ·
                refine ⟨1112880391378156452699319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1483840521837541936932425 1112880391378156452699319)
                ·
                  refine ⟨1669320587067234679048979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1112880391378156452699319 1669320587067234679048979)
                  ·
                    refine ⟨2503980880600852018573469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1669320587067234679048979 2503980880600852018573469)
                    ·
                      refine ⟨938992830225319506965051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2503980880600852018573469 938992830225319506965051)
                      ·
                        rfl

theorem cell23_1828682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 7, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 7, 2, 1, 1, 3].length) (baseStart_1828682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1828682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1828682 prefixEnd_1828682 := by exact prefixLift 1828682
  have htrace : WordTrace (prefixWord ++ tailWord_1828682) baseStart_1828682 baseEnd_1828682 := by
    simpa [prefixWord, tailWord_1828682, baseEnd_1828682] using wordTrace_append hprefix tailTrace_1828682
  have hstable : (prefixWord ++ tailWord_1828682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828682).length < 2 ^ (prefixWord ++ tailWord_1828682).sum := by decide
  have hdescent : baseEnd_1828682 < baseStart_1828682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828698 : List Nat := [3, 1, 1, 2, 1, 3, 3, 3, 2, 4]
def baseStart_1828698 : Nat := 118140960795 + 1828698 * 2 ^ 59
def prefixEnd_1828698 : Nat := 4983230072969 + 3 ^ 40 * 1828698 * 2
def baseEnd_1828698 : Nat := 313000348638597148121659

theorem tailTrace_1828698 : CollatzResearch.WordTrace tailWord_1828698 prefixEnd_1828698 313000348638597148121659 := by
  unfold tailWord_1828698
  simp only [CollatzResearch.WordTrace]
  refine ⟨16674523882236734399675687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44465397019297958399135165 16674523882236734399675687)
  ·
    refine ⟨25011785823355101599513531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16674523882236734399675687 25011785823355101599513531)
    ·
      refine ⟨37517678735032652399270297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25011785823355101599513531 37517678735032652399270297)
      ·
        refine ⟨28138259051274489299452723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37517678735032652399270297 28138259051274489299452723)
        ·
          refine ⟨42207388576911733949179085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28138259051274489299452723 42207388576911733949179085)
          ·
            refine ⟨15827770716341900230942157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42207388576911733949179085 15827770716341900230942157)
            ·
              refine ⟨5935414018628212586603309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15827770716341900230942157 5935414018628212586603309)
              ·
                refine ⟨2225780256985579719976241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5935414018628212586603309 2225780256985579719976241)
                ·
                  refine ⟨1669335192739184789982181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2225780256985579719976241 1669335192739184789982181)
                  ·
                    refine ⟨313000348638597148121659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1669335192739184789982181 313000348638597148121659)
                    ·
                      rfl

theorem cell23_1828698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 3, 2, 4].length) (baseStart_1828698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1828698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1828698 prefixEnd_1828698 := by exact prefixLift 1828698
  have htrace : WordTrace (prefixWord ++ tailWord_1828698) baseStart_1828698 baseEnd_1828698 := by
    simpa [prefixWord, tailWord_1828698, baseEnd_1828698] using wordTrace_append hprefix tailTrace_1828698
  have hstable : (prefixWord ++ tailWord_1828698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828698).length < 2 ^ (prefixWord ++ tailWord_1828698).sum := by decide
  have hdescent : baseEnd_1828698 < baseStart_1828698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828718 : List Nat := [4, 1, 2, 3, 1, 1, 1, 1, 3, 2, 4]
def baseStart_1828718 : Nat := 118140960795 + 1828718 * 2 ^ 59
def prefixEnd_1828718 : Nat := 4983230072969 + 3 ^ 40 * 1828718 * 2
def baseEnd_1828718 : Nat := 939011315528881366114885

theorem tailTrace_1828718 : CollatzResearch.WordTrace tailWord_1828718 prefixEnd_1828718 939011315528881366114885 := by
  unfold tailWord_1828718
  simp only [CollatzResearch.WordTrace]
  refine ⟨8337353123609310126803851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44465883325916320676287205 8337353123609310126803851)
  ·
    refine ⟨12506029685413965190205777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8337353123609310126803851 12506029685413965190205777)
    ·
      refine ⟨9379522264060473892654333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12506029685413965190205777 9379522264060473892654333)
      ·
        refine ⟨3517320849022677709745375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9379522264060473892654333 3517320849022677709745375)
        ·
          refine ⟨5275981273534016564618063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3517320849022677709745375 5275981273534016564618063)
          ·
            refine ⟨7913971910301024846927095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5275981273534016564618063 7913971910301024846927095)
            ·
              refine ⟨11870957865451537270390643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7913971910301024846927095 11870957865451537270390643)
              ·
                refine ⟨17806436798177305905585965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11870957865451537270390643 17806436798177305905585965)
                ·
                  refine ⟨6677413799316489714594737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17806436798177305905585965 6677413799316489714594737)
                  ·
                    refine ⟨5008060349487367285946053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6677413799316489714594737 5008060349487367285946053)
                    ·
                      refine ⟨939011315528881366114885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5008060349487367285946053 939011315528881366114885)
                      ·
                        rfl

theorem cell23_1828718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_1828718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1828718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1828718 prefixEnd_1828718 := by exact prefixLift 1828718
  have htrace : WordTrace (prefixWord ++ tailWord_1828718) baseStart_1828718 baseEnd_1828718 := by
    simpa [prefixWord, tailWord_1828718, baseEnd_1828718] using wordTrace_append hprefix tailTrace_1828718
  have hstable : (prefixWord ++ tailWord_1828718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828718).length < 2 ^ (prefixWord ++ tailWord_1828718).sum := by decide
  have hdescent : baseEnd_1828718 < baseStart_1828718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828722 : List Nat := [3, 2, 1, 2, 1, 1, 1, 7, 1, 2, 2]
def baseStart_1828722 : Nat := 118140960795 + 1828722 * 2 ^ 59
def prefixEnd_1828722 : Nat := 4983230072969 + 3 ^ 40 * 1828722 * 2
def baseEnd_1828722 : Nat := 939013369451499350464867

theorem tailTrace_1828722 : CollatzResearch.WordTrace tailWord_1828722 prefixEnd_1828722 939013369451499350464867 := by
  unfold tailWord_1828722
  simp only [CollatzResearch.WordTrace]
  refine ⟨16674742720214997424394105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44465980587239993131717613 16674742720214997424394105)
  ·
    refine ⟨12506057040161248068295579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16674742720214997424394105 12506057040161248068295579)
    ·
      refine ⟨18759085560241872102443369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12506057040161248068295579 18759085560241872102443369)
      ·
        refine ⟨14069314170181404076832527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18759085560241872102443369 14069314170181404076832527)
        ·
          refine ⟨21103971255272106115248791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14069314170181404076832527 21103971255272106115248791)
          ·
            refine ⟨31655956882908159172873187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21103971255272106115248791 31655956882908159172873187)
            ·
              refine ⟨47483935324362238759309781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31655956882908159172873187 47483935324362238759309781)
              ·
                refine ⟨1112904734164739970921323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 47483935324362238759309781 1112904734164739970921323)
                ·
                  refine ⟨1669357101247109956381985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1112904734164739970921323 1669357101247109956381985)
                  ·
                    refine ⟨1252017825935332467286489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1669357101247109956381985 1252017825935332467286489)
                    ·
                      refine ⟨939013369451499350464867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1252017825935332467286489 939013369451499350464867)
                      ·
                        rfl

theorem cell23_1828722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 7, 1, 2, 2].length) (baseStart_1828722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1828722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1828722 prefixEnd_1828722 := by exact prefixLift 1828722
  have htrace : WordTrace (prefixWord ++ tailWord_1828722) baseStart_1828722 baseEnd_1828722 := by
    simpa [prefixWord, tailWord_1828722, baseEnd_1828722] using wordTrace_append hprefix tailTrace_1828722
  have hstable : (prefixWord ++ tailWord_1828722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828722).length < 2 ^ (prefixWord ++ tailWord_1828722).sum := by decide
  have hdescent : baseEnd_1828722 < baseStart_1828722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828739 : List Nat := [1, 1, 1, 3, 4, 2, 4, 2, 1, 2, 2]
def baseStart_1828739 : Nat := 118140960795 + 1828739 * 2 ^ 59
def prefixEnd_1828739 : Nat := 4983230072969 + 3 ^ 40 * 1828739 * 2
def baseEnd_1828739 : Nat := 939022098622625783952289

theorem tailTrace_1828739 : CollatzResearch.WordTrace tailWord_1828739 prefixEnd_1828739 939022098622625783952289 := by
  unfold tailWord_1828739
  simp only [CollatzResearch.WordTrace]
  refine ⟨66699590921798401600945271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44466393947865601067296847 66699590921798401600945271)
  ·
    refine ⟨100049386382697602401417907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66699590921798401600945271 100049386382697602401417907)
    ·
      refine ⟨150074079574046403602126861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100049386382697602401417907 150074079574046403602126861)
      ·
        refine ⟨56277779840267401350797573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150074079574046403602126861 56277779840267401350797573)
        ·
          refine ⟨10552083720050137753274545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56277779840267401350797573 10552083720050137753274545)
          ·
            refine ⟨7914062790037603314955909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10552083720050137753274545 7914062790037603314955909)
            ·
              refine ⟨1483886773132050621554233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7914062790037603314955909 1483886773132050621554233)
              ·
                refine ⟨1112915079849037966165675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1483886773132050621554233 1112915079849037966165675)
                ·
                  refine ⟨1669372619773556949248513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1112915079849037966165675 1669372619773556949248513)
                  ·
                    refine ⟨1252029464830167711936385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1669372619773556949248513 1252029464830167711936385)
                    ·
                      refine ⟨939022098622625783952289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1252029464830167711936385 939022098622625783952289)
                      ·
                        rfl

theorem cell23_1828739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 4, 2, 1, 2, 2].length) (baseStart_1828739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1828739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1828739 prefixEnd_1828739 := by exact prefixLift 1828739
  have htrace : WordTrace (prefixWord ++ tailWord_1828739) baseStart_1828739 baseEnd_1828739 := by
    simpa [prefixWord, tailWord_1828739, baseEnd_1828739] using wordTrace_append hprefix tailTrace_1828739
  have hstable : (prefixWord ++ tailWord_1828739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828739).length < 2 ^ (prefixWord ++ tailWord_1828739).sum := by decide
  have hdescent : baseEnd_1828739 < baseStart_1828739 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828765 : List Nat := [1, 4, 2, 1, 2, 2, 2, 1, 3, 3, 2]
def baseStart_1828765 : Nat := 118140960795 + 1828765 * 2 ^ 59
def prefixEnd_1828765 : Nat := 4983230072969 + 3 ^ 40 * 1828765 * 2
def baseEnd_1828765 : Nat := 939035449119642682227169

theorem tailTrace_1828765 : CollatzResearch.WordTrace tailWord_1828765 prefixEnd_1828765 939035449119642682227169 := by
  unfold tailWord_1828765
  simp only [CollatzResearch.WordTrace]
  refine ⟨66700539219704208041391749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44467026146469472027594499 66700539219704208041391749)
  ·
    refine ⟨12506351103694539007760953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66700539219704208041391749 12506351103694539007760953)
    ·
      refine ⟨9379763327770904255820715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12506351103694539007760953 9379763327770904255820715)
      ·
        refine ⟨14069644991656356383731073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9379763327770904255820715 14069644991656356383731073)
        ·
          refine ⟨10552233743742267287798305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14069644991656356383731073 10552233743742267287798305)
          ·
            refine ⟨7914175307806700465848729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10552233743742267287798305 7914175307806700465848729)
            ·
              refine ⟨5935631480855025349386547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7914175307806700465848729 5935631480855025349386547)
              ·
                refine ⟨8903447221282538024079821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5935631480855025349386547 8903447221282538024079821)
                ·
                  refine ⟨3338792707980951759029933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8903447221282538024079821 3338792707980951759029933)
                  ·
                    refine ⟨1252047265492856909636225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3338792707980951759029933 1252047265492856909636225)
                    ·
                      refine ⟨939035449119642682227169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1252047265492856909636225 939035449119642682227169)
                      ·
                        rfl

theorem cell23_1828765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 1, 3, 3, 2].length) (baseStart_1828765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1828765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1828765 prefixEnd_1828765 := by exact prefixLift 1828765
  have htrace : WordTrace (prefixWord ++ tailWord_1828765) baseStart_1828765 baseEnd_1828765 := by
    simpa [prefixWord, tailWord_1828765, baseEnd_1828765] using wordTrace_append hprefix tailTrace_1828765
  have hstable : (prefixWord ++ tailWord_1828765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828765).length < 2 ^ (prefixWord ++ tailWord_1828765).sum := by decide
  have hdescent : baseEnd_1828765 < baseStart_1828765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828776 : List Nat := [2, 1, 6, 2, 1, 2, 2, 1, 1, 2, 3]
def baseStart_1828776 : Nat := 118140960795 + 1828776 * 2 ^ 59
def prefixEnd_1828776 : Nat := 4983230072969 + 3 ^ 40 * 1828776 * 2
def baseEnd_1828776 : Nat := 939041097406842139189619

theorem tailTrace_1828776 : CollatzResearch.WordTrace tailWord_1828776 prefixEnd_1828776 939041097406842139189619 := by
  unfold tailWord_1828776
  simp only [CollatzResearch.WordTrace]
  refine ⟨33350470211332178460021091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44467293615109571280028121 33350470211332178460021091)
  ·
    refine ⟨50025705316998267690031637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33350470211332178460021091 50025705316998267690031637)
    ·
      refine ⟨2344954936734293797970233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 50025705316998267690031637 2344954936734293797970233)
      ·
        refine ⟨1758716202550720348477675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2344954936734293797970233 1758716202550720348477675)
        ·
          refine ⟨2638074303826080522716513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1758716202550720348477675 2638074303826080522716513)
          ·
            refine ⟨1978555727869560392037385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2638074303826080522716513 1978555727869560392037385)
            ·
              refine ⟨1483916795902170294028039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1978555727869560392037385 1483916795902170294028039)
              ·
                refine ⟨2225875193853255441042059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1483916795902170294028039 2225875193853255441042059)
                ·
                  refine ⟨3338812790779883161563089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2225875193853255441042059 3338812790779883161563089)
                  ·
                    refine ⟨2504109593084912371172317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3338812790779883161563089 2504109593084912371172317)
                    ·
                      refine ⟨939041097406842139189619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2504109593084912371172317 939041097406842139189619)
                      ·
                        rfl

theorem cell23_1828776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_1828776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1828776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1828776 prefixEnd_1828776 := by exact prefixLift 1828776
  have htrace : WordTrace (prefixWord ++ tailWord_1828776) baseStart_1828776 baseEnd_1828776 := by
    simpa [prefixWord, tailWord_1828776, baseEnd_1828776] using wordTrace_append hprefix tailTrace_1828776
  have hstable : (prefixWord ++ tailWord_1828776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828776).length < 2 ^ (prefixWord ++ tailWord_1828776).sum := by decide
  have hdescent : baseEnd_1828776 < baseStart_1828776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828808 : List Nat := [2, 1, 3, 1, 4, 1, 2, 1, 2, 2, 4]
def baseStart_1828808 : Nat := 118140960795 + 1828808 * 2 ^ 59
def prefixEnd_1828808 : Nat := 4983230072969 + 3 ^ 40 * 1828808 * 2
def baseEnd_1828808 : Nat := 939057528787786013989471

theorem tailTrace_1828808 : CollatzResearch.WordTrace tailWord_1828808 prefixEnd_1828808 939057528787786013989471 := by
  unfold tailWord_1828808
  simp only [CollatzResearch.WordTrace]
  refine ⟨33351053779274213192603539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44468071705698950923471385 33351053779274213192603539)
  ·
    refine ⟨50026580668911319788905309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33351053779274213192603539 50026580668911319788905309)
    ·
      refine ⟨18759967750841744920839491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50026580668911319788905309 18759967750841744920839491)
      ·
        refine ⟨28139951626262617381259237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18759967750841744920839491 28139951626262617381259237)
        ·
          refine ⟨5276240929924240758986107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28139951626262617381259237 5276240929924240758986107)
          ·
            refine ⟨7914361394886361138479161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5276240929924240758986107 7914361394886361138479161)
            ·
              refine ⟨5935771046164770853859371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7914361394886361138479161 5935771046164770853859371)
              ·
                refine ⟨8903656569247156280789057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5935771046164770853859371 8903656569247156280789057)
                ·
                  refine ⟨6677742426935367210591793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8903656569247156280789057 6677742426935367210591793)
                  ·
                    refine ⟨5008306820201525407943845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6677742426935367210591793 5008306820201525407943845)
                    ·
                      refine ⟨939057528787786013989471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5008306820201525407943845 939057528787786013989471)
                      ·
                        rfl

theorem cell23_1828808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 1, 2, 2, 4].length) (baseStart_1828808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1828808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1828808 prefixEnd_1828808 := by exact prefixLift 1828808
  have htrace : WordTrace (prefixWord ++ tailWord_1828808) baseStart_1828808 baseEnd_1828808 := by
    simpa [prefixWord, tailWord_1828808, baseEnd_1828808] using wordTrace_append hprefix tailTrace_1828808
  have hstable : (prefixWord ++ tailWord_1828808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828808).length < 2 ^ (prefixWord ++ tailWord_1828808).sum := by decide
  have hdescent : baseEnd_1828808 < baseStart_1828808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828812 : List Nat := [2, 2, 1, 4, 1, 4, 1, 1, 1, 4, 2]
def baseStart_1828812 : Nat := 118140960795 + 1828812 * 2 ^ 59
def prefixEnd_1828812 : Nat := 4983230072969 + 3 ^ 40 * 1828812 * 2
def baseEnd_1828812 : Nat := 939059582710403998339453

theorem tailTrace_1828812 : CollatzResearch.WordTrace tailWord_1828812 prefixEnd_1828812 939059582710403998339453 := by
  unfold tailWord_1828812
  simp only [CollatzResearch.WordTrace]
  refine ⟨33351126725266967534176345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44468168967022623378901793 33351126725266967534176345)
  ·
    refine ⟨25013345043950225650632259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33351126725266967534176345 25013345043950225650632259)
    ·
      refine ⟨37520017565925338475948389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25013345043950225650632259 37520017565925338475948389)
      ·
        refine ⟨7035003293611000964240323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37520017565925338475948389 7035003293611000964240323)
        ·
          refine ⟨10552504940416501446360485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7035003293611000964240323 10552504940416501446360485)
          ·
            refine ⟨1978594676328094021192591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10552504940416501446360485 1978594676328094021192591)
            ·
              refine ⟨2967892014492141031788887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1978594676328094021192591 2967892014492141031788887)
              ·
                refine ⟨4451838021738211547683331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2967892014492141031788887 4451838021738211547683331)
                ·
                  refine ⟨6677757032607317321524997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4451838021738211547683331 6677757032607317321524997)
                  ·
                    refine ⟨1252079443613871997785937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6677757032607317321524997 1252079443613871997785937)
                    ·
                      refine ⟨939059582710403998339453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1252079443613871997785937 939059582710403998339453)
                      ·
                        rfl

theorem cell23_1828812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 1, 1, 4, 2].length) (baseStart_1828812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1828812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1828812 prefixEnd_1828812 := by exact prefixLift 1828812
  have htrace : WordTrace (prefixWord ++ tailWord_1828812) baseStart_1828812 baseEnd_1828812 := by
    simpa [prefixWord, tailWord_1828812, baseEnd_1828812] using wordTrace_append hprefix tailTrace_1828812
  have hstable : (prefixWord ++ tailWord_1828812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828812).length < 2 ^ (prefixWord ++ tailWord_1828812).sum := by decide
  have hdescent : baseEnd_1828812 < baseStart_1828812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828835 : List Nat := [1, 1, 1, 6, 1, 2, 3, 3, 5]
def baseStart_1828835 : Nat := 118140960795 + 1828835 * 2 ^ 59
def prefixEnd_1828835 : Nat := 4983230072969 + 3 ^ 40 * 1828835 * 2
def baseEnd_1828835 : Nat := 104341265862828600927983

theorem tailTrace_1828835 : CollatzResearch.WordTrace tailWord_1828835 prefixEnd_1828835 104341265862828600927983 := by
  unfold tailWord_1828835
  simp only [CollatzResearch.WordTrace]
  refine ⟨66703092329450609996439959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44468728219633739997626639 66703092329450609996439959)
  ·
    refine ⟨100054638494175914994659939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66703092329450609996439959 100054638494175914994659939)
    ·
      refine ⟨150081957741263872491989909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100054638494175914994659939 150081957741263872491989909)
      ·
        refine ⟨7035091769121744023062027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 150081957741263872491989909 7035091769121744023062027)
        ·
          refine ⟨10552637653682616034593041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7035091769121744023062027 10552637653682616034593041)
          ·
            refine ⟨7914478240261962025944781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10552637653682616034593041 7914478240261962025944781)
            ·
              refine ⟨2967929340098235759729293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7914478240261962025944781 2967929340098235759729293)
              ·
                refine ⟨1112973502536838409898485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2967929340098235759729293 1112973502536838409898485)
                ·
                  refine ⟨104341265862828600927983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1112973502536838409898485 104341265862828600927983)
                  ·
                    rfl

theorem cell23_1828835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 3, 5].length) (baseStart_1828835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1828835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1828835 prefixEnd_1828835 := by exact prefixLift 1828835
  have htrace : WordTrace (prefixWord ++ tailWord_1828835) baseStart_1828835 baseEnd_1828835 := by
    simpa [prefixWord, tailWord_1828835, baseEnd_1828835] using wordTrace_append hprefix tailTrace_1828835
  have hstable : (prefixWord ++ tailWord_1828835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828835).length < 2 ^ (prefixWord ++ tailWord_1828835).sum := by decide
  have hdescent : baseEnd_1828835 < baseStart_1828835 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828881 : List Nat := [1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 6]
def baseStart_1828881 : Nat := 118140960795 + 1828881 * 2 ^ 59
def prefixEnd_1828881 : Nat := 4983230072969 + 3 ^ 40 * 1828881 * 2
def baseEnd_1828881 : Nat := 939095012875564228376635

theorem tailTrace_1828881 : CollatzResearch.WordTrace tailWord_1828881 prefixEnd_1828881 939095012875564228376635 := by
  unfold tailWord_1828881
  simp only [CollatzResearch.WordTrace]
  refine ⟨66704770087283959852614497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44469846724855973235076331 66704770087283959852614497)
  ·
    refine ⟨50028577565462969889460873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66704770087283959852614497 50028577565462969889460873)
    ·
      refine ⟨37521433174097227417095655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50028577565462969889460873 37521433174097227417095655)
      ·
        refine ⟨56282149761145841125643483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37521433174097227417095655 56282149761145841125643483)
        ·
          refine ⟨84423224641718761688465225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56282149761145841125643483 84423224641718761688465225)
          ·
            refine ⟨63317418481289071266348919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84423224641718761688465225 63317418481289071266348919)
            ·
              refine ⟨94976127721933606899523379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63317418481289071266348919 94976127721933606899523379)
              ·
                refine ⟨142464191582900410349285069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94976127721933606899523379 142464191582900410349285069)
                ·
                  refine ⟨53424071843587653880981901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 142464191582900410349285069 53424071843587653880981901)
                  ·
                    refine ⟨20034026941345370205368213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53424071843587653880981901 20034026941345370205368213)
                    ·
                      refine ⟨939095012875564228376635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20034026941345370205368213 939095012875564228376635)
                      ·
                        rfl

theorem cell23_1828881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 6].length) (baseStart_1828881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1828881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1828881 prefixEnd_1828881 := by exact prefixLift 1828881
  have htrace : WordTrace (prefixWord ++ tailWord_1828881) baseStart_1828881 baseEnd_1828881 := by
    simpa [prefixWord, tailWord_1828881, baseEnd_1828881] using wordTrace_append hprefix tailTrace_1828881
  have hstable : (prefixWord ++ tailWord_1828881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828881).length < 2 ^ (prefixWord ++ tailWord_1828881).sum := by decide
  have hdescent : baseEnd_1828881 < baseStart_1828881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828891 : List Nat := [1, 1, 1, 1, 1, 1, 3, 6, 8]
def baseStart_1828891 : Nat := 118140960795 + 1828891 * 2 ^ 59
def prefixEnd_1828891 : Nat := 4983230072969 + 3 ^ 40 * 1828891 * 2
def baseEnd_1828891 : Nat := 104344460853567687694621

theorem tailTrace_1828891 : CollatzResearch.WordTrace tailWord_1828891 prefixEnd_1828891 104344460853567687694621 := by
  unfold tailWord_1828891
  simp only [CollatzResearch.WordTrace]
  refine ⟨66705134817247731560478527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44470089878165154373652351 66705134817247731560478527)
  ·
    refine ⟨100057702225871597340717791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66705134817247731560478527 100057702225871597340717791)
    ·
      refine ⟨150086553338807396011076687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100057702225871597340717791 150086553338807396011076687)
      ·
        refine ⟨225129830008211094016615031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150086553338807396011076687 225129830008211094016615031)
        ·
          refine ⟨337694745012316641024922547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225129830008211094016615031 337694745012316641024922547)
          ·
            refine ⟨506542117518474961537383821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 337694745012316641024922547 506542117518474961537383821)
            ·
              refine ⟨189953294069428110576518933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 506542117518474961537383821 189953294069428110576518933)
              ·
                refine ⟨8904060659504442683274325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 189953294069428110576518933 8904060659504442683274325)
                ·
                  refine ⟨104344460853567687694621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8904060659504442683274325 104344460853567687694621)
                  ·
                    rfl

theorem cell23_1828891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 6, 8].length) (baseStart_1828891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1828891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1828891 prefixEnd_1828891 := by exact prefixLift 1828891
  have htrace : WordTrace (prefixWord ++ tailWord_1828891) baseStart_1828891 baseEnd_1828891 := by
    simpa [prefixWord, tailWord_1828891, baseEnd_1828891] using wordTrace_append hprefix tailTrace_1828891
  have hstable : (prefixWord ++ tailWord_1828891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828891).length < 2 ^ (prefixWord ++ tailWord_1828891).sum := by decide
  have hdescent : baseEnd_1828891 < baseStart_1828891 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828898 : List Nat := [3, 3, 1, 1, 1, 2, 2, 1, 2, 1, 6]
def baseStart_1828898 : Nat := 118140960795 + 1828898 * 2 ^ 59
def prefixEnd_1828898 : Nat := 4983230072969 + 3 ^ 40 * 1828898 * 2
def baseEnd_1828898 : Nat := 939103742046690661864057

theorem tailTrace_1828898 : CollatzResearch.WordTrace tailWord_1828898 prefixEnd_1828898 939103742046690661864057 := by
  unfold tailWord_1828898
  simp only [CollatzResearch.WordTrace]
  refine ⟨16676347532055592938995837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44470260085481581170655565 16676347532055592938995837)
  ·
    refine ⟨6253630324520847352123439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16676347532055592938995837 6253630324520847352123439)
    ·
      refine ⟨9380445486781271028185159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6253630324520847352123439 9380445486781271028185159)
      ·
        refine ⟨14070668230171906542277739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9380445486781271028185159 14070668230171906542277739)
        ·
          refine ⟨21106002345257859813416609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14070668230171906542277739 21106002345257859813416609)
          ·
            refine ⟨15829501758943394860062457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21106002345257859813416609 15829501758943394860062457)
            ·
              refine ⟨11872126319207546145046843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15829501758943394860062457 11872126319207546145046843)
              ·
                refine ⟨17808189478811319217570265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11872126319207546145046843 17808189478811319217570265)
                ·
                  refine ⟨13356142109108489413177699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17808189478811319217570265 13356142109108489413177699)
                  ·
                    refine ⟨20034213163662734119766549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13356142109108489413177699 20034213163662734119766549)
                    ·
                      refine ⟨939103742046690661864057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20034213163662734119766549 939103742046690661864057)
                      ·
                        rfl

theorem cell23_1828898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_1828898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1828898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1828898 prefixEnd_1828898 := by exact prefixLift 1828898
  have htrace : WordTrace (prefixWord ++ tailWord_1828898) baseStart_1828898 baseEnd_1828898 := by
    simpa [prefixWord, tailWord_1828898, baseEnd_1828898] using wordTrace_append hprefix tailTrace_1828898
  have hstable : (prefixWord ++ tailWord_1828898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828898).length < 2 ^ (prefixWord ++ tailWord_1828898).sum := by decide
  have hdescent : baseEnd_1828898 < baseStart_1828898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828912 : List Nat := [2, 1, 1, 1, 2, 6, 1, 4, 1, 4]
def baseStart_1828912 : Nat := 118140960795 + 1828912 * 2 ^ 59
def prefixEnd_1828912 : Nat := 4983230072969 + 3 ^ 40 * 1828912 * 2
def baseEnd_1828912 : Nat := 313036976925284535696331

theorem tailTrace_1828912 : CollatzResearch.WordTrace tailWord_1828912 prefixEnd_1828912 313036976925284535696331 := by
  unfold tailWord_1828912
  simp only [CollatzResearch.WordTrace]
  refine ⟨33352950375085826073496495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44470600500114434764661993 33352950375085826073496495)
  ·
    refine ⟨50029425562628739110244743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33352950375085826073496495 50029425562628739110244743)
    ·
      refine ⟨75044138343943108665367115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50029425562628739110244743 75044138343943108665367115)
      ·
        refine ⟨112566207515914662998050673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75044138343943108665367115 112566207515914662998050673)
        ·
          refine ⟨84424655636935997248538005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112566207515914662998050673 84424655636935997248538005)
          ·
            refine ⟨3957405732981374871025219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 84424655636935997248538005 3957405732981374871025219)
            ·
              refine ⟨5936108599472062306537829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3957405732981374871025219 5936108599472062306537829)
              ·
                refine ⟨1113020362401011682475843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5936108599472062306537829 1113020362401011682475843)
                ·
                  refine ⟨1669530543601517523713765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1113020362401011682475843 1669530543601517523713765)
                  ·
                    refine ⟨313036976925284535696331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1669530543601517523713765 313036976925284535696331)
                    ·
                      rfl

theorem cell23_1828912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 4, 1, 4].length) (baseStart_1828912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1828912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1828912 prefixEnd_1828912 := by exact prefixLift 1828912
  have htrace : WordTrace (prefixWord ++ tailWord_1828912) baseStart_1828912 baseEnd_1828912 := by
    simpa [prefixWord, tailWord_1828912, baseEnd_1828912] using wordTrace_append hprefix tailTrace_1828912
  have hstable : (prefixWord ++ tailWord_1828912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828912).length < 2 ^ (prefixWord ++ tailWord_1828912).sum := by decide
  have hdescent : baseEnd_1828912 < baseStart_1828912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828948 : List Nat := [2, 4, 1, 1, 1, 1, 1, 1, 2, 4, 5]
def baseStart_1828948 : Nat := 118140960795 + 1828948 * 2 ^ 59
def prefixEnd_1828948 : Nat := 4983230072969 + 3 ^ 40 * 1828948 * 2
def baseEnd_1828948 : Nat := 939129416079415466238827

theorem tailTrace_1828948 : CollatzResearch.WordTrace tailWord_1828948 prefixEnd_1828948 939129416079415466238827 := by
  unfold tailWord_1828948
  simp only [CollatzResearch.WordTrace]
  refine ⟨33353606889020615147651749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44471475852027486863535665 33353606889020615147651749)
  ·
    refine ⟨6253801291691365340184703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33353606889020615147651749 6253801291691365340184703)
    ·
      refine ⟨9380701937537048010277055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6253801291691365340184703 9380701937537048010277055)
      ·
        refine ⟨14071052906305572015415583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9380701937537048010277055 14071052906305572015415583)
        ·
          refine ⟨21106579359458358023123375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14071052906305572015415583 21106579359458358023123375)
          ·
            refine ⟨31659869039187537034685063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21106579359458358023123375 31659869039187537034685063)
            ·
              refine ⟨47489803558781305552027595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31659869039187537034685063 47489803558781305552027595)
              ·
                refine ⟨71234705338171958328041393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47489803558781305552027595 71234705338171958328041393)
                ·
                  refine ⟨53426029003628968746031045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71234705338171958328041393 53426029003628968746031045)
                  ·
                    refine ⟨10017380438180431639880821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53426029003628968746031045 10017380438180431639880821)
                    ·
                      refine ⟨939129416079415466238827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10017380438180431639880821 939129416079415466238827)
                      ·
                        rfl

theorem cell23_1828948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_1828948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1828948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1828948 prefixEnd_1828948 := by exact prefixLift 1828948
  have htrace : WordTrace (prefixWord ++ tailWord_1828948) baseStart_1828948 baseEnd_1828948 := by
    simpa [prefixWord, tailWord_1828948, baseEnd_1828948] using wordTrace_append hprefix tailTrace_1828948
  have hstable : (prefixWord ++ tailWord_1828948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828948).length < 2 ^ (prefixWord ++ tailWord_1828948).sum := by decide
  have hdescent : baseEnd_1828948 < baseStart_1828948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828985 : List Nat := [1, 2, 1, 3, 4, 1, 3, 1, 1, 6]
def baseStart_1828985 : Nat := 118140960795 + 1828985 * 2 ^ 59
def prefixEnd_1828985 : Nat := 4983230072969 + 3 ^ 40 * 1828985 * 2
def baseEnd_1828985 : Nat := 313049471621210607158719

theorem tailTrace_1828985 : CollatzResearch.WordTrace tailWord_1828985 prefixEnd_1828985 313049471621210607158719 := by
  unfold tailWord_1828985
  simp only [CollatzResearch.WordTrace]
  refine ⟨66708563278907185614400409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44472375519271457076266939 66708563278907185614400409)
  ·
    refine ⟨50031422459180389210800307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66708563278907185614400409 50031422459180389210800307)
    ·
      refine ⟨75047133688770583816200461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50031422459180389210800307 75047133688770583816200461)
      ·
        refine ⟨28142675133288968931075173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75047133688770583816200461 28142675133288968931075173)
        ·
          refine ⟨5276751587491681674576595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28142675133288968931075173 5276751587491681674576595)
          ·
            refine ⟨7915127381237522511864893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5276751587491681674576595 7915127381237522511864893)
            ·
              refine ⟨2968172767964070941949335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7915127381237522511864893 2968172767964070941949335)
              ·
                refine ⟨4452259151946106412924003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2968172767964070941949335 4452259151946106412924003)
                ·
                  refine ⟨6678388727919159619386005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4452259151946106412924003 6678388727919159619386005)
                  ·
                    refine ⟨313049471621210607158719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6678388727919159619386005 313049471621210607158719)
                    ·
                      rfl

theorem cell23_1828985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 1, 1, 6].length) (baseStart_1828985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1828985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1828985 prefixEnd_1828985 := by exact prefixLift 1828985
  have htrace : WordTrace (prefixWord ++ tailWord_1828985) baseStart_1828985 baseEnd_1828985 := by
    simpa [prefixWord, tailWord_1828985, baseEnd_1828985] using wordTrace_append hprefix tailTrace_1828985
  have hstable : (prefixWord ++ tailWord_1828985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828985).length < 2 ^ (prefixWord ++ tailWord_1828985).sum := by decide
  have hdescent : baseEnd_1828985 < baseStart_1828985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829015 : List Nat := [1, 1, 3, 3, 4, 2, 9]
def baseStart_1829015 : Nat := 118140960795 + 1829015 * 2 ^ 59
def prefixEnd_1829015 : Nat := 4983230072969 + 3 ^ 40 * 1829015 * 2
def baseEnd_1829015 : Nat := 11594615052879835853099

theorem tailTrace_1829015 : CollatzResearch.WordTrace tailWord_1829015 prefixEnd_1829015 11594615052879835853099 := by
  unfold tailWord_1829015
  simp only [CollatzResearch.WordTrace]
  refine ⟨66709657468798500737992499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44473104979199000491994999 66709657468798500737992499)
  ·
    refine ⟨100064486203197751106988749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66709657468798500737992499 100064486203197751106988749)
    ·
      refine ⟨37524182326199156665120781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100064486203197751106988749 37524182326199156665120781)
      ·
        refine ⟨14071568372324683749420293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37524182326199156665120781 14071568372324683749420293)
        ·
          refine ⟨2638419069810878203016305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14071568372324683749420293 2638419069810878203016305)
          ·
            refine ⟨1978814302358158652262229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2638419069810878203016305 1978814302358158652262229)
            ·
              refine ⟨11594615052879835853099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1978814302358158652262229 11594615052879835853099)
              ·
                rfl

theorem cell23_1829015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 9].length) (baseStart_1829015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1829015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1829015 prefixEnd_1829015 := by exact prefixLift 1829015
  have htrace : WordTrace (prefixWord ++ tailWord_1829015) baseStart_1829015 baseEnd_1829015 := by
    simpa [prefixWord, tailWord_1829015, baseEnd_1829015] using wordTrace_append hprefix tailTrace_1829015
  have hstable : (prefixWord ++ tailWord_1829015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829015).length < 2 ^ (prefixWord ++ tailWord_1829015).sum := by decide
  have hdescent : baseEnd_1829015 < baseStart_1829015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829026 : List Nat := [3, 3, 1, 3, 1, 1, 3, 1, 3, 2, 2]
def baseStart_1829026 : Nat := 118140960795 + 1829026 * 2 ^ 59
def prefixEnd_1829026 : Nat := 4983230072969 + 3 ^ 40 * 1829026 * 2
def baseEnd_1829026 : Nat := 939169467570466161063469

theorem tailTrace_1829026 : CollatzResearch.WordTrace tailWord_1829026 prefixEnd_1829026 939169467570466161063469 := by
  unfold tailWord_1829026
  simp only [CollatzResearch.WordTrace]
  refine ⟨16677514667939662404160733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44473372447839099744428621 16677514667939662404160733)
  ·
    refine ⟨6254068000477373401560275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16677514667939662404160733 6254068000477373401560275)
    ·
      refine ⟨9381102000716060102340413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6254068000477373401560275 9381102000716060102340413)
      ·
        refine ⟨3517913250268522538377655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9381102000716060102340413 3517913250268522538377655)
        ·
          refine ⟨5276869875402783807566483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3517913250268522538377655 5276869875402783807566483)
          ·
            refine ⟨7915304813104175711349725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5276869875402783807566483 7915304813104175711349725)
            ·
              refine ⟨2968239304914065891756147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7915304813104175711349725 2968239304914065891756147)
              ·
                refine ⟨4452358957371098837634221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2968239304914065891756147 4452358957371098837634221)
                ·
                  refine ⟨1669634609014162064112833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4452358957371098837634221 1669634609014162064112833)
                  ·
                    refine ⟨1252225956760621548084625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1669634609014162064112833 1252225956760621548084625)
                    ·
                      refine ⟨939169467570466161063469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1252225956760621548084625 939169467570466161063469)
                      ·
                        rfl

theorem cell23_1829026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_1829026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1829026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1829026 prefixEnd_1829026 := by exact prefixLift 1829026
  have htrace : WordTrace (prefixWord ++ tailWord_1829026) baseStart_1829026 baseEnd_1829026 := by
    simpa [prefixWord, tailWord_1829026, baseEnd_1829026] using wordTrace_append hprefix tailTrace_1829026
  have hstable : (prefixWord ++ tailWord_1829026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829026).length < 2 ^ (prefixWord ++ tailWord_1829026).sum := by decide
  have hdescent : baseEnd_1829026 < baseStart_1829026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829077 : List Nat := [1, 3, 2, 4, 3, 1, 2, 2, 1, 2, 2]
def baseStart_1829077 : Nat := 118140960795 + 1829077 * 2 ^ 59
def prefixEnd_1829077 : Nat := 4983230072969 + 3 ^ 40 * 1829077 * 2
def baseEnd_1829077 : Nat := 939195655083845461525735

theorem tailTrace_1829077 : CollatzResearch.WordTrace tailWord_1829077 prefixEnd_1829077 939195655083845461525735 := by
  unfold tailWord_1829077
  simp only [CollatzResearch.WordTrace]
  refine ⟨66711918794573885326749485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44474612529715923551166323 66711918794573885326749485)
  ·
    refine ⟨25016969547965206997531057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66711918794573885326749485 25016969547965206997531057)
    ·
      refine ⟨18762727160973905248148293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25016969547965206997531057 18762727160973905248148293)
      ·
        refine ⟨3518011342682607234027805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18762727160973905248148293 3518011342682607234027805)
        ·
          refine ⟨1319254253505977712760427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3518011342682607234027805 1319254253505977712760427)
          ·
            refine ⟨1978881380258966569140641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1319254253505977712760427 1978881380258966569140641)
            ·
              refine ⟨1484161035194224926855481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1978881380258966569140641 1484161035194224926855481)
              ·
                refine ⟨1113120776395668695141611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1484161035194224926855481 1113120776395668695141611)
                ·
                  refine ⟨1669681164593503042712417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1113120776395668695141611 1669681164593503042712417)
                  ·
                    refine ⟨1252260873445127282034313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1669681164593503042712417 1252260873445127282034313)
                    ·
                      refine ⟨939195655083845461525735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1252260873445127282034313 939195655083845461525735)
                      ·
                        rfl

theorem cell23_1829077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_1829077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1829077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1829077 prefixEnd_1829077 := by exact prefixLift 1829077
  have htrace : WordTrace (prefixWord ++ tailWord_1829077) baseStart_1829077 baseEnd_1829077 := by
    simpa [prefixWord, tailWord_1829077, baseEnd_1829077] using wordTrace_append hprefix tailTrace_1829077
  have hstable : (prefixWord ++ tailWord_1829077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829077).length < 2 ^ (prefixWord ++ tailWord_1829077).sum := by decide
  have hdescent : baseEnd_1829077 < baseStart_1829077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829099 : List Nat := [1, 1, 1, 1, 2, 5, 1, 5, 2, 2, 2]
def baseStart_1829099 : Nat := 118140960795 + 1829099 * 2 ^ 59
def prefixEnd_1829099 : Nat := 4983230072969 + 3 ^ 40 * 1829099 * 2
def baseEnd_1829099 : Nat := 939206951658244375450633

theorem tailTrace_1829099 : CollatzResearch.WordTrace tailWord_1829099 prefixEnd_1829099 939206951658244375450633 := by
  unfold tailWord_1829099
  simp only [CollatzResearch.WordTrace]
  refine ⟨66712721200494183084050351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44475147466996122056033567 66712721200494183084050351)
  ·
    refine ⟨100069081800741274626075527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66712721200494183084050351 100069081800741274626075527)
    ·
      refine ⟨150103622701111911939113291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100069081800741274626075527 150103622701111911939113291)
      ·
        refine ⟨225155434051667867908669937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150103622701111911939113291 225155434051667867908669937)
        ·
          refine ⟨168866575538750900931502453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225155434051667867908669937 168866575538750900931502453)
          ·
            refine ⟨15831241456757896962328355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 168866575538750900931502453 15831241456757896962328355)
            ·
              refine ⟨23746862185136845443492533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15831241456757896962328355 23746862185136845443492533)
              ·
                refine ⟨2226268329856579260327425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23746862185136845443492533 2226268329856579260327425)
                ·
                  refine ⟨1669701247392434445245569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2226268329856579260327425 1669701247392434445245569)
                  ·
                    refine ⟨1252275935544325833934177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1669701247392434445245569 1252275935544325833934177)
                    ·
                      refine ⟨939206951658244375450633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1252275935544325833934177 939206951658244375450633)
                      ·
                        rfl

theorem cell23_1829099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 5, 2, 2, 2].length) (baseStart_1829099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1829099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1829099 prefixEnd_1829099 := by exact prefixLift 1829099
  have htrace : WordTrace (prefixWord ++ tailWord_1829099) baseStart_1829099 baseEnd_1829099 := by
    simpa [prefixWord, tailWord_1829099, baseEnd_1829099] using wordTrace_append hprefix tailTrace_1829099
  have hstable : (prefixWord ++ tailWord_1829099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829099).length < 2 ^ (prefixWord ++ tailWord_1829099).sum := by decide
  have hdescent : baseEnd_1829099 < baseStart_1829099 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829135 : List Nat := [1, 1, 2, 1, 1, 1, 3, 6, 2, 5]
def baseStart_1829135 : Nat := 118140960795 + 1829135 * 2 ^ 59
def prefixEnd_1829135 : Nat := 4983230072969 + 3 ^ 40 * 1829135 * 2
def baseEnd_1829135 : Nat := 313075145653935411533489

theorem tailTrace_1829135 : CollatzResearch.WordTrace tailWord_1829135 prefixEnd_1829135 313075145653935411533489 := by
  unfold tailWord_1829135
  simp only [CollatzResearch.WordTrace]
  refine ⟨66714034228363761232360859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44476022818909174154907239 66714034228363761232360859)
  ·
    refine ⟨100071051342545641848541289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66714034228363761232360859 100071051342545641848541289)
    ·
      refine ⟨75053288506909231386405967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100071051342545641848541289 75053288506909231386405967)
      ·
        refine ⟨112579932760363847079608951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75053288506909231386405967 112579932760363847079608951)
        ·
          refine ⟨168869899140545770619413427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112579932760363847079608951 168869899140545770619413427)
          ·
            refine ⟨253304848710818655929120141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168869899140545770619413427 253304848710818655929120141)
            ·
              refine ⟨94989318266556995973420053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 253304848710818655929120141 94989318266556995973420053)
              ·
                refine ⟨4452624293744859186254065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 94989318266556995973420053 4452624293744859186254065)
                ·
                  refine ⟨3339468220308644389690549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4452624293744859186254065 3339468220308644389690549)
                  ·
                    refine ⟨313075145653935411533489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3339468220308644389690549 313075145653935411533489)
                    ·
                      rfl

theorem cell23_1829135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 6, 2, 5].length) (baseStart_1829135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1829135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1829135 prefixEnd_1829135 := by exact prefixLift 1829135
  have htrace : WordTrace (prefixWord ++ tailWord_1829135) baseStart_1829135 baseEnd_1829135 := by
    simpa [prefixWord, tailWord_1829135, baseEnd_1829135] using wordTrace_append hprefix tailTrace_1829135
  have hstable : (prefixWord ++ tailWord_1829135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829135).length < 2 ^ (prefixWord ++ tailWord_1829135).sum := by decide
  have hdescent : baseEnd_1829135 < baseStart_1829135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829155 : List Nat := [1, 1, 1, 4, 2, 2, 1, 1, 3, 3, 4]
def baseStart_1829155 : Nat := 118140960795 + 1829155 * 2 ^ 59
def prefixEnd_1829155 : Nat := 4983230072969 + 3 ^ 40 * 1829155 * 2
def baseEnd_1829155 : Nat := 939235706574896156350375

theorem tailTrace_1829155 : CollatzResearch.WordTrace tailWord_1829155 prefixEnd_1829155 939235706574896156350375 := by
  unfold tailWord_1829155
  simp only [CollatzResearch.WordTrace]
  refine ⟨66714763688291304648088919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44476509125527536432059279 66714763688291304648088919)
  ·
    refine ⟨100072145532436956972133379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66714763688291304648088919 100072145532436956972133379)
    ·
      refine ⟨150108218298655435458200069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100072145532436956972133379 150108218298655435458200069)
      ·
        refine ⟨28145290930997894148412513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 150108218298655435458200069 28145290930997894148412513)
        ·
          refine ⟨21108968198248420611309385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28145290930997894148412513 21108968198248420611309385)
          ·
            refine ⟨15831726148686315458482039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21108968198248420611309385 15831726148686315458482039)
            ·
              refine ⟨23747589223029473187723059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15831726148686315458482039 23747589223029473187723059)
              ·
                refine ⟨35621383834544209781584589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23747589223029473187723059 35621383834544209781584589)
                ·
                  refine ⟨13358018937954078668094221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35621383834544209781584589 13358018937954078668094221)
                  ·
                    refine ⟨5009257101732779500535333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13358018937954078668094221 5009257101732779500535333)
                    ·
                      refine ⟨939235706574896156350375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5009257101732779500535333 939235706574896156350375)
                      ·
                        rfl

theorem cell23_1829155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 3, 3, 4].length) (baseStart_1829155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1829155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1829155 prefixEnd_1829155 := by exact prefixLift 1829155
  have htrace : WordTrace (prefixWord ++ tailWord_1829155) baseStart_1829155 baseEnd_1829155 := by
    simpa [prefixWord, tailWord_1829155, baseEnd_1829155] using wordTrace_append hprefix tailTrace_1829155
  have hstable : (prefixWord ++ tailWord_1829155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829155).length < 2 ^ (prefixWord ++ tailWord_1829155).sum := by decide
  have hdescent : baseEnd_1829155 < baseStart_1829155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829192 : List Nat := [2, 1, 3, 1, 1, 2, 3, 1, 4, 2, 3]
def baseStart_1829192 : Nat := 118140960795 + 1829192 * 2 ^ 59
def prefixEnd_1829192 : Nat := 4983230072969 + 3 ^ 40 * 1829192 * 2
def baseEnd_1829192 : Nat := 939254705359112511587705

theorem tailTrace_1829192 : CollatzResearch.WordTrace tailWord_1829192 prefixEnd_1829192 939254705359112511587705 := by
  unfold tailWord_1829192
  simp only [CollatzResearch.WordTrace]
  refine ⟨33358056594578629983592915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44477408792771506644790553 33358056594578629983592915)
  ·
    refine ⟨50037084891867944975389373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33358056594578629983592915 50037084891867944975389373)
    ·
      refine ⟨18763906834450479365771015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50037084891867944975389373 18763906834450479365771015)
      ·
        refine ⟨28145860251675719048656523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18763906834450479365771015 28145860251675719048656523)
        ·
          refine ⟨42218790377513578572984785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28145860251675719048656523 42218790377513578572984785)
          ·
            refine ⟨31664092783135183929738589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42218790377513578572984785 31664092783135183929738589)
            ·
              refine ⟨11874034793675693973651971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31664092783135183929738589 11874034793675693973651971)
              ·
                refine ⟨17811052190513540960477957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11874034793675693973651971 17811052190513540960477957)
                ·
                  refine ⟨3339572285721288930089617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17811052190513540960477957 3339572285721288930089617)
                  ·
                    refine ⟨2504679214290966697567213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3339572285721288930089617 2504679214290966697567213)
                    ·
                      refine ⟨939254705359112511587705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2504679214290966697567213 939254705359112511587705)
                      ·
                        rfl

theorem cell23_1829192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 4, 2, 3].length) (baseStart_1829192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1829192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1829192 prefixEnd_1829192 := by exact prefixLift 1829192
  have htrace : WordTrace (prefixWord ++ tailWord_1829192) baseStart_1829192 baseEnd_1829192 := by
    simpa [prefixWord, tailWord_1829192, baseEnd_1829192] using wordTrace_append hprefix tailTrace_1829192
  have hstable : (prefixWord ++ tailWord_1829192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829192).length < 2 ^ (prefixWord ++ tailWord_1829192).sum := by decide
  have hdescent : baseEnd_1829192 < baseStart_1829192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829215 : List Nat := [1, 1, 2, 3, 1, 2, 2, 2, 1, 2, 6]
def baseStart_1829215 : Nat := 118140960795 + 1829215 * 2 ^ 59
def prefixEnd_1829215 : Nat := 4983230072969 + 3 ^ 40 * 1829215 * 2
def baseEnd_1829215 : Nat := 939266515414165921600099

theorem tailTrace_1829215 : CollatzResearch.WordTrace tailWord_1829215 prefixEnd_1829215 939266515414165921600099 := by
  unfold tailWord_1829215
  simp only [CollatzResearch.WordTrace]
  refine ⟨66716952068073934895273099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44477968045382623263515399 66716952068073934895273099)
  ·
    refine ⟨100075428102110902342909649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66716952068073934895273099 100075428102110902342909649)
    ·
      refine ⟨75056571076583176757182237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100075428102110902342909649 75056571076583176757182237)
      ·
        refine ⟨28146214153718691283943339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75056571076583176757182237 28146214153718691283943339)
        ·
          refine ⟨42219321230578036925915009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28146214153718691283943339 42219321230578036925915009)
          ·
            refine ⟨31664490922933527694436257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42219321230578036925915009 31664490922933527694436257)
            ·
              refine ⟨23748368192200145770827193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31664490922933527694436257 23748368192200145770827193)
              ·
                refine ⟨17811276144150109328120395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23748368192200145770827193 17811276144150109328120395)
                ·
                  refine ⟨26716914216225163992180593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17811276144150109328120395 26716914216225163992180593)
                  ·
                    refine ⟨20037685662168872994135445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26716914216225163992180593 20037685662168872994135445)
                    ·
                      refine ⟨939266515414165921600099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20037685662168872994135445 939266515414165921600099)
                      ·
                        rfl

theorem cell23_1829215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 2, 6].length) (baseStart_1829215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1829215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1829215 prefixEnd_1829215 := by exact prefixLift 1829215
  have htrace : WordTrace (prefixWord ++ tailWord_1829215) baseStart_1829215 baseEnd_1829215 := by
    simpa [prefixWord, tailWord_1829215, baseEnd_1829215] using wordTrace_append hprefix tailTrace_1829215
  have hstable : (prefixWord ++ tailWord_1829215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829215).length < 2 ^ (prefixWord ++ tailWord_1829215).sum := by decide
  have hdescent : baseEnd_1829215 < baseStart_1829215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829226 : List Nat := [3, 1, 3, 3, 1, 2, 2, 1, 2, 2, 3]
def baseStart_1829226 : Nat := 118140960795 + 1829226 * 2 ^ 59
def prefixEnd_1829226 : Nat := 4983230072969 + 3 ^ 40 * 1829226 * 2
def baseEnd_1829226 : Nat := 939272163701365378562549

theorem tailTrace_1829226 : CollatzResearch.WordTrace tailWord_1829226 prefixEnd_1829226 939272163701365378562549 := by
  unfold tailWord_1829226
  simp only [CollatzResearch.WordTrace]
  refine ⟨16679338317758520943480883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44478235514022722515949021 16679338317758520943480883)
  ·
    refine ⟨25019007476637781415221325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16679338317758520943480883 25019007476637781415221325)
    ·
      refine ⟨9382127803739168030707997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25019007476637781415221325 9382127803739168030707997)
      ·
        refine ⟨3518297926402188011515499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9382127803739168030707997 3518297926402188011515499)
        ·
          refine ⟨5277446889603282017273249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3518297926402188011515499 5277446889603282017273249)
          ·
            refine ⟨3958085167202461512954937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5277446889603282017273249 3958085167202461512954937)
            ·
              refine ⟨2968563875401846134716203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3958085167202461512954937 2968563875401846134716203)
              ·
                refine ⟨4452845813102769202074305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2968563875401846134716203 4452845813102769202074305)
                ·
                  refine ⟨3339634359827076901555729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4452845813102769202074305 3339634359827076901555729)
                  ·
                    refine ⟨2504725769870307676166797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3339634359827076901555729 2504725769870307676166797)
                    ·
                      refine ⟨939272163701365378562549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2504725769870307676166797 939272163701365378562549)
                      ·
                        rfl

theorem cell23_1829226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_1829226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1829226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1829226 prefixEnd_1829226 := by exact prefixLift 1829226
  have htrace : WordTrace (prefixWord ++ tailWord_1829226) baseStart_1829226 baseEnd_1829226 := by
    simpa [prefixWord, tailWord_1829226, baseEnd_1829226] using wordTrace_append hprefix tailTrace_1829226
  have hstable : (prefixWord ++ tailWord_1829226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829226).length < 2 ^ (prefixWord ++ tailWord_1829226).sum := by decide
  have hdescent : baseEnd_1829226 < baseStart_1829226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829250 : List Nat := [3, 4, 2, 1, 2, 1, 1, 4, 1, 4]
def baseStart_1829250 : Nat := 118140960795 + 1829250 * 2 ^ 59
def prefixEnd_1829250 : Nat := 4983230072969 + 3 ^ 40 * 1829250 * 2
def baseEnd_1829250 : Nat := 313094829079024428220813

theorem tailTrace_1829250 : CollatzResearch.WordTrace tailWord_1829250 prefixEnd_1829250 313094829079024428220813 := by
  unfold tailWord_1829250
  simp only [CollatzResearch.WordTrace]
  refine ⟨16679557155736783968199301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44478819081964757248531469 16679557155736783968199301)
  ·
    refine ⟨3127416966700646994037369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16679557155736783968199301 3127416966700646994037369)
    ·
      refine ⟨2345562725025485245528027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3127416966700646994037369 2345562725025485245528027)
      ·
        refine ⟨3518344087538227868292041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2345562725025485245528027 3518344087538227868292041)
        ·
          refine ⟨2638758065653670901219031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3518344087538227868292041 2638758065653670901219031)
          ·
            refine ⟨3958137098480506351828547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2638758065653670901219031 3958137098480506351828547)
            ·
              refine ⟨5937205647720759527742821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3958137098480506351828547 5937205647720759527742821)
              ·
                refine ⟨1113226058947642411451779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5937205647720759527742821 1113226058947642411451779)
                ·
                  refine ⟨1669839088421463617177669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1113226058947642411451779 1669839088421463617177669)
                  ·
                    refine ⟨313094829079024428220813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1669839088421463617177669 313094829079024428220813)
                    ·
                      rfl

theorem cell23_1829250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_1829250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1829250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1829250 prefixEnd_1829250 := by exact prefixLift 1829250
  have htrace : WordTrace (prefixWord ++ tailWord_1829250) baseStart_1829250 baseEnd_1829250 := by
    simpa [prefixWord, tailWord_1829250, baseEnd_1829250] using wordTrace_append hprefix tailTrace_1829250
  have hstable : (prefixWord ++ tailWord_1829250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829250).length < 2 ^ (prefixWord ++ tailWord_1829250).sum := by decide
  have hdescent : baseEnd_1829250 < baseStart_1829250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829279 : List Nat := [1, 1, 2, 5, 1, 1, 2, 4, 1, 1, 4]
def baseStart_1829279 : Nat := 118140960795 + 1829279 * 2 ^ 59
def prefixEnd_1829279 : Nat := 4983230072969 + 3 ^ 40 * 1829279 * 2
def baseEnd_1829279 : Nat := 939299378176053671199805

theorem tailTrace_1829279 : CollatzResearch.WordTrace tailWord_1829279 prefixEnd_1829279 939299378176053671199805 := by
  unfold tailWord_1829279
  simp only [CollatzResearch.WordTrace]
  refine ⟨66719286339842073825602891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44479524226561382550401927 66719286339842073825602891)
  ·
    refine ⟨100078929509763110738404337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66719286339842073825602891 100078929509763110738404337)
    ·
      refine ⟨75059197132322333053803253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100078929509763110738404337 75059197132322333053803253)
      ·
        refine ⟨7036799731155218723794055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 75059197132322333053803253 7036799731155218723794055)
        ·
          refine ⟨10555199596732828085691083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7036799731155218723794055 10555199596732828085691083)
          ·
            refine ⟨15832799395099242128536625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10555199596732828085691083 15832799395099242128536625)
            ·
              refine ⟨11874599546324431596402469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15832799395099242128536625 11874599546324431596402469)
              ·
                refine ⟨2226487414935830924325463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11874599546324431596402469 2226487414935830924325463)
                ·
                  refine ⟨3339731122403746386488195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2226487414935830924325463 3339731122403746386488195)
                  ·
                    refine ⟨5009596683605619579732293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3339731122403746386488195 5009596683605619579732293)
                    ·
                      refine ⟨939299378176053671199805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5009596683605619579732293 939299378176053671199805)
                      ·
                        rfl

theorem cell23_1829279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_1829279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1829279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1829279 prefixEnd_1829279 := by exact prefixLift 1829279
  have htrace : WordTrace (prefixWord ++ tailWord_1829279) baseStart_1829279 baseEnd_1829279 := by
    simpa [prefixWord, tailWord_1829279, baseEnd_1829279] using wordTrace_append hprefix tailTrace_1829279
  have hstable : (prefixWord ++ tailWord_1829279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829279).length < 2 ^ (prefixWord ++ tailWord_1829279).sum := by decide
  have hdescent : baseEnd_1829279 < baseStart_1829279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829316 : List Nat := [2, 3, 3, 2, 2, 1, 1, 2, 1, 1, 5]
def baseStart_1829316 : Nat := 118140960795 + 1829316 * 2 ^ 59
def prefixEnd_1829316 : Nat := 4983230072969 + 3 ^ 40 * 1829316 * 2
def baseEnd_1829316 : Nat := 939318376960270026437135

theorem tailTrace_1829316 : CollatzResearch.WordTrace tailWord_1829316 prefixEnd_1829316 939318376960270026437135 := by
  unfold tailWord_1829316
  simp only [CollatzResearch.WordTrace]
  refine ⟨33360317920354014572349901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44480423893805352763133201 33360317920354014572349901)
  ·
    refine ⟨12510119220132755464631213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33360317920354014572349901 12510119220132755464631213)
    ·
      refine ⟨4691294707549783299236705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12510119220132755464631213 4691294707549783299236705)
      ·
        refine ⟨3518471030662337474427529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4691294707549783299236705 3518471030662337474427529)
        ·
          refine ⟨2638853272996753105820647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3518471030662337474427529 2638853272996753105820647)
          ·
            refine ⟨3958279909495129658730971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2638853272996753105820647 3958279909495129658730971)
            ·
              refine ⟨5937419864242694488096457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3958279909495129658730971 5937419864242694488096457)
              ·
                refine ⟨4453064898182020866072343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5937419864242694488096457 4453064898182020866072343)
                ·
                  refine ⟨6679597347273031299108515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4453064898182020866072343 6679597347273031299108515)
                  ·
                    refine ⟨10019396020909546948662773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6679597347273031299108515 10019396020909546948662773)
                    ·
                      refine ⟨939318376960270026437135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10019396020909546948662773 939318376960270026437135)
                      ·
                        rfl

theorem cell23_1829316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_1829316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1829316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1829316 prefixEnd_1829316 := by exact prefixLift 1829316
  have htrace : WordTrace (prefixWord ++ tailWord_1829316) baseStart_1829316 baseEnd_1829316 := by
    simpa [prefixWord, tailWord_1829316, baseEnd_1829316] using wordTrace_append hprefix tailTrace_1829316
  have hstable : (prefixWord ++ tailWord_1829316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829316).length < 2 ^ (prefixWord ++ tailWord_1829316).sum := by decide
  have hdescent : baseEnd_1829316 < baseStart_1829316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829347 : List Nat := [1, 1, 1, 6, 3, 2, 1, 3, 1, 2, 2]
def baseStart_1829347 : Nat := 118140960795 + 1829347 * 2 ^ 59
def prefixEnd_1829347 : Nat := 4983230072969 + 3 ^ 40 * 1829347 * 2
def baseEnd_1829347 : Nat := 939334294860559405149493

theorem tailTrace_1829347 : CollatzResearch.WordTrace tailWord_1829347 prefixEnd_1829347 939334294860559405149493 := by
  unfold tailWord_1829347
  simp only [CollatzResearch.WordTrace]
  refine ⟨66721766503595721439078295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44481177669063814292718863 66721766503595721439078295)
  ·
    refine ⟨100082649755393582158617443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66721766503595721439078295 100082649755393582158617443)
    ·
      refine ⟨150123974633090373237926165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100082649755393582158617443 150123974633090373237926165)
      ·
        refine ⟨7037061310926111245527789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 150123974633090373237926165 7037061310926111245527789)
        ·
          refine ⟨2638897991597291717072921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7037061310926111245527789 2638897991597291717072921)
          ·
            refine ⟨1979173493697968787804691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2638897991597291717072921 1979173493697968787804691)
            ·
              refine ⟨2968760240546953181707037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1979173493697968787804691 2968760240546953181707037)
              ·
                refine ⟨1113285090205107443140139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2968760240546953181707037 1113285090205107443140139)
                ·
                  refine ⟨1669927635307661164710209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1113285090205107443140139 1669927635307661164710209)
                  ·
                    refine ⟨1252445726480745873532657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1669927635307661164710209 1252445726480745873532657)
                    ·
                      refine ⟨939334294860559405149493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1252445726480745873532657 939334294860559405149493)
                      ·
                        rfl

theorem cell23_1829347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 3, 1, 2, 2].length) (baseStart_1829347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1829347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1829347 prefixEnd_1829347 := by exact prefixLift 1829347
  have htrace : WordTrace (prefixWord ++ tailWord_1829347) baseStart_1829347 baseEnd_1829347 := by
    simpa [prefixWord, tailWord_1829347, baseEnd_1829347] using wordTrace_append hprefix tailTrace_1829347
  have hstable : (prefixWord ++ tailWord_1829347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829347).length < 2 ^ (prefixWord ++ tailWord_1829347).sum := by decide
  have hdescent : baseEnd_1829347 < baseStart_1829347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829356 : List Nat := [2, 2, 1, 1, 2, 1, 3, 5, 1, 3, 2]
def baseStart_1829356 : Nat := 118140960795 + 1829356 * 2 ^ 59
def prefixEnd_1829356 : Nat := 4983230072969 + 3 ^ 40 * 1829356 * 2
def baseEnd_1829356 : Nat := 939338916186449869936951

theorem tailTrace_1829356 : CollatzResearch.WordTrace tailWord_1829356 prefixEnd_1829356 939338916186449869936951 := by
  unfold tailWord_1829356
  simp only [CollatzResearch.WordTrace]
  refine ⟨33361047380281557988077961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44481396507042077317437281 33361047380281557988077961)
  ·
    refine ⟨25020785535211168491058471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33361047380281557988077961 25020785535211168491058471)
    ·
      refine ⟨37531178302816752736587707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25020785535211168491058471 37531178302816752736587707)
      ·
        refine ⟨56296767454225129104881561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37531178302816752736587707 56296767454225129104881561)
        ·
          refine ⟨42222575590668846828661171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56296767454225129104881561 42222575590668846828661171)
          ·
            refine ⟨63333863386003270242991757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42222575590668846828661171 63333863386003270242991757)
            ·
              refine ⟨23750198769751226341121909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63333863386003270242991757 23750198769751226341121909)
              ·
                refine ⟨2226581134664177469480179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23750198769751226341121909 2226581134664177469480179)
                ·
                  refine ⟨3339871701996266204220269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2226581134664177469480179 3339871701996266204220269)
                  ·
                    refine ⟨1252451888248599826582601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3339871701996266204220269 1252451888248599826582601)
                    ·
                      refine ⟨939338916186449869936951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1252451888248599826582601 939338916186449869936951)
                      ·
                        rfl

theorem cell23_1829356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 3, 2].length) (baseStart_1829356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1829356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1829356 prefixEnd_1829356 := by exact prefixLift 1829356
  have htrace : WordTrace (prefixWord ++ tailWord_1829356) baseStart_1829356 baseEnd_1829356 := by
    simpa [prefixWord, tailWord_1829356, baseEnd_1829356] using wordTrace_append hprefix tailTrace_1829356
  have hstable : (prefixWord ++ tailWord_1829356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829356).length < 2 ^ (prefixWord ++ tailWord_1829356).sum := by decide
  have hdescent : baseEnd_1829356 < baseStart_1829356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829372 : List Nat := [2, 2, 2, 1, 2, 1, 1, 1, 3, 3, 5]
def baseStart_1829372 : Nat := 118140960795 + 1829372 * 2 ^ 59
def prefixEnd_1829372 : Nat := 4983230072969 + 3 ^ 40 * 1829372 * 2
def baseEnd_1829372 : Nat := 939347131876921807336877

theorem tailTrace_1829372 : CollatzResearch.WordTrace tailWord_1829372 prefixEnd_1829372 939347131876921807336877 := by
  unfold tailWord_1829372
  simp only [CollatzResearch.WordTrace]
  refine ⟨33361339164252575354369185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44481785552336767139158913 33361339164252575354369185)
  ·
    refine ⟨25021004373189431515776889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33361339164252575354369185 25021004373189431515776889)
    ·
      refine ⟨18765753279892073636832667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25021004373189431515776889 18765753279892073636832667)
      ·
        refine ⟨28148629919838110455249001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18765753279892073636832667 28148629919838110455249001)
        ·
          refine ⟨21111472439878582841436751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28148629919838110455249001 21111472439878582841436751)
          ·
            refine ⟨31667208659817874262155127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21111472439878582841436751 31667208659817874262155127)
            ·
              refine ⟨47500812989726811393232691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31667208659817874262155127 47500812989726811393232691)
              ·
                refine ⟨71251219484590217089849037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47500812989726811393232691 71251219484590217089849037)
                ·
                  refine ⟨26719207306721331408693389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71251219484590217089849037 26719207306721331408693389)
                  ·
                    refine ⟨10019702740020499278260021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26719207306721331408693389 10019702740020499278260021)
                    ·
                      refine ⟨939347131876921807336877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10019702740020499278260021 939347131876921807336877)
                      ·
                        rfl

theorem cell23_1829372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 3, 3, 5].length) (baseStart_1829372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1829372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1829372 prefixEnd_1829372 := by exact prefixLift 1829372
  have htrace : WordTrace (prefixWord ++ tailWord_1829372) baseStart_1829372 baseEnd_1829372 := by
    simpa [prefixWord, tailWord_1829372, baseEnd_1829372] using wordTrace_append hprefix tailTrace_1829372
  have hstable : (prefixWord ++ tailWord_1829372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829372).length < 2 ^ (prefixWord ++ tailWord_1829372).sum := by decide
  have hdescent : baseEnd_1829372 < baseStart_1829372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829380 : List Nat := [2, 3, 2, 3, 1, 1, 4, 1, 2, 1, 3]
def baseStart_1829380 : Nat := 118140960795 + 1829380 * 2 ^ 59
def prefixEnd_1829380 : Nat := 4983230072969 + 3 ^ 40 * 1829380 * 2
def baseEnd_1829380 : Nat := 939351239722157776036841

theorem tailTrace_1829380 : CollatzResearch.WordTrace tailWord_1829380 prefixEnd_1829380 939351239722157776036841 := by
  unfold tailWord_1829380
  simp only [CollatzResearch.WordTrace]
  refine ⟨33361485056238084037514797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44481980074984112050019729 33361485056238084037514797)
  ·
    refine ⟨12510556896089281514068049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33361485056238084037514797 12510556896089281514068049)
    ·
      refine ⟨9382917672066961135551037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12510556896089281514068049 9382917672066961135551037)
      ·
        refine ⟨3518594127025110425831639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9382917672066961135551037 3518594127025110425831639)
        ·
          refine ⟨5277891190537665638747459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3518594127025110425831639 5277891190537665638747459)
          ·
            refine ⟨7916836785806498458121189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5277891190537665638747459 7916836785806498458121189)
            ·
              refine ⟨1484406897338718460897723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7916836785806498458121189 1484406897338718460897723)
              ·
                refine ⟨2226610346008077691346585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1484406897338718460897723 2226610346008077691346585)
                ·
                  refine ⟨1669957759506058268509939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2226610346008077691346585 1669957759506058268509939)
                  ·
                    refine ⟨2504936639259087402764909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1669957759506058268509939 2504936639259087402764909)
                    ·
                      refine ⟨939351239722157776036841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2504936639259087402764909 939351239722157776036841)
                      ·
                        rfl

theorem cell23_1829380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_1829380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1829380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1829380 prefixEnd_1829380 := by exact prefixLift 1829380
  have htrace : WordTrace (prefixWord ++ tailWord_1829380) baseStart_1829380 baseEnd_1829380 := by
    simpa [prefixWord, tailWord_1829380, baseEnd_1829380] using wordTrace_append hprefix tailTrace_1829380
  have hstable : (prefixWord ++ tailWord_1829380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829380).length < 2 ^ (prefixWord ++ tailWord_1829380).sum := by decide
  have hdescent : baseEnd_1829380 < baseStart_1829380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829386 : List Nat := [3, 1, 2, 2, 2, 1, 2, 3, 1, 4, 2]
def baseStart_1829386 : Nat := 118140960795 + 1829386 * 2 ^ 59
def prefixEnd_1829386 : Nat := 4983230072969 + 3 ^ 40 * 1829386 * 2
def baseEnd_1829386 : Nat := 939354320606084752561813

theorem tailTrace_1829386 : CollatzResearch.WordTrace tailWord_1829386 prefixEnd_1829386 939354320606084752561813 := by
  unfold tailWord_1829386
  simp only [CollatzResearch.WordTrace]
  refine ⟨16680797237613607774937003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44482125966969620733165341 16680797237613607774937003)
  ·
    refine ⟨25021195856420411662405505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16680797237613607774937003 25021195856420411662405505)
    ·
      refine ⟨18765896892315308746804129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25021195856420411662405505 18765896892315308746804129)
      ·
        refine ⟨14074422669236481560103097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18765896892315308746804129 14074422669236481560103097)
        ·
          refine ⟨10555817001927361170077323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14074422669236481560103097 10555817001927361170077323)
          ·
            refine ⟨15833725502891041755115985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10555817001927361170077323 15833725502891041755115985)
            ·
              refine ⟨11875294127168281316336989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15833725502891041755115985 11875294127168281316336989)
              ·
                refine ⟨4453235297688105493626371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11875294127168281316336989 4453235297688105493626371)
                ·
                  refine ⟨6679852946532158240439557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4453235297688105493626371 6679852946532158240439557)
                  ·
                    refine ⟨1252472427474779670082417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6679852946532158240439557 1252472427474779670082417)
                    ·
                      refine ⟨939354320606084752561813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1252472427474779670082417 939354320606084752561813)
                      ·
                        rfl

theorem cell23_1829386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 3, 1, 4, 2].length) (baseStart_1829386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1829386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1829386 prefixEnd_1829386 := by exact prefixLift 1829386
  have htrace : WordTrace (prefixWord ++ tailWord_1829386) baseStart_1829386 baseEnd_1829386 := by
    simpa [prefixWord, tailWord_1829386, baseEnd_1829386] using wordTrace_append hprefix tailTrace_1829386
  have hstable : (prefixWord ++ tailWord_1829386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829386).length < 2 ^ (prefixWord ++ tailWord_1829386).sum := by decide
  have hdescent : baseEnd_1829386 < baseStart_1829386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829390 : List Nat := [4, 1, 1, 2, 3, 3, 1, 2, 1, 3, 2]
def baseStart_1829390 : Nat := 118140960795 + 1829390 * 2 ^ 59
def prefixEnd_1829390 : Nat := 4983230072969 + 3 ^ 40 * 1829390 * 2
def baseEnd_1829390 : Nat := 939356374528702736911795

theorem tailTrace_1829390 : CollatzResearch.WordTrace tailWord_1829390 prefixEnd_1829390 939356374528702736911795 := by
  unfold tailWord_1829390
  simp only [CollatzResearch.WordTrace]
  refine ⟨8340416855304992472861703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44482223228293293188595749 8340416855304992472861703)
  ·
    refine ⟨12510625282957488709292555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8340416855304992472861703 12510625282957488709292555)
    ·
      refine ⟨18765937924436233063938833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12510625282957488709292555 18765937924436233063938833)
      ·
        refine ⟨14074453443327174797954125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18765937924436233063938833 14074453443327174797954125)
        ·
          refine ⟨5277920041247690549232797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14074453443327174797954125 5277920041247690549232797)
          ·
            refine ⟨1979220015467883955962299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5277920041247690549232797 1979220015467883955962299)
            ·
              refine ⟨2968830023201825933943449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1979220015467883955962299 2968830023201825933943449)
              ·
                refine ⟨2226622517401369450457587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2968830023201825933943449 2226622517401369450457587)
                ·
                  refine ⟨3339933776102054175686381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2226622517401369450457587 3339933776102054175686381)
                  ·
                    refine ⟨1252475166038270315882393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3339933776102054175686381 1252475166038270315882393)
                    ·
                      refine ⟨939356374528702736911795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1252475166038270315882393 939356374528702736911795)
                      ·
                        rfl

theorem cell23_1829390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 2, 1, 3, 2].length) (baseStart_1829390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1829390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1829390 prefixEnd_1829390 := by exact prefixLift 1829390
  have htrace : WordTrace (prefixWord ++ tailWord_1829390) baseStart_1829390 baseEnd_1829390 := by
    simpa [prefixWord, tailWord_1829390, baseEnd_1829390] using wordTrace_append hprefix tailTrace_1829390
  have hstable : (prefixWord ++ tailWord_1829390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829390).length < 2 ^ (prefixWord ++ tailWord_1829390).sum := by decide
  have hdescent : baseEnd_1829390 < baseStart_1829390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829436 : List Nat := [2, 2, 2, 2, 3, 2, 1, 1, 2, 3, 3]
def baseStart_1829436 : Nat := 118140960795 + 1829436 * 2 ^ 59
def prefixEnd_1829436 : Nat := 4983230072969 + 3 ^ 40 * 1829436 * 2
def baseEnd_1829436 : Nat := 939379994638809556936583

theorem tailTrace_1829436 : CollatzResearch.WordTrace tailWord_1829436 prefixEnd_1829436 939379994638809556936583 := by
  unfold tailWord_1829436
  simp only [CollatzResearch.WordTrace]
  refine ⟨33362506300136644819534081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44483341733515526426045441 33362506300136644819534081)
  ·
    refine ⟨25021879725102483614650561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33362506300136644819534081 25021879725102483614650561)
    ·
      refine ⟨18766409793826862710987921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25021879725102483614650561 18766409793826862710987921)
      ·
        refine ⟨14074807345370147033240941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18766409793826862710987921 14074807345370147033240941)
        ·
          refine ⟨5278052754513805137465353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14074807345370147033240941 5278052754513805137465353)
          ·
            refine ⟨3958539565885353853099015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5278052754513805137465353 3958539565885353853099015)
            ·
              refine ⟨5937809348828030779648523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3958539565885353853099015 5937809348828030779648523)
              ·
                refine ⟨8906714023242046169472785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5937809348828030779648523 8906714023242046169472785)
                ·
                  refine ⟨6680035517431534627104589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8906714023242046169472785 6680035517431534627104589)
                  ·
                    refine ⟨2505013319036825485164221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6680035517431534627104589 2505013319036825485164221)
                    ·
                      refine ⟨939379994638809556936583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2505013319036825485164221 939379994638809556936583)
                      ·
                        rfl

theorem cell23_1829436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 1, 2, 3, 3].length) (baseStart_1829436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1829436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1829436 prefixEnd_1829436 := by exact prefixLift 1829436
  have htrace : WordTrace (prefixWord ++ tailWord_1829436) baseStart_1829436 baseEnd_1829436 := by
    simpa [prefixWord, tailWord_1829436, baseEnd_1829436] using wordTrace_append hprefix tailTrace_1829436
  have hstable : (prefixWord ++ tailWord_1829436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829436).length < 2 ^ (prefixWord ++ tailWord_1829436).sum := by decide
  have hdescent : baseEnd_1829436 < baseStart_1829436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829476 : List Nat := [2, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2]
def baseStart_1829476 : Nat := 118140960795 + 1829476 * 2 ^ 59
def prefixEnd_1829476 : Nat := 4983230072969 + 3 ^ 40 * 1829476 * 2
def baseEnd_1829476 : Nat := 939400533864989400436399

theorem tailTrace_1829476 : CollatzResearch.WordTrace tailWord_1829476 prefixEnd_1829476 939400533864989400436399 := by
  unfold tailWord_1829476
  simp only [CollatzResearch.WordTrace]
  refine ⟨33363235760064188235262141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44484314346752250980349521 33363235760064188235262141)
  ·
    refine ⟨12511213410024070588223303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33363235760064188235262141 12511213410024070588223303)
    ·
      refine ⟨18766820115036105882334955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12511213410024070588223303 18766820115036105882334955)
      ·
        refine ⟨28150230172554158823502433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18766820115036105882334955 28150230172554158823502433)
        ·
          refine ⟨21112672629415619117626825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28150230172554158823502433 21112672629415619117626825)
          ·
            refine ⟨15834504472061714338220119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21112672629415619117626825 15834504472061714338220119)
            ·
              refine ⟨23751756708092571507330179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15834504472061714338220119 23751756708092571507330179)
              ·
                refine ⟨35627635062138857260995269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23751756708092571507330179 35627635062138857260995269)
                ·
                  refine ⟨6680181574151035736436613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35627635062138857260995269 6680181574151035736436613)
                  ·
                    refine ⟨1252534045153319200581865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6680181574151035736436613 1252534045153319200581865)
                    ·
                      refine ⟨939400533864989400436399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1252534045153319200581865 939400533864989400436399)
                      ·
                        rfl

theorem cell23_1829476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2].length) (baseStart_1829476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1829476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1829476 prefixEnd_1829476 := by exact prefixLift 1829476
  have htrace : WordTrace (prefixWord ++ tailWord_1829476) baseStart_1829476 baseEnd_1829476 := by
    simpa [prefixWord, tailWord_1829476, baseEnd_1829476] using wordTrace_append hprefix tailTrace_1829476
  have hstable : (prefixWord ++ tailWord_1829476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829476).length < 2 ^ (prefixWord ++ tailWord_1829476).sum := by decide
  have hdescent : baseEnd_1829476 < baseStart_1829476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829530 : List Nat := [3, 1, 1, 6, 1, 1, 1, 2, 2, 2, 3]
def baseStart_1829530 : Nat := 118140960795 + 1829530 * 2 ^ 59
def prefixEnd_1829530 : Nat := 4983230072969 + 3 ^ 40 * 1829530 * 2
def baseEnd_1829530 : Nat := 939428261820332189161151

theorem tailTrace_1829530 : CollatzResearch.WordTrace tailWord_1829530 prefixEnd_1829530 939428261820332189161151 := by
  unfold tailWord_1829530
  simp only [CollatzResearch.WordTrace]
  refine ⟨16682110265483185923247511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44485627374621829128660029 16682110265483185923247511)
  ·
    refine ⟨25023165398224778884871267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16682110265483185923247511 25023165398224778884871267)
    ·
      refine ⟨37534748097337168327306901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25023165398224778884871267 37534748097337168327306901)
      ·
        refine ⟨1759441317062679765342511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 37534748097337168327306901 1759441317062679765342511)
        ·
          refine ⟨2639161975594019648013767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1759441317062679765342511 2639161975594019648013767)
          ·
            refine ⟨3958742963391029472020651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2639161975594019648013767 3958742963391029472020651)
            ·
              refine ⟨5938114445086544208030977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3958742963391029472020651 5938114445086544208030977)
              ·
                refine ⟨4453585833814908156023233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5938114445086544208030977 4453585833814908156023233)
                ·
                  refine ⟨3340189375361181117017425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4453585833814908156023233 3340189375361181117017425)
                  ·
                    refine ⟨2505142031520885837763069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3340189375361181117017425 2505142031520885837763069)
                    ·
                      refine ⟨939428261820332189161151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2505142031520885837763069 939428261820332189161151)
                      ·
                        rfl

theorem cell23_1829530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_1829530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1829530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1829530 prefixEnd_1829530 := by exact prefixLift 1829530
  have htrace : WordTrace (prefixWord ++ tailWord_1829530) baseStart_1829530 baseEnd_1829530 := by
    simpa [prefixWord, tailWord_1829530, baseEnd_1829530] using wordTrace_append hprefix tailTrace_1829530
  have hstable : (prefixWord ++ tailWord_1829530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829530).length < 2 ^ (prefixWord ++ tailWord_1829530).sum := by decide
  have hdescent : baseEnd_1829530 < baseStart_1829530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829537 : List Nat := [1, 2, 3, 3, 3, 1, 3, 2, 1, 4]
def baseStart_1829537 : Nat := 118140960795 + 1829537 * 2 ^ 59
def prefixEnd_1829537 : Nat := 4983230072969 + 3 ^ 40 * 1829537 * 2
def baseEnd_1829537 : Nat := 313143952061637887257873

theorem tailTrace_1829537 : CollatzResearch.WordTrace tailWord_1829537 prefixEnd_1829537 313143952061637887257873 := by
  unfold tailWord_1829537
  simp only [CollatzResearch.WordTrace]
  refine ⟨66728696372907383888494865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44485797581938255925663243 66728696372907383888494865)
  ·
    refine ⟨50046522279680537916371149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66728696372907383888494865 50046522279680537916371149)
    ·
      refine ⟨18767445854880201718639181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50046522279680537916371149 18767445854880201718639181)
      ·
        refine ⟨7037792195580075644489693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18767445854880201718639181 7037792195580075644489693)
        ·
          refine ⟨2639172073342528366683635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7037792195580075644489693 2639172073342528366683635)
          ·
            refine ⟨3958758110013792550025453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2639172073342528366683635 3958758110013792550025453)
            ·
              refine ⟨1484534291255172206259545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3958758110013792550025453 1484534291255172206259545)
              ·
                refine ⟨1113400718441379154694659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1484534291255172206259545 1113400718441379154694659)
                ·
                  refine ⟨1670101077662068732041989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1113400718441379154694659 1670101077662068732041989)
                  ·
                    refine ⟨313143952061637887257873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1670101077662068732041989 313143952061637887257873)
                    ·
                      rfl

theorem cell23_1829537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 3, 2, 1, 4].length) (baseStart_1829537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1829537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1829537 prefixEnd_1829537 := by exact prefixLift 1829537
  have htrace : WordTrace (prefixWord ++ tailWord_1829537) baseStart_1829537 baseEnd_1829537 := by
    simpa [prefixWord, tailWord_1829537, baseEnd_1829537] using wordTrace_append hprefix tailTrace_1829537
  have hstable : (prefixWord ++ tailWord_1829537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829537).length < 2 ^ (prefixWord ++ tailWord_1829537).sum := by decide
  have hdescent : baseEnd_1829537 < baseStart_1829537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829550 : List Nat := [4, 1, 4, 1, 1, 1, 4, 1, 6]
def baseStart_1829550 : Nat := 118140960795 + 1829550 * 2 ^ 59
def prefixEnd_1829550 : Nat := 4983230072969 + 3 ^ 40 * 1829550 * 2
def baseEnd_1829550 : Nat := 104382059048158012323451

theorem tailTrace_1829550 : CollatzResearch.WordTrace tailWord_1829550 prefixEnd_1829550 104382059048158012323451 := by
  unfold tailWord_1829550
  simp only [CollatzResearch.WordTrace]
  refine ⟨8341146315232535888589763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44486113681240191405812069 8341146315232535888589763)
  ·
    refine ⟨12511719472848803832884645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8341146315232535888589763 12511719472848803832884645)
    ·
      refine ⟨2345947401159150718665871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12511719472848803832884645 2345947401159150718665871)
      ·
        refine ⟨3518921101738726077998807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2345947401159150718665871 3518921101738726077998807)
        ·
          refine ⟨5278381652608089116998211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3518921101738726077998807 5278381652608089116998211)
          ·
            refine ⟨7917572478912133675497317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5278381652608089116998211 7917572478912133675497317)
            ·
              refine ⟨1484544839796025064155747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7917572478912133675497317 1484544839796025064155747)
              ·
                refine ⟨2226817259694037596233621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1484544839796025064155747 2226817259694037596233621)
                ·
                  refine ⟨104382059048158012323451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2226817259694037596233621 104382059048158012323451)
                  ·
                    rfl

theorem cell23_1829550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 4, 1, 6].length) (baseStart_1829550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1829550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1829550 prefixEnd_1829550 := by exact prefixLift 1829550
  have htrace : WordTrace (prefixWord ++ tailWord_1829550) baseStart_1829550 baseEnd_1829550 := by
    simpa [prefixWord, tailWord_1829550, baseEnd_1829550] using wordTrace_append hprefix tailTrace_1829550
  have hstable : (prefixWord ++ tailWord_1829550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829550).length < 2 ^ (prefixWord ++ tailWord_1829550).sum := by decide
  have hdescent : baseEnd_1829550 < baseStart_1829550 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829576 : List Nat := [2, 1, 3, 1, 2, 4, 1, 2, 1, 6]
def baseStart_1829576 : Nat := 118140960795 + 1829576 * 2 ^ 59
def prefixEnd_1829576 : Nat := 4983230072969 + 3 ^ 40 * 1829576 * 2
def baseEnd_1829576 : Nat := 313150627310146336395313

theorem tailTrace_1829576 : CollatzResearch.WordTrace tailWord_1829576 prefixEnd_1829576 313150627310146336395313 := by
  unfold tailWord_1829576
  simp only [CollatzResearch.WordTrace]
  refine ⟨33365059409883046774582291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44486745879844062366109721 33365059409883046774582291)
  ·
    refine ⟨50047589114824570161873437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33365059409883046774582291 50047589114824570161873437)
    ·
      refine ⟨18767845918059213810702539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50047589114824570161873437 18767845918059213810702539)
      ·
        refine ⟨28151768877088820716053809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18767845918059213810702539 28151768877088820716053809)
        ·
          refine ⟨21113826657816615537040357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28151768877088820716053809 21113826657816615537040357)
          ·
            refine ⟨3958842498340615413195067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21113826657816615537040357 3958842498340615413195067)
            ·
              refine ⟨5938263747510923119792601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3958842498340615413195067 5938263747510923119792601)
              ·
                refine ⟨4453697810633192339844451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5938263747510923119792601 4453697810633192339844451)
                ·
                  refine ⟨6680546715949788509766677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4453697810633192339844451 6680546715949788509766677)
                  ·
                    refine ⟨313150627310146336395313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6680546715949788509766677 313150627310146336395313)
                    ·
                      rfl

theorem cell23_1829576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 2, 1, 6].length) (baseStart_1829576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1829576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1829576 prefixEnd_1829576 := by exact prefixLift 1829576
  have htrace : WordTrace (prefixWord ++ tailWord_1829576) baseStart_1829576 baseEnd_1829576 := by
    simpa [prefixWord, tailWord_1829576, baseEnd_1829576] using wordTrace_append hprefix tailTrace_1829576
  have hstable : (prefixWord ++ tailWord_1829576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829576).length < 2 ^ (prefixWord ++ tailWord_1829576).sum := by decide
  have hdescent : baseEnd_1829576 < baseStart_1829576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829580 : List Nat := [2, 2, 1, 5, 1, 2, 3, 1, 1, 5]
def baseStart_1829580 : Nat := 118140960795 + 1829580 * 2 ^ 59
def prefixEnd_1829580 : Nat := 4983230072969 + 3 ^ 40 * 1829580 * 2
def baseEnd_1829580 : Nat := 313151311951018997845307

theorem tailTrace_1829580 : CollatzResearch.WordTrace tailWord_1829580 prefixEnd_1829580 313151311951018997845307 := by
  unfold tailWord_1829580
  simp only [CollatzResearch.WordTrace]
  refine ⟨33365132355875801116155097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44486843141167734821540129 33365132355875801116155097)
  ·
    refine ⟨25023849266906850837116323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33365132355875801116155097 25023849266906850837116323)
    ·
      refine ⟨37535773900360276255674485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25023849266906850837116323 37535773900360276255674485)
      ·
        refine ⟨3518978803158775898969483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37535773900360276255674485 3518978803158775898969483)
        ·
          refine ⟨5278468204738163848454225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3518978803158775898969483 5278468204738163848454225)
          ·
            refine ⟨3958851153553622886340669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5278468204738163848454225 3958851153553622886340669)
            ·
              refine ⟨1484569182582608582377751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3958851153553622886340669 1484569182582608582377751)
              ·
                refine ⟨2226853773873912873566627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1484569182582608582377751 2226853773873912873566627)
                ·
                  refine ⟨3340280660810869310349941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2226853773873912873566627 3340280660810869310349941)
                  ·
                    refine ⟨313151311951018997845307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3340280660810869310349941 313151311951018997845307)
                    ·
                      rfl

theorem cell23_1829580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 3, 1, 1, 5].length) (baseStart_1829580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1829580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1829580 prefixEnd_1829580 := by exact prefixLift 1829580
  have htrace : WordTrace (prefixWord ++ tailWord_1829580) baseStart_1829580 baseEnd_1829580 := by
    simpa [prefixWord, tailWord_1829580, baseEnd_1829580] using wordTrace_append hprefix tailTrace_1829580
  have hstable : (prefixWord ++ tailWord_1829580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829580).length < 2 ^ (prefixWord ++ tailWord_1829580).sum := by decide
  have hdescent : baseEnd_1829580 < baseStart_1829580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829593 : List Nat := [1, 2, 1, 2, 3, 2, 4, 2, 2, 4]
def baseStart_1829593 : Nat := 118140960795 + 1829593 * 2 ^ 59
def prefixEnd_1829593 : Nat := 4983230072969 + 3 ^ 40 * 1829593 * 2
def baseEnd_1829593 : Nat := 313153537033855147557787

theorem tailTrace_1829593 : CollatzResearch.WordTrace tailWord_1829593 prefixEnd_1829593 313153537033855147557787 := by
  unfold tailWord_1829593
  simp only [CollatzResearch.WordTrace]
  refine ⟨66730738860704505452533433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44487159240469670301688955 66730738860704505452533433)
  ·
    refine ⟨50048054145528379089400075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66730738860704505452533433 50048054145528379089400075)
    ·
      refine ⟨75072081218292568634100113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50048054145528379089400075 75072081218292568634100113)
      ·
        refine ⟨56304060913719426475575085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75072081218292568634100113 56304060913719426475575085)
        ·
          refine ⟨21114022842644784928340657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56304060913719426475575085 21114022842644784928340657)
          ·
            refine ⟨15835517131983588696255493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21114022842644784928340657 15835517131983588696255493)
            ·
              refine ⟨2969159462246922880547905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15835517131983588696255493 2969159462246922880547905)
              ·
                refine ⟨2226869596685192160410929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2969159462246922880547905 2226869596685192160410929)
                ·
                  refine ⟨1670152197513894120308197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2226869596685192160410929 1670152197513894120308197)
                  ·
                    refine ⟨313153537033855147557787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1670152197513894120308197 313153537033855147557787)
                    ·
                      rfl

theorem cell23_1829593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 2, 2, 4].length) (baseStart_1829593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1829593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1829593 prefixEnd_1829593 := by exact prefixLift 1829593
  have htrace : WordTrace (prefixWord ++ tailWord_1829593) baseStart_1829593 baseEnd_1829593 := by
    simpa [prefixWord, tailWord_1829593, baseEnd_1829593] using wordTrace_append hprefix tailTrace_1829593
  have hstable : (prefixWord ++ tailWord_1829593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829593).length < 2 ^ (prefixWord ++ tailWord_1829593).sum := by decide
  have hdescent : baseEnd_1829593 < baseStart_1829593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829603 : List Nat := [1, 1, 1, 7, 1, 1, 1, 2, 3, 2, 3]
def baseStart_1829603 : Nat := 118140960795 + 1829603 * 2 ^ 59
def prefixEnd_1829603 : Nat := 4983230072969 + 3 ^ 40 * 1829603 * 2
def baseEnd_1829603 : Nat := 939465745908110403548315

theorem tailTrace_1829603 : CollatzResearch.WordTrace tailWord_1829603 prefixEnd_1829603 939465745908110403548315 := by
  unfold tailWord_1829603
  simp only [CollatzResearch.WordTrace]
  refine ⟨66731103590668277160397463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44487402393778851440264975 66731103590668277160397463)
  ·
    refine ⟨100096655386002415740596195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66731103590668277160397463 100096655386002415740596195)
    ·
      refine ⟨150144983079003623610894293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100096655386002415740596195 150144983079003623610894293)
      ·
        refine ⟨3519023040914147428380335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 150144983079003623610894293 3519023040914147428380335)
        ·
          refine ⟨5278534561371221142570503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3519023040914147428380335 5278534561371221142570503)
          ·
            refine ⟨7917801842056831713855755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5278534561371221142570503 7917801842056831713855755)
            ·
              refine ⟨11876702763085247570783633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7917801842056831713855755 11876702763085247570783633)
              ·
                refine ⟨8907527072313935678087725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11876702763085247570783633 8907527072313935678087725)
                ·
                  refine ⟨3340322652117725879282897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8907527072313935678087725 3340322652117725879282897)
                  ·
                    refine ⟨2505241989088294409462173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3340322652117725879282897 2505241989088294409462173)
                    ·
                      refine ⟨939465745908110403548315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2505241989088294409462173 939465745908110403548315)
                      ·
                        rfl

theorem cell23_1829603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_1829603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1829603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1829603 prefixEnd_1829603 := by exact prefixLift 1829603
  have htrace : WordTrace (prefixWord ++ tailWord_1829603) baseStart_1829603 baseEnd_1829603 := by
    simpa [prefixWord, tailWord_1829603, baseEnd_1829603] using wordTrace_append hprefix tailTrace_1829603
  have hstable : (prefixWord ++ tailWord_1829603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829603).length < 2 ^ (prefixWord ++ tailWord_1829603).sum := by decide
  have hdescent : baseEnd_1829603 < baseStart_1829603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829609 : List Nat := [1, 2, 1, 1, 1, 2, 4, 1, 2, 2, 6]
def baseStart_1829609 : Nat := 118140960795 + 1829609 * 2 ^ 59
def prefixEnd_1829609 : Nat := 4983230072969 + 3 ^ 40 * 1829609 * 2
def baseEnd_1829609 : Nat := 939468826792037380073287

theorem tailTrace_1829609 : CollatzResearch.WordTrace tailWord_1829609 prefixEnd_1829609 939468826792037380073287 := by
  unfold tailWord_1829609
  simp only [CollatzResearch.WordTrace]
  refine ⟨66731322428646540185115881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44487548285764360123410587 66731322428646540185115881)
  ·
    refine ⟨50048491821484905138836911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66731322428646540185115881 50048491821484905138836911)
    ·
      refine ⟨75072737732227357708255367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50048491821484905138836911 75072737732227357708255367)
      ·
        refine ⟨112609106598341036562383051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75072737732227357708255367 112609106598341036562383051)
        ·
          refine ⟨168913659897511554843574577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112609106598341036562383051 168913659897511554843574577)
          ·
            refine ⟨126685244923133666132680933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168913659897511554843574577 126685244923133666132680933)
            ·
              refine ⟨23753483423087562399877675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 126685244923133666132680933 23753483423087562399877675)
              ·
                refine ⟨35630225134631343599816513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23753483423087562399877675 35630225134631343599816513)
                ·
                  refine ⟨26722668850973507699862385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35630225134631343599816513 26722668850973507699862385)
                  ·
                    refine ⟨20042001638230130774896789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26722668850973507699862385 20042001638230130774896789)
                    ·
                      refine ⟨939468826792037380073287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20042001638230130774896789 939468826792037380073287)
                      ·
                        rfl

theorem cell23_1829609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 2, 6].length) (baseStart_1829609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1829609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1829609 prefixEnd_1829609 := by exact prefixLift 1829609
  have htrace : WordTrace (prefixWord ++ tailWord_1829609) baseStart_1829609 baseEnd_1829609 := by
    simpa [prefixWord, tailWord_1829609, baseEnd_1829609] using wordTrace_append hprefix tailTrace_1829609
  have hstable : (prefixWord ++ tailWord_1829609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829609).length < 2 ^ (prefixWord ++ tailWord_1829609).sum := by decide
  have hdescent : baseEnd_1829609 < baseStart_1829609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829613 : List Nat := [1, 5, 1, 2, 1, 1, 4, 1, 1, 2, 4]
def baseStart_1829613 : Nat := 118140960795 + 1829613 * 2 ^ 59
def prefixEnd_1829613 : Nat := 4983230072969 + 3 ^ 40 * 1829613 * 2
def baseEnd_1829613 : Nat := 939470880714655364423269

theorem tailTrace_1829613 : CollatzResearch.WordTrace tailWord_1829613 prefixEnd_1829613 939470880714655364423269 := by
  unfold tailWord_1829613
  simp only [CollatzResearch.WordTrace]
  refine ⟨66731468320632048868261493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44487645547088032578840995 66731468320632048868261493)
  ·
    refine ⟨6256075155059254581399515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66731468320632048868261493 6256075155059254581399515)
    ·
      refine ⟨9384112732588881872099273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6256075155059254581399515 9384112732588881872099273)
      ·
        refine ⟨7038084549441661404074455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9384112732588881872099273 7038084549441661404074455)
        ·
          refine ⟨10557126824162492106111683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7038084549441661404074455 10557126824162492106111683)
          ·
            refine ⟨15835690236243738159167525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10557126824162492106111683 15835690236243738159167525)
            ·
              refine ⟨2969191919295700904843911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15835690236243738159167525 2969191919295700904843911)
              ·
                refine ⟨4453787878943551357265867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2969191919295700904843911 4453787878943551357265867)
                ·
                  refine ⟨6680681818415327035898801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4453787878943551357265867 6680681818415327035898801)
                  ·
                    refine ⟨5010511363811495276924101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6680681818415327035898801 5010511363811495276924101)
                    ·
                      refine ⟨939470880714655364423269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5010511363811495276924101 939470880714655364423269)
                      ·
                        rfl

theorem cell23_1829613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_1829613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1829613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1829613 prefixEnd_1829613 := by exact prefixLift 1829613
  have htrace : WordTrace (prefixWord ++ tailWord_1829613) baseStart_1829613 baseEnd_1829613 := by
    simpa [prefixWord, tailWord_1829613, baseEnd_1829613] using wordTrace_append hprefix tailTrace_1829613
  have hstable : (prefixWord ++ tailWord_1829613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829613).length < 2 ^ (prefixWord ++ tailWord_1829613).sum := by decide
  have hdescent : baseEnd_1829613 < baseStart_1829613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829619 : List Nat := [1, 1, 1, 2, 2, 3, 1, 1, 4, 7]
def baseStart_1829619 : Nat := 118140960795 + 1829619 * 2 ^ 59
def prefixEnd_1829619 : Nat := 4983230072969 + 3 ^ 40 * 1829619 * 2
def baseEnd_1829619 : Nat := 313157987199527446982747

theorem tailTrace_1829619 : CollatzResearch.WordTrace tailWord_1829619 prefixEnd_1829619 313157987199527446982747 := by
  unfold tailWord_1829619
  simp only [CollatzResearch.WordTrace]
  refine ⟨66731687158610311892979911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44487791439073541261986607 66731687158610311892979911)
  ·
    refine ⟨100097530737915467839469867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66731687158610311892979911 100097530737915467839469867)
    ·
      refine ⟨150146296106873201759204801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100097530737915467839469867 150146296106873201759204801)
      ·
        refine ⟨112609722080154901319403601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150146296106873201759204801 112609722080154901319403601)
        ·
          refine ⟨84457291560116175989552701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112609722080154901319403601 84457291560116175989552701)
          ·
            refine ⟨31671484335043565996082263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84457291560116175989552701 31671484335043565996082263)
            ·
              refine ⟨47507226502565348994123395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31671484335043565996082263 47507226502565348994123395)
              ·
                refine ⟨71260839753848023491185093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47507226502565348994123395 71260839753848023491185093)
                ·
                  refine ⟨13361407453846504404597205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71260839753848023491185093 13361407453846504404597205)
                  ·
                    refine ⟨313157987199527446982747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13361407453846504404597205 313157987199527446982747)
                    ·
                      rfl

theorem cell23_1829619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 4, 7].length) (baseStart_1829619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1829619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1829619 prefixEnd_1829619 := by exact prefixLift 1829619
  have htrace : WordTrace (prefixWord ++ tailWord_1829619) baseStart_1829619 baseEnd_1829619 := by
    simpa [prefixWord, tailWord_1829619, baseEnd_1829619] using wordTrace_append hprefix tailTrace_1829619
  have hstable : (prefixWord ++ tailWord_1829619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829619).length < 2 ^ (prefixWord ++ tailWord_1829619).sum := by decide
  have hdescent : baseEnd_1829619 < baseStart_1829619 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829621 : List Nat := [1, 3, 6, 1, 1, 2, 1, 1, 2, 3, 2]
def baseStart_1829621 : Nat := 118140960795 + 1829621 * 2 ^ 59
def prefixEnd_1829621 : Nat := 4983230072969 + 3 ^ 40 * 1829621 * 2
def baseEnd_1829621 : Nat := 939474988559891333123233

theorem tailTrace_1829621 : CollatzResearch.WordTrace tailWord_1829621 prefixEnd_1829621 939474988559891333123233 := by
  unfold tailWord_1829621
  simp only [CollatzResearch.WordTrace]
  refine ⟨66731760104603066234552717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44487840069735377489701811 66731760104603066234552717)
  ·
    refine ⟨25024410039226149837957269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66731760104603066234552717 25024410039226149837957269)
    ·
      refine ⟨1173019220588725773654247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 25024410039226149837957269 1173019220588725773654247)
      ·
        refine ⟨1759528830883088660481371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1173019220588725773654247 1759528830883088660481371)
        ·
          refine ⟨2639293246324632990722057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1759528830883088660481371 2639293246324632990722057)
          ·
            refine ⟨1979469934743474743041543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2639293246324632990722057 1979469934743474743041543)
            ·
              refine ⟨2969204902115212114562315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1979469934743474743041543 2969204902115212114562315)
              ·
                refine ⟨4453807353172818171843473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2969204902115212114562315 4453807353172818171843473)
                ·
                  refine ⟨3340355514879613628882605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4453807353172818171843473 3340355514879613628882605)
                  ·
                    refine ⟨1252633318079855110830977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3340355514879613628882605 1252633318079855110830977)
                    ·
                      refine ⟨939474988559891333123233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1252633318079855110830977 939474988559891333123233)
                      ·
                        rfl

theorem cell23_1829621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_1829621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1829621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1829621 prefixEnd_1829621 := by exact prefixLift 1829621
  have htrace : WordTrace (prefixWord ++ tailWord_1829621) baseStart_1829621 baseEnd_1829621 := by
    simpa [prefixWord, tailWord_1829621, baseEnd_1829621] using wordTrace_append hprefix tailTrace_1829621
  have hstable : (prefixWord ++ tailWord_1829621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829621).length < 2 ^ (prefixWord ++ tailWord_1829621).sum := by decide
  have hdescent : baseEnd_1829621 < baseStart_1829621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829633 : List Nat := [1, 2, 4, 1, 1, 1, 1, 4, 4, 1, 3]
def baseStart_1829633 : Nat := 118140960795 + 1829633 * 2 ^ 59
def prefixEnd_1829633 : Nat := 4983230072969 + 3 ^ 40 * 1829633 * 2
def baseEnd_1829633 : Nat := 939481150327745286173177

theorem tailTrace_1829633 : CollatzResearch.WordTrace tailWord_1829633 prefixEnd_1829633 939481150327745286173177 := by
  unfold tailWord_1829633
  simp only [CollatzResearch.WordTrace]
  refine ⟨66732197780559592283989553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44488131853706394855993035 66732197780559592283989553)
  ·
    refine ⟨50049148335419694212992165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66732197780559592283989553 50049148335419694212992165)
    ·
      refine ⟨9384215312891192664936031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50049148335419694212992165 9384215312891192664936031)
      ·
        refine ⟨14076322969336788997404047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9384215312891192664936031 14076322969336788997404047)
        ·
          refine ⟨21114484454005183496106071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14076322969336788997404047 21114484454005183496106071)
          ·
            refine ⟨31671726681007775244159107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21114484454005183496106071 31671726681007775244159107)
            ·
              refine ⟨47507590021511662866238661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31671726681007775244159107 47507590021511662866238661)
              ·
                refine ⟨8907673129033436787419749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47507590021511662866238661 8907673129033436787419749)
                ·
                  refine ⟨1670188711693769397641203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8907673129033436787419749 1670188711693769397641203)
                  ·
                    refine ⟨2505283067540654096461805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1670188711693769397641203 2505283067540654096461805)
                    ·
                      refine ⟨939481150327745286173177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2505283067540654096461805 939481150327745286173177)
                      ·
                        rfl

theorem cell23_1829633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 4, 4, 1, 3].length) (baseStart_1829633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1829633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1829633 prefixEnd_1829633 := by exact prefixLift 1829633
  have htrace : WordTrace (prefixWord ++ tailWord_1829633) baseStart_1829633 baseEnd_1829633 := by
    simpa [prefixWord, tailWord_1829633, baseEnd_1829633] using wordTrace_append hprefix tailTrace_1829633
  have hstable : (prefixWord ++ tailWord_1829633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829633).length < 2 ^ (prefixWord ++ tailWord_1829633).sum := by decide
  have hdescent : baseEnd_1829633 < baseStart_1829633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829634 : List Nat := [3, 4, 1, 1, 1, 2, 1, 5, 1, 2, 2]
def baseStart_1829634 : Nat := 118140960795 + 1829634 * 2 ^ 59
def prefixEnd_1829634 : Nat := 4983230072969 + 3 ^ 40 * 1829634 * 2
def baseEnd_1829634 : Nat := 939481663808399782260673

theorem tailTrace_1829634 : CollatzResearch.WordTrace tailWord_1829634 prefixEnd_1829634 939481663808399782260673 := by
  unfold tailWord_1829634
  simp only [CollatzResearch.WordTrace]
  refine ⟨16683058563388992363693989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44488156169037312969850637 16683058563388992363693989)
  ·
    refine ⟨3128073480635436068192623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16683058563388992363693989 3128073480635436068192623)
    ·
      refine ⟨4692110220953154102288935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3128073480635436068192623 4692110220953154102288935)
      ·
        refine ⟨7038165331429731153433403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4692110220953154102288935 7038165331429731153433403)
        ·
          refine ⟨10557247997144596730150105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7038165331429731153433403 10557247997144596730150105)
          ·
            refine ⟨7917935997858447547612579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10557247997144596730150105 7917935997858447547612579)
            ·
              refine ⟨11876903996787671321418869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7917935997858447547612579 11876903996787671321418869)
              ·
                refine ⟨1113459749698844186383019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11876903996787671321418869 1113459749698844186383019)
                ·
                  refine ⟨1670189624548266279574529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1113459749698844186383019 1670189624548266279574529)
                  ·
                    refine ⟨1252642218411199709680897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1670189624548266279574529 1252642218411199709680897)
                    ·
                      refine ⟨939481663808399782260673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1252642218411199709680897 939481663808399782260673)
                      ·
                        rfl

theorem cell23_1829634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 5, 1, 2, 2].length) (baseStart_1829634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1829634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1829634 prefixEnd_1829634 := by exact prefixLift 1829634
  have htrace : WordTrace (prefixWord ++ tailWord_1829634) baseStart_1829634 baseEnd_1829634 := by
    simpa [prefixWord, tailWord_1829634, baseEnd_1829634] using wordTrace_append hprefix tailTrace_1829634
  have hstable : (prefixWord ++ tailWord_1829634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829634).length < 2 ^ (prefixWord ++ tailWord_1829634).sum := by decide
  have hdescent : baseEnd_1829634 < baseStart_1829634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829676 : List Nat := [2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 5]
def baseStart_1829676 : Nat := 118140960795 + 1829676 * 2 ^ 59
def prefixEnd_1829676 : Nat := 4983230072969 + 3 ^ 40 * 1829676 * 2
def baseEnd_1829676 : Nat := 939503229995888617935479

theorem tailTrace_1829676 : CollatzResearch.WordTrace tailWord_1829676 prefixEnd_1829676 939503229995888617935479 := by
  unfold tailWord_1829676
  simp only [CollatzResearch.WordTrace]
  refine ⟨33366883059701905313902441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44489177412935873751869921 33366883059701905313902441)
  ·
    refine ⟨25025162294776428985426831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33366883059701905313902441 25025162294776428985426831)
    ·
      refine ⟨37537743442164643478140247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25025162294776428985426831 37537743442164643478140247)
      ·
        refine ⟨56306615163246965217210371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37537743442164643478140247 56306615163246965217210371)
        ·
          refine ⟨84459922744870447825815557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56306615163246965217210371 84459922744870447825815557)
          ·
            refine ⟨15836235514663208967340417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84459922744870447825815557 15836235514663208967340417)
            ·
              refine ⟨11877176635997406725505313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15836235514663208967340417 11877176635997406725505313)
              ·
                refine ⟨8907882476998055044128985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11877176635997406725505313 8907882476998055044128985)
                ·
                  refine ⟨6680911857748541283096739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8907882476998055044128985 6680911857748541283096739)
                  ·
                    refine ⟨10021367786622811924645109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6680911857748541283096739 10021367786622811924645109)
                    ·
                      refine ⟨939503229995888617935479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10021367786622811924645109 939503229995888617935479)
                      ·
                        rfl

theorem cell23_1829676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 5].length) (baseStart_1829676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1829676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1829676 prefixEnd_1829676 := by exact prefixLift 1829676
  have htrace : WordTrace (prefixWord ++ tailWord_1829676) baseStart_1829676 baseEnd_1829676 := by
    simpa [prefixWord, tailWord_1829676, baseEnd_1829676] using wordTrace_append hprefix tailTrace_1829676
  have hstable : (prefixWord ++ tailWord_1829676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829676).length < 2 ^ (prefixWord ++ tailWord_1829676).sum := by decide
  have hdescent : baseEnd_1829676 < baseStart_1829676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829724 : List Nat := [2, 2, 4, 2, 1, 2, 1, 3, 2, 2, 2]
def baseStart_1829724 : Nat := 118140960795 + 1829724 * 2 ^ 59
def prefixEnd_1829724 : Nat := 4983230072969 + 3 ^ 40 * 1829724 * 2
def baseEnd_1829724 : Nat := 939527877067304430135259

theorem tailTrace_1829724 : CollatzResearch.WordTrace tailWord_1829724 prefixEnd_1829724 939527877067304430135259 := by
  unfold tailWord_1829724
  simp only [CollatzResearch.WordTrace]
  refine ⟨33367758411614957412776113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44490344548819943217034817 33367758411614957412776113)
  ·
    refine ⟨25025818808711218059582085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33367758411614957412776113 25025818808711218059582085)
    ·
      refine ⟨4692341026633353386171641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25025818808711218059582085 4692341026633353386171641)
      ·
        refine ⟨3519255769975015039628731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4692341026633353386171641 3519255769975015039628731)
        ·
          refine ⟨5278883654962522559443097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3519255769975015039628731 5278883654962522559443097)
          ·
            refine ⟨3959162741221891919582323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5278883654962522559443097 3959162741221891919582323)
            ·
              refine ⟨5938744111832837879373485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3959162741221891919582323 5938744111832837879373485)
              ·
                refine ⟨2227029041937314204765057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5938744111832837879373485 2227029041937314204765057)
                ·
                  refine ⟨1670271781452985653573793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2227029041937314204765057 1670271781452985653573793)
                  ·
                    refine ⟨1252703836089739240180345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1670271781452985653573793 1252703836089739240180345)
                    ·
                      refine ⟨939527877067304430135259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1252703836089739240180345 939527877067304430135259)
                      ·
                        rfl

theorem cell23_1829724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_1829724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1829724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1829724 prefixEnd_1829724 := by exact prefixLift 1829724
  have htrace : WordTrace (prefixWord ++ tailWord_1829724) baseStart_1829724 baseEnd_1829724 := by
    simpa [prefixWord, tailWord_1829724, baseEnd_1829724] using wordTrace_append hprefix tailTrace_1829724
  have hstable : (prefixWord ++ tailWord_1829724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829724).length < 2 ^ (prefixWord ++ tailWord_1829724).sum := by decide
  have hdescent : baseEnd_1829724 < baseStart_1829724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829763 : List Nat := [1, 1, 1, 3, 4, 1, 1, 4, 2, 1, 4]
def baseStart_1829763 : Nat := 118140960795 + 1829763 * 2 ^ 59
def prefixEnd_1829763 : Nat := 4983230072969 + 3 ^ 40 * 1829763 * 2
def baseEnd_1829763 : Nat := 939547902812829777547579

theorem tailTrace_1829763 : CollatzResearch.WordTrace tailWord_1829763 prefixEnd_1829763 939547902812829777547579 := by
  unfold tailWord_1829763
  simp only [CollatzResearch.WordTrace]
  refine ⟨66736939270088624486221943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44491292846725749657481295 66736939270088624486221943)
  ·
    refine ⟨100105408905132936729332915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66736939270088624486221943 100105408905132936729332915)
    ·
      refine ⟨150158113357699405093999373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100105408905132936729332915 150158113357699405093999373)
      ·
        refine ⟨56309292509137276910249765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150158113357699405093999373 56309292509137276910249765)
        ·
          refine ⟨10557992345463239420671831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56309292509137276910249765 10557992345463239420671831)
          ·
            refine ⟨15836988518194859131007747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10557992345463239420671831 15836988518194859131007747)
            ·
              refine ⟨23755482777292288696511621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15836988518194859131007747 23755482777292288696511621)
              ·
                refine ⟨4454153020742304130595929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23755482777292288696511621 4454153020742304130595929)
                ·
                  refine ⟨3340614765556728097946947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4454153020742304130595929 3340614765556728097946947)
                  ·
                    refine ⟨5010922148335092146920421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3340614765556728097946947 5010922148335092146920421)
                    ·
                      refine ⟨939547902812829777547579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5010922148335092146920421 939547902812829777547579)
                      ·
                        rfl

theorem cell23_1829763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 4, 2, 1, 4].length) (baseStart_1829763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1829763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1829763 prefixEnd_1829763 := by exact prefixLift 1829763
  have htrace : WordTrace (prefixWord ++ tailWord_1829763) baseStart_1829763 baseEnd_1829763 := by
    simpa [prefixWord, tailWord_1829763, baseEnd_1829763] using wordTrace_append hprefix tailTrace_1829763
  have hstable : (prefixWord ++ tailWord_1829763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829763).length < 2 ^ (prefixWord ++ tailWord_1829763).sum := by decide
  have hdescent : baseEnd_1829763 < baseStart_1829763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829783 : List Nat := [1, 1, 3, 3, 1, 2, 2, 2, 1, 4, 3]
def baseStart_1829783 : Nat := 118140960795 + 1829783 * 2 ^ 59
def prefixEnd_1829783 : Nat := 4983230072969 + 3 ^ 40 * 1829783 * 2
def baseEnd_1829783 : Nat := 939558172425919699297487

theorem tailTrace_1829783 : CollatzResearch.WordTrace tailWord_1829783 prefixEnd_1829783 939558172425919699297487 := by
  unfold tailWord_1829783
  simp only [CollatzResearch.WordTrace]
  refine ⟨66737668730016167901950003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44491779153344111934633335 66737668730016167901950003)
  ·
    refine ⟨100106503095024251852925005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66737668730016167901950003 100106503095024251852925005)
    ·
      refine ⟨37539938660634094444846877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100106503095024251852925005 37539938660634094444846877)
      ·
        refine ⟨14077476997737785416817579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37539938660634094444846877 14077476997737785416817579)
        ·
          refine ⟨21116215496606678125226369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14077476997737785416817579 21116215496606678125226369)
          ·
            refine ⟨15837161622455008593919777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21116215496606678125226369 15837161622455008593919777)
            ·
              refine ⟨11877871216841256445439833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15837161622455008593919777 11877871216841256445439833)
              ·
                refine ⟨8908403412630942334079875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11877871216841256445439833 8908403412630942334079875)
                ·
                  refine ⟨13362605118946413501119813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8908403412630942334079875 13362605118946413501119813)
                  ·
                    refine ⟨2505488459802452531459965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13362605118946413501119813 2505488459802452531459965)
                    ·
                      refine ⟨939558172425919699297487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2505488459802452531459965 939558172425919699297487)
                      ·
                        rfl

theorem cell23_1829783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 2, 1, 4, 3].length) (baseStart_1829783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1829783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1829783 prefixEnd_1829783 := by exact prefixLift 1829783
  have htrace : WordTrace (prefixWord ++ tailWord_1829783) baseStart_1829783 baseEnd_1829783 := by
    simpa [prefixWord, tailWord_1829783, baseEnd_1829783] using wordTrace_append hprefix tailTrace_1829783
  have hstable : (prefixWord ++ tailWord_1829783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829783).length < 2 ^ (prefixWord ++ tailWord_1829783).sum := by decide
  have hdescent : baseEnd_1829783 < baseStart_1829783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829850 : List Nat := [3, 1, 1, 2, 4, 1, 1, 4, 1, 5]
def baseStart_1829850 : Nat := 118140960795 + 1829850 * 2 ^ 59
def prefixEnd_1829850 : Nat := 4983230072969 + 3 ^ 40 * 1829850 * 2
def baseEnd_1829850 : Nat := 313197525209923645719893

theorem tailTrace_1829850 : CollatzResearch.WordTrace tailWord_1829850 prefixEnd_1829850 313197525209923645719893 := by
  unfold tailWord_1829850
  simp only [CollatzResearch.WordTrace]
  refine ⟨16685028105193359586159751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44493408280515625563092669 16685028105193359586159751)
  ·
    refine ⟨25027542157790039379239627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16685028105193359586159751 25027542157790039379239627)
    ·
      refine ⟨37541313236685059068859441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25027542157790039379239627 37541313236685059068859441)
      ·
        refine ⟨28155984927513794301644581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37541313236685059068859441 28155984927513794301644581)
        ·
          refine ⟨5279247173908836431558359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28155984927513794301644581 5279247173908836431558359)
          ·
            refine ⟨7918870760863254647337539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5279247173908836431558359 7918870760863254647337539)
            ·
              refine ⟨11878306141294881971006309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7918870760863254647337539 11878306141294881971006309)
              ·
                refine ⟨2227182401492790369563683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11878306141294881971006309 2227182401492790369563683)
                ·
                  refine ⟨3340773602239185554345525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2227182401492790369563683 3340773602239185554345525)
                  ·
                    refine ⟨313197525209923645719893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3340773602239185554345525 313197525209923645719893)
                    ·
                      rfl

theorem cell23_1829850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 4, 1, 5].length) (baseStart_1829850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1829850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1829850 prefixEnd_1829850 := by exact prefixLift 1829850
  have htrace : WordTrace (prefixWord ++ tailWord_1829850) baseStart_1829850 baseEnd_1829850 := by
    simpa [prefixWord, tailWord_1829850, baseEnd_1829850] using wordTrace_append hprefix tailTrace_1829850
  have hstable : (prefixWord ++ tailWord_1829850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829850).length < 2 ^ (prefixWord ++ tailWord_1829850).sum := by decide
  have hdescent : baseEnd_1829850 < baseStart_1829850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829864 : List Nat := [2, 1, 4, 1, 1, 1, 5, 3, 1, 1, 3]
def baseStart_1829864 : Nat := 118140960795 + 1829864 * 2 ^ 59
def prefixEnd_1829864 : Nat := 4983230072969 + 3 ^ 40 * 1829864 * 2
def baseEnd_1829864 : Nat := 939599764358933882384615

theorem tailTrace_1829864 : CollatzResearch.WordTrace tailWord_1829864 prefixEnd_1829864 939599764358933882384615 := by
  unfold tailWord_1829864
  simp only [CollatzResearch.WordTrace]
  refine ⟨33370311521361359367824323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44493748695148479157099097 33370311521361359367824323)
  ·
    refine ⟨50055467282042039051736485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33370311521361359367824323 50055467282042039051736485)
    ·
      refine ⟨9385400115382882322200591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50055467282042039051736485 9385400115382882322200591)
      ·
        refine ⟨14078100173074323483300887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9385400115382882322200591 14078100173074323483300887)
        ·
          refine ⟨21117150259611485224951331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14078100173074323483300887 21117150259611485224951331)
          ·
            refine ⟨31675725389417227837426997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21117150259611485224951331 31675725389417227837426997)
            ·
              refine ⟨2969599255257865109758781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31675725389417227837426997 2969599255257865109758781)
              ·
                refine ⟨1113599720721699416159543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2969599255257865109758781 1113599720721699416159543)
                ·
                  refine ⟨1670399581082549124239315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1113599720721699416159543 1670399581082549124239315)
                  ·
                    refine ⟨2505599371623823686358973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1670399581082549124239315 2505599371623823686358973)
                    ·
                      refine ⟨939599764358933882384615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2505599371623823686358973 939599764358933882384615)
                      ·
                        rfl

theorem cell23_1829864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 3, 1, 1, 3].length) (baseStart_1829864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1829864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1829864 prefixEnd_1829864 := by exact prefixLift 1829864
  have htrace : WordTrace (prefixWord ++ tailWord_1829864) baseStart_1829864 baseEnd_1829864 := by
    simpa [prefixWord, tailWord_1829864, baseEnd_1829864] using wordTrace_append hprefix tailTrace_1829864
  have hstable : (prefixWord ++ tailWord_1829864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829864).length < 2 ^ (prefixWord ++ tailWord_1829864).sum := by decide
  have hdescent : baseEnd_1829864 < baseStart_1829864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829880 : List Nat := [2, 1, 2, 1, 1, 3, 1, 6, 2, 4]
def baseStart_1829880 : Nat := 118140960795 + 1829880 * 2 ^ 59
def prefixEnd_1829880 : Nat := 4983230072969 + 3 ^ 40 * 1829880 * 2
def baseEnd_1829880 : Nat := 313202660016468606594847

theorem tailTrace_1829880 : CollatzResearch.WordTrace tailWord_1829880 prefixEnd_1829880 313202660016468606594847 := by
  unfold tailWord_1829880
  simp only [CollatzResearch.WordTrace]
  refine ⟨33370603305332376734115547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44494137740443168978820729 33370603305332376734115547)
  ·
    refine ⟨50055904957998565101173321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33370603305332376734115547 50055904957998565101173321)
    ·
      refine ⟨37541928718498923825879991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50055904957998565101173321 37541928718498923825879991)
      ·
        refine ⟨56312893077748385738819987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37541928718498923825879991 56312893077748385738819987)
        ·
          refine ⟨84469339616622578608229981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56312893077748385738819987 84469339616622578608229981)
          ·
            refine ⟨31676002356233466978086243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84469339616622578608229981 31676002356233466978086243)
            ·
              refine ⟨47514003534350200467129365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31676002356233466978086243 47514003534350200467129365)
              ·
                refine ⟨2227218915672665646896689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 47514003534350200467129365 2227218915672665646896689)
                ·
                  refine ⟨1670414186754499235172517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2227218915672665646896689 1670414186754499235172517)
                  ·
                    refine ⟨313202660016468606594847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1670414186754499235172517 313202660016468606594847)
                    ·
                      rfl

theorem cell23_1829880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 6, 2, 4].length) (baseStart_1829880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1829880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1829880 prefixEnd_1829880 := by exact prefixLift 1829880
  have htrace : WordTrace (prefixWord ++ tailWord_1829880) baseStart_1829880 baseEnd_1829880 := by
    simpa [prefixWord, tailWord_1829880, baseEnd_1829880] using wordTrace_append hprefix tailTrace_1829880
  have hstable : (prefixWord ++ tailWord_1829880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829880).length < 2 ^ (prefixWord ++ tailWord_1829880).sum := by decide
  have hdescent : baseEnd_1829880 < baseStart_1829880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829893 : List Nat := [1, 3, 1, 1, 2, 3, 4, 8]
def baseStart_1829893 : Nat := 118140960795 + 1829893 * 2 ^ 59
def prefixEnd_1829893 : Nat := 4983230072969 + 3 ^ 40 * 1829893 * 2
def baseEnd_1829893 : Nat := 34800542788811639589703

theorem tailTrace_1829893 : CollatzResearch.WordTrace tailWord_1829893 prefixEnd_1829893 34800542788811639589703 := by
  unfold tailWord_1829893
  simp only [CollatzResearch.WordTrace]
  refine ⟨66741680759617656688454333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44494453839745104458969555 66741680759617656688454333)
  ·
    refine ⟨25028130284856621258170375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66741680759617656688454333 25028130284856621258170375)
    ·
      refine ⟨37542195427284931887255563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25028130284856621258170375 37542195427284931887255563)
      ·
        refine ⟨56313293140927397830883345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37542195427284931887255563 56313293140927397830883345)
        ·
          refine ⟨42234969855695548373162509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56313293140927397830883345 42234969855695548373162509)
          ·
            refine ⟨15838113695885830639935941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42234969855695548373162509 15838113695885830639935941)
            ·
              refine ⟨2969646317978593244987989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15838113695885830639935941 2969646317978593244987989)
              ·
                refine ⟨34800542788811639589703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2969646317978593244987989 34800542788811639589703)
                ·
                  rfl

theorem cell23_1829893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 8].length) (baseStart_1829893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1829893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1829893 prefixEnd_1829893 := by exact prefixLift 1829893
  have htrace : WordTrace (prefixWord ++ tailWord_1829893) baseStart_1829893 baseEnd_1829893 := by
    simpa [prefixWord, tailWord_1829893, baseEnd_1829893] using wordTrace_append hprefix tailTrace_1829893
  have hstable : (prefixWord ++ tailWord_1829893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829893).length < 2 ^ (prefixWord ++ tailWord_1829893).sum := by decide
  have hdescent : baseEnd_1829893 < baseStart_1829893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829917 : List Nat := [1, 4, 2, 2, 3, 1, 1, 2, 1, 2, 4]
def baseStart_1829917 : Nat := 118140960795 + 1829917 * 2 ^ 59
def prefixEnd_1829917 : Nat := 4983230072969 + 3 ^ 40 * 1829917 * 2
def baseEnd_1829917 : Nat := 939626978833622175021871

theorem tailTrace_1829917 : CollatzResearch.WordTrace tailWord_1829917 prefixEnd_1829917 939626978833622175021871 := by
  unfold tailWord_1829917
  simp only [CollatzResearch.WordTrace]
  refine ⟨66742556111530708787328005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44495037407687139191552003 66742556111530708787328005)
  ·
    refine ⟨12514229270912007897624001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66742556111530708787328005 12514229270912007897624001)
    ·
      refine ⟨9385671953184005923218001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12514229270912007897624001 9385671953184005923218001)
      ·
        refine ⟨7039253964888004442413501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9385671953184005923218001 7039253964888004442413501)
        ·
          refine ⟨2639720236833001665905063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7039253964888004442413501 2639720236833001665905063)
          ·
            refine ⟨3959580355249502498857595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2639720236833001665905063 3959580355249502498857595)
            ·
              refine ⟨5939370532874253748286393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3959580355249502498857595 5939370532874253748286393)
              ·
                refine ⟨4454527899655690311214795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5939370532874253748286393 4454527899655690311214795)
                ·
                  refine ⟨6681791849483535466822193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4454527899655690311214795 6681791849483535466822193)
                  ·
                    refine ⟨5011343887112651600116645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6681791849483535466822193 5011343887112651600116645)
                    ·
                      refine ⟨939626978833622175021871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5011343887112651600116645 939626978833622175021871)
                      ·
                        rfl

theorem cell23_1829917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_1829917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1829917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1829917 prefixEnd_1829917 := by exact prefixLift 1829917
  have htrace : WordTrace (prefixWord ++ tailWord_1829917) baseStart_1829917 baseEnd_1829917 := by
    simpa [prefixWord, tailWord_1829917, baseEnd_1829917] using wordTrace_append hprefix tailTrace_1829917
  have hstable : (prefixWord ++ tailWord_1829917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829917).length < 2 ^ (prefixWord ++ tailWord_1829917).sum := by decide
  have hdescent : baseEnd_1829917 < baseStart_1829917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829980 : List Nat := [2, 2, 4, 1, 1, 1, 2, 1, 1, 3, 5]
def baseStart_1829980 : Nat := 118140960795 + 1829980 * 2 ^ 59
def prefixEnd_1829980 : Nat := 4983230072969 + 3 ^ 40 * 1829980 * 2
def baseEnd_1829980 : Nat := 939659328114855428534081

theorem tailTrace_1829980 : CollatzResearch.WordTrace tailWord_1829980 prefixEnd_1829980 939659328114855428534081 := by
  unfold tailWord_1829980
  simp only [CollatzResearch.WordTrace]
  refine ⟨33372426955151235273435697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44496569273534980364580929 33372426955151235273435697)
  ·
    refine ⟨25029320216363426455076773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33372426955151235273435697 25029320216363426455076773)
    ·
      refine ⟨4692997540568142460326895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25029320216363426455076773 4692997540568142460326895)
      ·
        refine ⟨7039496310852213690490343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4692997540568142460326895 7039496310852213690490343)
        ·
          refine ⟨10559244466278320535735515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7039496310852213690490343 10559244466278320535735515)
          ·
            refine ⟨15838866699417480803603273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10559244466278320535735515 15838866699417480803603273)
            ·
              refine ⟨11879150024563110602702455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15838866699417480803603273 11879150024563110602702455)
              ·
                refine ⟨17818725036844665904053683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11879150024563110602702455 17818725036844665904053683)
                ·
                  refine ⟨26728087555266998856080525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17818725036844665904053683 26728087555266998856080525)
                  ·
                    refine ⟨10023032833225124571030197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26728087555266998856080525 10023032833225124571030197)
                    ·
                      refine ⟨939659328114855428534081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10023032833225124571030197 939659328114855428534081)
                      ·
                        rfl

theorem cell23_1829980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_1829980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1829980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1829980 prefixEnd_1829980 := by exact prefixLift 1829980
  have htrace : WordTrace (prefixWord ++ tailWord_1829980) baseStart_1829980 baseEnd_1829980 := by
    simpa [prefixWord, tailWord_1829980, baseEnd_1829980] using wordTrace_append hprefix tailTrace_1829980
  have hstable : (prefixWord ++ tailWord_1829980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829980).length < 2 ^ (prefixWord ++ tailWord_1829980).sum := by decide
  have hdescent : baseEnd_1829980 < baseStart_1829980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829983 : List Nat := [1, 1, 2, 3, 1, 1, 3, 2, 9]
def baseStart_1829983 : Nat := 118140960795 + 1829983 * 2 ^ 59
def prefixEnd_1829983 : Nat := 4983230072969 + 3 ^ 40 * 1829983 * 2
def baseEnd_1829983 : Nat := 104406763172979879644063

theorem tailTrace_1829983 : CollatzResearch.WordTrace tailWord_1829983 prefixEnd_1829983 104406763172979879644063 := by
  unfold tailWord_1829983
  simp only [CollatzResearch.WordTrace]
  refine ⟨66744963329291602059230603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44496642219527734706153735 66744963329291602059230603)
  ·
    refine ⟨100117444993937403088845905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66744963329291602059230603 100117444993937403088845905)
    ·
      refine ⟨75088083745453052316634429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100117444993937403088845905 75088083745453052316634429)
      ·
        refine ⟨28158031404544894618737911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75088083745453052316634429 28158031404544894618737911)
        ·
          refine ⟨42237047106817341928106867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28158031404544894618737911 42237047106817341928106867)
          ·
            refine ⟨63355570660226012892160301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42237047106817341928106867 63355570660226012892160301)
            ·
              refine ⟨23758338997584754834560113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63355570660226012892160301 23758338997584754834560113)
              ·
                refine ⟨17818754248188566125920085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23758338997584754834560113 17818754248188566125920085)
                ·
                  refine ⟨104406763172979879644063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 17818754248188566125920085 104406763172979879644063)
                  ·
                    rfl

theorem cell23_1829983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 9].length) (baseStart_1829983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1829983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1829983 prefixEnd_1829983 := by exact prefixLift 1829983
  have htrace : WordTrace (prefixWord ++ tailWord_1829983) baseStart_1829983 baseEnd_1829983 := by
    simpa [prefixWord, tailWord_1829983, baseEnd_1829983] using wordTrace_append hprefix tailTrace_1829983
  have hstable : (prefixWord ++ tailWord_1829983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829983).length < 2 ^ (prefixWord ++ tailWord_1829983).sum := by decide
  have hdescent : baseEnd_1829983 < baseStart_1829983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830000 : List Nat := [2, 1, 1, 1, 5, 1, 4, 1, 7]
def baseStart_1830000 : Nat := 118140960795 + 1830000 * 2 ^ 59
def prefixEnd_1830000 : Nat := 4983230072969 + 3 ^ 40 * 1830000 * 2
def baseEnd_1830000 : Nat := 104407733080882816698221

theorem tailTrace_1830000 : CollatzResearch.WordTrace tailWord_1830000 prefixEnd_1830000 104407733080882816698221 := by
  unfold tailWord_1830000
  simp only [CollatzResearch.WordTrace]
  refine ⟨33372791685115006981299727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44497055580153342641732969 33372791685115006981299727)
  ·
    refine ⟨50059187527672510471949591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33372791685115006981299727 50059187527672510471949591)
    ·
      refine ⟨75088781291508765707924387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50059187527672510471949591 75088781291508765707924387)
      ·
        refine ⟨112633171937263148561886581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75088781291508765707924387 112633171937263148561886581)
        ·
          refine ⟨10559359869118420177676867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 112633171937263148561886581 10559359869118420177676867)
          ·
            refine ⟨15839039803677630266515301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10559359869118420177676867 15839039803677630266515301)
            ·
              refine ⟨2969819963189555674971619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15839039803677630266515301 2969819963189555674971619)
              ·
                refine ⟨4454729944784333512457429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2969819963189555674971619 4454729944784333512457429)
                ·
                  refine ⟨104407733080882816698221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4454729944784333512457429 104407733080882816698221)
                  ·
                    rfl

theorem cell23_1830000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 1, 7].length) (baseStart_1830000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1830000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1830000 prefixEnd_1830000 := by exact prefixLift 1830000
  have htrace : WordTrace (prefixWord ++ tailWord_1830000) baseStart_1830000 baseEnd_1830000 := by
    simpa [prefixWord, tailWord_1830000, baseEnd_1830000] using wordTrace_append hprefix tailTrace_1830000
  have hstable : (prefixWord ++ tailWord_1830000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830000).length < 2 ^ (prefixWord ++ tailWord_1830000).sum := by decide
  have hdescent : baseEnd_1830000 < baseStart_1830000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830034 : List Nat := [3, 2, 3, 1, 1, 2, 3, 3, 5]
def baseStart_1830034 : Nat := 118140960795 + 1830034 * 2 ^ 59
def prefixEnd_1830034 : Nat := 4983230072969 + 3 ^ 40 * 1830034 * 2
def baseEnd_1830034 : Nat := 104409672896688690806537

theorem tailTrace_1830034 : CollatzResearch.WordTrace tailWord_1830034 prefixEnd_1830034 104409672896688690806537 := by
  unfold tailWord_1830034
  simp only [CollatzResearch.WordTrace]
  refine ⟨16686705863026709442334289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44497882301404558512891437 16686705863026709442334289)
  ·
    refine ⟨12515029397270032081750717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16686705863026709442334289 12515029397270032081750717)
    ·
      refine ⟨4693136023976262030656519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12515029397270032081750717 4693136023976262030656519)
      ·
        refine ⟨7039704035964393045984779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4693136023976262030656519 7039704035964393045984779)
        ·
          refine ⟨10559556053946589568977169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7039704035964393045984779 10559556053946589568977169)
          ·
            refine ⟨7919667040459942176732877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10559556053946589568977169 7919667040459942176732877)
            ·
              refine ⟨2969875140172478316274829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7919667040459942176732877 2969875140172478316274829)
              ·
                refine ⟨1113703177564679368603061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2969875140172478316274829 1113703177564679368603061)
                ·
                  refine ⟨104409672896688690806537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1113703177564679368603061 104409672896688690806537)
                  ·
                    rfl

theorem cell23_1830034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 3, 5].length) (baseStart_1830034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1830034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1830034 prefixEnd_1830034 := by exact prefixLift 1830034
  have htrace : WordTrace (prefixWord ++ tailWord_1830034) baseStart_1830034 baseEnd_1830034 := by
    simpa [prefixWord, tailWord_1830034, baseEnd_1830034] using wordTrace_append hprefix tailTrace_1830034
  have hstable : (prefixWord ++ tailWord_1830034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830034).length < 2 ^ (prefixWord ++ tailWord_1830034).sum := by decide
  have hdescent : baseEnd_1830034 < baseStart_1830034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830067 : List Nat := [1, 1, 1, 2, 3, 2, 2, 3, 2, 4, 2]
def baseStart_1830067 : Nat := 118140960795 + 1830067 * 2 ^ 59
def prefixEnd_1830067 : Nat := 4983230072969 + 3 ^ 40 * 1830067 * 2
def baseEnd_1830067 : Nat := 939704000931796588146181

theorem tailTrace_1830067 : CollatzResearch.WordTrace tailWord_1830067 prefixEnd_1830067 939704000931796588146181 := by
  unfold tailWord_1830067
  simp only [CollatzResearch.WordTrace]
  refine ⟨66748027060987284405288455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44498684707324856270192303 66748027060987284405288455)
  ·
    refine ⟨100122040591480926607932683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66748027060987284405288455 100122040591480926607932683)
    ·
      refine ⟨150183060887221389911899025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100122040591480926607932683 150183060887221389911899025)
      ·
        refine ⟨112637295665416042433924269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150183060887221389911899025 112637295665416042433924269)
        ·
          refine ⟨42238985874531015912721601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112637295665416042433924269 42238985874531015912721601)
          ·
            refine ⟨31679239405898261934541201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42238985874531015912721601 31679239405898261934541201)
            ·
              refine ⟨23759429554423696450905901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31679239405898261934541201 23759429554423696450905901)
              ·
                refine ⟨8909786082908886169089713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23759429554423696450905901 8909786082908886169089713)
                ·
                  refine ⟨6682339562181664626817285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8909786082908886169089713 6682339562181664626817285)
                  ·
                    refine ⟨1252938667909062117528241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6682339562181664626817285 1252938667909062117528241)
                    ·
                      refine ⟨939704000931796588146181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1252938667909062117528241 939704000931796588146181)
                      ·
                        rfl

theorem cell23_1830067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 3, 2, 4, 2].length) (baseStart_1830067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1830067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1830067 prefixEnd_1830067 := by exact prefixLift 1830067
  have htrace : WordTrace (prefixWord ++ tailWord_1830067) baseStart_1830067 baseEnd_1830067 := by
    simpa [prefixWord, tailWord_1830067, baseEnd_1830067] using wordTrace_append hprefix tailTrace_1830067
  have hstable : (prefixWord ++ tailWord_1830067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830067).length < 2 ^ (prefixWord ++ tailWord_1830067).sum := by decide
  have hdescent : baseEnd_1830067 < baseStart_1830067 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830077 : List Nat := [1, 4, 1, 2, 1, 1, 2, 4, 3, 4]
def baseStart_1830077 : Nat := 118140960795 + 1830077 * 2 ^ 59
def prefixEnd_1830077 : Nat := 4983230072969 + 3 ^ 40 * 1830077 * 2
def baseEnd_1830077 : Nat := 313236378579447183007045

theorem tailTrace_1830077 : CollatzResearch.WordTrace tailWord_1830077 prefixEnd_1830077 313236378579447183007045 := by
  unfold tailWord_1830077
  simp only [CollatzResearch.WordTrace]
  refine ⟨66748391790951056113152485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44498927860634037408768323 66748391790951056113152485)
  ·
    refine ⟨12515323460803323021216091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66748391790951056113152485 12515323460803323021216091)
    ·
      refine ⟨18772985191204984531824137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12515323460803323021216091 18772985191204984531824137)
      ·
        refine ⟨14079738893403738398868103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18772985191204984531824137 14079738893403738398868103)
        ·
          refine ⟨21119608340105607598302155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14079738893403738398868103 21119608340105607598302155)
          ·
            refine ⟨31679412510158411397453233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21119608340105607598302155 31679412510158411397453233)
            ·
              refine ⟨23759559382618808548089925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31679412510158411397453233 23759559382618808548089925)
              ·
                refine ⟨4454917384241026602766861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23759559382618808548089925 4454917384241026602766861)
                ·
                  refine ⟨1670594019090384976037573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4454917384241026602766861 1670594019090384976037573)
                  ·
                    refine ⟨313236378579447183007045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1670594019090384976037573 313236378579447183007045)
                    ·
                      rfl

theorem cell23_1830077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 4, 3, 4].length) (baseStart_1830077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1830077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1830077 prefixEnd_1830077 := by exact prefixLift 1830077
  have htrace : WordTrace (prefixWord ++ tailWord_1830077) baseStart_1830077 baseEnd_1830077 := by
    simpa [prefixWord, tailWord_1830077, baseEnd_1830077] using wordTrace_append hprefix tailTrace_1830077
  have hstable : (prefixWord ++ tailWord_1830077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830077).length < 2 ^ (prefixWord ++ tailWord_1830077).sum := by decide
  have hdescent : baseEnd_1830077 < baseStart_1830077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830111 : List Nat := [1, 1, 2, 3, 2, 1, 6, 2, 1, 4]
def baseStart_1830111 : Nat := 118140960795 + 1830111 * 2 ^ 59
def prefixEnd_1830111 : Nat := 4983230072969 + 3 ^ 40 * 1830111 * 2
def baseEnd_1830111 : Nat := 313242198026864805331993

theorem tailTrace_1830111 : CollatzResearch.WordTrace tailWord_1830111 prefixEnd_1830111 313242198026864805331993 := by
  unfold tailWord_1830111
  simp only [CollatzResearch.WordTrace]
  refine ⟨66749631872827879919890187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44499754581885253279926791 66749631872827879919890187)
  ·
    refine ⟨100124447809241819879835281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66749631872827879919890187 100124447809241819879835281)
    ·
      refine ⟨75093335856931364909876461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100124447809241819879835281 75093335856931364909876461)
      ·
        refine ⟨28160000946349261841203673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75093335856931364909876461 28160000946349261841203673)
        ·
          refine ⟨21120000709761946380902755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28160000946349261841203673 21120000709761946380902755)
          ·
            refine ⟨31680001064642919571354133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21120000709761946380902755 31680001064642919571354133)
            ·
              refine ⟨1485000049905136854907225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 31680001064642919571354133 1485000049905136854907225)
              ·
                refine ⟨1113750037428852641180419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1485000049905136854907225 1113750037428852641180419)
                ·
                  refine ⟨1670625056143278961770629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1113750037428852641180419 1670625056143278961770629)
                  ·
                    refine ⟨313242198026864805331993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1670625056143278961770629 313242198026864805331993)
                    ·
                      rfl

theorem cell23_1830111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 6, 2, 1, 4].length) (baseStart_1830111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1830111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1830111 prefixEnd_1830111 := by exact prefixLift 1830111
  have htrace : WordTrace (prefixWord ++ tailWord_1830111) baseStart_1830111 baseEnd_1830111 := by
    simpa [prefixWord, tailWord_1830111, baseEnd_1830111] using wordTrace_append hprefix tailTrace_1830111
  have hstable : (prefixWord ++ tailWord_1830111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830111).length < 2 ^ (prefixWord ++ tailWord_1830111).sum := by decide
  have hdescent : baseEnd_1830111 < baseStart_1830111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830137 : List Nat := [1, 2, 1, 3, 1, 1, 4, 4, 1, 5]
def baseStart_1830137 : Nat := 118140960795 + 1830137 * 2 ^ 59
def prefixEnd_1830137 : Nat := 4983230072969 + 3 ^ 40 * 1830137 * 2
def baseEnd_1830137 : Nat := 313246648192537104756953

theorem tailTrace_1830137 : CollatzResearch.WordTrace tailWord_1830137 prefixEnd_1830137 313246648192537104756953 := by
  unfold tailWord_1830137
  simp only [CollatzResearch.WordTrace]
  refine ⟨66750580170733686360336665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44500386780489124240224443 66750580170733686360336665)
  ·
    refine ⟨50062935128050264770252499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66750580170733686360336665 50062935128050264770252499)
    ·
      refine ⟨75094402692075397155378749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50062935128050264770252499 75094402692075397155378749)
      ·
        refine ⟨28160401009528273933267031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75094402692075397155378749 28160401009528273933267031)
        ·
          refine ⟨42240601514292410899900547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28160401009528273933267031 42240601514292410899900547)
          ·
            refine ⟨63360902271438616349850821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42240601514292410899900547 63360902271438616349850821)
            ·
              refine ⟨11880169175894740565597029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63360902271438616349850821 11880169175894740565597029)
              ·
                refine ⟨2227531720480263856049443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11880169175894740565597029 2227531720480263856049443)
                ·
                  refine ⟨3341297580720395784074165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2227531720480263856049443 3341297580720395784074165)
                  ·
                    refine ⟨313246648192537104756953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3341297580720395784074165 313246648192537104756953)
                    ·
                      rfl

theorem cell23_1830137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 4, 1, 5].length) (baseStart_1830137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1830137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1830137 prefixEnd_1830137 := by exact prefixLift 1830137
  have htrace : WordTrace (prefixWord ++ tailWord_1830137) baseStart_1830137 baseEnd_1830137 := by
    simpa [prefixWord, tailWord_1830137, baseEnd_1830137] using wordTrace_append hprefix tailTrace_1830137
  have hstable : (prefixWord ++ tailWord_1830137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830137).length < 2 ^ (prefixWord ++ tailWord_1830137).sum := by decide
  have hdescent : baseEnd_1830137 < baseStart_1830137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830184 : List Nat := [2, 1, 5, 1, 2, 1, 3, 1, 1, 6]
def baseStart_1830184 : Nat := 118140960795 + 1830184 * 2 ^ 59
def prefixEnd_1830184 : Nat := 4983230072969 + 3 ^ 40 * 1830184 * 2
def baseEnd_1830184 : Nat := 313254692722790876794381

theorem tailTrace_1830184 : CollatzResearch.WordTrace tailWord_1830184 prefixEnd_1830184 313254692722790876794381 := by
  unfold tailWord_1830184
  simp only [CollatzResearch.WordTrace]
  refine ⟨33376147200781706693648803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44501529601042275591531737 33376147200781706693648803)
  ·
    refine ⟨50064220801172560040473205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33376147200781706693648803 50064220801172560040473205)
    ·
      refine ⟨4693520700109927503794363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50064220801172560040473205 4693520700109927503794363)
      ·
        refine ⟨7040281050164891255691545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4693520700109927503794363 7040281050164891255691545)
        ·
          refine ⟨5280210787623668441768659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7040281050164891255691545 5280210787623668441768659)
          ·
            refine ⟨7920316181435502662652989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5280210787623668441768659 7920316181435502662652989)
            ·
              refine ⟨2970118568038313498494871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7920316181435502662652989 2970118568038313498494871)
              ·
                refine ⟨4455177852057470247742307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2970118568038313498494871 4455177852057470247742307)
                ·
                  refine ⟨6682766778086205371613461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4455177852057470247742307 6682766778086205371613461)
                  ·
                    refine ⟨313254692722790876794381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6682766778086205371613461 313254692722790876794381)
                    ·
                      rfl

theorem cell23_1830184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_1830184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1830184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1830184 prefixEnd_1830184 := by exact prefixLift 1830184
  have htrace : WordTrace (prefixWord ++ tailWord_1830184) baseStart_1830184 baseEnd_1830184 := by
    simpa [prefixWord, tailWord_1830184, baseEnd_1830184] using wordTrace_append hprefix tailTrace_1830184
  have hstable : (prefixWord ++ tailWord_1830184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830184).length < 2 ^ (prefixWord ++ tailWord_1830184).sum := by decide
  have hdescent : baseEnd_1830184 < baseStart_1830184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830197 : List Nat := [1, 3, 3, 1, 2, 3, 1, 9]
def baseStart_1830197 : Nat := 118140960795 + 1830197 * 2 ^ 59
def prefixEnd_1830197 : Nat := 4983230072969 + 3 ^ 40 * 1830197 * 2
def baseEnd_1830197 : Nat := 34806324200625225167429

theorem tailTrace_1830197 : CollatzResearch.WordTrace tailWord_1830197 prefixEnd_1830197 34806324200625225167429 := by
  unfold tailWord_1830197
  simp only [CollatzResearch.WordTrace]
  refine ⟨66752768550516316607520845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44501845700344211071680563 66752768550516316607520845)
  ·
    refine ⟨25032288206443618727820317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66752768550516316607520845 25032288206443618727820317)
    ·
      refine ⟨9387108077416357022932619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25032288206443618727820317 9387108077416357022932619)
      ·
        refine ⟨14080662116124535534398929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9387108077416357022932619 14080662116124535534398929)
        ·
          refine ⟨10560496587093401650799197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14080662116124535534398929 10560496587093401650799197)
          ·
            refine ⟨3960186220160025619049699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10560496587093401650799197 3960186220160025619049699)
            ·
              refine ⟨5940279330240038428574549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3960186220160025619049699 5940279330240038428574549)
              ·
                refine ⟨34806324200625225167429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5940279330240038428574549 34806324200625225167429)
                ·
                  rfl

theorem cell23_1830197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 9].length) (baseStart_1830197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1830197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1830197 prefixEnd_1830197 := by exact prefixLift 1830197
  have htrace : WordTrace (prefixWord ++ tailWord_1830197) baseStart_1830197 baseEnd_1830197 := by
    simpa [prefixWord, tailWord_1830197, baseEnd_1830197] using wordTrace_append hprefix tailTrace_1830197
  have hstable : (prefixWord ++ tailWord_1830197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830197).length < 2 ^ (prefixWord ++ tailWord_1830197).sum := by decide
  have hdescent : baseEnd_1830197 < baseStart_1830197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830224 : List Nat := [2, 1, 1, 1, 1, 5, 1, 3, 4, 1, 3]
def baseStart_1830224 : Nat := 118140960795 + 1830224 * 2 ^ 59
def prefixEnd_1830224 : Nat := 4983230072969 + 3 ^ 40 * 1830224 * 2
def baseEnd_1830224 : Nat := 939784617394552473882959

theorem tailTrace_1830224 : CollatzResearch.WordTrace tailWord_1830224 prefixEnd_1830224 939784617394552473882959 := by
  unfold tailWord_1830224
  simp only [CollatzResearch.WordTrace]
  refine ⟨33376876660709250109376863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44502502214279000145835817 33376876660709250109376863)
  ·
    refine ⟨50065314991063875164065295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33376876660709250109376863 50065314991063875164065295)
    ·
      refine ⟨75097972486595812746097943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50065314991063875164065295 75097972486595812746097943)
      ·
        refine ⟨112646958729893719119146915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75097972486595812746097943 112646958729893719119146915)
        ·
          refine ⟨168970438094840578678720373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112646958729893719119146915 168970438094840578678720373)
          ·
            refine ⟨15840978571391304251130035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 168970438094840578678720373 15840978571391304251130035)
            ·
              refine ⟨23761467857086956376695053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15840978571391304251130035 23761467857086956376695053)
              ·
                refine ⟨8910550446407608641260645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23761467857086956376695053 8910550446407608641260645)
                ·
                  refine ⟨1670728208701426620236371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8910550446407608641260645 1670728208701426620236371)
                  ·
                    refine ⟨2506092313052139930354557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1670728208701426620236371 2506092313052139930354557)
                    ·
                      refine ⟨939784617394552473882959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2506092313052139930354557 939784617394552473882959)
                      ·
                        rfl

theorem cell23_1830224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 3, 4, 1, 3].length) (baseStart_1830224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1830224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1830224 prefixEnd_1830224 := by exact prefixLift 1830224
  have htrace : WordTrace (prefixWord ++ tailWord_1830224) baseStart_1830224 baseEnd_1830224 := by
    simpa [prefixWord, tailWord_1830224, baseEnd_1830224] using wordTrace_append hprefix tailTrace_1830224
  have hstable : (prefixWord ++ tailWord_1830224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830224).length < 2 ^ (prefixWord ++ tailWord_1830224).sum := by decide
  have hdescent : baseEnd_1830224 < baseStart_1830224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830225 : List Nat := [1, 2, 2, 1, 4, 1, 5, 2, 1, 2, 2]
def baseStart_1830225 : Nat := 118140960795 + 1830225 * 2 ^ 59
def prefixEnd_1830225 : Nat := 4983230072969 + 3 ^ 40 * 1830225 * 2
def baseEnd_1830225 : Nat := 939785130875206969970455

theorem tailTrace_1830225 : CollatzResearch.WordTrace tailWord_1830225 prefixEnd_1830225 939785130875206969970455 := by
  unfold tailWord_1830225
  simp only [CollatzResearch.WordTrace]
  refine ⟨66753789794414877389540129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44502526529609918259693419 66753789794414877389540129)
  ·
    refine ⟨50065342345811158042155097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66753789794414877389540129 50065342345811158042155097)
    ·
      refine ⟨37549006759358368531616323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50065342345811158042155097 37549006759358368531616323)
      ·
        refine ⟨56323510139037552797424485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37549006759358368531616323 56323510139037552797424485)
        ·
          refine ⟨10560658151069541149517091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56323510139037552797424485 10560658151069541149517091)
          ·
            refine ⟨15840987226604311724275637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10560658151069541149517091 15840987226604311724275637)
            ·
              refine ⟨1485092552494154224150841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15840987226604311724275637 1485092552494154224150841)
              ·
                refine ⟨1113819414370615668113131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1485092552494154224150841 1113819414370615668113131)
                ·
                  refine ⟨1670729121555923502169697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1113819414370615668113131 1670729121555923502169697)
                  ·
                    refine ⟨1253046841166942626627273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1670729121555923502169697 1253046841166942626627273)
                    ·
                      refine ⟨939785130875206969970455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1253046841166942626627273 939785130875206969970455)
                      ·
                        rfl

theorem cell23_1830225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 5, 2, 1, 2, 2].length) (baseStart_1830225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1830225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1830225 prefixEnd_1830225 := by exact prefixLift 1830225
  have htrace : WordTrace (prefixWord ++ tailWord_1830225) baseStart_1830225 baseEnd_1830225 := by
    simpa [prefixWord, tailWord_1830225, baseEnd_1830225] using wordTrace_append hprefix tailTrace_1830225
  have hstable : (prefixWord ++ tailWord_1830225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830225).length < 2 ^ (prefixWord ++ tailWord_1830225).sum := by decide
  have hdescent : baseEnd_1830225 < baseStart_1830225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830267 : List Nat := [1, 1, 1, 1, 1, 6, 1, 3, 2, 1, 5]
def baseStart_1830267 : Nat := 118140960795 + 1830267 * 2 ^ 59
def prefixEnd_1830267 : Nat := 4983230072969 + 3 ^ 40 * 1830267 * 2
def baseEnd_1830267 : Nat := 939806697062695805645261

theorem tailTrace_1830267 : CollatzResearch.WordTrace tailWord_1830267 prefixEnd_1830267 939806697062695805645261 := by
  unfold tailWord_1830267
  simp only [CollatzResearch.WordTrace]
  refine ⟨66755321660262718562569055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44503547773508479041712703 66755321660262718562569055)
  ·
    refine ⟨100132982490394077843853583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66755321660262718562569055 100132982490394077843853583)
    ·
      refine ⟨150199473735591116765780375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100132982490394077843853583 150199473735591116765780375)
      ·
        refine ⟨225299210603386675148670563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150199473735591116765780375 225299210603386675148670563)
        ·
          refine ⟨337948815905080012723005845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225299210603386675148670563 337948815905080012723005845)
          ·
            refine ⟨15841350745550625596390899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 337948815905080012723005845 15841350745550625596390899)
            ·
              refine ⟨23762026118325938394586349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15841350745550625596390899 23762026118325938394586349)
              ·
                refine ⟨8910759794372226897969881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23762026118325938394586349 8910759794372226897969881)
                ·
                  refine ⟨6683069845779170173477411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8910759794372226897969881 6683069845779170173477411)
                  ·
                    refine ⟨10024604768668755260216117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6683069845779170173477411 10024604768668755260216117)
                    ·
                      refine ⟨939806697062695805645261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10024604768668755260216117 939806697062695805645261)
                      ·
                        rfl

theorem cell23_1830267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 3, 2, 1, 5].length) (baseStart_1830267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1830267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1830267 prefixEnd_1830267 := by exact prefixLift 1830267
  have htrace : WordTrace (prefixWord ++ tailWord_1830267) baseStart_1830267 baseEnd_1830267 := by
    simpa [prefixWord, tailWord_1830267, baseEnd_1830267] using wordTrace_append hprefix tailTrace_1830267
  have hstable : (prefixWord ++ tailWord_1830267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830267).length < 2 ^ (prefixWord ++ tailWord_1830267).sum := by decide
  have hdescent : baseEnd_1830267 < baseStart_1830267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830268 : List Nat := [2, 2, 2, 1, 1, 1, 7, 1, 1, 3, 2]
def baseStart_1830268 : Nat := 118140960795 + 1830268 * 2 ^ 59
def prefixEnd_1830268 : Nat := 4983230072969 + 3 ^ 40 * 1830268 * 2
def baseEnd_1830268 : Nat := 939807210543350301732757

theorem tailTrace_1830268 : CollatzResearch.WordTrace tailWord_1830268 prefixEnd_1830268 939807210543350301732757 := by
  unfold tailWord_1830268
  simp only [CollatzResearch.WordTrace]
  refine ⟨33377679066629547866677729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44503572088839397155570305 33377679066629547866677729)
  ·
    refine ⟨25033259299972160900008297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33377679066629547866677729 25033259299972160900008297)
    ·
      refine ⟨18774944474979120675006223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25033259299972160900008297 18774944474979120675006223)
      ·
        refine ⟨28162416712468681012509335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18774944474979120675006223 28162416712468681012509335)
        ·
          refine ⟨42243625068703021518764003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28162416712468681012509335 42243625068703021518764003)
          ·
            refine ⟨63365437603054532278146005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42243625068703021518764003 63365437603054532278146005)
            ·
              refine ⟨1485127443821590600269047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 63365437603054532278146005 1485127443821590600269047)
              ·
                refine ⟨2227691165732385900403571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1485127443821590600269047 2227691165732385900403571)
                ·
                  refine ⟨3341536748598578850605357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2227691165732385900403571 3341536748598578850605357)
                  ·
                    refine ⟨1253076280724467068977009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3341536748598578850605357 1253076280724467068977009)
                    ·
                      refine ⟨939807210543350301732757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1253076280724467068977009 939807210543350301732757)
                      ·
                        rfl

theorem cell23_1830268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 7, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 7, 1, 1, 3, 2].length) (baseStart_1830268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1830268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1830268 prefixEnd_1830268 := by exact prefixLift 1830268
  have htrace : WordTrace (prefixWord ++ tailWord_1830268) baseStart_1830268 baseEnd_1830268 := by
    simpa [prefixWord, tailWord_1830268, baseEnd_1830268] using wordTrace_append hprefix tailTrace_1830268
  have hstable : (prefixWord ++ tailWord_1830268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830268).length < 2 ^ (prefixWord ++ tailWord_1830268).sum := by decide
  have hdescent : baseEnd_1830268 < baseStart_1830268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830298 : List Nat := [3, 1, 1, 4, 1, 1, 1, 5, 2, 2, 2]
def baseStart_1830298 : Nat := 118140960795 + 1830298 * 2 ^ 59
def prefixEnd_1830298 : Nat := 4983230072969 + 3 ^ 40 * 1830298 * 2
def baseEnd_1830298 : Nat := 939822614962985184357619

theorem tailTrace_1830298 : CollatzResearch.WordTrace tailWord_1830298 prefixEnd_1830298 939822614962985184357619 := by
  unfold tailWord_1830298
  simp only [CollatzResearch.WordTrace]
  refine ⟨16689113080787602714236887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44504301548766940571298365 16689113080787602714236887)
  ·
    refine ⟨25033669621181404071355331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16689113080787602714236887 25033669621181404071355331)
    ·
      refine ⟨37550504431772106107032997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25033669621181404071355331 37550504431772106107032997)
      ·
        refine ⟨7040719580957269895068687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37550504431772106107032997 7040719580957269895068687)
        ·
          refine ⟨10561079371435904842603031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7040719580957269895068687 10561079371435904842603031)
          ·
            refine ⟨15841619057153857263904547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10561079371435904842603031 15841619057153857263904547)
            ·
              refine ⟨23762428585730785895856821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15841619057153857263904547 23762428585730785895856821)
              ·
                refine ⟨2227727679912261177736577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23762428585730785895856821 2227727679912261177736577)
                ·
                  refine ⟨1670795759934195883302433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2227727679912261177736577 1670795759934195883302433)
                  ·
                    refine ⟨1253096819950646912476825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1670795759934195883302433 1253096819950646912476825)
                    ·
                      refine ⟨939822614962985184357619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1253096819950646912476825 939822614962985184357619)
                      ·
                        rfl

theorem cell23_1830298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 5, 2, 2, 2].length) (baseStart_1830298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1830298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1830298 prefixEnd_1830298 := by exact prefixLift 1830298
  have htrace : WordTrace (prefixWord ++ tailWord_1830298) baseStart_1830298 baseEnd_1830298 := by
    simpa [prefixWord, tailWord_1830298, baseEnd_1830298] using wordTrace_append hprefix tailTrace_1830298
  have hstable : (prefixWord ++ tailWord_1830298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830298).length < 2 ^ (prefixWord ++ tailWord_1830298).sum := by decide
  have hdescent : baseEnd_1830298 < baseStart_1830298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830321 : List Nat := [1, 2, 2, 4, 1, 1, 4, 3, 5]
def baseStart_1830321 : Nat := 118140960795 + 1830321 * 2 ^ 59
def prefixEnd_1830321 : Nat := 4983230072969 + 3 ^ 40 * 1830321 * 2
def baseEnd_1830321 : Nat := 104426047224226510485557

theorem tailTrace_1830321 : CollatzResearch.WordTrace tailWord_1830321 prefixEnd_1830321 104426047224226510485557 := by
  unfold tailWord_1830321
  simp only [CollatzResearch.WordTrace]
  refine ⟨66757291202067085785034817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44504860801378057190023211 66757291202067085785034817)
  ·
    refine ⟨50067968401550314338776113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66757291202067085785034817 50067968401550314338776113)
    ·
      refine ⟨37550976301162735754082085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50067968401550314338776113 37550976301162735754082085)
      ·
        refine ⟨7040808056468012953890391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37550976301162735754082085 7040808056468012953890391)
        ·
          refine ⟨10561212084702019430835587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7040808056468012953890391 10561212084702019430835587)
          ·
            refine ⟨15841818127053029146253381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10561212084702019430835587 15841818127053029146253381)
            ·
              refine ⟨2970340898822442964922509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15841818127053029146253381 2970340898822442964922509)
              ·
                refine ⟨1113877837058416111845941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2970340898822442964922509 1113877837058416111845941)
                ·
                  refine ⟨104426047224226510485557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1113877837058416111845941 104426047224226510485557)
                  ·
                    rfl

theorem cell23_1830321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 3, 5].length) (baseStart_1830321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1830321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1830321 prefixEnd_1830321 := by exact prefixLift 1830321
  have htrace : WordTrace (prefixWord ++ tailWord_1830321) baseStart_1830321 baseEnd_1830321 := by
    simpa [prefixWord, tailWord_1830321, baseEnd_1830321] using wordTrace_append hprefix tailTrace_1830321
  have hstable : (prefixWord ++ tailWord_1830321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830321).length < 2 ^ (prefixWord ++ tailWord_1830321).sum := by decide
  have hdescent : baseEnd_1830321 < baseStart_1830321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830332 : List Nat := [2, 2, 2, 4, 2, 2, 1, 2, 2, 2, 2]
def baseStart_1830332 : Nat := 118140960795 + 1830332 * 2 ^ 59
def prefixEnd_1830332 : Nat := 4983230072969 + 3 ^ 40 * 1830332 * 2
def baseEnd_1830332 : Nat := 939840073305238051332463

theorem tailTrace_1830332 : CollatzResearch.WordTrace tailWord_1830332 prefixEnd_1830332 939840073305238051332463 := by
  unfold tailWord_1830332
  simp only [CollatzResearch.WordTrace]
  refine ⟨33378846202513617331842625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44505128270018156442456833 33378846202513617331842625)
  ·
    refine ⟨25034134651885212998881969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33378846202513617331842625 25034134651885212998881969)
    ·
      refine ⟨18775600988913909749161477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25034134651885212998881969 18775600988913909749161477)
      ·
        refine ⟨3520425185421358077967777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18775600988913909749161477 3520425185421358077967777)
        ·
          refine ⟨2640318889066018558475833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3520425185421358077967777 2640318889066018558475833)
          ·
            refine ⟨1980239166799513918856875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2640318889066018558475833 1980239166799513918856875)
            ·
              refine ⟨2970358750199270878285313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1980239166799513918856875 2970358750199270878285313)
              ·
                refine ⟨2227769062649453158713985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2970358750199270878285313 2227769062649453158713985)
                ·
                  refine ⟨1670826796987089869035489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2227769062649453158713985 1670826796987089869035489)
                  ·
                    refine ⟨1253120097740317401776617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1670826796987089869035489 1253120097740317401776617)
                    ·
                      refine ⟨939840073305238051332463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1253120097740317401776617 939840073305238051332463)
                      ·
                        rfl

theorem cell23_1830332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_1830332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1830332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1830332 prefixEnd_1830332 := by exact prefixLift 1830332
  have htrace : WordTrace (prefixWord ++ tailWord_1830332) baseStart_1830332 baseEnd_1830332 := by
    simpa [prefixWord, tailWord_1830332, baseEnd_1830332] using wordTrace_append hprefix tailTrace_1830332
  have hstable : (prefixWord ++ tailWord_1830332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830332).length < 2 ^ (prefixWord ++ tailWord_1830332).sum := by decide
  have hdescent : baseEnd_1830332 < baseStart_1830332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830334 : List Nat := [4, 2, 1, 1, 1, 1, 1, 3, 4, 5]
def baseStart_1830334 : Nat := 118140960795 + 1830334 * 2 ^ 59
def prefixEnd_1830334 : Nat := 4983230072969 + 3 ^ 40 * 1830334 * 2
def baseEnd_1830334 : Nat := 313280366755515681169151

theorem tailTrace_1830334 : CollatzResearch.WordTrace tailWord_1830334 prefixEnd_1830334 313280366755515681169151 := by
  unfold tailWord_1830334
  simp only [CollatzResearch.WordTrace]
  refine ⟨8344720668877498625657257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44505176900679992670172037 8344720668877498625657257)
  ·
    refine ⟨6258540501658123969242943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8344720668877498625657257 6258540501658123969242943)
    ·
      refine ⟨9387810752487185953864415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6258540501658123969242943 9387810752487185953864415)
      ·
        refine ⟨14081716128730778930796623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9387810752487185953864415 14081716128730778930796623)
        ·
          refine ⟨21122574193096168396194935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14081716128730778930796623 21122574193096168396194935)
          ·
            refine ⟨31683861289644252594292403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21122574193096168396194935 31683861289644252594292403)
            ·
              refine ⟨47525791934466378891438605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31683861289644252594292403 47525791934466378891438605)
              ·
                refine ⟨17822171975424892084289477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47525791934466378891438605 17822171975424892084289477)
                ·
                  refine ⟨3341657245392167265804277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17822171975424892084289477 3341657245392167265804277)
                  ·
                    refine ⟨313280366755515681169151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3341657245392167265804277 313280366755515681169151)
                    ·
                      rfl

theorem cell23_1830334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 4, 5].length) (baseStart_1830334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1830334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1830334 prefixEnd_1830334 := by exact prefixLift 1830334
  have htrace : WordTrace (prefixWord ++ tailWord_1830334) baseStart_1830334 baseEnd_1830334 := by
    simpa [prefixWord, tailWord_1830334, baseEnd_1830334] using wordTrace_append hprefix tailTrace_1830334
  have hstable : (prefixWord ++ tailWord_1830334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830334).length < 2 ^ (prefixWord ++ tailWord_1830334).sum := by decide
  have hdescent : baseEnd_1830334 < baseStart_1830334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830394 : List Nat := [3, 1, 1, 1, 1, 2, 4, 4, 6]
def baseStart_1830394 : Nat := 118140960795 + 1830394 * 2 ^ 59
def prefixEnd_1830394 : Nat := 4983230072969 + 3 ^ 40 * 1830394 * 2
def baseEnd_1830394 : Nat := 104430212122868534306353

theorem tailTrace_1830394 : CollatzResearch.WordTrace tailWord_1830394 prefixEnd_1830394 104430212122868534306353 := by
  unfold tailWord_1830394
  simp only [CollatzResearch.WordTrace]
  refine ⟨16689988432700654813110559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44506635820535079501628157 16689988432700654813110559)
  ·
    refine ⟨25034982649050982219665839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16689988432700654813110559 25034982649050982219665839)
    ·
      refine ⟨37552473973576473329498759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25034982649050982219665839 37552473973576473329498759)
      ·
        refine ⟨56328710960364709994248139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37552473973576473329498759 56328710960364709994248139)
        ·
          refine ⟨84493066440547064991372209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56328710960364709994248139 84493066440547064991372209)
          ·
            refine ⟨63369799830410298743529157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84493066440547064991372209 63369799830410298743529157)
            ·
              refine ⟨11881837468201931014411717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63369799830410298743529157 11881837468201931014411717)
              ·
                refine ⟨2227844525287862065202197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11881837468201931014411717 2227844525287862065202197)
                ·
                  refine ⟨104430212122868534306353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2227844525287862065202197 104430212122868534306353)
                  ·
                    rfl

theorem cell23_1830394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 4, 6].length) (baseStart_1830394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1830394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1830394 prefixEnd_1830394 := by exact prefixLift 1830394
  have htrace : WordTrace (prefixWord ++ tailWord_1830394) baseStart_1830394 baseEnd_1830394 := by
    simpa [prefixWord, tailWord_1830394, baseEnd_1830394] using wordTrace_append hprefix tailTrace_1830394
  have hstable : (prefixWord ++ tailWord_1830394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830394).length < 2 ^ (prefixWord ++ tailWord_1830394).sum := by decide
  have hdescent : baseEnd_1830394 < baseStart_1830394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830411 : List Nat := [1, 1, 1, 1, 8, 1, 1, 3, 6]
def baseStart_1830411 : Nat := 118140960795 + 1830411 * 2 ^ 59
def prefixEnd_1830411 : Nat := 4983230072969 + 3 ^ 40 * 1830411 * 2
def baseEnd_1830411 : Nat := 104431182030771471360511

theorem tailTrace_1830411 : CollatzResearch.WordTrace tailWord_1830411 prefixEnd_1830411 104431182030771471360511 := by
  unfold tailWord_1830411
  simp only [CollatzResearch.WordTrace]
  refine ⟨66760573771741031155811087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44507049181160687437207391 66760573771741031155811087)
  ·
    refine ⟨100140860657611546733716631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66760573771741031155811087 100140860657611546733716631)
    ·
      refine ⟨150211290986417320100574947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100140860657611546733716631 150211290986417320100574947)
      ·
        refine ⟨225316936479625980150862421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150211290986417320100574947 225316936479625980150862421)
        ·
          refine ⟨2640432849370616954892919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 225316936479625980150862421 2640432849370616954892919)
          ·
            refine ⟨3960649274055925432339379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2640432849370616954892919 3960649274055925432339379)
            ·
              refine ⟨5940973911083888148509069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3960649274055925432339379 5940973911083888148509069)
              ·
                refine ⟨2227865216656458055690901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5940973911083888148509069 2227865216656458055690901)
                ·
                  refine ⟨104431182030771471360511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2227865216656458055690901 104431182030771471360511)
                  ·
                    rfl

theorem cell23_1830411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 3, 6].length) (baseStart_1830411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1830411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1830411 prefixEnd_1830411 := by exact prefixLift 1830411
  have htrace : WordTrace (prefixWord ++ tailWord_1830411) baseStart_1830411 baseEnd_1830411 := by
    simpa [prefixWord, tailWord_1830411, baseEnd_1830411] using wordTrace_append hprefix tailTrace_1830411
  have hstable : (prefixWord ++ tailWord_1830411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830411).length < 2 ^ (prefixWord ++ tailWord_1830411).sum := by decide
  have hdescent : baseEnd_1830411 < baseStart_1830411 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830431 : List Nat := [1, 1, 2, 4, 1, 1, 2, 3, 1, 5, 2]
def baseStart_1830431 : Nat := 118140960795 + 1830431 * 2 ^ 59
def prefixEnd_1830431 : Nat := 4983230072969 + 3 ^ 40 * 1830431 * 2
def baseEnd_1830431 : Nat := 939890907890033163994507

theorem tailTrace_1830431 : CollatzResearch.WordTrace tailWord_1830431 prefixEnd_1830431 939890907890033163994507 := by
  unfold tailWord_1830431
  simp only [CollatzResearch.WordTrace]
  refine ⟨66761303231668574571539147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44507535487779049714359431 66761303231668574571539147)
  ·
    refine ⟨100141954847502861857308721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66761303231668574571539147 100141954847502861857308721)
    ·
      refine ⟨75106466135627146392981541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100141954847502861857308721 75106466135627146392981541)
      ·
        refine ⟨14082462400430089948684039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75106466135627146392981541 14082462400430089948684039)
        ·
          refine ⟨21123693600645134923026059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14082462400430089948684039 21123693600645134923026059)
          ·
            refine ⟨31685540400967702384539089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21123693600645134923026059 31685540400967702384539089)
            ·
              refine ⟨23764155300725776788404317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31685540400967702384539089 23764155300725776788404317)
              ·
                refine ⟨8911558237772166295651619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23764155300725776788404317 8911558237772166295651619)
                ·
                  refine ⟨13367337356658249443477429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8911558237772166295651619 13367337356658249443477429)
                  ·
                    refine ⟨1253187877186710885326009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13367337356658249443477429 1253187877186710885326009)
                    ·
                      refine ⟨939890907890033163994507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1253187877186710885326009 939890907890033163994507)
                      ·
                        rfl

theorem cell23_1830431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 3, 1, 5, 2].length) (baseStart_1830431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1830431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1830431 prefixEnd_1830431 := by exact prefixLift 1830431
  have htrace : WordTrace (prefixWord ++ tailWord_1830431) baseStart_1830431 baseEnd_1830431 := by
    simpa [prefixWord, tailWord_1830431, baseEnd_1830431] using wordTrace_append hprefix tailTrace_1830431
  have hstable : (prefixWord ++ tailWord_1830431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830431).length < 2 ^ (prefixWord ++ tailWord_1830431).sum := by decide
  have hdescent : baseEnd_1830431 < baseStart_1830431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830455 : List Nat := [1, 1, 3, 1, 2, 5, 1, 4, 1, 1, 3]
def baseStart_1830455 : Nat := 118140960795 + 1830455 * 2 ^ 59
def prefixEnd_1830455 : Nat := 4983230072969 + 3 ^ 40 * 1830455 * 2
def baseEnd_1830455 : Nat := 939903231425741070094397

theorem tailTrace_1830455 : CollatzResearch.WordTrace tailWord_1830455 prefixEnd_1830455 939903231425741070094397 := by
  unfold tailWord_1830455
  simp only [CollatzResearch.WordTrace]
  refine ⟨66762178583581626670412819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44508119055721084446941879 66762178583581626670412819)
  ·
    refine ⟨100143267875372440005619229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66762178583581626670412819 100143267875372440005619229)
    ·
      refine ⟨37553725453264665002107211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100143267875372440005619229 37553725453264665002107211)
      ·
        refine ⟨56330588179896997503160817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37553725453264665002107211 56330588179896997503160817)
        ·
          refine ⟨42247941134922748127370613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56330588179896997503160817 42247941134922748127370613)
          ·
            refine ⟨3960744481399007636940995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42247941134922748127370613 3960744481399007636940995)
            ·
              refine ⟨5941116722098511455411493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3960744481399007636940995 5941116722098511455411493)
              ·
                refine ⟨1113959385393470897889655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5941116722098511455411493 1113959385393470897889655)
                ·
                  refine ⟨1670939078090206346834483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1113959385393470897889655 1670939078090206346834483)
                  ·
                    refine ⟨2506408617135309520251725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1670939078090206346834483 2506408617135309520251725)
                    ·
                      refine ⟨939903231425741070094397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2506408617135309520251725 939903231425741070094397)
                      ·
                        rfl

theorem cell23_1830455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 4, 1, 1, 3].length) (baseStart_1830455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1830455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1830455 prefixEnd_1830455 := by exact prefixLift 1830455
  have htrace : WordTrace (prefixWord ++ tailWord_1830455) baseStart_1830455 baseEnd_1830455 := by
    simpa [prefixWord, tailWord_1830455, baseEnd_1830455] using wordTrace_append hprefix tailTrace_1830455
  have hstable : (prefixWord ++ tailWord_1830455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830455).length < 2 ^ (prefixWord ++ tailWord_1830455).sum := by decide
  have hdescent : baseEnd_1830455 < baseStart_1830455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830464 : List Nat := [2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 5]
def baseStart_1830464 : Nat := 118140960795 + 1830464 * 2 ^ 59
def prefixEnd_1830464 : Nat := 4983230072969 + 3 ^ 40 * 1830464 * 2
def baseEnd_1830464 : Nat := 939907852751631534881855

theorem tailTrace_1830464 : CollatzResearch.WordTrace tailWord_1830464 prefixEnd_1830464 939907852751631534881855 := by
  unfold tailWord_1830464
  simp only [CollatzResearch.WordTrace]
  refine ⟨33381253420274510603745223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44508337893699347471660297 33381253420274510603745223)
  ·
    refine ⟨50071880130411765905617835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33381253420274510603745223 50071880130411765905617835)
    ·
      refine ⟨75107820195617648858426753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50071880130411765905617835 75107820195617648858426753)
      ·
        refine ⟨56330865146713236643820065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75107820195617648858426753 56330865146713236643820065)
        ·
          refine ⟨42248148860034927482865049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56330865146713236643820065 42248148860034927482865049)
          ·
            refine ⟨31686111645026195612148787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42248148860034927482865049 31686111645026195612148787)
            ·
              refine ⟨47529167467539293418223181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31686111645026195612148787 47529167467539293418223181)
              ·
                refine ⟨17823437800327235031833693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47529167467539293418223181 17823437800327235031833693)
                ·
                  refine ⟨6683789175122713136937635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17823437800327235031833693 6683789175122713136937635)
                  ·
                    refine ⟨10025683762684069705406453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6683789175122713136937635 10025683762684069705406453)
                    ·
                      refine ⟨939907852751631534881855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10025683762684069705406453 939907852751631534881855)
                      ·
                        rfl

theorem cell23_1830464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 5].length) (baseStart_1830464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1830464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1830464 prefixEnd_1830464 := by exact prefixLift 1830464
  have htrace : WordTrace (prefixWord ++ tailWord_1830464) baseStart_1830464 baseEnd_1830464 := by
    simpa [prefixWord, tailWord_1830464, baseEnd_1830464] using wordTrace_append hprefix tailTrace_1830464
  have hstable : (prefixWord ++ tailWord_1830464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830464).length < 2 ^ (prefixWord ++ tailWord_1830464).sum := by decide
  have hdescent : baseEnd_1830464 < baseStart_1830464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830481 : List Nat := [1, 2, 2, 1, 3, 2, 1, 3, 3, 2, 3]
def baseStart_1830481 : Nat := 118140960795 + 1830481 * 2 ^ 59
def prefixEnd_1830481 : Nat := 4983230072969 + 3 ^ 40 * 1830481 * 2
def baseEnd_1830481 : Nat := 939916581922757968369277

theorem tailTrace_1830481 : CollatzResearch.WordTrace tailWord_1830481 prefixEnd_1830481 939916581922757968369277 := by
  unfold tailWord_1830481
  simp only [CollatzResearch.WordTrace]
  refine ⟨66763126881487433110859297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44508751254324955407239531 66763126881487433110859297)
  ·
    refine ⟨50072345161115574833144473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66763126881487433110859297 50072345161115574833144473)
    ·
      refine ⟨37554258870836681124858355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50072345161115574833144473 37554258870836681124858355)
      ·
        refine ⟨56331388306255021687287533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37554258870836681124858355 56331388306255021687287533)
        ·
          refine ⟨21124270614845633132732825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56331388306255021687287533 21124270614845633132732825)
          ·
            refine ⟨15843202961134224849549619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21124270614845633132732825 15843202961134224849549619)
            ·
              refine ⟨23764804441701337274324429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15843202961134224849549619 23764804441701337274324429)
              ·
                refine ⟨8911801665638001477871661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23764804441701337274324429 8911801665638001477871661)
                ·
                  refine ⟨3341925624614250554201873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8911801665638001477871661 3341925624614250554201873)
                  ·
                    refine ⟨2506444218460687915651405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3341925624614250554201873 2506444218460687915651405)
                    ·
                      refine ⟨939916581922757968369277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2506444218460687915651405 939916581922757968369277)
                      ·
                        rfl

theorem cell23_1830481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 3, 3, 2, 3].length) (baseStart_1830481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1830481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1830481 prefixEnd_1830481 := by exact prefixLift 1830481
  have htrace : WordTrace (prefixWord ++ tailWord_1830481) baseStart_1830481 baseEnd_1830481 := by
    simpa [prefixWord, tailWord_1830481, baseEnd_1830481] using wordTrace_append hprefix tailTrace_1830481
  have hstable : (prefixWord ++ tailWord_1830481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830481).length < 2 ^ (prefixWord ++ tailWord_1830481).sum := by decide
  have hdescent : baseEnd_1830481 < baseStart_1830481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830512 : List Nat := [2, 1, 1, 1, 6, 1, 2, 4, 1, 2, 2]
def baseStart_1830512 : Nat := 118140960795 + 1830512 * 2 ^ 59
def prefixEnd_1830512 : Nat := 4983230072969 + 3 ^ 40 * 1830512 * 2
def baseEnd_1830512 : Nat := 939932499823047347081635

theorem tailTrace_1830512 : CollatzResearch.WordTrace tailWord_1830512 prefixEnd_1830512 939932499823047347081635 := by
  unfold tailWord_1830512
  simp only [CollatzResearch.WordTrace]
  refine ⟨33382128772187562702618895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44509505029583416936825193 33382128772187562702618895)
  ·
    refine ⟨50073193158281344053928343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33382128772187562702618895 50073193158281344053928343)
    ·
      refine ⟨75109789737422016080892515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50073193158281344053928343 75109789737422016080892515)
      ·
        refine ⟨112664684606133024121338773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75109789737422016080892515 112664684606133024121338773)
        ·
          refine ⟨5281157090912485505687755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 112664684606133024121338773 5281157090912485505687755)
          ·
            refine ⟨7921735636368728258531633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5281157090912485505687755 7921735636368728258531633)
            ·
              refine ⟨5941301727276546193898725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7921735636368728258531633 5941301727276546193898725)
              ·
                refine ⟨1113994073864352411356011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5941301727276546193898725 1113994073864352411356011)
                ·
                  refine ⟨1670991110796528617034017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1113994073864352411356011 1670991110796528617034017)
                  ·
                    refine ⟨1253243333097396462775513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1670991110796528617034017 1253243333097396462775513)
                    ·
                      refine ⟨939932499823047347081635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1253243333097396462775513 939932499823047347081635)
                      ·
                        rfl

theorem cell23_1830512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 4, 1, 2, 2].length) (baseStart_1830512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1830512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1830512 prefixEnd_1830512 := by exact prefixLift 1830512
  have htrace : WordTrace (prefixWord ++ tailWord_1830512) baseStart_1830512 baseEnd_1830512 := by
    simpa [prefixWord, tailWord_1830512, baseEnd_1830512] using wordTrace_append hprefix tailTrace_1830512
  have hstable : (prefixWord ++ tailWord_1830512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830512).length < 2 ^ (prefixWord ++ tailWord_1830512).sum := by decide
  have hdescent : baseEnd_1830512 < baseStart_1830512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830544 : List Nat := [2, 1, 1, 1, 1, 1, 3, 4, 1, 8]
def baseStart_1830544 : Nat := 118140960795 + 1830544 * 2 ^ 59
def prefixEnd_1830544 : Nat := 4983230072969 + 3 ^ 40 * 1830544 * 2
def baseEnd_1830544 : Nat := 313316310401330407293829

theorem tailTrace_1830544 : CollatzResearch.WordTrace tailWord_1830544 prefixEnd_1830544 313316310401330407293829 := by
  unfold tailWord_1830544
  simp only [CollatzResearch.WordTrace]
  refine ⟨33382712340129597435201343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44510283120172796580268457 33382712340129597435201343)
  ·
    refine ⟨50074068510194396152802015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33382712340129597435201343 50074068510194396152802015)
    ·
      refine ⟨75111102765291594229203023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50074068510194396152802015 75111102765291594229203023)
      ·
        refine ⟨112666654147937391343804535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75111102765291594229203023 112666654147937391343804535)
        ·
          refine ⟨168999981221906087015706803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112666654147937391343804535 168999981221906087015706803)
          ·
            refine ⟨253499971832859130523560205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168999981221906087015706803 253499971832859130523560205)
            ·
              refine ⟨95062489437322173946335077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 253499971832859130523560205 95062489437322173946335077)
              ·
                refine ⟨17824216769497907614937827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95062489437322173946335077 17824216769497907614937827)
                ·
                  refine ⟨26736325154246861422406741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17824216769497907614937827 26736325154246861422406741)
                  ·
                    refine ⟨313316310401330407293829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 26736325154246861422406741 313316310401330407293829)
                    ·
                      rfl

theorem cell23_1830544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 1, 8].length) (baseStart_1830544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1830544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1830544 prefixEnd_1830544 := by exact prefixLift 1830544
  have htrace : WordTrace (prefixWord ++ tailWord_1830544) baseStart_1830544 baseEnd_1830544 := by
    simpa [prefixWord, tailWord_1830544, baseEnd_1830544] using wordTrace_append hprefix tailTrace_1830544
  have hstable : (prefixWord ++ tailWord_1830544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830544).length < 2 ^ (prefixWord ++ tailWord_1830544).sum := by decide
  have hdescent : baseEnd_1830544 < baseStart_1830544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830546 : List Nat := [3, 2, 3, 1, 3, 2, 1, 3, 1, 2, 2]
def baseStart_1830546 : Nat := 118140960795 + 1830546 * 2 ^ 59
def prefixEnd_1830546 : Nat := 4983230072969 + 3 ^ 40 * 1830546 * 2
def baseEnd_1830546 : Nat := 939949958165300214056479

theorem tailTrace_1830546 : CollatzResearch.WordTrace tailWord_1830546 prefixEnd_1830546 939949958165300214056479 := by
  unfold tailWord_1830546
  simp only [CollatzResearch.WordTrace]
  refine ⟨16691374406562987302993873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44510331750834632807983661 16691374406562987302993873)
  ·
    refine ⟨12518530804922240477245405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16691374406562987302993873 12518530804922240477245405)
    ·
      refine ⟨4694449051845840178967027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12518530804922240477245405 4694449051845840178967027)
      ·
        refine ⟨7041673577768760268450541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4694449051845840178967027 7041673577768760268450541)
        ·
          refine ⟨2640627591663285100668953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7041673577768760268450541 2640627591663285100668953)
          ·
            refine ⟨1980470693747463825501715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2640627591663285100668953 1980470693747463825501715)
            ·
              refine ⟨2970706040621195738252573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1980470693747463825501715 2970706040621195738252573)
              ·
                refine ⟨1114014765232948401844715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2970706040621195738252573 1114014765232948401844715)
                ·
                  refine ⟨1671022147849422602767073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1114014765232948401844715 1671022147849422602767073)
                  ·
                    refine ⟨1253266610887066952075305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1671022147849422602767073 1253266610887066952075305)
                    ·
                      refine ⟨939949958165300214056479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1253266610887066952075305 939949958165300214056479)
                      ·
                        rfl

theorem cell23_1830546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 3, 1, 2, 2].length) (baseStart_1830546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1830546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1830546 prefixEnd_1830546 := by exact prefixLift 1830546
  have htrace : WordTrace (prefixWord ++ tailWord_1830546) baseStart_1830546 baseEnd_1830546 := by
    simpa [prefixWord, tailWord_1830546, baseEnd_1830546] using wordTrace_append hprefix tailTrace_1830546
  have hstable : (prefixWord ++ tailWord_1830546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830546).length < 2 ^ (prefixWord ++ tailWord_1830546).sum := by decide
  have hdescent : baseEnd_1830546 < baseStart_1830546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830605 : List Nat := [1, 6, 2, 1, 1, 1, 2, 1, 2, 1, 5]
def baseStart_1830605 : Nat := 118140960795 + 1830605 * 2 ^ 59
def prefixEnd_1830605 : Nat := 4983230072969 + 3 ^ 40 * 1830605 * 2
def baseEnd_1830605 : Nat := 939980253523915483218707

theorem tailTrace_1830605 : CollatzResearch.WordTrace tailWord_1830605 prefixEnd_1830605 939980253523915483218707 := by
  unfold tailWord_1830605
  simp only [CollatzResearch.WordTrace]
  refine ⟨66767649533038202288373269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44511766355358801525582179 66767649533038202288373269)
  ·
    refine ⟨3129733571861165732267497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 66767649533038202288373269 3129733571861165732267497)
    ·
      refine ⟨2347300178895874299200623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3129733571861165732267497 2347300178895874299200623)
      ·
        refine ⟨3520950268343811448800935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2347300178895874299200623 3520950268343811448800935)
        ·
          refine ⟨5281425402515717173201403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3520950268343811448800935 5281425402515717173201403)
          ·
            refine ⟨7922138103773575759802105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5281425402515717173201403 7922138103773575759802105)
            ·
              refine ⟨5941603577830181819851579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7922138103773575759802105 5941603577830181819851579)
              ·
                refine ⟨8912405366745272729777369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5941603577830181819851579 8912405366745272729777369)
                ·
                  refine ⟨6684304025058954547333027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8912405366745272729777369 6684304025058954547333027)
                  ·
                    refine ⟨10026456037588431820999541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6684304025058954547333027 10026456037588431820999541)
                    ·
                      refine ⟨939980253523915483218707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10026456037588431820999541 939980253523915483218707)
                      ·
                        rfl

theorem cell23_1830605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_1830605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1830605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1830605 prefixEnd_1830605 := by exact prefixLift 1830605
  have htrace : WordTrace (prefixWord ++ tailWord_1830605) baseStart_1830605 baseEnd_1830605 := by
    simpa [prefixWord, tailWord_1830605, baseEnd_1830605] using wordTrace_append hprefix tailTrace_1830605
  have hstable : (prefixWord ++ tailWord_1830605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830605).length < 2 ^ (prefixWord ++ tailWord_1830605).sum := by decide
  have hdescent : baseEnd_1830605 < baseStart_1830605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830625 : List Nat := [1, 2, 3, 1, 5, 1, 1, 4, 5]
def baseStart_1830625 : Nat := 118140960795 + 1830625 * 2 ^ 59
def prefixEnd_1830625 : Nat := 4983230072969 + 3 ^ 40 * 1830625 * 2
def baseEnd_1830625 : Nat := 104443391459667267218735

theorem tailTrace_1830625 : CollatzResearch.WordTrace tailWord_1830625 prefixEnd_1830625 104443391459667267218735 := by
  unfold tailWord_1830625
  simp only [CollatzResearch.WordTrace]
  refine ⟨66768378992965745704101329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44512252661977163802734219 66768378992965745704101329)
  ·
    refine ⟨50076284244724309278075997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66768378992965745704101329 50076284244724309278075997)
    ·
      refine ⟨18778606591771615979278499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50076284244724309278075997 18778606591771615979278499)
      ·
        refine ⟨28167909887657423968917749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18778606591771615979278499 28167909887657423968917749)
        ·
          refine ⟨2640741551967883497086039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28167909887657423968917749 2640741551967883497086039)
          ·
            refine ⟨3961112327951825245629059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2640741551967883497086039 3961112327951825245629059)
            ·
              refine ⟨5941668491927737868443589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3961112327951825245629059 5941668491927737868443589)
              ·
                refine ⟨1114062842236450850333173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5941668491927737868443589 1114062842236450850333173)
                ·
                  refine ⟨104443391459667267218735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1114062842236450850333173 104443391459667267218735)
                  ·
                    rfl

theorem cell23_1830625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 4, 5].length) (baseStart_1830625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1830625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1830625 prefixEnd_1830625 := by exact prefixLift 1830625
  have htrace : WordTrace (prefixWord ++ tailWord_1830625) baseStart_1830625 baseEnd_1830625 := by
    simpa [prefixWord, tailWord_1830625, baseEnd_1830625] using wordTrace_append hprefix tailTrace_1830625
  have hstable : (prefixWord ++ tailWord_1830625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830625).length < 2 ^ (prefixWord ++ tailWord_1830625).sum := by decide
  have hdescent : baseEnd_1830625 < baseStart_1830625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830628 : List Nat := [2, 3, 1, 1, 1, 3, 1, 1, 1, 7, 2]
def baseStart_1830628 : Nat := 118140960795 + 1830628 * 2 ^ 59
def prefixEnd_1830628 : Nat := 4983230072969 + 3 ^ 40 * 1830628 * 2
def baseEnd_1830628 : Nat := 939992063578968893231101

theorem tailTrace_1830628 : CollatzResearch.WordTrace tailWord_1830628 prefixEnd_1830628 939992063578968893231101 := by
  unfold tailWord_1830628
  simp only [CollatzResearch.WordTrace]
  refine ⟨33384244205977438608230269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44512325607969918144307025 33384244205977438608230269)
  ·
    refine ⟨12519091577241539478086351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33384244205977438608230269 12519091577241539478086351)
    ·
      refine ⟨18778637365862309217129527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12519091577241539478086351 18778637365862309217129527)
      ·
        refine ⟨28167956048793463825694291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18778637365862309217129527 28167956048793463825694291)
        ·
          refine ⟨42251934073190195738541437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28167956048793463825694291 42251934073190195738541437)
          ·
            refine ⟨15844475277446323401953039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42251934073190195738541437 15844475277446323401953039)
            ·
              refine ⟨23766712916169485102929559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15844475277446323401953039 23766712916169485102929559)
              ·
                refine ⟨35650069374254227654394339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23766712916169485102929559 35650069374254227654394339)
                ·
                  refine ⟨53475104061381341481591509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35650069374254227654394339 53475104061381341481591509)
                  ·
                    refine ⟨1253322751438625190974801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53475104061381341481591509 1253322751438625190974801)
                    ·
                      refine ⟨939992063578968893231101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1253322751438625190974801 939992063578968893231101)
                      ·
                        rfl

theorem cell23_1830628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 1, 7, 2].length) (baseStart_1830628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1830628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1830628 prefixEnd_1830628 := by exact prefixLift 1830628
  have htrace : WordTrace (prefixWord ++ tailWord_1830628) baseStart_1830628 baseEnd_1830628 := by
    simpa [prefixWord, tailWord_1830628, baseEnd_1830628] using wordTrace_append hprefix tailTrace_1830628
  have hstable : (prefixWord ++ tailWord_1830628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830628).length < 2 ^ (prefixWord ++ tailWord_1830628).sum := by decide
  have hdescent : baseEnd_1830628 < baseStart_1830628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830719 : List Nat := [1, 1, 2, 2, 6, 2, 1, 3, 1, 4]
def baseStart_1830719 : Nat := 118140960795 + 1830719 * 2 ^ 59
def prefixEnd_1830719 : Nat := 4983230072969 + 3 ^ 40 * 1830719 * 2
def baseEnd_1830719 : Nat := 313346263439509345731061

theorem tailTrace_1830719 : CollatzResearch.WordTrace tailWord_1830719 prefixEnd_1830719 313346263439509345731061 := by
  unfold tailWord_1830719
  simp only [CollatzResearch.WordTrace]
  refine ⟨66771807454625199758023211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44514538303083466505348807 66771807454625199758023211)
  ·
    refine ⟨100157711181937799637034817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66771807454625199758023211 100157711181937799637034817)
    ·
      refine ⟨75118283386453349727776113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100157711181937799637034817 75118283386453349727776113)
      ·
        refine ⟨56338712539840012295832085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75118283386453349727776113 56338712539840012295832085)
        ·
          refine ⟨2640877150305000576367129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 56338712539840012295832085 2640877150305000576367129)
          ·
            refine ⟨1980657862728750432275347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2640877150305000576367129 1980657862728750432275347)
            ·
              refine ⟨2970986794093125648413021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1980657862728750432275347 2970986794093125648413021)
              ·
                refine ⟨1114120047784922118154883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2970986794093125648413021 1114120047784922118154883)
                ·
                  refine ⟨1671180071677383177232325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1114120047784922118154883 1671180071677383177232325)
                  ·
                    refine ⟨313346263439509345731061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1671180071677383177232325 313346263439509345731061)
                    ·
                      rfl

theorem cell23_1830719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 3, 1, 4].length) (baseStart_1830719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1830719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1830719 prefixEnd_1830719 := by exact prefixLift 1830719
  have htrace : WordTrace (prefixWord ++ tailWord_1830719) baseStart_1830719 baseEnd_1830719 := by
    simpa [prefixWord, tailWord_1830719, baseEnd_1830719] using wordTrace_append hprefix tailTrace_1830719
  have hstable : (prefixWord ++ tailWord_1830719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830719).length < 2 ^ (prefixWord ++ tailWord_1830719).sum := by decide
  have hdescent : baseEnd_1830719 < baseStart_1830719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830762 : List Nat := [3, 1, 3, 4, 1, 1, 1, 1, 3, 5]
def baseStart_1830762 : Nat := 118140960795 + 1830762 * 2 ^ 59
def prefixEnd_1830762 : Nat := 4983230072969 + 3 ^ 40 * 1830762 * 2
def baseEnd_1830762 : Nat := 313353623328890456318495

theorem tailTrace_1830762 : CollatzResearch.WordTrace tailWord_1830762 prefixEnd_1830762 313353623328890456318495 := by
  unfold tailWord_1830762
  simp only [CollatzResearch.WordTrace]
  refine ⟨16693343948367354525459635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44515583862312945401225693 16693343948367354525459635)
  ·
    refine ⟨25040015922551031788189453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16693343948367354525459635 25040015922551031788189453)
    ·
      refine ⟨9390005970956636920571045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25040015922551031788189453 9390005970956636920571045)
      ·
        refine ⟨1760626119554369422607071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9390005970956636920571045 1760626119554369422607071)
        ·
          refine ⟨2640939179331554133910607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1760626119554369422607071 2640939179331554133910607)
          ·
            refine ⟨3961408768997331200865911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2640939179331554133910607 3961408768997331200865911)
            ·
              refine ⟨5942113153495996801298867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3961408768997331200865911 5942113153495996801298867)
              ·
                refine ⟨8913169730243995201948301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5942113153495996801298867 8913169730243995201948301)
                ·
                  refine ⟨3342438648841498200730613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8913169730243995201948301 3342438648841498200730613)
                  ·
                    refine ⟨313353623328890456318495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3342438648841498200730613 313353623328890456318495)
                    ·
                      rfl

theorem cell23_1830762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 1, 3, 5].length) (baseStart_1830762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1830762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1830762 prefixEnd_1830762 := by exact prefixLift 1830762
  have htrace : WordTrace (prefixWord ++ tailWord_1830762) baseStart_1830762 baseEnd_1830762 := by
    simpa [prefixWord, tailWord_1830762, baseEnd_1830762] using wordTrace_append hprefix tailTrace_1830762
  have hstable : (prefixWord ++ tailWord_1830762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830762).length < 2 ^ (prefixWord ++ tailWord_1830762).sum := by decide
  have hdescent : baseEnd_1830762 < baseStart_1830762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830765 : List Nat := [1, 5, 1, 1, 1, 1, 2, 1, 2, 6, 2]
def baseStart_1830765 : Nat := 118140960795 + 1830765 * 2 ^ 59
def prefixEnd_1830765 : Nat := 4983230072969 + 3 ^ 40 * 1830765 * 2
def baseEnd_1830765 : Nat := 940062410428634857217971

theorem tailTrace_1830765 : CollatzResearch.WordTrace tailWord_1830765 prefixEnd_1830765 940062410428634857217971 := by
  unfold tailWord_1830765
  simp only [CollatzResearch.WordTrace]
  refine ⟨66773485212458549614197749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44515656808305699742798499 66773485212458549614197749)
  ·
    refine ⟨6260014238667989026331039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66773485212458549614197749 6260014238667989026331039)
    ·
      refine ⟨9390021358001983539496559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6260014238667989026331039 9390021358001983539496559)
      ·
        refine ⟨14085032037002975309244839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9390021358001983539496559 14085032037002975309244839)
        ·
          refine ⟨21127548055504462963867259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14085032037002975309244839 21127548055504462963867259)
          ·
            refine ⟨31691322083256694445800889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21127548055504462963867259 31691322083256694445800889)
            ·
              refine ⟨23768491562442520834350667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31691322083256694445800889 23768491562442520834350667)
              ·
                refine ⟨35652737343663781251526001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23768491562442520834350667 35652737343663781251526001)
                ·
                  refine ⟨26739553007747835938644501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35652737343663781251526001 26739553007747835938644501)
                  ·
                    refine ⟨1253416547238179809623961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26739553007747835938644501 1253416547238179809623961)
                    ·
                      refine ⟨940062410428634857217971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1253416547238179809623961 940062410428634857217971)
                      ·
                        rfl

theorem cell23_1830765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 6, 2].length) (baseStart_1830765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1830765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1830765 prefixEnd_1830765 := by exact prefixLift 1830765
  have htrace : WordTrace (prefixWord ++ tailWord_1830765) baseStart_1830765 baseEnd_1830765 := by
    simpa [prefixWord, tailWord_1830765, baseEnd_1830765] using wordTrace_append hprefix tailTrace_1830765
  have hstable : (prefixWord ++ tailWord_1830765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830765).length < 2 ^ (prefixWord ++ tailWord_1830765).sum := by decide
  have hdescent : baseEnd_1830765 < baseStart_1830765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830778 : List Nat := [3, 1, 1, 1, 1, 1, 5, 1, 3, 2, 4]
def baseStart_1830778 : Nat := 118140960795 + 1830778 * 2 ^ 59
def prefixEnd_1830778 : Nat := 4983230072969 + 3 ^ 40 * 1830778 * 2
def baseEnd_1830778 : Nat := 940069085677143306355411

theorem tailTrace_1830778 : CollatzResearch.WordTrace tailWord_1830778 prefixEnd_1830778 940069085677143306355411 := by
  unfold tailWord_1830778
  simp only [CollatzResearch.WordTrace]
  refine ⟨16693489840352863208605247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44515972907607635222947325 16693489840352863208605247)
  ·
    refine ⟨25040234760529294812907871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16693489840352863208605247 25040234760529294812907871)
    ·
      refine ⟨37560352140793942219361807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25040234760529294812907871 37560352140793942219361807)
      ·
        refine ⟨56340528211190913329042711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37560352140793942219361807 56340528211190913329042711)
        ·
          refine ⟨84510792316786369993564067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56340528211190913329042711 84510792316786369993564067)
          ·
            refine ⟨126766188475179554990346101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84510792316786369993564067 126766188475179554990346101)
            ·
              refine ⟨11884330169548083280344947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 126766188475179554990346101 11884330169548083280344947)
              ·
                refine ⟨17826495254322124920517421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11884330169548083280344947 17826495254322124920517421)
                ·
                  refine ⟨6684935720370796845194033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17826495254322124920517421 6684935720370796845194033)
                  ·
                    refine ⟨5013701790278097633895525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6684935720370796845194033 5013701790278097633895525)
                    ·
                      refine ⟨940069085677143306355411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5013701790278097633895525 940069085677143306355411)
                      ·
                        rfl

theorem cell23_1830778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 3, 2, 4].length) (baseStart_1830778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1830778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1830778 prefixEnd_1830778 := by exact prefixLift 1830778
  have htrace : WordTrace (prefixWord ++ tailWord_1830778) baseStart_1830778 baseEnd_1830778 := by
    simpa [prefixWord, tailWord_1830778, baseEnd_1830778] using wordTrace_append hprefix tailTrace_1830778
  have hstable : (prefixWord ++ tailWord_1830778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830778).length < 2 ^ (prefixWord ++ tailWord_1830778).sum := by decide
  have hdescent : baseEnd_1830778 < baseStart_1830778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830802 : List Nat := [3, 2, 3, 2, 1, 1, 1, 2, 3, 2, 3]
def baseStart_1830802 : Nat := 118140960795 + 1830802 * 2 ^ 59
def prefixEnd_1830802 : Nat := 4983230072969 + 3 ^ 40 * 1830802 * 2
def baseEnd_1830802 : Nat := 940081409212851212455301

theorem tailTrace_1830802 : CollatzResearch.WordTrace tailWord_1830802 prefixEnd_1830802 940081409212851212455301 := by
  unfold tailWord_1830802
  simp only [CollatzResearch.WordTrace]
  refine ⟨16693708678331126233323665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44516556475549669955529773 16693708678331126233323665)
  ·
    refine ⟨12520281508748344674992749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16693708678331126233323665 12520281508748344674992749)
    ·
      refine ⟨4695105565780629253122281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12520281508748344674992749 4695105565780629253122281)
      ·
        refine ⟨3521329174335471939841711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4695105565780629253122281 3521329174335471939841711)
        ·
          refine ⟨5281993761503207909762567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3521329174335471939841711 5281993761503207909762567)
          ·
            refine ⟨7922990642254811864643851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5281993761503207909762567 7922990642254811864643851)
            ·
              refine ⟨11884485963382217796965777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7922990642254811864643851 11884485963382217796965777)
              ·
                refine ⟨8913364472536663347724333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11884485963382217796965777 8913364472536663347724333)
                ·
                  refine ⟨3342511677201248755396625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8913364472536663347724333 3342511677201248755396625)
                  ·
                    refine ⟨2506883757900936566547469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3342511677201248755396625 2506883757900936566547469)
                    ·
                      refine ⟨940081409212851212455301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2506883757900936566547469 940081409212851212455301)
                      ·
                        rfl

theorem cell23_1830802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_1830802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1830802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1830802 prefixEnd_1830802 := by exact prefixLift 1830802
  have htrace : WordTrace (prefixWord ++ tailWord_1830802) baseStart_1830802 baseEnd_1830802 := by
    simpa [prefixWord, tailWord_1830802, baseEnd_1830802] using wordTrace_append hprefix tailTrace_1830802
  have hstable : (prefixWord ++ tailWord_1830802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830802).length < 2 ^ (prefixWord ++ tailWord_1830802).sum := by decide
  have hdescent : baseEnd_1830802 < baseStart_1830802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830812 : List Nat := [2, 2, 3, 3, 1, 2, 2, 1, 1, 2, 4]
def baseStart_1830812 : Nat := 118140960795 + 1830812 * 2 ^ 59
def prefixEnd_1830812 : Nat := 4983230072969 + 3 ^ 40 * 1830812 * 2
def baseEnd_1830812 : Nat := 940086544019396173330255

theorem tailTrace_1830812 : CollatzResearch.WordTrace tailWord_1830812 prefixEnd_1830812 940086544019396173330255 := by
  unfold tailWord_1830812
  simp only [CollatzResearch.WordTrace]
  refine ⟨33387599721644138320579345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44516799628858851094105793 33387599721644138320579345)
  ·
    refine ⟨25040699791233103740434509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33387599721644138320579345 25040699791233103740434509)
    ·
      refine ⟨9390262421712413902662941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25040699791233103740434509 9390262421712413902662941)
      ·
        refine ⟨3521348408142155213498603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9390262421712413902662941 3521348408142155213498603)
        ·
          refine ⟨5282022612213232820247905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3521348408142155213498603 5282022612213232820247905)
          ·
            refine ⟨3961516959159924615185929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5282022612213232820247905 3961516959159924615185929)
            ·
              refine ⟨2971137719369943461389447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3961516959159924615185929 2971137719369943461389447)
              ·
                refine ⟨4456706579054915192084171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2971137719369943461389447 4456706579054915192084171)
                ·
                  refine ⟨6685059868582372788126257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4456706579054915192084171 6685059868582372788126257)
                  ·
                    refine ⟨5013794901436779591094693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6685059868582372788126257 5013794901436779591094693)
                    ·
                      refine ⟨940086544019396173330255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5013794901436779591094693 940086544019396173330255)
                      ·
                        rfl

theorem cell23_1830812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_1830812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1830812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1830812 prefixEnd_1830812 := by exact prefixLift 1830812
  have htrace : WordTrace (prefixWord ++ tailWord_1830812) baseStart_1830812 baseEnd_1830812 := by
    simpa [prefixWord, tailWord_1830812, baseEnd_1830812] using wordTrace_append hprefix tailTrace_1830812
  have hstable : (prefixWord ++ tailWord_1830812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830812).length < 2 ^ (prefixWord ++ tailWord_1830812).sum := by decide
  have hdescent : baseEnd_1830812 < baseStart_1830812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830830 : List Nat := [4, 1, 5, 1, 2, 1, 2, 1, 1, 5]
def baseStart_1830830 : Nat := 118140960795 + 1830830 * 2 ^ 59
def prefixEnd_1830830 : Nat := 4983230072969 + 3 ^ 40 * 1830830 * 2
def baseEnd_1830830 : Nat := 313365262223725700968391

theorem tailTrace_1830830 : CollatzResearch.WordTrace tailWord_1830830 prefixEnd_1830830 313365262223725700968391 := by
  unfold tailWord_1830830
  simp only [CollatzResearch.WordTrace]
  refine ⟨8346981994652883214414243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44517237304815377143542629 8346981994652883214414243)
  ·
    refine ⟨12520472991979324821621365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8346981994652883214414243 12520472991979324821621365)
    ·
      refine ⟨1173794342998061702027003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12520472991979324821621365 1173794342998061702027003)
      ·
        refine ⟨1760691514497092553040505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1173794342998061702027003 1760691514497092553040505)
        ·
          refine ⟨1320518635872819414780379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1760691514497092553040505 1320518635872819414780379)
          ·
            refine ⟨1980777953809229122170569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1320518635872819414780379 1980777953809229122170569)
            ·
              refine ⟨1485583465356921841627927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1980777953809229122170569 1485583465356921841627927)
              ·
                refine ⟨2228375198035382762441891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1485583465356921841627927 2228375198035382762441891)
                ·
                  refine ⟨3342562797053074143662837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2228375198035382762441891 3342562797053074143662837)
                  ·
                    refine ⟨313365262223725700968391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3342562797053074143662837 313365262223725700968391)
                    ·
                      rfl

theorem cell23_1830830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_1830830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1830830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1830830 prefixEnd_1830830 := by exact prefixLift 1830830
  have htrace : WordTrace (prefixWord ++ tailWord_1830830) baseStart_1830830 baseEnd_1830830 := by
    simpa [prefixWord, tailWord_1830830, baseEnd_1830830] using wordTrace_append hprefix tailTrace_1830830
  have hstable : (prefixWord ++ tailWord_1830830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830830).length < 2 ^ (prefixWord ++ tailWord_1830830).sum := by decide
  have hdescent : baseEnd_1830830 < baseStart_1830830 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830836 : List Nat := [2, 5, 2, 1, 2, 1, 1, 3, 1, 2, 3]
def baseStart_1830836 : Nat := 118140960795 + 1830836 * 2 ^ 59
def prefixEnd_1830836 : Nat := 4983230072969 + 3 ^ 40 * 1830836 * 2
def baseEnd_1830836 : Nat := 940098867555104079430145

theorem tailTrace_1830836 : CollatzResearch.WordTrace tailWord_1830836 prefixEnd_1830836 940098867555104079430145 := by
  unfold tailWord_1830836
  simp only [CollatzResearch.WordTrace]
  refine ⟨33388037397600664370016181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44517383196800885826688241 33388037397600664370016181)
  ·
    refine ⟨3130128506025062284689017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33388037397600664370016181 3130128506025062284689017)
    ·
      refine ⟨2347596379518796713516763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3130128506025062284689017 2347596379518796713516763)
      ·
        refine ⟨3521394569278195070275145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2347596379518796713516763 3521394569278195070275145)
        ·
          refine ⟨2641045926958646302706359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3521394569278195070275145 2641045926958646302706359)
          ·
            refine ⟨3961568890437969454059539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2641045926958646302706359 3961568890437969454059539)
            ·
              refine ⟨5942353335656954181089309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3961568890437969454059539 5942353335656954181089309)
              ·
                refine ⟨2228382500871357817908491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5942353335656954181089309 2228382500871357817908491)
                ·
                  refine ⟨3342573751307036726862737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2228382500871357817908491 3342573751307036726862737)
                  ·
                    refine ⟨2506930313480277545147053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3342573751307036726862737 2506930313480277545147053)
                    ·
                      refine ⟨940098867555104079430145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2506930313480277545147053 940098867555104079430145)
                      ·
                        rfl

theorem cell23_1830836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_1830836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1830836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1830836 prefixEnd_1830836 := by exact prefixLift 1830836
  have htrace : WordTrace (prefixWord ++ tailWord_1830836) baseStart_1830836 baseEnd_1830836 := by
    simpa [prefixWord, tailWord_1830836, baseEnd_1830836] using wordTrace_append hprefix tailTrace_1830836
  have hstable : (prefixWord ++ tailWord_1830836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830836).length < 2 ^ (prefixWord ++ tailWord_1830836).sum := by decide
  have hdescent : baseEnd_1830836 < baseStart_1830836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830848 : List Nat := [2, 1, 1, 2, 3, 2, 1, 1, 4, 6]
def baseStart_1830848 : Nat := 118140960795 + 1830848 * 2 ^ 59
def prefixEnd_1830848 : Nat := 4983230072969 + 3 ^ 40 * 1830848 * 2
def baseEnd_1830848 : Nat := 313368343107652677493363

theorem tailTrace_1830848 : CollatzResearch.WordTrace tailWord_1830848 prefixEnd_1830848 313368343107652677493363 := by
  unfold tailWord_1830848
  simp only [CollatzResearch.WordTrace]
  refine ⟨33388256235578927394734599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44517674980771903192979465 33388256235578927394734599)
  ·
    refine ⟨50082384353368391092101899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33388256235578927394734599 50082384353368391092101899)
    ·
      refine ⟨75123576530052586638152849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50082384353368391092101899 75123576530052586638152849)
      ·
        refine ⟨56342682397539439978614637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75123576530052586638152849 56342682397539439978614637)
        ·
          refine ⟨21128505899077289991980489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56342682397539439978614637 21128505899077289991980489)
          ·
            refine ⟨15846379424307967493985367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21128505899077289991980489 15846379424307967493985367)
            ·
              refine ⟨23769569136461951240978051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15846379424307967493985367 23769569136461951240978051)
              ·
                refine ⟨35654353704692926861467077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23769569136461951240978051 35654353704692926861467077)
                ·
                  refine ⟨6685191319629923786525077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35654353704692926861467077 6685191319629923786525077)
                  ·
                    refine ⟨313368343107652677493363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6685191319629923786525077 313368343107652677493363)
                    ·
                      rfl

theorem cell23_1830848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 4, 6].length) (baseStart_1830848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1830848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1830848 prefixEnd_1830848 := by exact prefixLift 1830848
  have htrace : WordTrace (prefixWord ++ tailWord_1830848) baseStart_1830848 baseEnd_1830848 := by
    simpa [prefixWord, tailWord_1830848, baseEnd_1830848] using wordTrace_append hprefix tailTrace_1830848
  have hstable : (prefixWord ++ tailWord_1830848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830848).length < 2 ^ (prefixWord ++ tailWord_1830848).sum := by decide
  have hdescent : baseEnd_1830848 < baseStart_1830848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830866 : List Nat := [3, 2, 2, 3, 3, 1, 1, 1, 1, 3, 3]
def baseStart_1830866 : Nat := 118140960795 + 1830866 * 2 ^ 59
def prefixEnd_1830866 : Nat := 4983230072969 + 3 ^ 40 * 1830866 * 2
def baseEnd_1830866 : Nat := 940114271974738962055007

theorem tailTrace_1830866 : CollatzResearch.WordTrace tailWord_1830866 prefixEnd_1830866 940114271974738962055007 := by
  unfold tailWord_1830866
  simp only [CollatzResearch.WordTrace]
  refine ⟨16694292246273160965906113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44518112656728429242416301 16694292246273160965906113)
  ·
    refine ⟨12520719184704870724429585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16694292246273160965906113 12520719184704870724429585)
    ·
      refine ⟨9390539388528653043322189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12520719184704870724429585 9390539388528653043322189)
      ·
        refine ⟨3521452270698244891245821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9390539388528653043322189 3521452270698244891245821)
        ·
          refine ⟨1320544601511841834217183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3521452270698244891245821 1320544601511841834217183)
          ·
            refine ⟨1980816902267762751325775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1320544601511841834217183 1980816902267762751325775)
            ·
              refine ⟨2971225353401644126988663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1980816902267762751325775 2971225353401644126988663)
              ·
                refine ⟨4456838030102466190482995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2971225353401644126988663 4456838030102466190482995)
                ·
                  refine ⟨6685257045153699285724493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4456838030102466190482995 6685257045153699285724493)
                  ·
                    refine ⟨2506971391932637232146685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6685257045153699285724493 2506971391932637232146685)
                    ·
                      refine ⟨940114271974738962055007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2506971391932637232146685 940114271974738962055007)
                      ·
                        rfl

theorem cell23_1830866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_1830866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1830866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1830866 prefixEnd_1830866 := by exact prefixLift 1830866
  have htrace : WordTrace (prefixWord ++ tailWord_1830866) baseStart_1830866 baseEnd_1830866 := by
    simpa [prefixWord, tailWord_1830866, baseEnd_1830866] using wordTrace_append hprefix tailTrace_1830866
  have hstable : (prefixWord ++ tailWord_1830866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830866).length < 2 ^ (prefixWord ++ tailWord_1830866).sum := by decide
  have hdescent : baseEnd_1830866 < baseStart_1830866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830955 : List Nat := [1, 1, 1, 1, 2, 1, 4, 1, 7, 4]
def baseStart_1830955 : Nat := 118140960795 + 1830955 * 2 ^ 59
def prefixEnd_1830955 : Nat := 4983230072969 + 3 ^ 40 * 1830955 * 2
def baseEnd_1830955 : Nat := 313386657250996371280699

theorem tailTrace_1830955 : CollatzResearch.WordTrace tailWord_1830955 prefixEnd_1830955 313386657250996371280699 := by
  unfold tailWord_1830955
  simp only [CollatzResearch.WordTrace]
  refine ⟨66780415081770212063614319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44520276721180141375742879 66780415081770212063614319)
  ·
    refine ⟨100170622622655318095421479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66780415081770212063614319 100170622622655318095421479)
    ·
      refine ⟨150255933933982977143132219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100170622622655318095421479 150255933933982977143132219)
      ·
        refine ⟨225383900900974465714698329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150255933933982977143132219 225383900900974465714698329)
        ·
          refine ⟨169037925675730849286023747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225383900900974465714698329 169037925675730849286023747)
          ·
            refine ⟨253556888513596273929035621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169037925675730849286023747 253556888513596273929035621)
            ·
              refine ⟨47541916596299301361694179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 253556888513596273929035621 47541916596299301361694179)
              ·
                refine ⟨71312874894448952042541269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47541916596299301361694179 71312874894448952042541269)
                ·
                  refine ⟨1671395505338647313497061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 71312874894448952042541269 1671395505338647313497061)
                  ·
                    refine ⟨313386657250996371280699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1671395505338647313497061 313386657250996371280699)
                    ·
                      rfl

theorem cell23_1830955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 7, 4].length) (baseStart_1830955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1830955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1830955 prefixEnd_1830955 := by exact prefixLift 1830955
  have htrace : WordTrace (prefixWord ++ tailWord_1830955) baseStart_1830955 baseEnd_1830955 := by
    simpa [prefixWord, tailWord_1830955, baseEnd_1830955] using wordTrace_append hprefix tailTrace_1830955
  have hstable : (prefixWord ++ tailWord_1830955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830955).length < 2 ^ (prefixWord ++ tailWord_1830955).sum := by decide
  have hdescent : baseEnd_1830955 < baseStart_1830955 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830962 : List Nat := [3, 2, 1, 1, 2, 3, 2, 2, 2, 1, 4]
def baseStart_1830962 : Nat := 118140960795 + 1830962 * 2 ^ 59
def prefixEnd_1830962 : Nat := 4983230072969 + 3 ^ 40 * 1830962 * 2
def baseEnd_1830962 : Nat := 940163566117570586454565

theorem tailTrace_1830962 : CollatzResearch.WordTrace tailWord_1830962 prefixEnd_1830962 940163566117570586454565 := by
  unfold tailWord_1830962
  simp only [CollatzResearch.WordTrace]
  refine ⟨16695167598186213064779785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44520446928496568172746093 16695167598186213064779785)
  ·
    refine ⟨12521375698639659798584839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16695167598186213064779785 12521375698639659798584839)
    ·
      refine ⟨18782063547959489697877259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12521375698639659798584839 18782063547959489697877259)
      ·
        refine ⟨28173095321939234546815889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18782063547959489697877259 28173095321939234546815889)
        ·
          refine ⟨21129821491454425910111917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28173095321939234546815889 21129821491454425910111917)
          ·
            refine ⟨7923683059295409716291969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21129821491454425910111917 7923683059295409716291969)
            ·
              refine ⟨5942762294471557287218977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7923683059295409716291969 5942762294471557287218977)
              ·
                refine ⟨4457071720853667965414233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5942762294471557287218977 4457071720853667965414233)
                ·
                  refine ⟨3342803790640250974060675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4457071720853667965414233 3342803790640250974060675)
                  ·
                    refine ⟨5014205685960376461091013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3342803790640250974060675 5014205685960376461091013)
                    ·
                      refine ⟨940163566117570586454565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5014205685960376461091013 940163566117570586454565)
                      ·
                        rfl

theorem cell23_1830962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 2, 2, 1, 4].length) (baseStart_1830962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1830962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1830962 prefixEnd_1830962 := by exact prefixLift 1830962
  have htrace : WordTrace (prefixWord ++ tailWord_1830962) baseStart_1830962 baseEnd_1830962 := by
    simpa [prefixWord, tailWord_1830962, baseEnd_1830962] using wordTrace_append hprefix tailTrace_1830962
  have hstable : (prefixWord ++ tailWord_1830962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830962).length < 2 ^ (prefixWord ++ tailWord_1830962).sum := by decide
  have hdescent : baseEnd_1830962 < baseStart_1830962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830972 : List Nat := [2, 2, 2, 2, 2, 1, 2, 3, 3, 4]
def baseStart_1830972 : Nat := 118140960795 + 1830972 * 2 ^ 59
def prefixEnd_1830972 : Nat := 4983230072969 + 3 ^ 40 * 1830972 * 2
def baseEnd_1830972 : Nat := 313389566974705182443173

theorem tailTrace_1830972 : CollatzResearch.WordTrace tailWord_1830972 prefixEnd_1830972 313389566974705182443173 := by
  unfold tailWord_1830972
  simp only [CollatzResearch.WordTrace]
  refine ⟨33390517561354311983491585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44520690081805749311322113 33390517561354311983491585)
  ·
    refine ⟨25042888171015733987618689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33390517561354311983491585 25042888171015733987618689)
    ·
      refine ⟨18782166128261800490714017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25042888171015733987618689 18782166128261800490714017)
      ·
        refine ⟨14086624596196350368035513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18782166128261800490714017 14086624596196350368035513)
        ·
          refine ⟨10564968447147262776026635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14086624596196350368035513 10564968447147262776026635)
          ·
            refine ⟨15847452670720894164039953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10564968447147262776026635 15847452670720894164039953)
            ·
              refine ⟨11885589503040670623029965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15847452670720894164039953 11885589503040670623029965)
              ·
                refine ⟨4457096063640251483636237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11885589503040670623029965 4457096063640251483636237)
                ·
                  refine ⟨1671411023865094306363589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4457096063640251483636237 1671411023865094306363589)
                  ·
                    refine ⟨313389566974705182443173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1671411023865094306363589 313389566974705182443173)
                    ·
                      rfl

theorem cell23_1830972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 3, 3, 4].length) (baseStart_1830972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1830972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1830972 prefixEnd_1830972 := by exact prefixLift 1830972
  have htrace : WordTrace (prefixWord ++ tailWord_1830972) baseStart_1830972 baseEnd_1830972 := by
    simpa [prefixWord, tailWord_1830972, baseEnd_1830972] using wordTrace_append hprefix tailTrace_1830972
  have hstable : (prefixWord ++ tailWord_1830972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830972).length < 2 ^ (prefixWord ++ tailWord_1830972).sum := by decide
  have hdescent : baseEnd_1830972 < baseStart_1830972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830985 : List Nat := [1, 2, 1, 1, 2, 2, 3, 5, 6]
def baseStart_1830985 : Nat := 118140960795 + 1830985 * 2 ^ 59
def prefixEnd_1830985 : Nat := 4983230072969 + 3 ^ 40 * 1830985 * 2
def baseEnd_1830985 : Nat := 104463930685847110718551

theorem tailTrace_1830985 : CollatzResearch.WordTrace tailWord_1830985 prefixEnd_1830985 104463930685847110718551 := by
  unfold tailWord_1830985
  simp only [CollatzResearch.WordTrace]
  refine ⟨66781509271661527187206409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44521006181107684791470939 66781509271661527187206409)
  ·
    refine ⟨50086131953746145390404807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66781509271661527187206409 50086131953746145390404807)
    ·
      refine ⟨75129197930619218085607211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50086131953746145390404807 75129197930619218085607211)
      ·
        refine ⟨112693796895928827128410817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75129197930619218085607211 112693796895928827128410817)
        ·
          refine ⟨84520347671946620346308113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112693796895928827128410817 84520347671946620346308113)
          ·
            refine ⟨63390260753959965259731085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84520347671946620346308113 63390260753959965259731085)
            ·
              refine ⟨23771347782734986972399157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63390260753959965259731085 23771347782734986972399157)
              ·
                refine ⟨2228563854631405028662421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23771347782734986972399157 2228563854631405028662421)
                ·
                  refine ⟨104463930685847110718551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2228563854631405028662421 104463930685847110718551)
                  ·
                    rfl

theorem cell23_1830985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 5, 6].length) (baseStart_1830985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1830985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1830985 prefixEnd_1830985 := by exact prefixLift 1830985
  have htrace : WordTrace (prefixWord ++ tailWord_1830985) baseStart_1830985 baseEnd_1830985 := by
    simpa [prefixWord, tailWord_1830985, baseEnd_1830985] using wordTrace_append hprefix tailTrace_1830985
  have hstable : (prefixWord ++ tailWord_1830985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830985).length < 2 ^ (prefixWord ++ tailWord_1830985).sum := by decide
  have hdescent : baseEnd_1830985 < baseStart_1830985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830989 : List Nat := [1, 6, 1, 1, 1, 1, 3, 2, 3, 4]
def baseStart_1830989 : Nat := 118140960795 + 1830989 * 2 ^ 59
def prefixEnd_1830989 : Nat := 4983230072969 + 3 ^ 40 * 1830989 * 2
def baseEnd_1830989 : Nat := 313392476698413993605647

theorem tailTrace_1830989 : CollatzResearch.WordTrace tailWord_1830989 prefixEnd_1830989 313392476698413993605647 := by
  unfold tailWord_1830989
  simp only [CollatzResearch.WordTrace]
  refine ⟨66781655163647035870352021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44521103442431357246901347 66781655163647035870352021)
  ·
    refine ⟨3130390085795954806422751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 66781655163647035870352021 3130390085795954806422751)
    ·
      refine ⟨4695585128693932209634127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3130390085795954806422751 4695585128693932209634127)
      ·
        refine ⟨7043377693040898314451191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4695585128693932209634127 7043377693040898314451191)
        ·
          refine ⟨10565066539561347471676787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7043377693040898314451191 10565066539561347471676787)
          ·
            refine ⟨15847599809342021207515181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10565066539561347471676787 15847599809342021207515181)
            ·
              refine ⟨5942849928503257952818193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15847599809342021207515181 5942849928503257952818193)
              ·
                refine ⟨4457137446377443464613645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5942849928503257952818193 4457137446377443464613645)
                ·
                  refine ⟨1671426542391541299230117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4457137446377443464613645 1671426542391541299230117)
                  ·
                    refine ⟨313392476698413993605647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1671426542391541299230117 313392476698413993605647)
                    ·
                      rfl

theorem cell23_1830989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_1830989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1830989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1830989 prefixEnd_1830989 := by exact prefixLift 1830989
  have htrace : WordTrace (prefixWord ++ tailWord_1830989) baseStart_1830989 baseEnd_1830989 := by
    simpa [prefixWord, tailWord_1830989, baseEnd_1830989] using wordTrace_append hprefix tailTrace_1830989
  have hstable : (prefixWord ++ tailWord_1830989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830989).length < 2 ^ (prefixWord ++ tailWord_1830989).sum := by decide
  have hdescent : baseEnd_1830989 < baseStart_1830989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831069 : List Nat := [1, 4, 2, 1, 1, 3, 2, 3, 1, 1, 4]
def baseStart_1831069 : Nat := 118140960795 + 1831069 * 2 ^ 59
def prefixEnd_1831069 : Nat := 4983230072969 + 3 ^ 40 * 1831069 * 2
def baseEnd_1831069 : Nat := 940218508547601667816573

theorem tailTrace_1831069 : CollatzResearch.WordTrace tailWord_1831069 prefixEnd_1831069 940218508547601667816573 := by
  unfold tailWord_1831069
  simp only [CollatzResearch.WordTrace]
  refine ⟨66784573003357209533264261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44523048668904806355509507 66784573003357209533264261)
  ·
    refine ⟨12522107438129476787487049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66784573003357209533264261 12522107438129476787487049)
    ·
      refine ⟨9391580578597107590615287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12522107438129476787487049 9391580578597107590615287)
      ·
        refine ⟨14087370867895661385922931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9391580578597107590615287 14087370867895661385922931)
        ·
          refine ⟨21131056301843492078884397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14087370867895661385922931 21131056301843492078884397)
          ·
            refine ⟨7924146113191309529581649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21131056301843492078884397 7924146113191309529581649)
            ·
              refine ⟨5943109584893482147186237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7924146113191309529581649 5943109584893482147186237)
              ·
                refine ⟨2228666094335055805194839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5943109584893482147186237 2228666094335055805194839)
                ·
                  refine ⟨3342999141502583707792259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2228666094335055805194839 3342999141502583707792259)
                  ·
                    refine ⟨5014498712253875561688389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3342999141502583707792259 5014498712253875561688389)
                    ·
                      refine ⟨940218508547601667816573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5014498712253875561688389 940218508547601667816573)
                      ·
                        rfl

theorem cell23_1831069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 3, 1, 1, 4].length) (baseStart_1831069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1831069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1831069 prefixEnd_1831069 := by exact prefixLift 1831069
  have htrace : WordTrace (prefixWord ++ tailWord_1831069) baseStart_1831069 baseEnd_1831069 := by
    simpa [prefixWord, tailWord_1831069, baseEnd_1831069] using wordTrace_append hprefix tailTrace_1831069
  have hstable : (prefixWord ++ tailWord_1831069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831069).length < 2 ^ (prefixWord ++ tailWord_1831069).sum := by decide
  have hdescent : baseEnd_1831069 < baseStart_1831069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831072 : List Nat := [2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 5]
def baseStart_1831072 : Nat := 118140960795 + 1831072 * 2 ^ 59
def prefixEnd_1831072 : Nat := 4983230072969 + 3 ^ 40 * 1831072 * 2
def baseEnd_1831072 : Nat := 940220048989565156079059

theorem tailTrace_1831072 : CollatzResearch.WordTrace tailWord_1831072 prefixEnd_1831072 940220048989565156079059 := by
  unfold tailWord_1831072
  simp only [CollatzResearch.WordTrace]
  refine ⟨33392341211173170522811735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44523121614897560697082313 33392341211173170522811735)
  ·
    refine ⟨50088511816759755784217603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33392341211173170522811735 50088511816759755784217603)
    ·
      refine ⟨75132767725139633676326405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50088511816759755784217603 75132767725139633676326405)
      ·
        refine ⟨14087393948463681314311201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75132767725139633676326405 14087393948463681314311201)
        ·
          refine ⟨10565545461347760985733401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14087393948463681314311201 10565545461347760985733401)
          ·
            refine ⟨7924159096010820739300051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10565545461347760985733401 7924159096010820739300051)
            ·
              refine ⟨11886238644016231108950077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7924159096010820739300051 11886238644016231108950077)
              ·
                refine ⟨4457339491506086665856279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11886238644016231108950077 4457339491506086665856279)
                ·
                  refine ⟨6686009237259129998784419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4457339491506086665856279 6686009237259129998784419)
                  ·
                    refine ⟨10029013855888694998176629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6686009237259129998784419 10029013855888694998176629)
                    ·
                      refine ⟨940220048989565156079059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10029013855888694998176629 940220048989565156079059)
                      ·
                        rfl

theorem cell23_1831072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_1831072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1831072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1831072 prefixEnd_1831072 := by exact prefixLift 1831072
  have htrace : WordTrace (prefixWord ++ tailWord_1831072) baseStart_1831072 baseEnd_1831072 := by
    simpa [prefixWord, tailWord_1831072, baseEnd_1831072] using wordTrace_append hprefix tailTrace_1831072
  have hstable : (prefixWord ++ tailWord_1831072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831072).length < 2 ^ (prefixWord ++ tailWord_1831072).sum := by decide
  have hdescent : baseEnd_1831072 < baseStart_1831072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831116 : List Nat := [2, 2, 1, 6, 1, 1, 1, 2, 1, 2, 4]
def baseStart_1831116 : Nat := 118140960795 + 1831116 * 2 ^ 59
def prefixEnd_1831116 : Nat := 4983230072969 + 3 ^ 40 * 1831116 * 2
def baseEnd_1831116 : Nat := 940242642138362983928857

theorem tailTrace_1831116 : CollatzResearch.WordTrace tailWord_1831116 prefixEnd_1831116 940242642138362983928857 := by
  unfold tailWord_1831116
  simp only [CollatzResearch.WordTrace]
  refine ⟨33393143617093468280112601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44524191489457957706816801 33393143617093468280112601)
  ·
    refine ⟨25044857712820101210084451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33393143617093468280112601 25044857712820101210084451)
    ·
      refine ⟨37567286569230151815126677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25044857712820101210084451 37567286569230151815126677)
      ·
        refine ⟨1760966557932663366334063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 37567286569230151815126677 1760966557932663366334063)
        ·
          refine ⟨2641449836898995049501095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1760966557932663366334063 2641449836898995049501095)
          ·
            refine ⟨3962174755348492574251643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2641449836898995049501095 3962174755348492574251643)
            ·
              refine ⟨5943262133022738861377465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3962174755348492574251643 5943262133022738861377465)
              ·
                refine ⟨4457446599767054146033099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5943262133022738861377465 4457446599767054146033099)
                ·
                  refine ⟨6686169899650581219049649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4457446599767054146033099 6686169899650581219049649)
                  ·
                    refine ⟨5014627424737935914287237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6686169899650581219049649 5014627424737935914287237)
                    ·
                      refine ⟨940242642138362983928857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5014627424737935914287237 940242642138362983928857)
                      ·
                        rfl

theorem cell23_1831116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_1831116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1831116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1831116 prefixEnd_1831116 := by exact prefixLift 1831116
  have htrace : WordTrace (prefixWord ++ tailWord_1831116) baseStart_1831116 baseEnd_1831116 := by
    simpa [prefixWord, tailWord_1831116, baseEnd_1831116] using wordTrace_append hprefix tailTrace_1831116
  have hstable : (prefixWord ++ tailWord_1831116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831116).length < 2 ^ (prefixWord ++ tailWord_1831116).sum := by decide
  have hdescent : baseEnd_1831116 < baseStart_1831116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831136 : List Nat := [2, 1, 1, 3, 1, 3, 4, 2, 2, 1, 3]
def baseStart_1831136 : Nat := 118140960795 + 1831136 * 2 ^ 59
def prefixEnd_1831136 : Nat := 4983230072969 + 3 ^ 40 * 1831136 * 2
def baseEnd_1831136 : Nat := 940252911751452905678765

theorem tailTrace_1831136 : CollatzResearch.WordTrace tailWord_1831136 prefixEnd_1831136 940252911751452905678765 := by
  unfold tailWord_1831136
  simp only [CollatzResearch.WordTrace]
  refine ⟨33393508347057239987976631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44524677796076319983968841 33393508347057239987976631)
  ·
    refine ⟨50090262520585859981964947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33393508347057239987976631 50090262520585859981964947)
    ·
      refine ⟨75135393780878789972947421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50090262520585859981964947 75135393780878789972947421)
      ·
        refine ⟨28175772667829546239855283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75135393780878789972947421 28175772667829546239855283)
        ·
          refine ⟨42263659001744319359782925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28175772667829546239855283 42263659001744319359782925)
          ·
            refine ⟨15848872125654119759918597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42263659001744319359782925 15848872125654119759918597)
            ·
              refine ⟨2971663523560147454984737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15848872125654119759918597 2971663523560147454984737)
              ·
                refine ⟨2228747642670110591238553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2971663523560147454984737 2228747642670110591238553)
                ·
                  refine ⟨1671560732002582943428915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2228747642670110591238553 1671560732002582943428915)
                  ·
                    refine ⟨2507341098003874415143373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1671560732002582943428915 2507341098003874415143373)
                    ·
                      refine ⟨940252911751452905678765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2507341098003874415143373 940252911751452905678765)
                      ·
                        rfl

theorem cell23_1831136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 2, 2, 1, 3].length) (baseStart_1831136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1831136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1831136 prefixEnd_1831136 := by exact prefixLift 1831136
  have htrace : WordTrace (prefixWord ++ tailWord_1831136) baseStart_1831136 baseEnd_1831136 := by
    simpa [prefixWord, tailWord_1831136, baseEnd_1831136] using wordTrace_append hprefix tailTrace_1831136
  have hstable : (prefixWord ++ tailWord_1831136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831136).length < 2 ^ (prefixWord ++ tailWord_1831136).sum := by decide
  have hdescent : baseEnd_1831136 < baseStart_1831136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831176 : List Nat := [2, 1, 3, 2, 3, 1, 2, 2, 1, 4, 2]
def baseStart_1831176 : Nat := 118140960795 + 1831176 * 2 ^ 59
def prefixEnd_1831176 : Nat := 4983230072969 + 3 ^ 40 * 1831176 * 2
def baseEnd_1831176 : Nat := 940273450977632749178581

theorem tailTrace_1831176 : CollatzResearch.WordTrace tailWord_1831176 prefixEnd_1831176 940273450977632749178581 := by
  unfold tailWord_1831176
  simp only [CollatzResearch.WordTrace]
  refine ⟨33394237806984783403704691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44525650409313044538272921 33394237806984783403704691)
  ·
    refine ⟨50091356710477175105557037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33394237806984783403704691 50091356710477175105557037)
    ·
      refine ⟨18784258766428940664583889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50091356710477175105557037 18784258766428940664583889)
      ·
        refine ⟨14088194074821705498437917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18784258766428940664583889 14088194074821705498437917)
        ·
          refine ⟨5283072778058139561914219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14088194074821705498437917 5283072778058139561914219)
          ·
            refine ⟨7924609167087209342871329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5283072778058139561914219 7924609167087209342871329)
            ·
              refine ⟨5943456875315407007153497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7924609167087209342871329 5943456875315407007153497)
              ·
                refine ⟨4457592656486555255365123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5943456875315407007153497 4457592656486555255365123)
                ·
                  refine ⟨6686388984729832883047685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4457592656486555255365123 6686388984729832883047685)
                  ·
                    refine ⟨1253697934636843665571441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6686388984729832883047685 1253697934636843665571441)
                    ·
                      refine ⟨940273450977632749178581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1253697934636843665571441 940273450977632749178581)
                      ·
                        rfl

theorem cell23_1831176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 2, 1, 4, 2].length) (baseStart_1831176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1831176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1831176 prefixEnd_1831176 := by exact prefixLift 1831176
  have htrace : WordTrace (prefixWord ++ tailWord_1831176) baseStart_1831176 baseEnd_1831176 := by
    simpa [prefixWord, tailWord_1831176, baseEnd_1831176] using wordTrace_append hprefix tailTrace_1831176
  have hstable : (prefixWord ++ tailWord_1831176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831176).length < 2 ^ (prefixWord ++ tailWord_1831176).sum := by decide
  have hdescent : baseEnd_1831176 < baseStart_1831176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831182 : List Nat := [4, 1, 1, 2, 1, 2, 1, 2, 9]
def baseStart_1831182 : Nat := 118140960795 + 1831182 * 2 ^ 59
def prefixEnd_1831182 : Nat := 4983230072969 + 3 ^ 40 * 1831182 * 2
def baseEnd_1831182 : Nat := 104475170206839969522617

theorem tailTrace_1831182 : CollatzResearch.WordTrace tailWord_1831182 prefixEnd_1831182 104475170206839969522617 := by
  unfold tailWord_1831182
  simp only [CollatzResearch.WordTrace]
  refine ⟨8348586806493478729015975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44525796301298553221418533 8348586806493478729015975)
  ·
    refine ⟨12522880209740218093523963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8348586806493478729015975 12522880209740218093523963)
    ·
      refine ⟨18784320314610327140285945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12522880209740218093523963 18784320314610327140285945)
      ·
        refine ⟨14088240235957745355214459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18784320314610327140285945 14088240235957745355214459)
        ·
          refine ⟨21132360353936618032821689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14088240235957745355214459 21132360353936618032821689)
          ·
            refine ⟨15849270265452463524616267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21132360353936618032821689 15849270265452463524616267)
            ·
              refine ⟨23773905398178695286924401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15849270265452463524616267 23773905398178695286924401)
              ·
                refine ⟨17830429048634021465193301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23773905398178695286924401 17830429048634021465193301)
                ·
                  refine ⟨104475170206839969522617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 17830429048634021465193301 104475170206839969522617)
                  ·
                    rfl

theorem cell23_1831182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 9].length) (baseStart_1831182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1831182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1831182 prefixEnd_1831182 := by exact prefixLift 1831182
  have htrace : WordTrace (prefixWord ++ tailWord_1831182) baseStart_1831182 baseEnd_1831182 := by
    simpa [prefixWord, tailWord_1831182, baseEnd_1831182] using wordTrace_append hprefix tailTrace_1831182
  have hstable : (prefixWord ++ tailWord_1831182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831182).length < 2 ^ (prefixWord ++ tailWord_1831182).sum := by decide
  have hdescent : baseEnd_1831182 < baseStart_1831182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831199 : List Nat := [1, 1, 2, 4, 3, 2, 2, 1, 7]
def baseStart_1831199 : Nat := 118140960795 + 1831199 * 2 ^ 59
def prefixEnd_1831199 : Nat := 4983230072969 + 3 ^ 40 * 1831199 * 2
def baseEnd_1831199 : Nat := 104476140114742906576775

theorem tailTrace_1831199 : CollatzResearch.WordTrace tailWord_1831199 prefixEnd_1831199 104476140114742906576775 := by
  unfold tailWord_1831199
  simp only [CollatzResearch.WordTrace]
  refine ⟨66789314492886241735496651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44526209661924161156997767 66789314492886241735496651)
  ·
    refine ⟨100183971739329362603244977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66789314492886241735496651 100183971739329362603244977)
    ·
      refine ⟨75137978804497021952433733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100183971739329362603244977 75137978804497021952433733)
      ·
        refine ⟨14088371025843191616081325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75137978804497021952433733 14088371025843191616081325)
        ·
          refine ⟨5283139134691196856030497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14088371025843191616081325 5283139134691196856030497)
          ·
            refine ⟨3962354351018397642022873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5283139134691196856030497 3962354351018397642022873)
            ·
              refine ⟨2971765763263798231517155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3962354351018397642022873 2971765763263798231517155)
              ·
                refine ⟨4457648644895697347275733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2971765763263798231517155 4457648644895697347275733)
                ·
                  refine ⟨104476140114742906576775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4457648644895697347275733 104476140114742906576775)
                  ·
                    rfl

theorem cell23_1831199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 1, 7].length) (baseStart_1831199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1831199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1831199 prefixEnd_1831199 := by exact prefixLift 1831199
  have htrace : WordTrace (prefixWord ++ tailWord_1831199) baseStart_1831199 baseEnd_1831199 := by
    simpa [prefixWord, tailWord_1831199, baseEnd_1831199] using wordTrace_append hprefix tailTrace_1831199
  have hstable : (prefixWord ++ tailWord_1831199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831199).length < 2 ^ (prefixWord ++ tailWord_1831199).sum := by decide
  have hdescent : baseEnd_1831199 < baseStart_1831199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831210 : List Nat := [3, 1, 4, 2, 2, 2, 1, 1, 1, 4, 2]
def baseStart_1831210 : Nat := 118140960795 + 1831210 * 2 ^ 59
def prefixEnd_1831210 : Nat := 4983230072969 + 3 ^ 40 * 1831210 * 2
def baseEnd_1831210 : Nat := 940290909319885616153425

theorem tailTrace_1831210 : CollatzResearch.WordTrace tailWord_1831210 prefixEnd_1831210 940290909319885616153425 := by
  unfold tailWord_1831210
  simp only [CollatzResearch.WordTrace]
  refine ⟨16697428923961597653536771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44526477130564260409431389 16697428923961597653536771)
  ·
    refine ⟨25046143385942396480305157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16697428923961597653536771 25046143385942396480305157)
    ·
      refine ⟨4696151884864199340057217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25046143385942396480305157 4696151884864199340057217)
      ·
        refine ⟨3522113913648149505042913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4696151884864199340057217 3522113913648149505042913)
        ·
          refine ⟨2641585435236112128782185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3522113913648149505042913 2641585435236112128782185)
          ·
            refine ⟨1981189076427084096586639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2641585435236112128782185 1981189076427084096586639)
            ·
              refine ⟨2971783614640626144879959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1981189076427084096586639 2971783614640626144879959)
              ·
                refine ⟨4457675421960939217319939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2971783614640626144879959 4457675421960939217319939)
                ·
                  refine ⟨6686513132941408825979909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4457675421960939217319939 6686513132941408825979909)
                  ·
                    refine ⟨1253721212426514154871233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6686513132941408825979909 1253721212426514154871233)
                    ·
                      refine ⟨940290909319885616153425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1253721212426514154871233 940290909319885616153425)
                      ·
                        rfl

theorem cell23_1831210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_1831210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1831210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1831210 prefixEnd_1831210 := by exact prefixLift 1831210
  have htrace : WordTrace (prefixWord ++ tailWord_1831210) baseStart_1831210 baseEnd_1831210 := by
    simpa [prefixWord, tailWord_1831210, baseEnd_1831210] using wordTrace_append hprefix tailTrace_1831210
  have hstable : (prefixWord ++ tailWord_1831210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831210).length < 2 ^ (prefixWord ++ tailWord_1831210).sum := by decide
  have hdescent : baseEnd_1831210 < baseStart_1831210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831212 : List Nat := [2, 2, 1, 1, 1, 3, 3, 2, 1, 7]
def baseStart_1831212 : Nat := 118140960795 + 1831212 * 2 ^ 59
def prefixEnd_1831212 : Nat := 4983230072969 + 3 ^ 40 * 1831212 * 2
def baseEnd_1831212 : Nat := 313430645427064869442805

theorem tailTrace_1831212 : CollatzResearch.WordTrace tailWord_1831212 prefixEnd_1831212 313430645427064869442805 := by
  unfold tailWord_1831212
  simp only [CollatzResearch.WordTrace]
  refine ⟨33394894320919572477859945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44526525761226096637146593 33394894320919572477859945)
  ·
    refine ⟨25046170740689679358394959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33394894320919572477859945 25046170740689679358394959)
    ·
      refine ⟨37569256111034519037592439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25046170740689679358394959 37569256111034519037592439)
      ·
        refine ⟨56353884166551778556388659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37569256111034519037592439 56353884166551778556388659)
        ·
          refine ⟨84530826249827667834582989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56353884166551778556388659 84530826249827667834582989)
          ·
            refine ⟨31699059843685375437968621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84530826249827667834582989 31699059843685375437968621)
            ·
              refine ⟨11887147441382015789238233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31699059843685375437968621 11887147441382015789238233)
              ·
                refine ⟨8915360581036511841928675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11887147441382015789238233 8915360581036511841928675)
                ·
                  refine ⟨13373040871554767762893013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8915360581036511841928675 13373040871554767762893013)
                  ·
                    refine ⟨313430645427064869442805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13373040871554767762893013 313430645427064869442805)
                    ·
                      rfl

theorem cell23_1831212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 7].length) (baseStart_1831212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1831212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1831212 prefixEnd_1831212 := by exact prefixLift 1831212
  have htrace : WordTrace (prefixWord ++ tailWord_1831212) baseStart_1831212 baseEnd_1831212 := by
    simpa [prefixWord, tailWord_1831212, baseEnd_1831212] using wordTrace_append hprefix tailTrace_1831212
  have hstable : (prefixWord ++ tailWord_1831212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831212).length < 2 ^ (prefixWord ++ tailWord_1831212).sum := by decide
  have hdescent : baseEnd_1831212 < baseStart_1831212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831249 : List Nat := [1, 2, 2, 1, 4, 2, 1, 1, 4, 1, 4]
def baseStart_1831249 : Nat := 118140960795 + 1831249 * 2 ^ 59
def prefixEnd_1831249 : Nat := 4983230072969 + 3 ^ 40 * 1831249 * 2
def baseEnd_1831249 : Nat := 940310935065410963565745

theorem tailTrace_1831249 : CollatzResearch.WordTrace tailWord_1831249 prefixEnd_1831249 940310935065410963565745 := by
  unfold tailWord_1831249
  simp only [CollatzResearch.WordTrace]
  refine ⟨66791138142705100274816801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44527425428470066849877867 66791138142705100274816801)
  ·
    refine ⟨50093353607028825206112601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66791138142705100274816801 50093353607028825206112601)
    ·
      refine ⟨37570015205271618904584451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50093353607028825206112601 37570015205271618904584451)
      ·
        refine ⟨56355022807907428356876677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37570015205271618904584451 56355022807907428356876677)
        ·
          refine ⟨10566566776482642816914377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56355022807907428356876677 10566566776482642816914377)
          ·
            refine ⟨7924925082361982112685783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10566566776482642816914377 7924925082361982112685783)
            ·
              refine ⟨11887387623542973169028675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7924925082361982112685783 11887387623542973169028675)
              ·
                refine ⟨17831081435314459753543013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11887387623542973169028675 17831081435314459753543013)
                ·
                  refine ⟨3343327769121461203789315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17831081435314459753543013 3343327769121461203789315)
                  ·
                    refine ⟨5014991653682191805683973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3343327769121461203789315 5014991653682191805683973)
                    ·
                      refine ⟨940310935065410963565745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5014991653682191805683973 940310935065410963565745)
                      ·
                        rfl

theorem cell23_1831249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 4, 1, 4].length) (baseStart_1831249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1831249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1831249 prefixEnd_1831249 := by exact prefixLift 1831249
  have htrace : WordTrace (prefixWord ++ tailWord_1831249) baseStart_1831249 baseEnd_1831249 := by
    simpa [prefixWord, tailWord_1831249, baseEnd_1831249] using wordTrace_append hprefix tailTrace_1831249
  have hstable : (prefixWord ++ tailWord_1831249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831249).length < 2 ^ (prefixWord ++ tailWord_1831249).sum := by decide
  have hdescent : baseEnd_1831249 < baseStart_1831249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831310 : List Nat := [4, 1, 1, 4, 1, 2, 1, 4, 1, 4]
def baseStart_1831310 : Nat := 118140960795 + 1831310 * 2 ^ 59
def prefixEnd_1831310 : Nat := 4983230072969 + 3 ^ 40 * 1831310 * 2
def baseEnd_1831310 : Nat := 313447419128445074967655

theorem tailTrace_1831310 : CollatzResearch.WordTrace tailWord_1831310 prefixEnd_1831310 313447419128445074967655 := by
  unfold tailWord_1831310
  simp only [CollatzResearch.WordTrace]
  refine ⟨8349170374435513461598423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44528908663656071795191589 8349170374435513461598423)
  ·
    refine ⟨12523755561653270192397635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8349170374435513461598423 12523755561653270192397635)
    ·
      refine ⟨18785633342479905288596453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12523755561653270192397635 18785633342479905288596453)
      ·
        refine ⟨3522306251714982241611835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18785633342479905288596453 3522306251714982241611835)
        ·
          refine ⟨5283459377572473362417753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3522306251714982241611835 5283459377572473362417753)
          ·
            refine ⟨3962594533179355021813315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5283459377572473362417753 3962594533179355021813315)
            ·
              refine ⟨5943891799769032532719973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3962594533179355021813315 5943891799769032532719973)
              ·
                refine ⟨1114479712456693599884995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5943891799769032532719973 1114479712456693599884995)
                ·
                  refine ⟨1671719568685040399827493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1114479712456693599884995 1671719568685040399827493)
                  ·
                    refine ⟨313447419128445074967655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1671719568685040399827493 313447419128445074967655)
                    ·
                      rfl

theorem cell23_1831310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 4, 1, 4].length) (baseStart_1831310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1831310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1831310 prefixEnd_1831310 := by exact prefixLift 1831310
  have htrace : WordTrace (prefixWord ++ tailWord_1831310) baseStart_1831310 baseEnd_1831310 := by
    simpa [prefixWord, tailWord_1831310, baseEnd_1831310] using wordTrace_append hprefix tailTrace_1831310
  have hstable : (prefixWord ++ tailWord_1831310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831310).length < 2 ^ (prefixWord ++ tailWord_1831310).sum := by decide
  have hdescent : baseEnd_1831310 < baseStart_1831310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831319 : List Nat := [1, 1, 3, 3, 1, 1, 3, 2, 3, 5]
def baseStart_1831319 : Nat := 118140960795 + 1831319 * 2 ^ 59
def prefixEnd_1831319 : Nat := 4983230072969 + 3 ^ 40 * 1831319 * 2
def baseEnd_1831319 : Nat := 313448959570408563230141

theorem tailTrace_1831319 : CollatzResearch.WordTrace tailWord_1831319 prefixEnd_1831319 313448959570408563230141 := by
  unfold tailWord_1831319
  simp only [CollatzResearch.WordTrace]
  refine ⟨66793691252451502229865011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44529127501634334819910007 66793691252451502229865011)
  ·
    refine ⟨100190536878677253344797517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66793691252451502229865011 100190536878677253344797517)
    ·
      refine ⟨37571451329503970004299069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100190536878677253344797517 37571451329503970004299069)
      ·
        refine ⟨14089294248563988751612151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37571451329503970004299069 14089294248563988751612151)
        ·
          refine ⟨21133941372845983127418227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14089294248563988751612151 21133941372845983127418227)
          ·
            refine ⟨31700912059268974691127341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21133941372845983127418227 31700912059268974691127341)
            ·
              refine ⟨11887842022225865509172753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31700912059268974691127341 11887842022225865509172753)
              ·
                refine ⟨8915881516669399131879565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11887842022225865509172753 8915881516669399131879565)
                ·
                  refine ⟨3343455568751024674454837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8915881516669399131879565 3343455568751024674454837)
                  ·
                    refine ⟨313448959570408563230141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3343455568751024674454837 313448959570408563230141)
                    ·
                      rfl

theorem cell23_1831319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 2, 3, 5].length) (baseStart_1831319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1831319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1831319 prefixEnd_1831319 := by exact prefixLift 1831319
  have htrace : WordTrace (prefixWord ++ tailWord_1831319) baseStart_1831319 baseEnd_1831319 := by
    simpa [prefixWord, tailWord_1831319, baseEnd_1831319] using wordTrace_append hprefix tailTrace_1831319
  have hstable : (prefixWord ++ tailWord_1831319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831319).length < 2 ^ (prefixWord ++ tailWord_1831319).sum := by decide
  have hdescent : baseEnd_1831319 < baseStart_1831319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831353 : List Nat := [1, 2, 1, 4, 3, 1, 4, 1, 1, 5]
def baseStart_1831353 : Nat := 118140960795 + 1831353 * 2 ^ 59
def prefixEnd_1831353 : Nat := 4983230072969 + 3 ^ 40 * 1831353 * 2
def baseEnd_1831353 : Nat := 313454779017826185555089

theorem tailTrace_1831353 : CollatzResearch.WordTrace tailWord_1831353 prefixEnd_1831353 313454779017826185555089 := by
  unfold tailWord_1831353
  simp only [CollatzResearch.WordTrace]
  refine ⟨66794931334328326036602713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44529954222885550691068475 66794931334328326036602713)
  ·
    refine ⟨50096198500746244527452035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66794931334328326036602713 50096198500746244527452035)
    ·
      refine ⟨75144297751119366791178053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50096198500746244527452035 75144297751119366791178053)
      ·
        refine ⟨14089555828334881273345885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75144297751119366791178053 14089555828334881273345885)
        ·
          refine ⟨5283583435625580477504707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14089555828334881273345885 5283583435625580477504707)
          ·
            refine ⟨7925375153438370716257061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5283583435625580477504707 7925375153438370716257061)
            ·
              refine ⟨1486007841269694509298199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7925375153438370716257061 1486007841269694509298199)
              ·
                refine ⟨2229011761904541763947299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1486007841269694509298199 2229011761904541763947299)
                ·
                  refine ⟨3343517642856812645920949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2229011761904541763947299 3343517642856812645920949)
                  ·
                    refine ⟨313454779017826185555089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3343517642856812645920949 313454779017826185555089)
                    ·
                      rfl

theorem cell23_1831353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 4, 1, 1, 5].length) (baseStart_1831353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1831353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1831353 prefixEnd_1831353 := by exact prefixLift 1831353
  have htrace : WordTrace (prefixWord ++ tailWord_1831353) baseStart_1831353 baseEnd_1831353 := by
    simpa [prefixWord, tailWord_1831353, baseEnd_1831353] using wordTrace_append hprefix tailTrace_1831353
  have hstable : (prefixWord ++ tailWord_1831353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831353).length < 2 ^ (prefixWord ++ tailWord_1831353).sum := by decide
  have hdescent : baseEnd_1831353 < baseStart_1831353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831369 : List Nat := [1, 2, 1, 1, 2, 1, 4, 2, 3, 2, 4]
def baseStart_1831369 : Nat := 118140960795 + 1831369 * 2 ^ 59
def prefixEnd_1831369 : Nat := 4983230072969 + 3 ^ 40 * 1831369 * 2
def baseEnd_1831369 : Nat := 940372552743950494065193

theorem tailTrace_1831369 : CollatzResearch.WordTrace tailWord_1831369 prefixEnd_1831369 940372552743950494065193 := by
  unfold tailWord_1831369
  simp only [CollatzResearch.WordTrace]
  refine ⟨66795514902270360769185161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44530343268180240512790107 66795514902270360769185161)
  ·
    refine ⟨50096636176702770576888871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66795514902270360769185161 50096636176702770576888871)
    ·
      refine ⟨75144954265054155865333307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50096636176702770576888871 75144954265054155865333307)
      ·
        refine ⟨112717431397581233797999961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75144954265054155865333307 112717431397581233797999961)
        ·
          refine ⟨84538073548185925348499971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112717431397581233797999961 84538073548185925348499971)
          ·
            refine ⟨126807110322278888022749957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84538073548185925348499971 126807110322278888022749957)
            ·
              refine ⟨23776333185427291504265617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 126807110322278888022749957 23776333185427291504265617)
              ·
                refine ⟨17832249889070468628199213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23776333185427291504265617 17832249889070468628199213)
                ·
                  refine ⟨6687093708401425735574705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17832249889070468628199213 6687093708401425735574705)
                  ·
                    refine ⟨5015320281301069301681029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6687093708401425735574705 5015320281301069301681029)
                    ·
                      refine ⟨940372552743950494065193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5015320281301069301681029 940372552743950494065193)
                      ·
                        rfl

theorem cell23_1831369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 3, 2, 4].length) (baseStart_1831369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1831369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1831369 prefixEnd_1831369 := by exact prefixLift 1831369
  have htrace : WordTrace (prefixWord ++ tailWord_1831369) baseStart_1831369 baseEnd_1831369 := by
    simpa [prefixWord, tailWord_1831369, baseEnd_1831369] using wordTrace_append hprefix tailTrace_1831369
  have hstable : (prefixWord ++ tailWord_1831369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831369).length < 2 ^ (prefixWord ++ tailWord_1831369).sum := by decide
  have hdescent : baseEnd_1831369 < baseStart_1831369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831393 : List Nat := [1, 2, 3, 1, 2, 2, 4, 2, 1, 2, 3]
def baseStart_1831393 : Nat := 118140960795 + 1831393 * 2 ^ 59
def prefixEnd_1831393 : Nat := 4983230072969 + 3 ^ 40 * 1831393 * 2
def baseEnd_1831393 : Nat := 940384876279658400165083

theorem tailTrace_1831393 : CollatzResearch.WordTrace tailWord_1831393 prefixEnd_1831393 940384876279658400165083 := by
  unfold tailWord_1831393
  simp only [CollatzResearch.WordTrace]
  refine ⟨66796390254183412868058833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44530926836122275245372555 66796390254183412868058833)
  ·
    refine ⟨50097292690637559651044125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66796390254183412868058833 50097292690637559651044125)
    ·
      refine ⟨18786484758989084869141547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50097292690637559651044125 18786484758989084869141547)
      ·
        refine ⟨28179727138483627303712321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18786484758989084869141547 28179727138483627303712321)
        ·
          refine ⟨21134795353862720477784241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28179727138483627303712321 21134795353862720477784241)
          ·
            refine ⟨15851096515397040358338181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21134795353862720477784241 15851096515397040358338181)
            ·
              refine ⟨2972080596636945067188409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15851096515397040358338181 2972080596636945067188409)
              ·
                refine ⟨2229060447477708800391307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2972080596636945067188409 2229060447477708800391307)
                ·
                  refine ⟨3343590671216563200586961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2229060447477708800391307 3343590671216563200586961)
                  ·
                    refine ⟨2507693003412422400440221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3343590671216563200586961 2507693003412422400440221)
                    ·
                      refine ⟨940384876279658400165083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2507693003412422400440221 940384876279658400165083)
                      ·
                        rfl

theorem cell23_1831393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 2, 1, 2, 3].length) (baseStart_1831393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1831393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1831393 prefixEnd_1831393 := by exact prefixLift 1831393
  have htrace : WordTrace (prefixWord ++ tailWord_1831393) baseStart_1831393 baseEnd_1831393 := by
    simpa [prefixWord, tailWord_1831393, baseEnd_1831393] using wordTrace_append hprefix tailTrace_1831393
  have hstable : (prefixWord ++ tailWord_1831393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831393).length < 2 ^ (prefixWord ++ tailWord_1831393).sum := by decide
  have hdescent : baseEnd_1831393 < baseStart_1831393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831413 : List Nat := [1, 3, 5, 1, 2, 2, 9]
def baseStart_1831413 : Nat := 118140960795 + 1831413 * 2 ^ 59
def prefixEnd_1831413 : Nat := 4983230072969 + 3 ^ 40 * 1831413 * 2
def baseEnd_1831413 : Nat := 11609816615959855826111

theorem tailTrace_1831413 : CollatzResearch.WordTrace tailWord_1831413 prefixEnd_1831413 11609816615959855826111 := by
  unfold tailWord_1831413
  simp only [CollatzResearch.WordTrace]
  refine ⟨66797119714110956283786893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44531413142740637522524595 66797119714110956283786893)
  ·
    refine ⟨25048919892791608606420085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66797119714110956283786893 25048919892791608606420085)
    ·
      refine ⟨2348336239949213306851883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25048919892791608606420085 2348336239949213306851883)
      ·
        refine ⟨3522504359923819960277825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2348336239949213306851883 3522504359923819960277825)
        ·
          refine ⟨2641878269942864970208369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3522504359923819960277825 2641878269942864970208369)
          ·
            refine ⟨1981408702457148727656277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2641878269942864970208369 1981408702457148727656277)
            ·
              refine ⟨11609816615959855826111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1981408702457148727656277 11609816615959855826111)
              ·
                rfl

theorem cell23_1831413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 9].length) (baseStart_1831413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1831413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1831413 prefixEnd_1831413 := by exact prefixLift 1831413
  have htrace : WordTrace (prefixWord ++ tailWord_1831413) baseStart_1831413 baseEnd_1831413 := by
    simpa [prefixWord, tailWord_1831413, baseEnd_1831413] using wordTrace_append hprefix tailTrace_1831413
  have hstable : (prefixWord ++ tailWord_1831413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831413).length < 2 ^ (prefixWord ++ tailWord_1831413).sum := by decide
  have hdescent : baseEnd_1831413 < baseStart_1831413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831423 : List Nat := [1, 1, 2, 2, 1, 2, 4, 4, 2, 1, 3]
def baseStart_1831423 : Nat := 118140960795 + 1831423 * 2 ^ 59
def prefixEnd_1831423 : Nat := 4983230072969 + 3 ^ 40 * 1831423 * 2
def baseEnd_1831423 : Nat := 940400280699293282789945

theorem tailTrace_1831423 : CollatzResearch.WordTrace tailWord_1831423 prefixEnd_1831423 940400280699293282789945 := by
  unfold tailWord_1831423
  simp only [CollatzResearch.WordTrace]
  refine ⟨66797484444074727991650923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44531656296049818661100615 66797484444074727991650923)
  ·
    refine ⟨100196226666112091987476385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66797484444074727991650923 100196226666112091987476385)
    ·
      refine ⟨75147169999584068990607289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100196226666112091987476385 75147169999584068990607289)
      ·
        refine ⟨56360377499688051742955467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75147169999584068990607289 56360377499688051742955467)
        ·
          refine ⟨84540566249532077614433201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56360377499688051742955467 84540566249532077614433201)
          ·
            refine ⟨63405424687149058210824901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84540566249532077614433201 63405424687149058210824901)
            ·
              refine ⟨11888517128840448414529669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63405424687149058210824901 11888517128840448414529669)
              ·
                refine ⟨2229096961657584077724313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11888517128840448414529669 2229096961657584077724313)
                ·
                  refine ⟨1671822721243188058293235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2229096961657584077724313 1671822721243188058293235)
                  ·
                    refine ⟨2507734081864782087439853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1671822721243188058293235 2507734081864782087439853)
                    ·
                      refine ⟨940400280699293282789945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2507734081864782087439853 940400280699293282789945)
                      ·
                        rfl

theorem cell23_1831423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 4, 2, 1, 3].length) (baseStart_1831423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1831423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1831423 prefixEnd_1831423 := by exact prefixLift 1831423
  have htrace : WordTrace (prefixWord ++ tailWord_1831423) baseStart_1831423 baseEnd_1831423 := by
    simpa [prefixWord, tailWord_1831423, baseEnd_1831423] using wordTrace_append hprefix tailTrace_1831423
  have hstable : (prefixWord ++ tailWord_1831423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831423).length < 2 ^ (prefixWord ++ tailWord_1831423).sum := by decide
  have hdescent : baseEnd_1831423 < baseStart_1831423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831430 : List Nat := [6, 2, 1, 1, 1, 1, 1, 10]
def baseStart_1831430 : Nat := 118140960795 + 1831430 * 2 ^ 59
def prefixEnd_1831430 : Nat := 4983230072969 + 3 ^ 40 * 1831430 * 2
def baseEnd_1831430 : Nat := 34829773150513879829719

theorem tailTrace_1831430 : CollatzResearch.WordTrace tailWord_1831430 prefixEnd_1831430 34829773150513879829719 := by
  unfold tailWord_1831430
  simp only [CollatzResearch.WordTrace]
  refine ⟨2087429367345292755848617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 44531826503366245458103829 2087429367345292755848617)
  ·
    refine ⟨1565572025508969566886463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2087429367345292755848617 1565572025508969566886463)
    ·
      refine ⟨2348358038263454350329695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1565572025508969566886463 2348358038263454350329695)
      ·
        refine ⟨3522537057395181525494543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2348358038263454350329695 3522537057395181525494543)
        ·
          refine ⟨5283805586092772288241815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3522537057395181525494543 5283805586092772288241815)
          ·
            refine ⟨7925708379139158432362723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5283805586092772288241815 7925708379139158432362723)
            ·
              refine ⟨11888562568708737648544085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7925708379139158432362723 11888562568708737648544085)
              ·
                refine ⟨34829773150513879829719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 11888562568708737648544085 34829773150513879829719)
                ·
                  rfl

theorem cell23_1831430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 10].length) (baseStart_1831430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1831430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1831430 prefixEnd_1831430 := by exact prefixLift 1831430
  have htrace : WordTrace (prefixWord ++ tailWord_1831430) baseStart_1831430 baseEnd_1831430 := by
    simpa [prefixWord, tailWord_1831430, baseEnd_1831430] using wordTrace_append hprefix tailTrace_1831430
  have hstable : (prefixWord ++ tailWord_1831430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831430).length < 2 ^ (prefixWord ++ tailWord_1831430).sum := by decide
  have hdescent : baseEnd_1831430 < baseStart_1831430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831449 : List Nat := [1, 2, 1, 2, 1, 1, 2, 2, 3, 3, 5]
def baseStart_1831449 : Nat := 118140960795 + 1831449 * 2 ^ 59
def prefixEnd_1831449 : Nat := 4983230072969 + 3 ^ 40 * 1831449 * 2
def baseEnd_1831449 : Nat := 940413631196310181064825

theorem tailTrace_1831449 : CollatzResearch.WordTrace tailWord_1831449 prefixEnd_1831449 940413631196310181064825 := by
  unfold tailWord_1831449
  simp only [CollatzResearch.WordTrace]
  refine ⟨66798432741980534432097401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44532288494653689621398267 66798432741980534432097401)
  ·
    refine ⟨50098824556485400824073051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66798432741980534432097401 50098824556485400824073051)
    ·
      refine ⟨75148236834728101236109577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50098824556485400824073051 75148236834728101236109577)
      ·
        refine ⟨56361177626046075927082183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75148236834728101236109577 56361177626046075927082183)
        ·
          refine ⟨84541766439069113890623275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56361177626046075927082183 84541766439069113890623275)
          ·
            refine ⟨126812649658603670835934913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84541766439069113890623275 126812649658603670835934913)
            ·
              refine ⟨95109487243952753126951185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126812649658603670835934913 95109487243952753126951185)
              ·
                refine ⟨71332115432964564845213389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95109487243952753126951185 71332115432964564845213389)
                ·
                  refine ⟨26749543287361711816955021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71332115432964564845213389 26749543287361711816955021)
                  ·
                    refine ⟨10031078732760641931358133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26749543287361711816955021 10031078732760641931358133)
                    ·
                      refine ⟨940413631196310181064825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10031078732760641931358133 940413631196310181064825)
                      ·
                        rfl

theorem cell23_1831449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 3, 5].length) (baseStart_1831449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1831449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1831449 prefixEnd_1831449 := by exact prefixLift 1831449
  have htrace : WordTrace (prefixWord ++ tailWord_1831449) baseStart_1831449 baseEnd_1831449 := by
    simpa [prefixWord, tailWord_1831449, baseEnd_1831449] using wordTrace_append hprefix tailTrace_1831449
  have hstable : (prefixWord ++ tailWord_1831449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831449).length < 2 ^ (prefixWord ++ tailWord_1831449).sum := by decide
  have hdescent : baseEnd_1831449 < baseStart_1831449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831450 : List Nat := [3, 1, 1, 3, 1, 1, 5, 2, 1, 3, 2]
def baseStart_1831450 : Nat := 118140960795 + 1831450 * 2 ^ 59
def prefixEnd_1831450 : Nat := 4983230072969 + 3 ^ 40 * 1831450 * 2
def baseEnd_1831450 : Nat := 940414144676964677152321

theorem tailTrace_1831450 : CollatzResearch.WordTrace tailWord_1831450 prefixEnd_1831450 940414144676964677152321 := by
  unfold tailWord_1831450
  simp only [CollatzResearch.WordTrace]
  refine ⟨16699617303744227900720951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44532312809984607735255869 16699617303744227900720951)
  ·
    refine ⟨25049425955616341851081427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16699617303744227900720951 25049425955616341851081427)
    ·
      refine ⟨37574138933424512776622141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25049425955616341851081427 37574138933424512776622141)
      ·
        refine ⟨14090302100034192291233303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37574138933424512776622141 14090302100034192291233303)
        ·
          refine ⟨21135453150051288436849955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14090302100034192291233303 21135453150051288436849955)
          ·
            refine ⟨31703179725076932655274933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21135453150051288436849955 31703179725076932655274933)
            ·
              refine ⟨2972173099225962436432025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31703179725076932655274933 2972173099225962436432025)
              ·
                refine ⟨2229129824419471827324019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2972173099225962436432025 2229129824419471827324019)
                ·
                  refine ⟨3343694736629207740986029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2229129824419471827324019 3343694736629207740986029)
                  ·
                    refine ⟨1253885526235952902869761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3343694736629207740986029 1253885526235952902869761)
                    ·
                      refine ⟨940414144676964677152321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1253885526235952902869761 940414144676964677152321)
                      ·
                        rfl

theorem cell23_1831450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 2, 1, 3, 2].length) (baseStart_1831450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1831450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1831450 prefixEnd_1831450 := by exact prefixLift 1831450
  have htrace : WordTrace (prefixWord ++ tailWord_1831450) baseStart_1831450 baseEnd_1831450 := by
    simpa [prefixWord, tailWord_1831450, baseEnd_1831450] using wordTrace_append hprefix tailTrace_1831450
  have hstable : (prefixWord ++ tailWord_1831450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831450).length < 2 ^ (prefixWord ++ tailWord_1831450).sum := by decide
  have hdescent : baseEnd_1831450 < baseStart_1831450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831576 : List Nat := [2, 1, 2, 4, 1, 1, 1, 1, 10]
def baseStart_1831576 : Nat := 118140960795 + 1831576 * 2 ^ 59
def prefixEnd_1831576 : Nat := 4983230072969 + 3 ^ 40 * 1831576 * 2
def baseEnd_1831576 : Nat := 104497649248825687130749

theorem tailTrace_1831576 : CollatzResearch.WordTrace tailWord_1831576 prefixEnd_1831576 104497649248825687130749 := by
  unfold tailWord_1831576
  simp only [CollatzResearch.WordTrace]
  refine ⟨33401532406260217560985291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44535376541680290081313721 33401532406260217560985291)
  ·
    refine ⟨50102298609390326341477937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33401532406260217560985291 50102298609390326341477937)
    ·
      refine ⟨37576723957042744756108453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50102298609390326341477937 37576723957042744756108453)
      ·
        refine ⟨7045635741945514641770335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37576723957042744756108453 7045635741945514641770335)
        ·
          refine ⟨10568453612918271962655503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7045635741945514641770335 10568453612918271962655503)
          ·
            refine ⟨15852680419377407943983255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10568453612918271962655503 15852680419377407943983255)
            ·
              refine ⟨23779020629066111915974883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15852680419377407943983255 23779020629066111915974883)
              ·
                refine ⟨35668530943599167873962325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23779020629066111915974883 35668530943599167873962325)
                ·
                  refine ⟨104497649248825687130749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 35668530943599167873962325 104497649248825687130749)
                  ·
                    rfl

theorem cell23_1831576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 10].length) (baseStart_1831576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1831576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1831576 prefixEnd_1831576 := by exact prefixLift 1831576
  have htrace : WordTrace (prefixWord ++ tailWord_1831576) baseStart_1831576 baseEnd_1831576 := by
    simpa [prefixWord, tailWord_1831576, baseEnd_1831576] using wordTrace_append hprefix tailTrace_1831576
  have hstable : (prefixWord ++ tailWord_1831576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831576).length < 2 ^ (prefixWord ++ tailWord_1831576).sum := by decide
  have hdescent : baseEnd_1831576 < baseStart_1831576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831597 : List Nat := [1, 5, 2, 1, 1, 4, 1, 1, 3, 4]
def baseStart_1831597 : Nat := 118140960795 + 1831597 * 2 ^ 59
def prefixEnd_1831597 : Nat := 4983230072969 + 3 ^ 40 * 1831597 * 2
def baseEnd_1831597 : Nat := 313496542111058534004715

theorem tailTrace_1831597 : CollatzResearch.WordTrace tailWord_1831597 prefixEnd_1831597 313496542111058534004715 := by
  unfold tailWord_1831597
  simp only [CollatzResearch.WordTrace]
  refine ⟨66803830745444355708485045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44535887163629570472323363 66803830745444355708485045)
  ·
    refine ⟨6262859132385408347670473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66803830745444355708485045 6262859132385408347670473)
    ·
      refine ⟨4697144349289056260752855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6262859132385408347670473 4697144349289056260752855)
      ·
        refine ⟨7045716523933584391129283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4697144349289056260752855 7045716523933584391129283)
        ·
          refine ⟨10568574785900376586693925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7045716523933584391129283 10568574785900376586693925)
          ·
            refine ⟨1981607772356320610005111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10568574785900376586693925 1981607772356320610005111)
            ·
              refine ⟨2972411658534480915007667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1981607772356320610005111 2972411658534480915007667)
              ·
                refine ⟨4458617487801721372511501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2972411658534480915007667 4458617487801721372511501)
                ·
                  refine ⟨1671981557925645514691813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4458617487801721372511501 1671981557925645514691813)
                  ·
                    refine ⟨313496542111058534004715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1671981557925645514691813 313496542111058534004715)
                    ·
                      rfl

theorem cell23_1831597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_1831597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1831597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1831597 prefixEnd_1831597 := by exact prefixLift 1831597
  have htrace : WordTrace (prefixWord ++ tailWord_1831597) baseStart_1831597 baseEnd_1831597 := by
    simpa [prefixWord, tailWord_1831597, baseEnd_1831597] using wordTrace_append hprefix tailTrace_1831597
  have hstable : (prefixWord ++ tailWord_1831597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831597).length < 2 ^ (prefixWord ++ tailWord_1831597).sum := by decide
  have hdescent : baseEnd_1831597 < baseStart_1831597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831623 : List Nat := [1, 1, 4, 1, 1, 1, 2, 6, 1, 5]
def baseStart_1831623 : Nat := 118140960795 + 1831623 * 2 ^ 59
def prefixEnd_1831623 : Nat := 4983230072969 + 3 ^ 40 * 1831623 * 2
def baseEnd_1831623 : Nat := 313500992276730833429675

theorem tailTrace_1831623 : CollatzResearch.WordTrace tailWord_1831623 prefixEnd_1831623 313500992276730833429675 := by
  unfold tailWord_1831623
  simp only [CollatzResearch.WordTrace]
  refine ⟨66804779043350162148931523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44536519362233441432621015 66804779043350162148931523)
  ·
    refine ⟨100207168565025243223397285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66804779043350162148931523 100207168565025243223397285)
    ·
      refine ⟨18788844105942233104386991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100207168565025243223397285 18788844105942233104386991)
      ·
        refine ⟨28183266158913349656580487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18788844105942233104386991 28183266158913349656580487)
        ·
          refine ⟨42274899238370024484870731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28183266158913349656580487 42274899238370024484870731)
          ·
            refine ⟨63412348857555036727306097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42274899238370024484870731 63412348857555036727306097)
            ·
              refine ⟨47559261643166277545479573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63412348857555036727306097 47559261643166277545479573)
              ·
                refine ⟨2229340389523419259944355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 47559261643166277545479573 2229340389523419259944355)
                ·
                  refine ⟨3344010584285128889916533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2229340389523419259944355 3344010584285128889916533)
                  ·
                    refine ⟨313500992276730833429675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3344010584285128889916533 313500992276730833429675)
                    ·
                      rfl

theorem cell23_1831623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 6, 1, 5].length) (baseStart_1831623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1831623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1831623 prefixEnd_1831623 := by exact prefixLift 1831623
  have htrace : WordTrace (prefixWord ++ tailWord_1831623) baseStart_1831623 baseEnd_1831623 := by
    simpa [prefixWord, tailWord_1831623, baseEnd_1831623] using wordTrace_append hprefix tailTrace_1831623
  have hstable : (prefixWord ++ tailWord_1831623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831623).length < 2 ^ (prefixWord ++ tailWord_1831623).sum := by decide
  have hdescent : baseEnd_1831623 < baseStart_1831623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831643 : List Nat := [1, 1, 1, 1, 1, 1, 1, 3, 3, 8, 2]
def baseStart_1831643 : Nat := 118140960795 + 1831643 * 2 ^ 59
def prefixEnd_1831643 : Nat := 4983230072969 + 3 ^ 40 * 1831643 * 2
def baseEnd_1831643 : Nat := 940513246443282422038933

theorem tailTrace_1831643 : CollatzResearch.WordTrace tailWord_1831643 prefixEnd_1831643 940513246443282422038933 := by
  unfold tailWord_1831643
  simp only [CollatzResearch.WordTrace]
  refine ⟨66805508503277705564659583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44537005668851803709773055 66805508503277705564659583)
  ·
    refine ⟨100208262754916558346989375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66805508503277705564659583 100208262754916558346989375)
    ·
      refine ⟨150312394132374837520484063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100208262754916558346989375 150312394132374837520484063)
      ·
        refine ⟨225468591198562256280726095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150312394132374837520484063 225468591198562256280726095)
        ·
          refine ⟨338202886797843384421089143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225468591198562256280726095 338202886797843384421089143)
          ·
            refine ⟨507304330196765076631633715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 338202886797843384421089143 507304330196765076631633715)
            ·
              refine ⟨760956495295147614947450573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 507304330196765076631633715 760956495295147614947450573)
              ·
                refine ⟨285358685735680355605293965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 760956495295147614947450573 285358685735680355605293965)
                ·
                  refine ⟨107009507150880133351985237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 285358685735680355605293965 107009507150880133351985237)
                  ·
                    refine ⟨1254017661924376562718577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 107009507150880133351985237 1254017661924376562718577)
                    ·
                      refine ⟨940513246443282422038933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1254017661924376562718577 940513246443282422038933)
                      ·
                        rfl

theorem cell23_1831643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 8, 2].length) (baseStart_1831643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1831643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1831643 prefixEnd_1831643 := by exact prefixLift 1831643
  have htrace : WordTrace (prefixWord ++ tailWord_1831643) baseStart_1831643 baseEnd_1831643 := by
    simpa [prefixWord, tailWord_1831643, baseEnd_1831643] using wordTrace_append hprefix tailTrace_1831643
  have hstable : (prefixWord ++ tailWord_1831643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831643).length < 2 ^ (prefixWord ++ tailWord_1831643).sum := by decide
  have hdescent : baseEnd_1831643 < baseStart_1831643 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831670 : List Nat := [5, 1, 1, 1, 1, 2, 4, 1, 1, 6]
def baseStart_1831670 : Nat := 118140960795 + 1831670 * 2 ^ 59
def prefixEnd_1831670 : Nat := 4983230072969 + 3 ^ 40 * 1831670 * 2
def baseEnd_1831670 : Nat := 313509036806984605467103

theorem tailTrace_1831670 : CollatzResearch.WordTrace tailWord_1831670 prefixEnd_1831670 313509036806984605467103 := by
  unfold tailWord_1831670
  simp only [CollatzResearch.WordTrace]
  refine ⟨4175405829636243073493279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44537662182786592783928309 4175405829636243073493279)
  ·
    refine ⟨6263108744454364610239919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4175405829636243073493279 6263108744454364610239919)
    ·
      refine ⟨9394663116681546915359879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6263108744454364610239919 9394663116681546915359879)
      ·
        refine ⟨14091994675022320373039819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9394663116681546915359879 14091994675022320373039819)
        ·
          refine ⟨21137992012533480559559729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14091994675022320373039819 21137992012533480559559729)
          ·
            refine ⟨15853494009400110419669797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21137992012533480559559729 15853494009400110419669797)
            ·
              refine ⟨2972530126762520703688087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15853494009400110419669797 2972530126762520703688087)
              ·
                refine ⟨4458795190143781055532131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2972530126762520703688087 4458795190143781055532131)
                ·
                  refine ⟨6688192785215671583298197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4458795190143781055532131 6688192785215671583298197)
                  ·
                    refine ⟨313509036806984605467103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6688192785215671583298197 313509036806984605467103)
                    ·
                      rfl

theorem cell23_1831670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 1, 1, 6].length) (baseStart_1831670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1831670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1831670 prefixEnd_1831670 := by exact prefixLift 1831670
  have htrace : WordTrace (prefixWord ++ tailWord_1831670) baseStart_1831670 baseEnd_1831670 := by
    simpa [prefixWord, tailWord_1831670, baseEnd_1831670] using wordTrace_append hprefix tailTrace_1831670
  have hstable : (prefixWord ++ tailWord_1831670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831670).length < 2 ^ (prefixWord ++ tailWord_1831670).sum := by decide
  have hdescent : baseEnd_1831670 < baseStart_1831670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831677 : List Nat := [1, 4, 1, 1, 1, 1, 5, 2, 3, 2, 2]
def baseStart_1831677 : Nat := 118140960795 + 1831677 * 2 ^ 59
def prefixEnd_1831677 : Nat := 4983230072969 + 3 ^ 40 * 1831677 * 2
def baseEnd_1831677 : Nat := 940530704785535289013777

theorem tailTrace_1831677 : CollatzResearch.WordTrace tailWord_1831677 prefixEnd_1831677 940530704785535289013777 := by
  unfold tailWord_1831677
  simp only [CollatzResearch.WordTrace]
  refine ⟨66806748585154529371397285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44537832390103019580931523 66806748585154529371397285)
  ·
    refine ⟨12526265359716474257136991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66806748585154529371397285 12526265359716474257136991)
    ·
      refine ⟨18789398039574711385705487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12526265359716474257136991 18789398039574711385705487)
      ·
        refine ⟨28184097059362067078558231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18789398039574711385705487 28184097059362067078558231)
        ·
          refine ⟨42276145589043100617837347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28184097059362067078558231 42276145589043100617837347)
          ·
            refine ⟨63414218383564650926756021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42276145589043100617837347 63414218383564650926756021)
            ·
              refine ⟨5945082973459186024383377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63414218383564650926756021 5945082973459186024383377)
              ·
                refine ⟨4458812230094389518287533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5945082973459186024383377 4458812230094389518287533)
                ·
                  refine ⟨1672054586285396069357825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4458812230094389518287533 1672054586285396069357825)
                  ·
                    refine ⟨1254040939714047052018369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1672054586285396069357825 1254040939714047052018369)
                    ·
                      refine ⟨940530704785535289013777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1254040939714047052018369 940530704785535289013777)
                      ·
                        rfl

theorem cell23_1831677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 2, 3, 2, 2].length) (baseStart_1831677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1831677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1831677 prefixEnd_1831677 := by exact prefixLift 1831677
  have htrace : WordTrace (prefixWord ++ tailWord_1831677) baseStart_1831677 baseEnd_1831677 := by
    simpa [prefixWord, tailWord_1831677, baseEnd_1831677] using wordTrace_append hprefix tailTrace_1831677
  have hstable : (prefixWord ++ tailWord_1831677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831677).length < 2 ^ (prefixWord ++ tailWord_1831677).sum := by decide
  have hdescent : baseEnd_1831677 < baseStart_1831677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831697 : List Nat := [1, 2, 2, 1, 1, 3, 6, 1, 1, 2, 3]
def baseStart_1831697 : Nat := 118140960795 + 1831697 * 2 ^ 59
def prefixEnd_1831697 : Nat := 4983230072969 + 3 ^ 40 * 1831697 * 2
def baseEnd_1831697 : Nat := 940540974398625210763685

theorem tailTrace_1831697 : CollatzResearch.WordTrace tailWord_1831697 prefixEnd_1831697 940540974398625210763685 := by
  unfold tailWord_1831697
  simp only [CollatzResearch.WordTrace]
  refine ⟨66807478045082072787125345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44538318696721381858083563 66807478045082072787125345)
  ·
    refine ⟨50105608533811554590344009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66807478045082072787125345 50105608533811554590344009)
    ·
      refine ⟨37579206400358665942758007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50105608533811554590344009 37579206400358665942758007)
      ·
        refine ⟨56368809600537998914137011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37579206400358665942758007 56368809600537998914137011)
        ·
          refine ⟨84553214400806998371205517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56368809600537998914137011 84553214400806998371205517)
          ·
            refine ⟨31707455400302624389202069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84553214400806998371205517 31707455400302624389202069)
            ·
              refine ⟨1486286971889185518243847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 31707455400302624389202069 1486286971889185518243847)
              ·
                refine ⟨2229430457833778277365771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1486286971889185518243847 2229430457833778277365771)
                ·
                  refine ⟨3344145686750667416048657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2229430457833778277365771 3344145686750667416048657)
                  ·
                    refine ⟨2508109265063000562036493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3344145686750667416048657 2508109265063000562036493)
                    ·
                      refine ⟨940540974398625210763685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2508109265063000562036493 940540974398625210763685)
                      ·
                        rfl

theorem cell23_1831697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 6, 1, 1, 2, 3].length) (baseStart_1831697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1831697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1831697 prefixEnd_1831697 := by exact prefixLift 1831697
  have htrace : WordTrace (prefixWord ++ tailWord_1831697) baseStart_1831697 baseEnd_1831697 := by
    simpa [prefixWord, tailWord_1831697, baseEnd_1831697] using wordTrace_append hprefix tailTrace_1831697
  have hstable : (prefixWord ++ tailWord_1831697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831697).length < 2 ^ (prefixWord ++ tailWord_1831697).sum := by decide
  have hdescent : baseEnd_1831697 < baseStart_1831697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831734 : List Nat := [5, 1, 2, 2, 2, 2, 2, 7]
def baseStart_1831734 : Nat := 118140960795 + 1831734 * 2 ^ 59
def prefixEnd_1831734 : Nat := 4983230072969 + 3 ^ 40 * 1831734 * 2
def baseEnd_1831734 : Nat := 34835554562327465407445

theorem tailTrace_1831734 : CollatzResearch.WordTrace tailWord_1831734 prefixEnd_1831734 34835554562327465407445 := by
  unfold tailWord_1831734
  simp only [CollatzResearch.WordTrace]
  refine ⟨4175551721621751756638891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44539218363965352070814837 4175551721621751756638891)
  ·
    refine ⟨6263327582432627634958337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4175551721621751756638891 6263327582432627634958337)
    ·
      refine ⟨4697495686824470726218753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6263327582432627634958337 4697495686824470726218753)
      ·
        refine ⟨3523121765118353044664065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4697495686824470726218753 3523121765118353044664065)
        ·
          refine ⟨2642341323838764783498049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3523121765118353044664065 2642341323838764783498049)
          ·
            refine ⟨1981755992879073587623537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2642341323838764783498049 1981755992879073587623537)
            ·
              refine ⟨1486316994659305190717653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1981755992879073587623537 1486316994659305190717653)
              ·
                refine ⟨34835554562327465407445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1486316994659305190717653 34835554562327465407445)
                ·
                  rfl

theorem cell23_1831734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 2, 7].length) (baseStart_1831734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1831734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1831734 prefixEnd_1831734 := by exact prefixLift 1831734
  have htrace : WordTrace (prefixWord ++ tailWord_1831734) baseStart_1831734 baseEnd_1831734 := by
    simpa [prefixWord, tailWord_1831734, baseEnd_1831734] using wordTrace_append hprefix tailTrace_1831734
  have hstable : (prefixWord ++ tailWord_1831734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831734).length < 2 ^ (prefixWord ++ tailWord_1831734).sum := by decide
  have hdescent : baseEnd_1831734 < baseStart_1831734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831745 : List Nat := [1, 2, 5, 3, 1, 2, 1, 3, 1, 2, 2]
def baseStart_1831745 : Nat := 118140960795 + 1831745 * 2 ^ 59
def prefixEnd_1831745 : Nat := 4983230072969 + 3 ^ 40 * 1831745 * 2
def baseEnd_1831745 : Nat := 940565621470041022963465

theorem tailTrace_1831745 : CollatzResearch.WordTrace tailWord_1831745 prefixEnd_1831745 940565621470041022963465 := by
  unfold tailWord_1831745
  simp only [CollatzResearch.WordTrace]
  refine ⟨66809228748908176984872689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44539485832605451323248459 66809228748908176984872689)
  ·
    refine ⟨50106921561681132738654517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66809228748908176984872689 50106921561681132738654517)
    ·
      refine ⟨4697523896407606194248861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50106921561681132738654517 4697523896407606194248861)
      ·
        refine ⟨1761571461152852322843323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4697523896407606194248861 1761571461152852322843323)
        ·
          refine ⟨2642357191729278484264985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1761571461152852322843323 2642357191729278484264985)
          ·
            refine ⟨1981767893796958863198739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2642357191729278484264985 1981767893796958863198739)
            ·
              refine ⟨2972651840695438294798109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1981767893796958863198739 2972651840695438294798109)
              ·
                refine ⟨1114744440260789360549291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2972651840695438294798109 1114744440260789360549291)
                ·
                  refine ⟨1672116660391184040823937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1114744440260789360549291 1672116660391184040823937)
                  ·
                    refine ⟨1254087495293388030617953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1672116660391184040823937 1254087495293388030617953)
                    ·
                      refine ⟨940565621470041022963465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1254087495293388030617953 940565621470041022963465)
                      ·
                        rfl

theorem cell23_1831745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_1831745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1831745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1831745 prefixEnd_1831745 := by exact prefixLift 1831745
  have htrace : WordTrace (prefixWord ++ tailWord_1831745) baseStart_1831745 baseEnd_1831745 := by
    simpa [prefixWord, tailWord_1831745, baseEnd_1831745] using wordTrace_append hprefix tailTrace_1831745
  have hstable : (prefixWord ++ tailWord_1831745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831745).length < 2 ^ (prefixWord ++ tailWord_1831745).sum := by decide
  have hdescent : baseEnd_1831745 < baseStart_1831745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831753 : List Nat := [1, 2, 1, 1, 2, 5, 1, 1, 1, 3, 5]
def baseStart_1831753 : Nat := 118140960795 + 1831753 * 2 ^ 59
def prefixEnd_1831753 : Nat := 4983230072969 + 3 ^ 40 * 1831753 * 2
def baseEnd_1831753 : Nat := 940569729315276991663427

theorem tailTrace_1831753 : CollatzResearch.WordTrace tailWord_1831753 prefixEnd_1831753 940569729315276991663427 := by
  unfold tailWord_1831753
  simp only [CollatzResearch.WordTrace]
  refine ⟨66809520532879194351163913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44539680355252796234109275 66809520532879194351163913)
  ·
    refine ⟨50107140399659395763372935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66809520532879194351163913 50107140399659395763372935)
    ·
      refine ⟨75160710599489093645059403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50107140399659395763372935 75160710599489093645059403)
      ·
        refine ⟨112741065899233640467589105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75160710599489093645059403 112741065899233640467589105)
        ·
          refine ⟨84555799424425230350691829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112741065899233640467589105 84555799424425230350691829)
          ·
            refine ⟨7927106196039865345377359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84555799424425230350691829 7927106196039865345377359)
            ·
              refine ⟨11890659294059798018066039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7927106196039865345377359 11890659294059798018066039)
              ·
                refine ⟨17835988941089697027099059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11890659294059798018066039 17835988941089697027099059)
                ·
                  refine ⟨26753983411634545540648589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17835988941089697027099059 26753983411634545540648589)
                  ·
                    refine ⟨10032743779362954577743221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26753983411634545540648589 10032743779362954577743221)
                    ·
                      refine ⟨940569729315276991663427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10032743779362954577743221 940569729315276991663427)
                      ·
                        rfl

theorem cell23_1831753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 3, 5].length) (baseStart_1831753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1831753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1831753 prefixEnd_1831753 := by exact prefixLift 1831753
  have htrace : WordTrace (prefixWord ++ tailWord_1831753) baseStart_1831753 baseEnd_1831753 := by
    simpa [prefixWord, tailWord_1831753, baseEnd_1831753] using wordTrace_append hprefix tailTrace_1831753
  have hstable : (prefixWord ++ tailWord_1831753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831753).length < 2 ^ (prefixWord ++ tailWord_1831753).sum := by decide
  have hdescent : baseEnd_1831753 < baseStart_1831753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831763 : List Nat := [1, 1, 1, 2, 1, 1, 3, 3, 4, 2, 4]
def baseStart_1831763 : Nat := 118140960795 + 1831763 * 2 ^ 59
def prefixEnd_1831763 : Nat := 4983230072969 + 3 ^ 40 * 1831763 * 2
def baseEnd_1831763 : Nat := 940574864121821952538381

theorem tailTrace_1831763 : CollatzResearch.WordTrace tailWord_1831763 prefixEnd_1831763 940574864121821952538381 := by
  unfold tailWord_1831763
  simp only [CollatzResearch.WordTrace]
  refine ⟨66809885262842966059027943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44539923508561977372685295 66809885262842966059027943)
  ·
    refine ⟨100214827894264449088541915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66809885262842966059027943 100214827894264449088541915)
    ·
      refine ⟨150322241841396673632812873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100214827894264449088541915 150322241841396673632812873)
      ·
        refine ⟨112741681381047505224609655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150322241841396673632812873 112741681381047505224609655)
        ·
          refine ⟨169112522071571257836914483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112741681381047505224609655 169112522071571257836914483)
          ·
            refine ⟨253668783107356886755371725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169112522071571257836914483 253668783107356886755371725)
            ·
              refine ⟨95125793665258832533264397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 253668783107356886755371725 95125793665258832533264397)
              ·
                refine ⟨35672172624472062199974149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95125793665258832533264397 35672172624472062199974149)
                ·
                  refine ⟨6688532367088511662495153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35672172624472062199974149 6688532367088511662495153)
                  ·
                    refine ⟨5016399275316383746871365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6688532367088511662495153 5016399275316383746871365)
                    ·
                      refine ⟨940574864121821952538381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5016399275316383746871365 940574864121821952538381)
                      ·
                        rfl

theorem cell23_1831763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 4, 2, 4].length) (baseStart_1831763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1831763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1831763 prefixEnd_1831763 := by exact prefixLift 1831763
  have htrace : WordTrace (prefixWord ++ tailWord_1831763) baseStart_1831763 baseEnd_1831763 := by
    simpa [prefixWord, tailWord_1831763, baseEnd_1831763] using wordTrace_append hprefix tailTrace_1831763
  have hstable : (prefixWord ++ tailWord_1831763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831763).length < 2 ^ (prefixWord ++ tailWord_1831763).sum := by decide
  have hdescent : baseEnd_1831763 < baseStart_1831763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831778 : List Nat := [3, 3, 2, 1, 3, 2, 2, 1, 2, 1, 3]
def baseStart_1831778 : Nat := 118140960795 + 1831778 * 2 ^ 59
def prefixEnd_1831778 : Nat := 4983230072969 + 3 ^ 40 * 1831778 * 2
def baseEnd_1831778 : Nat := 940582566331639393850813

theorem tailTrace_1831778 : CollatzResearch.WordTrace tailWord_1831778 prefixEnd_1831778 940582566331639393850813 := by
  unfold tailWord_1831778
  simp only [CollatzResearch.WordTrace]
  refine ⟨16702608089447155905205997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44540288238525749080549325 16702608089447155905205997)
  ·
    refine ⟨6263478033542683464452249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16702608089447155905205997 6263478033542683464452249)
    ·
      refine ⟨4697608525157012598339187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6263478033542683464452249 4697608525157012598339187)
      ·
        refine ⟨7046412787735518897508781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4697608525157012598339187 7046412787735518897508781)
        ·
          refine ⟨2642404795400819586565793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7046412787735518897508781 2642404795400819586565793)
          ·
            refine ⟨1981803596550614689924345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2642404795400819586565793 1981803596550614689924345)
            ·
              refine ⟨1486352697412961017443259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1981803596550614689924345 1486352697412961017443259)
              ·
                refine ⟨2229529046119441526164889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1486352697412961017443259 2229529046119441526164889)
                ·
                  refine ⟨1672146784589581144623667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2229529046119441526164889 1672146784589581144623667)
                  ·
                    refine ⟨2508220176884371716935501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1672146784589581144623667 2508220176884371716935501)
                    ·
                      refine ⟨940582566331639393850813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2508220176884371716935501 940582566331639393850813)
                      ·
                        rfl

theorem cell23_1831778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 2, 1, 2, 1, 3].length) (baseStart_1831778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1831778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1831778 prefixEnd_1831778 := by exact prefixLift 1831778
  have htrace : WordTrace (prefixWord ++ tailWord_1831778) baseStart_1831778 baseEnd_1831778 := by
    simpa [prefixWord, tailWord_1831778, baseEnd_1831778] using wordTrace_append hprefix tailTrace_1831778
  have hstable : (prefixWord ++ tailWord_1831778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831778).length < 2 ^ (prefixWord ++ tailWord_1831778).sum := by decide
  have hdescent : baseEnd_1831778 < baseStart_1831778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831803 : List Nat := [1, 1, 1, 1, 1, 5, 2, 3, 1, 7]
def baseStart_1831803 : Nat := 118140960795 + 1831803 * 2 ^ 59
def prefixEnd_1831803 : Nat := 4983230072969 + 3 ^ 40 * 1831803 * 2
def baseEnd_1831803 : Nat := 313531801116000598679399

theorem tailTrace_1831803 : CollatzResearch.WordTrace tailWord_1831803 prefixEnd_1831803 313531801116000598679399 := by
  unfold tailWord_1831803
  simp only [CollatzResearch.WordTrace]
  refine ⟨66811344182698052890484063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44540896121798701926989375 66811344182698052890484063)
  ·
    refine ⟨100217016274047079335726095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66811344182698052890484063 100217016274047079335726095)
    ·
      refine ⟨150325524411070619003589143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100217016274047079335726095 150325524411070619003589143)
      ·
        refine ⟨225488286616605928505383715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150325524411070619003589143 225488286616605928505383715)
        ·
          refine ⟨338232429924908892758075573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225488286616605928505383715 338232429924908892758075573)
          ·
            refine ⟨31709290305460208696069585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 338232429924908892758075573 31709290305460208696069585)
            ·
              refine ⟨23781967729095156522052189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31709290305460208696069585 23781967729095156522052189)
              ·
                refine ⟨8918237898410683695769571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23781967729095156522052189 8918237898410683695769571)
                ·
                  refine ⟨13377356847616025543654357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8918237898410683695769571 13377356847616025543654357)
                  ·
                    refine ⟨313531801116000598679399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13377356847616025543654357 313531801116000598679399)
                    ·
                      rfl

theorem cell23_1831803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 3, 1, 7].length) (baseStart_1831803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1831803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1831803 prefixEnd_1831803 := by exact prefixLift 1831803
  have htrace : WordTrace (prefixWord ++ tailWord_1831803) baseStart_1831803 baseEnd_1831803 := by
    simpa [prefixWord, tailWord_1831803, baseEnd_1831803] using wordTrace_append hprefix tailTrace_1831803
  have hstable : (prefixWord ++ tailWord_1831803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831803).length < 2 ^ (prefixWord ++ tailWord_1831803).sum := by decide
  have hdescent : baseEnd_1831803 < baseStart_1831803 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831820 : List Nat := [2, 2, 1, 2, 1, 2, 4, 2, 2, 5]
def baseStart_1831820 : Nat := 118140960795 + 1831820 * 2 ^ 59
def prefixEnd_1831820 : Nat := 4983230072969 + 3 ^ 40 * 1831820 * 2
def baseEnd_1831820 : Nat := 313534710839709409841873

theorem tailTrace_1831820 : CollatzResearch.WordTrace tailWord_1831820 prefixEnd_1831820 313534710839709409841873 := by
  unfold tailWord_1831820
  simp only [CollatzResearch.WordTrace]
  refine ⟨33405982111818232396926457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44541309482424309862568609 33405982111818232396926457)
  ·
    refine ⟨25054486583863674297694843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33405982111818232396926457 25054486583863674297694843)
    ·
      refine ⟨37581729875795511446542265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25054486583863674297694843 37581729875795511446542265)
      ·
        refine ⟨28186297406846633584906699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37581729875795511446542265 28186297406846633584906699)
        ·
          refine ⟨42279446110269950377360049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28186297406846633584906699 42279446110269950377360049)
          ·
            refine ⟨31709584582702462783020037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42279446110269950377360049 31709584582702462783020037)
            ·
              refine ⟨5945547109256711771816257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31709584582702462783020037 5945547109256711771816257)
              ·
                refine ⟨4459160331942533828862193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5945547109256711771816257 4459160331942533828862193)
                ·
                  refine ⟨3344370248956900371646645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4459160331942533828862193 3344370248956900371646645)
                  ·
                    refine ⟨313534710839709409841873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3344370248956900371646645 313534710839709409841873)
                    ·
                      rfl

theorem cell23_1831820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 2, 2, 5].length) (baseStart_1831820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1831820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1831820 prefixEnd_1831820 := by exact prefixLift 1831820
  have htrace : WordTrace (prefixWord ++ tailWord_1831820) baseStart_1831820 baseEnd_1831820 := by
    simpa [prefixWord, tailWord_1831820, baseEnd_1831820] using wordTrace_append hprefix tailTrace_1831820
  have hstable : (prefixWord ++ tailWord_1831820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831820).length < 2 ^ (prefixWord ++ tailWord_1831820).sum := by decide
  have hdescent : baseEnd_1831820 < baseStart_1831820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831833 : List Nat := [1, 2, 1, 2, 1, 3, 1, 2, 2, 8]
def baseStart_1831833 : Nat := 118140960795 + 1831833 * 2 ^ 59
def prefixEnd_1831833 : Nat := 4983230072969 + 3 ^ 40 * 1831833 * 2
def baseEnd_1831833 : Nat := 313536935922545559554353

theorem tailTrace_1831833 : CollatzResearch.WordTrace tailWord_1831833 prefixEnd_1831833 313536935922545559554353 := by
  unfold tailWord_1831833
  simp only [CollatzResearch.WordTrace]
  refine ⟨66812438372589368014076153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44541625581726245342717435 66812438372589368014076153)
  ·
    refine ⟨50109328779442026010557115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66812438372589368014076153 50109328779442026010557115)
    ·
      refine ⟨75163993169163039015835673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50109328779442026010557115 75163993169163039015835673)
      ·
        refine ⟨56372994876872279261876755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75163993169163039015835673 56372994876872279261876755)
        ·
          refine ⟨84559492315308418892815133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56372994876872279261876755 84559492315308418892815133)
          ·
            refine ⟨31709809618240657084805675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84559492315308418892815133 31709809618240657084805675)
            ·
              refine ⟨47564714427360985627208513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31709809618240657084805675 47564714427360985627208513)
              ·
                refine ⟨35673535820520739220406385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47564714427360985627208513 35673535820520739220406385)
                ·
                  refine ⟨26755151865390554415304789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35673535820520739220406385 26755151865390554415304789)
                  ·
                    refine ⟨313536935922545559554353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 26755151865390554415304789 313536935922545559554353)
                    ·
                      rfl

theorem cell23_1831833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 8].length) (baseStart_1831833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1831833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1831833 prefixEnd_1831833 := by exact prefixLift 1831833
  have htrace : WordTrace (prefixWord ++ tailWord_1831833) baseStart_1831833 baseEnd_1831833 := by
    simpa [prefixWord, tailWord_1831833, baseEnd_1831833] using wordTrace_append hprefix tailTrace_1831833
  have hstable : (prefixWord ++ tailWord_1831833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831833).length < 2 ^ (prefixWord ++ tailWord_1831833).sum := by decide
  have hdescent : baseEnd_1831833 < baseStart_1831833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831840 : List Nat := [2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 4]
def baseStart_1831840 : Nat := 118140960795 + 1831840 * 2 ^ 59
def prefixEnd_1831840 : Nat := 4983230072969 + 3 ^ 40 * 1831840 * 2
def baseEnd_1831840 : Nat := 940614402132218151275527

theorem tailTrace_1831840 : CollatzResearch.WordTrace tailWord_1831840 prefixEnd_1831840 940614402132218151275527 := by
  unfold tailWord_1831840
  simp only [CollatzResearch.WordTrace]
  refine ⟨33406346841782004104790487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44541795789042672139720649 33406346841782004104790487)
  ·
    refine ⟨50109520262673006157185731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33406346841782004104790487 50109520262673006157185731)
    ·
      refine ⟨75164280394009509235778597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50109520262673006157185731 75164280394009509235778597)
      ·
        refine ⟨14093302573876782981708487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75164280394009509235778597 14093302573876782981708487)
        ·
          refine ⟨21139953860815174472562731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14093302573876782981708487 21139953860815174472562731)
          ·
            refine ⟨31709930791222761708844097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21139953860815174472562731 31709930791222761708844097)
            ·
              refine ⟨23782448093417071281633073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31709930791222761708844097 23782448093417071281633073)
              ·
                refine ⟨17836836070062803461224805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23782448093417071281633073 17836836070062803461224805)
                ·
                  refine ⟨3344406763136775648979651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17836836070062803461224805 3344406763136775648979651)
                  ·
                    refine ⟨5016610144705163473469477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3344406763136775648979651 5016610144705163473469477)
                    ·
                      refine ⟨940614402132218151275527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5016610144705163473469477 940614402132218151275527)
                      ·
                        rfl

theorem cell23_1831840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_1831840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1831840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1831840 prefixEnd_1831840 := by exact prefixLift 1831840
  have htrace : WordTrace (prefixWord ++ tailWord_1831840) baseStart_1831840 baseEnd_1831840 := by
    simpa [prefixWord, tailWord_1831840, baseEnd_1831840] using wordTrace_append hprefix tailTrace_1831840
  have hstable : (prefixWord ++ tailWord_1831840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831840).length < 2 ^ (prefixWord ++ tailWord_1831840).sum := by decide
  have hdescent : baseEnd_1831840 < baseStart_1831840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831857 : List Nat := [1, 2, 2, 4, 3, 1, 1, 1, 1, 3, 4]
def baseStart_1831857 : Nat := 118140960795 + 1831857 * 2 ^ 59
def prefixEnd_1831857 : Nat := 4983230072969 + 3 ^ 40 * 1831857 * 2
def baseEnd_1831857 : Nat := 940623131303344584762949

theorem tailTrace_1831857 : CollatzResearch.WordTrace tailWord_1831857 prefixEnd_1831857 940623131303344584762949 := by
  unfold tailWord_1831857
  simp only [CollatzResearch.WordTrace]
  refine ⟨66813313724502420112949825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44542209149668280075299883 66813313724502420112949825)
  ·
    refine ⟨50109985293376815084712369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66813313724502420112949825 50109985293376815084712369)
    ·
      refine ⟨37582488970032611313534277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50109985293376815084712369 37582488970032611313534277)
      ·
        refine ⟨7046716681881114621287677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37582488970032611313534277 7046716681881114621287677)
        ·
          refine ⟨2642518755705417982982879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7046716681881114621287677 2642518755705417982982879)
          ·
            refine ⟨3963778133558126974474319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2642518755705417982982879 3963778133558126974474319)
            ·
              refine ⟨5945667200337190461711479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3963778133558126974474319 5945667200337190461711479)
              ·
                refine ⟨8918500800505785692567219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5945667200337190461711479 8918500800505785692567219)
                ·
                  refine ⟨13377751200758678538850829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8918500800505785692567219 13377751200758678538850829)
                  ·
                    refine ⟨5016656700284504452069061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13377751200758678538850829 5016656700284504452069061)
                    ·
                      refine ⟨940623131303344584762949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5016656700284504452069061 940623131303344584762949)
                      ·
                        rfl

theorem cell23_1831857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_1831857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1831857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1831857 prefixEnd_1831857 := by exact prefixLift 1831857
  have htrace : WordTrace (prefixWord ++ tailWord_1831857) baseStart_1831857 baseEnd_1831857 := by
    simpa [prefixWord, tailWord_1831857, baseEnd_1831857] using wordTrace_append hprefix tailTrace_1831857
  have hstable : (prefixWord ++ tailWord_1831857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831857).length < 2 ^ (prefixWord ++ tailWord_1831857).sum := by decide
  have hdescent : baseEnd_1831857 < baseStart_1831857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831870 : List Nat := [4, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6]
def baseStart_1831870 : Nat := 118140960795 + 1831870 * 2 ^ 59
def prefixEnd_1831870 : Nat := 4983230072969 + 3 ^ 40 * 1831870 * 2
def baseEnd_1831870 : Nat := 940629806551853033900389

theorem tailTrace_1831870 : CollatzResearch.WordTrace tailWord_1831870 prefixEnd_1831870 940629806551853033900389 := by
  unfold tailWord_1831870
  simp only [CollatzResearch.WordTrace]
  refine ⟨8351723484181915416646633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44542525248970215555448709 8351723484181915416646633)
  ·
    refine ⟨6263792613136436562484975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8351723484181915416646633 6263792613136436562484975)
    ·
      refine ⟨9395688919704654843727463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6263792613136436562484975 9395688919704654843727463)
      ·
        refine ⟨14093533379556982265591195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9395688919704654843727463 14093533379556982265591195)
        ·
          refine ⟨21140300069335473398386793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14093533379556982265591195 21140300069335473398386793)
          ·
            refine ⟨15855225052001605048790095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21140300069335473398386793 15855225052001605048790095)
            ·
              refine ⟨23782837578002407573185143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15855225052001605048790095 23782837578002407573185143)
              ·
                refine ⟨35674256367003611359777715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23782837578002407573185143 35674256367003611359777715)
                ·
                  refine ⟨53511384550505417039666573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35674256367003611359777715 53511384550505417039666573)
                  ·
                    refine ⟨20066769206439531389874965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53511384550505417039666573 20066769206439531389874965)
                    ·
                      refine ⟨940629806551853033900389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20066769206439531389874965 940629806551853033900389)
                      ·
                        rfl

theorem cell23_1831870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_1831870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1831870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1831870 prefixEnd_1831870 := by exact prefixLift 1831870
  have htrace : WordTrace (prefixWord ++ tailWord_1831870) baseStart_1831870 baseEnd_1831870 := by
    simpa [prefixWord, tailWord_1831870, baseEnd_1831870] using wordTrace_append hprefix tailTrace_1831870
  have hstable : (prefixWord ++ tailWord_1831870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831870).length < 2 ^ (prefixWord ++ tailWord_1831870).sum := by decide
  have hdescent : baseEnd_1831870 < baseStart_1831870 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831884 : List Nat := [2, 2, 1, 4, 1, 1, 1, 6, 1, 4]
def baseStart_1831884 : Nat := 118140960795 + 1831884 * 2 ^ 59
def prefixEnd_1831884 : Nat := 4983230072969 + 3 ^ 40 * 1831884 * 2
def baseEnd_1831884 : Nat := 313545665093671993041775

theorem tailTrace_1831884 : CollatzResearch.WordTrace tailWord_1831884 prefixEnd_1831884 313545665093671993041775 := by
  unfold tailWord_1831884
  simp only [CollatzResearch.WordTrace]
  refine ⟨33407149247702301862091353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44542865663603069149455137 33407149247702301862091353)
  ·
    refine ⟨25055361935776726396568515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33407149247702301862091353 25055361935776726396568515)
    ·
      refine ⟨37583042903665089594852773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25055361935776726396568515 37583042903665089594852773)
      ·
        refine ⟨7046820544437204299034895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37583042903665089594852773 7046820544437204299034895)
        ·
          refine ⟨10570230816655806448552343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7046820544437204299034895 10570230816655806448552343)
          ·
            refine ⟨15855346224983709672828515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10570230816655806448552343 15855346224983709672828515)
            ·
              refine ⟨23783019337475564509242773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15855346224983709672828515 23783019337475564509242773)
              ·
                refine ⟨1114829031444167086370755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23783019337475564509242773 1114829031444167086370755)
                ·
                  refine ⟨1672243547166250629556133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1114829031444167086370755 1672243547166250629556133)
                  ·
                    refine ⟨313545665093671993041775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1672243547166250629556133 313545665093671993041775)
                    ·
                      rfl

theorem cell23_1831884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 6, 1, 4].length) (baseStart_1831884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1831884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1831884 prefixEnd_1831884 := by exact prefixLift 1831884
  have htrace : WordTrace (prefixWord ++ tailWord_1831884) baseStart_1831884 baseEnd_1831884 := by
    simpa [prefixWord, tailWord_1831884, baseEnd_1831884] using wordTrace_append hprefix tailTrace_1831884
  have hstable : (prefixWord ++ tailWord_1831884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831884).length < 2 ^ (prefixWord ++ tailWord_1831884).sum := by decide
  have hdescent : baseEnd_1831884 < baseStart_1831884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831894 : List Nat := [5, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3]
def baseStart_1831894 : Nat := 118140960795 + 1831894 * 2 ^ 59
def prefixEnd_1831894 : Nat := 4983230072969 + 3 ^ 40 * 1831894 * 2
def baseEnd_1831894 : Nat := 940642130087560940000279

theorem tailTrace_1831894 : CollatzResearch.WordTrace tailWord_1831894 prefixEnd_1831894 940642130087560940000279 := by
  unfold tailWord_1831894
  simp only [CollatzResearch.WordTrace]
  refine ⟨4175916451585523464502921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44543108816912250288031157 4175916451585523464502921)
  ·
    refine ⟨3131937338689142598377191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4175916451585523464502921 3131937338689142598377191)
    ·
      refine ⟨4697906008033713897565787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3131937338689142598377191 4697906008033713897565787)
      ·
        refine ⟨7046859012050570846348681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4697906008033713897565787 7046859012050570846348681)
        ·
          refine ⟨5285144259037928134761511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7046859012050570846348681 5285144259037928134761511)
          ·
            refine ⟨7927716388556892202142267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5285144259037928134761511 7927716388556892202142267)
            ·
              refine ⟨11891574582835338303213401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7927716388556892202142267 11891574582835338303213401)
              ·
                refine ⟨8918680937126503727410051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11891574582835338303213401 8918680937126503727410051)
                ·
                  refine ⟨13378021405689755591115077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8918680937126503727410051 13378021405689755591115077)
                  ·
                    refine ⟨2508379013566829173334077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13378021405689755591115077 2508379013566829173334077)
                    ·
                      refine ⟨940642130087560940000279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2508379013566829173334077 940642130087560940000279)
                      ·
                        rfl

theorem cell23_1831894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_1831894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1831894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1831894 prefixEnd_1831894 := by exact prefixLift 1831894
  have htrace : WordTrace (prefixWord ++ tailWord_1831894) baseStart_1831894 baseEnd_1831894 := by
    simpa [prefixWord, tailWord_1831894, baseEnd_1831894] using wordTrace_append hprefix tailTrace_1831894
  have hstable : (prefixWord ++ tailWord_1831894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831894).length < 2 ^ (prefixWord ++ tailWord_1831894).sum := by decide
  have hdescent : baseEnd_1831894 < baseStart_1831894 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831918 : List Nat := [4, 1, 2, 1, 4, 2, 1, 3, 1, 4]
def baseStart_1831918 : Nat := 118140960795 + 1831918 * 2 ^ 59
def prefixEnd_1831918 : Nat := 4983230072969 + 3 ^ 40 * 1831918 * 2
def baseEnd_1831918 : Nat := 313551484541089615366723

theorem tailTrace_1831918 : CollatzResearch.WordTrace tailWord_1831918 prefixEnd_1831918 313551484541089615366723 := by
  unfold tailWord_1831918
  simp only [CollatzResearch.WordTrace]
  refine ⟨8351942322160178441365051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44543692384854285020613605 8351942322160178441365051)
  ·
    refine ⟨12527913483240267662047577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8351942322160178441365051 12527913483240267662047577)
    ·
      refine ⟨9395935112430200746535683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12527913483240267662047577 9395935112430200746535683)
      ·
        refine ⟨14093902668645301119803525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9395935112430200746535683 14093902668645301119803525)
        ·
          refine ⟨2642606750370993959963161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14093902668645301119803525 2642606750370993959963161)
          ·
            refine ⟨1981955062778245469972371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2642606750370993959963161 1981955062778245469972371)
            ·
              refine ⟨2972932594167368204958557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1981955062778245469972371 2972932594167368204958557)
              ·
                refine ⟨1114849722812763076859459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2972932594167368204958557 1114849722812763076859459)
                ·
                  refine ⟨1672274584219144615289189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1114849722812763076859459 1672274584219144615289189)
                  ·
                    refine ⟨313551484541089615366723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1672274584219144615289189 313551484541089615366723)
                    ·
                      rfl

theorem cell23_1831918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 3, 1, 4].length) (baseStart_1831918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1831918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1831918 prefixEnd_1831918 := by exact prefixLift 1831918
  have htrace : WordTrace (prefixWord ++ tailWord_1831918) baseStart_1831918 baseEnd_1831918 := by
    simpa [prefixWord, tailWord_1831918, baseEnd_1831918] using wordTrace_append hprefix tailTrace_1831918
  have hstable : (prefixWord ++ tailWord_1831918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831918).length < 2 ^ (prefixWord ++ tailWord_1831918).sum := by decide
  have hdescent : baseEnd_1831918 < baseStart_1831918 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831964 : List Nat := [2, 2, 3, 1, 4, 1, 1, 1, 3, 1, 4]
def baseStart_1831964 : Nat := 118140960795 + 1831964 * 2 ^ 59
def prefixEnd_1831964 : Nat := 4983230072969 + 3 ^ 40 * 1831964 * 2
def baseEnd_1831964 : Nat := 940678073733375666124957

theorem tailTrace_1831964 : CollatzResearch.WordTrace tailWord_1831964 prefixEnd_1831964 940678073733375666124957 := by
  unfold tailWord_1831964
  simp only [CollatzResearch.WordTrace]
  refine ⟨33408608167557388693547473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44544810890076518258063297 33408608167557388693547473)
  ·
    refine ⟨25056456125668041520160605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33408608167557388693547473 25056456125668041520160605)
    ·
      refine ⟨9396171047125515570060227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25056456125668041520160605 9396171047125515570060227)
      ·
        refine ⟨14094256570688273355090341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9396171047125515570060227 14094256570688273355090341)
        ·
          refine ⟨2642673107004051254079439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14094256570688273355090341 2642673107004051254079439)
          ·
            refine ⟨3964009660506076881119159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2642673107004051254079439 3964009660506076881119159)
            ·
              refine ⟨5946014490759115321678739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3964009660506076881119159 5946014490759115321678739)
              ·
                refine ⟨8919021736138672982518109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5946014490759115321678739 8919021736138672982518109)
                ·
                  refine ⟨3344633151052002368444291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8919021736138672982518109 3344633151052002368444291)
                  ·
                    refine ⟨5016949726578003552666437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3344633151052002368444291 5016949726578003552666437)
                    ·
                      refine ⟨940678073733375666124957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5016949726578003552666437 940678073733375666124957)
                      ·
                        rfl

theorem cell23_1831964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 1, 3, 1, 4].length) (baseStart_1831964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1831964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1831964 prefixEnd_1831964 := by exact prefixLift 1831964
  have htrace : WordTrace (prefixWord ++ tailWord_1831964) baseStart_1831964 baseEnd_1831964 := by
    simpa [prefixWord, tailWord_1831964, baseEnd_1831964] using wordTrace_append hprefix tailTrace_1831964
  have hstable : (prefixWord ++ tailWord_1831964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831964).length < 2 ^ (prefixWord ++ tailWord_1831964).sum := by decide
  have hdescent : baseEnd_1831964 < baseStart_1831964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831968 : List Nat := [2, 1, 1, 7, 1, 1, 2, 1, 2, 3, 2]
def baseStart_1831968 : Nat := 118140960795 + 1831968 * 2 ^ 59
def prefixEnd_1831968 : Nat := 4983230072969 + 3 ^ 40 * 1831968 * 2
def baseEnd_1831968 : Nat := 940680127655993650474939

theorem tailTrace_1831968 : CollatzResearch.WordTrace tailWord_1831968 prefixEnd_1831968 940680127655993650474939 := by
  unfold tailWord_1831968
  simp only [CollatzResearch.WordTrace]
  refine ⟨33408681113550143035120279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44544908151400190713493705 33408681113550143035120279)
  ·
    refine ⟨50113021670325214552680419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33408681113550143035120279 50113021670325214552680419)
    ·
      refine ⟨75169532505487821829020629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50113021670325214552680419 75169532505487821829020629)
      ·
        refine ⟨1761785918097370824117671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 75169532505487821829020629 1761785918097370824117671)
        ·
          refine ⟨2642678877146056236176507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1761785918097370824117671 2642678877146056236176507)
          ·
            refine ⟨3964018315719084354264761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2642678877146056236176507 3964018315719084354264761)
            ·
              refine ⟨2973013736789313265698571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3964018315719084354264761 2973013736789313265698571)
              ·
                refine ⟨4459520605183969898547857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2973013736789313265698571 4459520605183969898547857)
                ·
                  refine ⟨3344640453887977423910893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4459520605183969898547857 3344640453887977423910893)
                  ·
                    refine ⟨1254240170207991533966585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3344640453887977423910893 1254240170207991533966585)
                    ·
                      refine ⟨940680127655993650474939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1254240170207991533966585 940680127655993650474939)
                      ·
                        rfl

theorem cell23_1831968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_1831968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1831968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1831968 prefixEnd_1831968 := by exact prefixLift 1831968
  have htrace : WordTrace (prefixWord ++ tailWord_1831968) baseStart_1831968 baseEnd_1831968 := by
    simpa [prefixWord, tailWord_1831968, baseEnd_1831968] using wordTrace_append hprefix tailTrace_1831968
  have hstable : (prefixWord ++ tailWord_1831968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831968).length < 2 ^ (prefixWord ++ tailWord_1831968).sum := by decide
  have hdescent : baseEnd_1831968 < baseStart_1831968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832000 : List Nat := [2, 1, 1, 2, 2, 3, 1, 1, 1, 9]
def baseStart_1832000 : Nat := 118140960795 + 1832000 * 2 ^ 59
def prefixEnd_1832000 : Nat := 4983230072969 + 3 ^ 40 * 1832000 * 2
def baseEnd_1832000 : Nat := 313565519678979175091597

theorem tailTrace_1832000 : CollatzResearch.WordTrace tailWord_1832000 prefixEnd_1832000 313565519678979175091597 := by
  unfold tailWord_1832000
  simp only [CollatzResearch.WordTrace]
  refine ⟨33409264681492177767702727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44545686241989570356936969 33409264681492177767702727)
  ·
    refine ⟨50113897022238266651554091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33409264681492177767702727 50113897022238266651554091)
    ·
      refine ⟨75170845533357399977331137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50113897022238266651554091 75170845533357399977331137)
      ·
        refine ⟨56378134150018049982998353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75170845533357399977331137 56378134150018049982998353)
        ·
          refine ⟨42283600612513537487248765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56378134150018049982998353 42283600612513537487248765)
          ·
            refine ⟨15856350229692576557718287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42283600612513537487248765 15856350229692576557718287)
            ·
              refine ⟨23784525344538864836577431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15856350229692576557718287 23784525344538864836577431)
              ·
                refine ⟨35676788016808297254866147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23784525344538864836577431 35676788016808297254866147)
                ·
                  refine ⟨53515182025212445882299221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35676788016808297254866147 53515182025212445882299221)
                  ·
                    refine ⟨313565519678979175091597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 53515182025212445882299221 313565519678979175091597)
                    ·
                      rfl

theorem cell23_1832000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 1, 9].length) (baseStart_1832000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1832000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1832000 prefixEnd_1832000 := by exact prefixLift 1832000
  have htrace : WordTrace (prefixWord ++ tailWord_1832000) baseStart_1832000 baseEnd_1832000 := by
    simpa [prefixWord, tailWord_1832000, baseEnd_1832000] using wordTrace_append hprefix tailTrace_1832000
  have hstable : (prefixWord ++ tailWord_1832000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832000).length < 2 ^ (prefixWord ++ tailWord_1832000).sum := by decide
  have hdescent : baseEnd_1832000 < baseStart_1832000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832014 : List Nat := [4, 1, 1, 1, 1, 3, 4, 1, 1, 3, 3]
def baseStart_1832014 : Nat := 118140960795 + 1832014 * 2 ^ 59
def prefixEnd_1832014 : Nat := 4983230072969 + 3 ^ 40 * 1832014 * 2
def baseEnd_1832014 : Nat := 940703747766100470499727

theorem tailTrace_1832014 : CollatzResearch.WordTrace tailWord_1832014 prefixEnd_1832014 940703747766100470499727 := by
  unfold tailWord_1832014
  simp only [CollatzResearch.WordTrace]
  refine ⟨8352379998116704490801887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44546026656622423950943397 8352379998116704490801887)
  ·
    refine ⟨12528569997175056736202831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8352379998116704490801887 12528569997175056736202831)
    ·
      refine ⟨18792854995762585104304247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12528569997175056736202831 18792854995762585104304247)
      ·
        refine ⟨28189282493643877656456371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18792854995762585104304247 28189282493643877656456371)
        ·
          refine ⟨42283923740465816484684557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28189282493643877656456371 42283923740465816484684557)
          ·
            refine ⟨15856471402674681181756709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42283923740465816484684557 15856471402674681181756709)
            ·
              refine ⟨2973088388001502721579383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15856471402674681181756709 2973088388001502721579383)
              ·
                refine ⟨4459632582002254082369075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2973088388001502721579383 4459632582002254082369075)
                ·
                  refine ⟨6689448873003381123553613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4459632582002254082369075 6689448873003381123553613)
                  ·
                    refine ⟨2508543327376267921332605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6689448873003381123553613 2508543327376267921332605)
                    ·
                      refine ⟨940703747766100470499727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2508543327376267921332605 940703747766100470499727)
                      ·
                        rfl

theorem cell23_1832014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 1, 1, 3, 3].length) (baseStart_1832014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1832014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1832014 prefixEnd_1832014 := by exact prefixLift 1832014
  have htrace : WordTrace (prefixWord ++ tailWord_1832014) baseStart_1832014 baseEnd_1832014 := by
    simpa [prefixWord, tailWord_1832014, baseEnd_1832014] using wordTrace_append hprefix tailTrace_1832014
  have hstable : (prefixWord ++ tailWord_1832014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832014).length < 2 ^ (prefixWord ++ tailWord_1832014).sum := by decide
  have hdescent : baseEnd_1832014 < baseStart_1832014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832024 : List Nat := [2, 1, 2, 2, 1, 3, 1, 3, 3, 3, 2]
def baseStart_1832024 : Nat := 118140960795 + 1832024 * 2 ^ 59
def prefixEnd_1832024 : Nat := 4983230072969 + 3 ^ 40 * 1832024 * 2
def baseEnd_1832024 : Nat := 940708882572645431374681

theorem tailTrace_1832024 : CollatzResearch.WordTrace tailWord_1832024 prefixEnd_1832024 940708882572645431374681 := by
  unfold tailWord_1832024
  simp only [CollatzResearch.WordTrace]
  refine ⟨33409702357448703817139563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44546269809931605089519417 33409702357448703817139563)
  ·
    refine ⟨50114553536173055725709345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33409702357448703817139563 50114553536173055725709345)
    ·
      refine ⟨37585915152129791794282009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50114553536173055725709345 37585915152129791794282009)
      ·
        refine ⟨28189436364097343845711507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37585915152129791794282009 28189436364097343845711507)
        ·
          refine ⟨42284154546146015768567261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28189436364097343845711507 42284154546146015768567261)
          ·
            refine ⟨15856557954804755913212723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42284154546146015768567261 15856557954804755913212723)
            ·
              refine ⟨23784836932207133869819085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15856557954804755913212723 23784836932207133869819085)
              ·
                refine ⟨8919313849577675201182157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23784836932207133869819085 8919313849577675201182157)
                ·
                  refine ⟨3344742693591628200443309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8919313849577675201182157 3344742693591628200443309)
                  ·
                    refine ⟨1254278510096860575166241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3344742693591628200443309 1254278510096860575166241)
                    ·
                      refine ⟨940708882572645431374681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1254278510096860575166241 940708882572645431374681)
                      ·
                        rfl

theorem cell23_1832024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 3, 3, 3, 2].length) (baseStart_1832024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1832024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1832024 prefixEnd_1832024 := by exact prefixLift 1832024
  have htrace : WordTrace (prefixWord ++ tailWord_1832024) baseStart_1832024 baseEnd_1832024 := by
    simpa [prefixWord, tailWord_1832024, baseEnd_1832024] using wordTrace_append hprefix tailTrace_1832024
  have hstable : (prefixWord ++ tailWord_1832024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832024).length < 2 ^ (prefixWord ++ tailWord_1832024).sum := by decide
  have hdescent : baseEnd_1832024 < baseStart_1832024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832041 : List Nat := [1, 2, 1, 1, 1, 7, 1, 3, 1, 3, 2]
def baseStart_1832041 : Nat := 118140960795 + 1832041 * 2 ^ 59
def prefixEnd_1832041 : Nat := 4983230072969 + 3 ^ 40 * 1832041 * 2
def baseEnd_1832041 : Nat := 940717611743771864862103

theorem tailTrace_1832041 : CollatzResearch.WordTrace tailWord_1832041 prefixEnd_1832041 940717611743771864862103 := by
  unfold tailWord_1832041
  simp only [CollatzResearch.WordTrace]
  refine ⟨66820024755835819537647977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44546683170557213025098651 66820024755835819537647977)
  ·
    refine ⟨50115018566876864653235983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66820024755835819537647977 50115018566876864653235983)
    ·
      refine ⟨75172527850315296979853975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50115018566876864653235983 75172527850315296979853975)
      ·
        refine ⟨112758791775472945469780963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75172527850315296979853975 112758791775472945469780963)
        ·
          refine ⟨169138187663209418204671445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112758791775472945469780963 169138187663209418204671445)
          ·
            refine ⟨3964176273356470739171987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 169138187663209418204671445 3964176273356470739171987)
            ·
              refine ⟨5946264410034706108757981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3964176273356470739171987 5946264410034706108757981)
              ·
                refine ⟨2229849153763014790784243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5946264410034706108757981 2229849153763014790784243)
                ·
                  refine ⟨3344773730644522186176365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2229849153763014790784243 3344773730644522186176365)
                  ·
                    refine ⟨1254290148991695819816137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3344773730644522186176365 1254290148991695819816137)
                    ·
                      refine ⟨940717611743771864862103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1254290148991695819816137 940717611743771864862103)
                      ·
                        rfl

theorem cell23_1832041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 3, 1, 3, 2].length) (baseStart_1832041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1832041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1832041 prefixEnd_1832041 := by exact prefixLift 1832041
  have htrace : WordTrace (prefixWord ++ tailWord_1832041) baseStart_1832041 baseEnd_1832041 := by
    simpa [prefixWord, tailWord_1832041, baseEnd_1832041] using wordTrace_append hprefix tailTrace_1832041
  have hstable : (prefixWord ++ tailWord_1832041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832041).length < 2 ^ (prefixWord ++ tailWord_1832041).sum := by decide
  have hdescent : baseEnd_1832041 < baseStart_1832041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832062 : List Nat := [4, 2, 4, 1, 2, 1, 1, 1, 1, 2, 4]
def baseStart_1832062 : Nat := 118140960795 + 1832062 * 2 ^ 59
def prefixEnd_1832062 : Nat := 4983230072969 + 3 ^ 40 * 1832062 * 2
def baseEnd_1832062 : Nat := 940728394837516282699507

theorem tailTrace_1832062 : CollatzResearch.WordTrace tailWord_1832062 prefixEnd_1832062 940728394837516282699507 := by
  unfold tailWord_1832062
  simp only [CollatzResearch.WordTrace]
  refine ⟨8352598836094967515520305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44547193792506493416108293 8352598836094967515520305)
  ·
    refine ⟨6264449127071225636640229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8352598836094967515520305 6264449127071225636640229)
    ·
      refine ⟨1174584211325854806870043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6264449127071225636640229 1174584211325854806870043)
      ·
        refine ⟨1761876316988782210305065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1174584211325854806870043 1761876316988782210305065)
        ·
          refine ⟨1321407237741586657728799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1761876316988782210305065 1321407237741586657728799)
          ·
            refine ⟨1982110856612379986593199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1321407237741586657728799 1982110856612379986593199)
            ·
              refine ⟨2973166284918569979889799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1982110856612379986593199 2973166284918569979889799)
              ·
                refine ⟨4459749427377854969834699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2973166284918569979889799 4459749427377854969834699)
                ·
                  refine ⟨6689624141066782454752049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4459749427377854969834699 6689624141066782454752049)
                  ·
                    refine ⟨5017218105800086841064037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6689624141066782454752049 5017218105800086841064037)
                    ·
                      refine ⟨940728394837516282699507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5017218105800086841064037 940728394837516282699507)
                      ·
                        rfl

theorem cell23_1832062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_1832062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1832062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1832062 prefixEnd_1832062 := by exact prefixLift 1832062
  have htrace : WordTrace (prefixWord ++ tailWord_1832062) baseStart_1832062 baseEnd_1832062 := by
    simpa [prefixWord, tailWord_1832062, baseEnd_1832062] using wordTrace_append hprefix tailTrace_1832062
  have hstable : (prefixWord ++ tailWord_1832062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832062).length < 2 ^ (prefixWord ++ tailWord_1832062).sum := by decide
  have hdescent : baseEnd_1832062 < baseStart_1832062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832067 : List Nat := [1, 1, 1, 3, 3, 2, 1, 3, 2, 2, 4]
def baseStart_1832067 : Nat := 118140960795 + 1832067 * 2 ^ 59
def prefixEnd_1832067 : Nat := 4983230072969 + 3 ^ 40 * 1832067 * 2
def baseEnd_1832067 : Nat := 940730962240788763136983

theorem tailTrace_1832067 : CollatzResearch.WordTrace tailWord_1832067 prefixEnd_1832067 940730962240788763136983 := by
  unfold tailWord_1832067
  simp only [CollatzResearch.WordTrace]
  refine ⟨66820973053741625978094455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44547315369161083985396303 66820973053741625978094455)
  ·
    refine ⟨100231459580612438967141683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66820973053741625978094455 100231459580612438967141683)
    ·
      refine ⟨150347189370918658450712525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100231459580612438967141683 150347189370918658450712525)
      ·
        refine ⟨56380196014094496919017197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150347189370918658450712525 56380196014094496919017197)
        ·
          refine ⟨21142573505285436344631449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56380196014094496919017197 21142573505285436344631449)
          ·
            refine ⟨15856930128964077258473587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21142573505285436344631449 15856930128964077258473587)
            ·
              refine ⟨23785395193446115887710381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15856930128964077258473587 23785395193446115887710381)
              ·
                refine ⟨8919523197542293457891393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23785395193446115887710381 8919523197542293457891393)
                ·
                  refine ⟨6689642398156720093418545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8919523197542293457891393 6689642398156720093418545)
                  ·
                    refine ⟨5017231798617540070063909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6689642398156720093418545 5017231798617540070063909)
                    ·
                      refine ⟨940730962240788763136983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5017231798617540070063909 940730962240788763136983)
                      ·
                        rfl

theorem cell23_1832067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 3, 2, 2, 4].length) (baseStart_1832067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1832067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1832067 prefixEnd_1832067 := by exact prefixLift 1832067
  have htrace : WordTrace (prefixWord ++ tailWord_1832067) baseStart_1832067 baseEnd_1832067 := by
    simpa [prefixWord, tailWord_1832067, baseEnd_1832067] using wordTrace_append hprefix tailTrace_1832067
  have hstable : (prefixWord ++ tailWord_1832067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832067).length < 2 ^ (prefixWord ++ tailWord_1832067).sum := by decide
  have hdescent : baseEnd_1832067 < baseStart_1832067 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832127 : List Nat := [1, 1, 2, 2, 2, 2, 2, 1, 3, 3, 4]
def baseStart_1832127 : Nat := 118140960795 + 1832127 * 2 ^ 59
def prefixEnd_1832127 : Nat := 4983230072969 + 3 ^ 40 * 1832127 * 2
def baseEnd_1832127 : Nat := 940761771080058528386707

theorem tailTrace_1832127 : CollatzResearch.WordTrace tailWord_1832127 prefixEnd_1832127 940761771080058528386707 := by
  unfold tailWord_1832127
  simp only [CollatzResearch.WordTrace]
  refine ⟨66823161433524256225278635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44548774289016170816852423 66823161433524256225278635)
  ·
    refine ⟨100234742150286384337917953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66823161433524256225278635 100234742150286384337917953)
    ·
      refine ⟨75176056612714788253438465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100234742150286384337917953 75176056612714788253438465)
      ·
        refine ⟨56382042459536091190078849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75176056612714788253438465 56382042459536091190078849)
        ·
          refine ⟨42286531844652068392559137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56382042459536091190078849 42286531844652068392559137)
          ·
            refine ⟨31714898883489051294419353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42286531844652068392559137 31714898883489051294419353)
            ·
              refine ⟨23786174162616788470814515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31714898883489051294419353 23786174162616788470814515)
              ·
                refine ⟨35679261243925182706221773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23786174162616788470814515 35679261243925182706221773)
                ·
                  refine ⟨13379722966471943514833165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35679261243925182706221773 13379722966471943514833165)
                  ·
                    refine ⟨5017396112426978818062437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13379722966471943514833165 5017396112426978818062437)
                    ·
                      refine ⟨940761771080058528386707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5017396112426978818062437 940761771080058528386707)
                      ·
                        rfl

theorem cell23_1832127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 3, 3, 4].length) (baseStart_1832127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1832127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1832127 prefixEnd_1832127 := by exact prefixLift 1832127
  have htrace : WordTrace (prefixWord ++ tailWord_1832127) baseStart_1832127 baseEnd_1832127 := by
    simpa [prefixWord, tailWord_1832127, baseEnd_1832127] using wordTrace_append hprefix tailTrace_1832127
  have hstable : (prefixWord ++ tailWord_1832127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832127).length < 2 ^ (prefixWord ++ tailWord_1832127).sum := by decide
  have hdescent : baseEnd_1832127 < baseStart_1832127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832178 : List Nat := [3, 2, 1, 3, 3, 1, 1, 1, 2, 4, 2]
def baseStart_1832178 : Nat := 118140960795 + 1832178 * 2 ^ 59
def prefixEnd_1832178 : Nat := 4983230072969 + 3 ^ 40 * 1832178 * 2
def baseEnd_1832178 : Nat := 940787958593437828848973

theorem tailTrace_1832178 : CollatzResearch.WordTrace tailWord_1832178 prefixEnd_1832178 940787958593437828848973 := by
  unfold tailWord_1832178
  simp only [CollatzResearch.WordTrace]
  refine ⟨16706255389084872983846297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44550014370892994623590125 16706255389084872983846297)
  ·
    refine ⟨12529691541813654737884723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16706255389084872983846297 12529691541813654737884723)
    ·
      refine ⟨18794537312720482106827085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12529691541813654737884723 18794537312720482106827085)
      ·
        refine ⟨7047951492270180790060157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18794537312720482106827085 7047951492270180790060157)
        ·
          refine ⟨2642981809601317796272559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7047951492270180790060157 2642981809601317796272559)
          ·
            refine ⟨3964472714401976694408839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2642981809601317796272559 3964472714401976694408839)
            ·
              refine ⟨5946709071602965041613259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3964472714401976694408839 5946709071602965041613259)
              ·
                refine ⟨8920063607404447562419889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5946709071602965041613259 8920063607404447562419889)
                ·
                  refine ⟨6690047705553335671814917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8920063607404447562419889 6690047705553335671814917)
                  ·
                    refine ⟨1254383944791250438465297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6690047705553335671814917 1254383944791250438465297)
                    ·
                      refine ⟨940787958593437828848973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1254383944791250438465297 940787958593437828848973)
                      ·
                        rfl

theorem cell23_1832178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 1, 2, 4, 2].length) (baseStart_1832178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1832178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1832178 prefixEnd_1832178 := by exact prefixLift 1832178
  have htrace : WordTrace (prefixWord ++ tailWord_1832178) baseStart_1832178 baseEnd_1832178 := by
    simpa [prefixWord, tailWord_1832178, baseEnd_1832178] using wordTrace_append hprefix tailTrace_1832178
  have hstable : (prefixWord ++ tailWord_1832178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832178).length < 2 ^ (prefixWord ++ tailWord_1832178).sum := by decide
  have hdescent : baseEnd_1832178 < baseStart_1832178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832207 : List Nat := [1, 1, 2, 1, 1, 1, 3, 1, 1, 6, 5]
def baseStart_1832207 : Nat := 118140960795 + 1832207 * 2 ^ 59
def prefixEnd_1832207 : Nat := 4983230072969 + 3 ^ 40 * 1832207 * 2
def baseEnd_1832207 : Nat := 940802849532418215386339

theorem tailTrace_1832207 : CollatzResearch.WordTrace tailWord_1832207 prefixEnd_1832207 940802849532418215386339 := by
  unfold tailWord_1832207
  simp only [CollatzResearch.WordTrace]
  refine ⟨66826079273234429888190875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44550719515489619925460583 66826079273234429888190875)
  ·
    refine ⟨100239118909851644832286313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66826079273234429888190875 100239118909851644832286313)
    ·
      refine ⟨75179339182388733624214735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100239118909851644832286313 75179339182388733624214735)
      ·
        refine ⟨112769008773583100436322103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75179339182388733624214735 112769008773583100436322103)
        ·
          refine ⟨169153513160374650654483155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112769008773583100436322103 169153513160374650654483155)
          ·
            refine ⟨253730269740561975981724733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169153513160374650654483155 253730269740561975981724733)
            ·
              refine ⟨95148851152710740993146775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 253730269740561975981724733 95148851152710740993146775)
              ·
                refine ⟨142723276729066111489720163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95148851152710740993146775 142723276729066111489720163)
                ·
                  refine ⟨214084915093599167234580245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 142723276729066111489720163 214084915093599167234580245)
                  ·
                    refine ⟨10035230395012460964120949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 214084915093599167234580245 10035230395012460964120949)
                    ·
                      refine ⟨940802849532418215386339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10035230395012460964120949 940802849532418215386339)
                      ·
                        rfl

theorem cell23_1832207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 6, 5].length) (baseStart_1832207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1832207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1832207 prefixEnd_1832207 := by exact prefixLift 1832207
  have htrace : WordTrace (prefixWord ++ tailWord_1832207) baseStart_1832207 baseEnd_1832207 := by
    simpa [prefixWord, tailWord_1832207, baseEnd_1832207] using wordTrace_append hprefix tailTrace_1832207
  have hstable : (prefixWord ++ tailWord_1832207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832207).length < 2 ^ (prefixWord ++ tailWord_1832207).sum := by decide
  have hdescent : baseEnd_1832207 < baseStart_1832207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832228 : List Nat := [2, 3, 1, 3, 1, 1, 4, 1, 3, 1, 3]
def baseStart_1832228 : Nat := 118140960795 + 1832228 * 2 ^ 59
def prefixEnd_1832228 : Nat := 4983230072969 + 3 ^ 40 * 1832228 * 2
def baseEnd_1832228 : Nat := 940813632626162633223743

theorem tailTrace_1832228 : CollatzResearch.WordTrace tailWord_1832228 prefixEnd_1832228 940813632626162633223743 := by
  unfold tailWord_1832228
  simp only [CollatzResearch.WordTrace]
  refine ⟨33413422603079175237352669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44551230137438900316470225 33413422603079175237352669)
  ·
    refine ⟨12530033476154690714007251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33413422603079175237352669 12530033476154690714007251)
    ·
      refine ⟨18795050214232036071010877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12530033476154690714007251 18795050214232036071010877)
      ·
        refine ⟨7048143830337013526629079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18795050214232036071010877 7048143830337013526629079)
        ·
          refine ⟨10572215745505520289943619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7048143830337013526629079 10572215745505520289943619)
          ·
            refine ⟨15858323618258280434915429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10572215745505520289943619 15858323618258280434915429)
            ·
              refine ⟨2973435678423427581546643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15858323618258280434915429 2973435678423427581546643)
              ·
                refine ⟨4460153517635141372319965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2973435678423427581546643 4460153517635141372319965)
                ·
                  refine ⟨1672557569113178014619987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4460153517635141372319965 1672557569113178014619987)
                  ·
                    refine ⟨2508836353669767021929981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1672557569113178014619987 2508836353669767021929981)
                    ·
                      refine ⟨940813632626162633223743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2508836353669767021929981 940813632626162633223743)
                      ·
                        rfl

theorem cell23_1832228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_1832228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1832228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1832228 prefixEnd_1832228 := by exact prefixLift 1832228
  have htrace : WordTrace (prefixWord ++ tailWord_1832228) baseStart_1832228 baseEnd_1832228 := by
    simpa [prefixWord, tailWord_1832228, baseEnd_1832228] using wordTrace_append hprefix tailTrace_1832228
  have hstable : (prefixWord ++ tailWord_1832228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832228).length < 2 ^ (prefixWord ++ tailWord_1832228).sum := by decide
  have hdescent : baseEnd_1832228 < baseStart_1832228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832264 : List Nat := [2, 1, 3, 1, 1, 2, 1, 3, 3, 2, 4]
def baseStart_1832264 : Nat := 118140960795 + 1832264 * 2 ^ 59
def prefixEnd_1832264 : Nat := 4983230072969 + 3 ^ 40 * 1832264 * 2
def baseEnd_1832264 : Nat := 940832117929724492373577

theorem tailTrace_1832264 : CollatzResearch.WordTrace tailWord_1832264 prefixEnd_1832264 940832117929724492373577 := by
  unfold tailWord_1832264
  simp only [CollatzResearch.WordTrace]
  refine ⟨33414079117013964311507923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44552105489351952415343897 33414079117013964311507923)
  ·
    refine ⟨50121118675520946467261885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33414079117013964311507923 50121118675520946467261885)
    ·
      refine ⟨18795419503320354925223207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50121118675520946467261885 18795419503320354925223207)
      ·
        refine ⟨28193129254980532387834811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18795419503320354925223207 28193129254980532387834811)
        ·
          refine ⟨42289693882470798581752217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28193129254980532387834811 42289693882470798581752217)
          ·
            refine ⟨31717270411853098936314163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42289693882470798581752217 31717270411853098936314163)
            ·
              refine ⟨47575905617779648404471245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31717270411853098936314163 47575905617779648404471245)
              ·
                refine ⟨17840964606667368151676717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47575905617779648404471245 17840964606667368151676717)
                ·
                  refine ⟨6690361727500263056878769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17840964606667368151676717 6690361727500263056878769)
                  ·
                    refine ⟨5017771295625197292659077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6690361727500263056878769 5017771295625197292659077)
                    ·
                      refine ⟨940832117929724492373577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5017771295625197292659077 940832117929724492373577)
                      ·
                        rfl

theorem cell23_1832264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 3, 2, 4].length) (baseStart_1832264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1832264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1832264 prefixEnd_1832264 := by exact prefixLift 1832264
  have htrace : WordTrace (prefixWord ++ tailWord_1832264) baseStart_1832264 baseEnd_1832264 := by
    simpa [prefixWord, tailWord_1832264, baseEnd_1832264] using wordTrace_append hprefix tailTrace_1832264
  have hstable : (prefixWord ++ tailWord_1832264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832264).length < 2 ^ (prefixWord ++ tailWord_1832264).sum := by decide
  have hdescent : baseEnd_1832264 < baseStart_1832264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832302 : List Nat := [4, 1, 2, 4, 1, 2, 1, 2, 1, 1, 4]
def baseStart_1832302 : Nat := 118140960795 + 1832302 * 2 ^ 59
def prefixEnd_1832302 : Nat := 4983230072969 + 3 ^ 40 * 1832302 * 2
def baseEnd_1832302 : Nat := 940851630194595343698403

theorem tailTrace_1832302 : CollatzResearch.WordTrace tailWord_1832302 prefixEnd_1832302 940851630194595343698403 := by
  unfold tailWord_1832302
  simp only [CollatzResearch.WordTrace]
  refine ⟨8353693025986282639112395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44553029471926840741932773 8353693025986282639112395)
  ·
    refine ⟨12530539538979423958668593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8353693025986282639112395 12530539538979423958668593)
    ·
      refine ⟨9397904654234567969001445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12530539538979423958668593 9397904654234567969001445)
      ·
        refine ⟨1762107122668981494187771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9397904654234567969001445 1762107122668981494187771)
        ·
          refine ⟨2643160684003472241281657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1762107122668981494187771 2643160684003472241281657)
          ·
            refine ⟨1982370513002604180961243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2643160684003472241281657 1982370513002604180961243)
            ·
              refine ⟨2973555769503906271441865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1982370513002604180961243 2973555769503906271441865)
              ·
                refine ⟨2230166827127929703581399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2973555769503906271441865 2230166827127929703581399)
                ·
                  refine ⟨3345250240691894555372099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2230166827127929703581399 3345250240691894555372099)
                  ·
                    refine ⟨5017875361037841833058149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3345250240691894555372099 5017875361037841833058149)
                    ·
                      refine ⟨940851630194595343698403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5017875361037841833058149 940851630194595343698403)
                      ·
                        rfl

theorem cell23_1832302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_1832302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1832302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1832302 prefixEnd_1832302 := by exact prefixLift 1832302
  have htrace : WordTrace (prefixWord ++ tailWord_1832302) baseStart_1832302 baseEnd_1832302 := by
    simpa [prefixWord, tailWord_1832302, baseEnd_1832302] using wordTrace_append hprefix tailTrace_1832302
  have hstable : (prefixWord ++ tailWord_1832302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832302).length < 2 ^ (prefixWord ++ tailWord_1832302).sum := by decide
  have hdescent : baseEnd_1832302 < baseStart_1832302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832351 : List Nat := [1, 1, 2, 5, 1, 3, 1, 1, 2, 6]
def baseStart_1832351 : Nat := 118140960795 + 1832351 * 2 ^ 59
def prefixEnd_1832351 : Nat := 4983230072969 + 3 ^ 40 * 1832351 * 2
def baseEnd_1832351 : Nat := 313625596915555217328559

theorem tailTrace_1832351 : CollatzResearch.WordTrace tailWord_1832351 prefixEnd_1832351 313625596915555217328559 := by
  unfold tailWord_1832351
  simp only [CollatzResearch.WordTrace]
  refine ⟨66831331384712742481432907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44554220923141828320955271 66831331384712742481432907)
  ·
    refine ⟨100246997077069113722149361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66831331384712742481432907 100246997077069113722149361)
    ·
      refine ⟨75185247807801835291612021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100246997077069113722149361 75185247807801835291612021)
      ·
        refine ⟨7048616981981422058588627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 75185247807801835291612021 7048616981981422058588627)
        ·
          refine ⟨10572925472972133087882941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7048616981981422058588627 10572925472972133087882941)
          ·
            refine ⟨3964847052364549907956103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10572925472972133087882941 3964847052364549907956103)
            ·
              refine ⟨5947270578546824861934155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3964847052364549907956103 5947270578546824861934155)
              ·
                refine ⟨8920905867820237292901233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5947270578546824861934155 8920905867820237292901233)
                ·
                  refine ⟨6690679400865177969675925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8920905867820237292901233 6690679400865177969675925)
                  ·
                    refine ⟨313625596915555217328559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6690679400865177969675925 313625596915555217328559)
                    ·
                      rfl

theorem cell23_1832351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 1, 2, 6].length) (baseStart_1832351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1832351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1832351 prefixEnd_1832351 := by exact prefixLift 1832351
  have htrace : WordTrace (prefixWord ++ tailWord_1832351) baseStart_1832351 baseEnd_1832351 := by
    simpa [prefixWord, tailWord_1832351, baseEnd_1832351] using wordTrace_append hprefix tailTrace_1832351
  have hstable : (prefixWord ++ tailWord_1832351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832351).length < 2 ^ (prefixWord ++ tailWord_1832351).sum := by decide
  have hdescent : baseEnd_1832351 < baseStart_1832351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832364 : List Nat := [2, 2, 1, 1, 1, 1, 5, 1, 9]
def baseStart_1832364 : Nat := 118140960795 + 1832364 * 2 ^ 59
def prefixEnd_1832364 : Nat := 4983230072969 + 3 ^ 40 * 1832364 * 2
def baseEnd_1832364 : Nat := 104542607332797122347013

theorem tailTrace_1832364 : CollatzResearch.WordTrace tailWord_1832364 prefixEnd_1832364 104542607332797122347013 := by
  unfold tailWord_1832364
  simp only [CollatzResearch.WordTrace]
  refine ⟨33415902766832822850828073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44554537022443763801104097 33415902766832822850828073)
  ·
    refine ⟨25061927075124617138121055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33415902766832822850828073 25061927075124617138121055)
    ·
      refine ⟨37592890612686925707181583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25061927075124617138121055 37592890612686925707181583)
      ·
        refine ⟨56389335919030388560772375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37592890612686925707181583 56389335919030388560772375)
        ·
          refine ⟨84584003878545582841158563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56389335919030388560772375 84584003878545582841158563)
          ·
            refine ⟨126876005817818374261737845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84584003878545582841158563 126876005817818374261737845)
            ·
              refine ⟨11894625545420472587037923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 126876005817818374261737845 11894625545420472587037923)
              ·
                refine ⟨17841938318130708880556885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11894625545420472587037923 17841938318130708880556885)
                ·
                  refine ⟨104542607332797122347013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 17841938318130708880556885 104542607332797122347013)
                  ·
                    rfl

theorem cell23_1832364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 9].length) (baseStart_1832364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1832364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1832364 prefixEnd_1832364 := by exact prefixLift 1832364
  have htrace : WordTrace (prefixWord ++ tailWord_1832364) baseStart_1832364 baseEnd_1832364 := by
    simpa [prefixWord, tailWord_1832364, baseEnd_1832364] using wordTrace_append hprefix tailTrace_1832364
  have hstable : (prefixWord ++ tailWord_1832364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832364).length < 2 ^ (prefixWord ++ tailWord_1832364).sum := by decide
  have hdescent : baseEnd_1832364 < baseStart_1832364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832386 : List Nat := [3, 5, 2, 1, 1, 1, 1, 1, 4, 1, 3]
def baseStart_1832386 : Nat := 118140960795 + 1832386 * 2 ^ 59
def prefixEnd_1832386 : Nat := 4983230072969 + 3 ^ 40 * 1832386 * 2
def baseEnd_1832386 : Nat := 940894762569573015048017

theorem tailTrace_1832386 : CollatzResearch.WordTrace tailWord_1832386 prefixEnd_1832386 940894762569573015048017 := by
  unfold tailWord_1832386
  simp only [CollatzResearch.WordTrace]
  refine ⟨16708151984896485864739253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44555071959723962305971341 16708151984896485864739253)
  ·
    refine ⟨1566389248584045549819305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16708151984896485864739253 1566389248584045549819305)
    ·
      refine ⟨1174791936438034162364479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1566389248584045549819305 1174791936438034162364479)
      ·
        refine ⟨1762187904657051243546719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1174791936438034162364479 1762187904657051243546719)
        ·
          refine ⟨2643281856985576865320079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1762187904657051243546719 2643281856985576865320079)
          ·
            refine ⟨3964922785478365297980119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2643281856985576865320079 3964922785478365297980119)
            ·
              refine ⟨5947384178217547946970179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3964922785478365297980119 5947384178217547946970179)
              ·
                refine ⟨8921076267326321920455269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5947384178217547946970179 8921076267326321920455269)
                ·
                  refine ⟨1672701800123685360085363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8921076267326321920455269 1672701800123685360085363)
                  ·
                    refine ⟨2509052700185528040128045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1672701800123685360085363 2509052700185528040128045)
                    ·
                      refine ⟨940894762569573015048017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2509052700185528040128045 940894762569573015048017)
                      ·
                        rfl

theorem cell23_1832386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_1832386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1832386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1832386 prefixEnd_1832386 := by exact prefixLift 1832386
  have htrace : WordTrace (prefixWord ++ tailWord_1832386) baseStart_1832386 baseEnd_1832386 := by
    simpa [prefixWord, tailWord_1832386, baseEnd_1832386] using wordTrace_append hprefix tailTrace_1832386
  have hstable : (prefixWord ++ tailWord_1832386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832386).length < 2 ^ (prefixWord ++ tailWord_1832386).sum := by decide
  have hdescent : baseEnd_1832386 < baseStart_1832386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832388 : List Nat := [2, 3, 3, 2, 1, 1, 1, 2, 2, 2, 4]
def baseStart_1832388 : Nat := 118140960795 + 1832388 * 2 ^ 59
def prefixEnd_1832388 : Nat := 4983230072969 + 3 ^ 40 * 1832388 * 2
def baseEnd_1832388 : Nat := 940895789530882007223007

theorem tailTrace_1832388 : CollatzResearch.WordTrace tailWord_1832388 prefixEnd_1832388 940895789530882007223007 := by
  unfold tailWord_1832388
  simp only [CollatzResearch.WordTrace]
  refine ⟨33416340442789348900264909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44555120590385798533686545 33416340442789348900264909)
  ·
    refine ⟨12531127666046005837599341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33416340442789348900264909 12531127666046005837599341)
    ·
      refine ⟨4699172874767252189099753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12531127666046005837599341 4699172874767252189099753)
      ·
        refine ⟨3524379656075439141824815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4699172874767252189099753 3524379656075439141824815)
        ·
          refine ⟨5286569484113158712737223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3524379656075439141824815 5286569484113158712737223)
          ·
            refine ⟨7929854226169738069105835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5286569484113158712737223 7929854226169738069105835)
            ·
              refine ⟨11894781339254607103658753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7929854226169738069105835 11894781339254607103658753)
              ·
                refine ⟨8921086004440955327744065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11894781339254607103658753 8921086004440955327744065)
                ·
                  refine ⟨6690814503330716495808049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8921086004440955327744065 6690814503330716495808049)
                  ·
                    refine ⟨5018110877498037371856037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6690814503330716495808049 5018110877498037371856037)
                    ·
                      refine ⟨940895789530882007223007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5018110877498037371856037 940895789530882007223007)
                      ·
                        rfl

theorem cell23_1832388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_1832388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1832388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1832388 prefixEnd_1832388 := by exact prefixLift 1832388
  have htrace : WordTrace (prefixWord ++ tailWord_1832388) baseStart_1832388 baseEnd_1832388 := by
    simpa [prefixWord, tailWord_1832388, baseEnd_1832388] using wordTrace_append hprefix tailTrace_1832388
  have hstable : (prefixWord ++ tailWord_1832388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832388).length < 2 ^ (prefixWord ++ tailWord_1832388).sum := by decide
  have hdescent : baseEnd_1832388 < baseStart_1832388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832391 : List Nat := [1, 1, 4, 1, 1, 3, 1, 1, 4, 3, 3]
def baseStart_1832391 : Nat := 118140960795 + 1832391 * 2 ^ 59
def prefixEnd_1832391 : Nat := 4983230072969 + 3 ^ 40 * 1832391 * 2
def baseEnd_1832391 : Nat := 940897329972845495485493

theorem tailTrace_1832391 : CollatzResearch.WordTrace tailWord_1832391 prefixEnd_1832391 940897329972845495485493 := by
  unfold tailWord_1832391
  simp only [CollatzResearch.WordTrace]
  refine ⟨66832790304567829312889027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44555193536378552875259351 66832790304567829312889027)
  ·
    refine ⟨100249185456851743969333541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66832790304567829312889027 100249185456851743969333541)
    ·
      refine ⟨18796722273159701994250039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100249185456851743969333541 18796722273159701994250039)
      ·
        refine ⟨28195083409739552991375059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18796722273159701994250039 28195083409739552991375059)
        ·
          refine ⟨42292625114609329487062589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28195083409739552991375059 42292625114609329487062589)
          ·
            refine ⟨15859734417978498557648471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42292625114609329487062589 15859734417978498557648471)
            ·
              refine ⟨23789601626967747836472707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15859734417978498557648471 23789601626967747836472707)
              ·
                refine ⟨35684402440451621754709061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23789601626967747836472707 35684402440451621754709061)
                ·
                  refine ⟨6690825457584679079007949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35684402440451621754709061 6690825457584679079007949)
                  ·
                    refine ⟨2509059546594254654627981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6690825457584679079007949 2509059546594254654627981)
                    ·
                      refine ⟨940897329972845495485493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2509059546594254654627981 940897329972845495485493)
                      ·
                        rfl

theorem cell23_1832391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 4, 3, 3].length) (baseStart_1832391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1832391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1832391 prefixEnd_1832391 := by exact prefixLift 1832391
  have htrace : WordTrace (prefixWord ++ tailWord_1832391) baseStart_1832391 baseEnd_1832391 := by
    simpa [prefixWord, tailWord_1832391, baseEnd_1832391] using wordTrace_append hprefix tailTrace_1832391
  have hstable : (prefixWord ++ tailWord_1832391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832391).length < 2 ^ (prefixWord ++ tailWord_1832391).sum := by decide
  have hdescent : baseEnd_1832391 < baseStart_1832391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832398 : List Nat := [4, 1, 1, 1, 2, 1, 4, 4, 5]
def baseStart_1832398 : Nat := 118140960795 + 1832398 * 2 ^ 59
def prefixEnd_1832398 : Nat := 4983230072969 + 3 ^ 40 * 1832398 * 2
def baseEnd_1832398 : Nat := 104544547148602996455329

theorem tailTrace_1832398 : CollatzResearch.WordTrace tailWord_1832398 prefixEnd_1832398 104544547148602996455329 := by
  unfold tailWord_1832398
  simp only [CollatzResearch.WordTrace]
  refine ⟨8354130701942808688549231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44555363743694979672262565 8354130701942808688549231)
  ·
    refine ⟨12531196052914213032823847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8354130701942808688549231 12531196052914213032823847)
    ·
      refine ⟨18796794079371319549235771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12531196052914213032823847 18796794079371319549235771)
      ·
        refine ⟨28195191119056979323853657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18796794079371319549235771 28195191119056979323853657)
        ·
          refine ⟨21146393339292734492890243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28195191119056979323853657 21146393339292734492890243)
          ·
            refine ⟨31719590008939101739335365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21146393339292734492890243 31719590008939101739335365)
            ·
              refine ⟨5947423126676081576125381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31719590008939101739335365 5947423126676081576125381)
              ·
                refine ⟨1115141836251765295523509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5947423126676081576125381 1115141836251765295523509)
                ·
                  refine ⟨104544547148602996455329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1115141836251765295523509 104544547148602996455329)
                  ·
                    rfl

theorem cell23_1832398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 4, 5].length) (baseStart_1832398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1832398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1832398 prefixEnd_1832398 := by exact prefixLift 1832398
  have htrace : WordTrace (prefixWord ++ tailWord_1832398) baseStart_1832398 baseEnd_1832398 := by
    simpa [prefixWord, tailWord_1832398, baseEnd_1832398] using wordTrace_append hprefix tailTrace_1832398
  have hstable : (prefixWord ++ tailWord_1832398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832398).length < 2 ^ (prefixWord ++ tailWord_1832398).sum := by decide
  have hdescent : baseEnd_1832398 < baseStart_1832398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832431 : List Nat := [1, 1, 2, 1, 4, 1, 4, 1, 1, 3, 4]
def baseStart_1832431 : Nat := 118140960795 + 1832431 * 2 ^ 59
def prefixEnd_1832431 : Nat := 4983230072969 + 3 ^ 40 * 1832431 * 2
def baseEnd_1832431 : Nat := 940917869199025338985309

theorem tailTrace_1832431 : CollatzResearch.WordTrace tailWord_1832431 prefixEnd_1832431 940917869199025338985309 := by
  unfold tailWord_1832431
  simp only [CollatzResearch.WordTrace]
  refine ⟨66834249224422916144345147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44556166149615277429563431 66834249224422916144345147)
  ·
    refine ⟨100251373836634374216517721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66834249224422916144345147 100251373836634374216517721)
    ·
      refine ⟨75188530377475780662388291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100251373836634374216517721 75188530377475780662388291)
      ·
        refine ⟨112782795566213670993582437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75188530377475780662388291 112782795566213670993582437)
        ·
          refine ⟨21146774168665063311296707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112782795566213670993582437 21146774168665063311296707)
          ·
            refine ⟨31720161252997594966945061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21146774168665063311296707 31720161252997594966945061)
            ·
              refine ⟨5947530234937049056302199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31720161252997594966945061 5947530234937049056302199)
              ·
                refine ⟨8921295352405573584453299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5947530234937049056302199 8921295352405573584453299)
                ·
                  refine ⟨13381943028608360376679949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8921295352405573584453299 13381943028608360376679949)
                  ·
                    refine ⟨5018228635728135141254981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13381943028608360376679949 5018228635728135141254981)
                    ·
                      refine ⟨940917869199025338985309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5018228635728135141254981 940917869199025338985309)
                      ·
                        rfl

theorem cell23_1832431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 1, 1, 3, 4].length) (baseStart_1832431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1832431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1832431 prefixEnd_1832431 := by exact prefixLift 1832431
  have htrace : WordTrace (prefixWord ++ tailWord_1832431) baseStart_1832431 baseEnd_1832431 := by
    simpa [prefixWord, tailWord_1832431, baseEnd_1832431] using wordTrace_append hprefix tailTrace_1832431
  have hstable : (prefixWord ++ tailWord_1832431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832431).length < 2 ^ (prefixWord ++ tailWord_1832431).sum := by decide
  have hdescent : baseEnd_1832431 < baseStart_1832431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832451 : List Nat := [1, 1, 1, 3, 2, 1, 2, 2, 3, 4, 3]
def baseStart_1832451 : Nat := 118140960795 + 1832451 * 2 ^ 59
def prefixEnd_1832451 : Nat := 4983230072969 + 3 ^ 40 * 1832451 * 2
def baseEnd_1832451 : Nat := 940928138812115260735217

theorem tailTrace_1832451 : CollatzResearch.WordTrace tailWord_1832451 prefixEnd_1832451 940928138812115260735217 := by
  unfold tailWord_1832451
  simp only [CollatzResearch.WordTrace]
  refine ⟨66834978684350459560073207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44556652456233639706715471 66834978684350459560073207)
  ·
    refine ⟨100252468026525689340109811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66834978684350459560073207 100252468026525689340109811)
    ·
      refine ⟨150378702039788534010164717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100252468026525689340109811 150378702039788534010164717)
      ·
        refine ⟨56392013264920700253811769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150378702039788534010164717 56392013264920700253811769)
        ·
          refine ⟨42294009948690525190358827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56392013264920700253811769 42294009948690525190358827)
          ·
            refine ⟨63441014923035787785538241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42294009948690525190358827 63441014923035787785538241)
            ·
              refine ⟨47580761192276840839153681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63441014923035787785538241 47580761192276840839153681)
              ·
                refine ⟨35685570894207630629365261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47580761192276840839153681 35685570894207630629365261)
                ·
                  refine ⟨13382089085327861486011973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35685570894207630629365261 13382089085327861486011973)
                  ·
                    refine ⟨2509141703498974028627245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13382089085327861486011973 2509141703498974028627245)
                    ·
                      refine ⟨940928138812115260735217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2509141703498974028627245 940928138812115260735217)
                      ·
                        rfl

theorem cell23_1832451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 3, 4, 3].length) (baseStart_1832451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1832451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1832451 prefixEnd_1832451 := by exact prefixLift 1832451
  have htrace : WordTrace (prefixWord ++ tailWord_1832451) baseStart_1832451 baseEnd_1832451 := by
    simpa [prefixWord, tailWord_1832451, baseEnd_1832451] using wordTrace_append hprefix tailTrace_1832451
  have hstable : (prefixWord ++ tailWord_1832451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832451).length < 2 ^ (prefixWord ++ tailWord_1832451).sum := by decide
  have hdescent : baseEnd_1832451 < baseStart_1832451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832548 : List Nat := [2, 3, 1, 1, 2, 3, 2, 2, 1, 6]
def baseStart_1832548 : Nat := 118140960795 + 1832548 * 2 ^ 59
def prefixEnd_1832548 : Nat := 4983230072969 + 3 ^ 40 * 1832548 * 2
def baseEnd_1832548 : Nat := 313659315478533793740757

theorem tailTrace_1832548 : CollatzResearch.WordTrace tailWord_1832548 prefixEnd_1832548 313659315478533793740757 := by
  unfold tailWord_1832548
  simp only [CollatzResearch.WordTrace]
  refine ⟨33419258282499522563177149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44559011043332696750902865 33419258282499522563177149)
  ·
    refine ⟨12532221855937320961191431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33419258282499522563177149 12532221855937320961191431)
    ·
      refine ⟨18798332783905981441787147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12532221855937320961191431 18798332783905981441787147)
      ·
        refine ⟨28197499175858972162680721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18798332783905981441787147 28197499175858972162680721)
        ·
          refine ⟨21148124381894229122010541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28197499175858972162680721 21148124381894229122010541)
          ·
            refine ⟨7930546643210335920753953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21148124381894229122010541 7930546643210335920753953)
            ·
              refine ⟨5947909982407751940565465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7930546643210335920753953 5947909982407751940565465)
              ·
                refine ⟨4460932486805813955424099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5947909982407751940565465 4460932486805813955424099)
                ·
                  refine ⟨6691398730208720933136149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4460932486805813955424099 6691398730208720933136149)
                  ·
                    refine ⟨313659315478533793740757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6691398730208720933136149 313659315478533793740757)
                    ·
                      rfl

theorem cell23_1832548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 2, 1, 6].length) (baseStart_1832548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1832548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1832548 prefixEnd_1832548 := by exact prefixLift 1832548
  have htrace : WordTrace (prefixWord ++ tailWord_1832548) baseStart_1832548 baseEnd_1832548 := by
    simpa [prefixWord, tailWord_1832548, baseEnd_1832548] using wordTrace_append hprefix tailTrace_1832548
  have hstable : (prefixWord ++ tailWord_1832548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832548).length < 2 ^ (prefixWord ++ tailWord_1832548).sum := by decide
  have hdescent : baseEnd_1832548 < baseStart_1832548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832549 : List Nat := [1, 3, 1, 3, 3, 2, 2, 3, 1, 1, 3]
def baseStart_1832549 : Nat := 118140960795 + 1832549 * 2 ^ 59
def prefixEnd_1832549 : Nat := 4983230072969 + 3 ^ 40 * 1832549 * 2
def baseEnd_1832549 : Nat := 940978459916255877309767

theorem tailTrace_1832549 : CollatzResearch.WordTrace tailWord_1832549 prefixEnd_1832549 940978459916255877309767 := by
  unfold tailWord_1832549
  simp only [CollatzResearch.WordTrace]
  refine ⟨66838553037995422297140701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44559035358663614864760467 66838553037995422297140701)
  ·
    refine ⟨25064457389248283361427763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66838553037995422297140701 25064457389248283361427763)
    ·
      refine ⟨37596686083872425042141645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25064457389248283361427763 37596686083872425042141645)
      ·
        refine ⟨14098757281452159390803117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37596686083872425042141645 14098757281452159390803117)
        ·
          refine ⟨5287033980544559771551169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14098757281452159390803117 5287033980544559771551169)
          ·
            refine ⟨3965275485408419828663377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5287033980544559771551169 3965275485408419828663377)
            ·
              refine ⟨2973956614056314871497533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3965275485408419828663377 2973956614056314871497533)
              ·
                refine ⟨1115233730271118076811575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2973956614056314871497533 1115233730271118076811575)
                ·
                  refine ⟨1672850595406677115217363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1115233730271118076811575 1672850595406677115217363)
                  ·
                    refine ⟨2509275893110015672826045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1672850595406677115217363 2509275893110015672826045)
                    ·
                      refine ⟨940978459916255877309767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2509275893110015672826045 940978459916255877309767)
                      ·
                        rfl

theorem cell23_1832549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 3, 1, 1, 3].length) (baseStart_1832549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1832549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1832549 prefixEnd_1832549 := by exact prefixLift 1832549
  have htrace : WordTrace (prefixWord ++ tailWord_1832549) baseStart_1832549 baseEnd_1832549 := by
    simpa [prefixWord, tailWord_1832549, baseEnd_1832549] using wordTrace_append hprefix tailTrace_1832549
  have hstable : (prefixWord ++ tailWord_1832549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832549).length < 2 ^ (prefixWord ++ tailWord_1832549).sum := by decide
  have hdescent : baseEnd_1832549 < baseStart_1832549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832552 : List Nat := [2, 1, 4, 3, 1, 1, 4, 1, 1, 5]
def baseStart_1832552 : Nat := 118140960795 + 1832552 * 2 ^ 59
def prefixEnd_1832552 : Nat := 4983230072969 + 3 ^ 40 * 1832552 * 2
def baseEnd_1832552 : Nat := 313660000119406455190751

theorem tailTrace_1832552 : CollatzResearch.WordTrace tailWord_1832552 prefixEnd_1832552 313660000119406455190751 := by
  unfold tailWord_1832552
  simp only [CollatzResearch.WordTrace]
  refine ⟨33419331228492276904749955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44559108304656369206333273 33419331228492276904749955)
  ·
    refine ⟨50128996842738415357124933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33419331228492276904749955 50128996842738415357124933)
    ·
      refine ⟨9399186908013452879460925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50128996842738415357124933 9399186908013452879460925)
      ·
        refine ⟨3524695090505044829797847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9399186908013452879460925 3524695090505044829797847)
        ·
          refine ⟨5287042635757567244696771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3524695090505044829797847 5287042635757567244696771)
          ·
            refine ⟨7930563953636350867045157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5287042635757567244696771 7930563953636350867045157)
            ·
              refine ⟨1486980741306815787570967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7930563953636350867045157 1486980741306815787570967)
              ·
                refine ⟨2230471111960223681356451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1486980741306815787570967 2230471111960223681356451)
                ·
                  refine ⟨3345706667940335522034677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2230471111960223681356451 3345706667940335522034677)
                  ·
                    refine ⟨313660000119406455190751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3345706667940335522034677 313660000119406455190751)
                    ·
                      rfl

theorem cell23_1832552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 4, 1, 1, 5].length) (baseStart_1832552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1832552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1832552 prefixEnd_1832552 := by exact prefixLift 1832552
  have htrace : WordTrace (prefixWord ++ tailWord_1832552) baseStart_1832552 baseEnd_1832552 := by
    simpa [prefixWord, tailWord_1832552, baseEnd_1832552] using wordTrace_append hprefix tailTrace_1832552
  have hstable : (prefixWord ++ tailWord_1832552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832552).length < 2 ^ (prefixWord ++ tailWord_1832552).sum := by decide
  have hdescent : baseEnd_1832552 < baseStart_1832552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832648 : List Nat := [2, 1, 3, 1, 2, 2, 1, 1, 4, 1, 5]
def baseStart_1832648 : Nat := 118140960795 + 1832648 * 2 ^ 59
def prefixEnd_1832648 : Nat := 4983230072969 + 3 ^ 40 * 1832648 * 2
def baseEnd_1832648 : Nat := 941029294501050989971811

theorem tailTrace_1832648 : CollatzResearch.WordTrace tailWord_1832648 prefixEnd_1832648 941029294501050989971811 := by
  unfold tailWord_1832648
  simp only [CollatzResearch.WordTrace]
  refine ⟨33421081932318381102497299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44561442576424508136663065 33421081932318381102497299)
  ·
    refine ⟨50131622898477571653745949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33421081932318381102497299 50131622898477571653745949)
    ·
      refine ⟨18799358586929089370154731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50131622898477571653745949 18799358586929089370154731)
      ·
        refine ⟨28199037880393634055232097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18799358586929089370154731 28199037880393634055232097)
        ·
          refine ⟨21149278410295225541424073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28199037880393634055232097 21149278410295225541424073)
          ·
            refine ⟨15861958807721419156068055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21149278410295225541424073 15861958807721419156068055)
            ·
              refine ⟨23792938211582128734102083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15861958807721419156068055 23792938211582128734102083)
              ·
                refine ⟨35689407317373193101153125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23792938211582128734102083 35689407317373193101153125)
                ·
                  refine ⟨6691763872007473706466211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35689407317373193101153125 6691763872007473706466211)
                  ·
                    refine ⟨10037645808011210559699317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6691763872007473706466211 10037645808011210559699317)
                    ·
                      refine ⟨941029294501050989971811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10037645808011210559699317 941029294501050989971811)
                      ·
                        rfl

theorem cell23_1832648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 4, 1, 5].length) (baseStart_1832648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1832648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1832648 prefixEnd_1832648 := by exact prefixLift 1832648
  have htrace : WordTrace (prefixWord ++ tailWord_1832648) baseStart_1832648 baseEnd_1832648 := by
    simpa [prefixWord, tailWord_1832648, baseEnd_1832648] using wordTrace_append hprefix tailTrace_1832648
  have hstable : (prefixWord ++ tailWord_1832648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832648).length < 2 ^ (prefixWord ++ tailWord_1832648).sum := by decide
  have hdescent : baseEnd_1832648 < baseStart_1832648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832698 : List Nat := [3, 1, 1, 1, 1, 3, 1, 4, 1, 7]
def baseStart_1832698 : Nat := 118140960795 + 1832698 * 2 ^ 59
def prefixEnd_1832698 : Nat := 4983230072969 + 3 ^ 40 * 1832698 * 2
def baseEnd_1832698 : Nat := 313684989511258598115527

theorem tailTrace_1832698 : CollatzResearch.WordTrace tailWord_1832698 prefixEnd_1832698 313684989511258598115527 := by
  unfold tailWord_1832698
  simp only [CollatzResearch.WordTrace]
  refine ⟨16710996878613905186078687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44562658342970413829543165 16710996878613905186078687)
  ·
    refine ⟨25066495317920857779118031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16710996878613905186078687 25066495317920857779118031)
    ·
      refine ⟨37599742976881286668677047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25066495317920857779118031 37599742976881286668677047)
      ·
        refine ⟨56399614465321930003015571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37599742976881286668677047 56399614465321930003015571)
        ·
          refine ⟨84599421697982895004523357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56399614465321930003015571 84599421697982895004523357)
          ·
            refine ⟨31724783136743585626696259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84599421697982895004523357 31724783136743585626696259)
            ·
              refine ⟨47587174705115378440044389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31724783136743585626696259 47587174705115378440044389)
              ·
                refine ⟨8922595257209133457508323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47587174705115378440044389 8922595257209133457508323)
                ·
                  refine ⟨13383892885813700186262485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8922595257209133457508323 13383892885813700186262485)
                  ·
                    refine ⟨313684989511258598115527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13383892885813700186262485 313684989511258598115527)
                    ·
                      rfl

theorem cell23_1832698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 4, 1, 7].length) (baseStart_1832698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1832698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1832698 prefixEnd_1832698 := by exact prefixLift 1832698
  have htrace : WordTrace (prefixWord ++ tailWord_1832698) baseStart_1832698 baseEnd_1832698 := by
    simpa [prefixWord, tailWord_1832698, baseEnd_1832698] using wordTrace_append hprefix tailTrace_1832698
  have hstable : (prefixWord ++ tailWord_1832698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832698).length < 2 ^ (prefixWord ++ tailWord_1832698).sum := by decide
  have hdescent : baseEnd_1832698 < baseStart_1832698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832702 : List Nat := [4, 2, 2, 1, 3, 1, 1, 2, 7]
def baseStart_1832702 : Nat := 118140960795 + 1832702 * 2 ^ 59
def prefixEnd_1832702 : Nat := 4983230072969 + 3 ^ 40 * 1832702 * 2
def baseEnd_1832702 : Nat := 104561891384043753188507

theorem tailTrace_1832702 : CollatzResearch.WordTrace tailWord_1832702 prefixEnd_1832702 104561891384043753188507 := by
  unfold tailWord_1832702
  simp only [CollatzResearch.WordTrace]
  refine ⟨8355516675805141178432545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44562755604294086284973573 8355516675805141178432545)
  ·
    refine ⟨6266637506853855883824409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8355516675805141178432545 6266637506853855883824409)
    ·
      refine ⟨4699978130140391912868307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6266637506853855883824409 4699978130140391912868307)
      ·
        refine ⟨7049967195210587869302461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4699978130140391912868307 7049967195210587869302461)
        ·
          refine ⟨2643737698203970450988423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7049967195210587869302461 2643737698203970450988423)
          ·
            refine ⟨3965606547305955676482635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2643737698203970450988423 3965606547305955676482635)
            ·
              refine ⟨5948409820958933514723953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3965606547305955676482635 5948409820958933514723953)
              ·
                refine ⟨4461307365719200136042965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5948409820958933514723953 4461307365719200136042965)
                ·
                  refine ⟨104561891384043753188507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4461307365719200136042965 104561891384043753188507)
                  ·
                    rfl

theorem cell23_1832702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 2, 7].length) (baseStart_1832702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1832702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1832702 prefixEnd_1832702 := by exact prefixLift 1832702
  have htrace : WordTrace (prefixWord ++ tailWord_1832702) baseStart_1832702 baseEnd_1832702 := by
    simpa [prefixWord, tailWord_1832702, baseEnd_1832702] using wordTrace_append hprefix tailTrace_1832702
  have hstable : (prefixWord ++ tailWord_1832702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832702).length < 2 ^ (prefixWord ++ tailWord_1832702).sum := by decide
  have hdescent : baseEnd_1832702 < baseStart_1832702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832715 : List Nat := [1, 1, 1, 1, 5, 1, 5, 1, 2, 5]
def baseStart_1832715 : Nat := 118140960795 + 1832715 * 2 ^ 59
def prefixEnd_1832715 : Nat := 4983230072969 + 3 ^ 40 * 1832715 * 2
def baseEnd_1832715 : Nat := 313687899234967409278001

theorem tailTrace_1832715 : CollatzResearch.WordTrace tailWord_1832715 prefixEnd_1832715 313687899234967409278001 := by
  unfold tailWord_1832715
  simp only [CollatzResearch.WordTrace]
  refine ⟨66844607555394032647683599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44563071703596021765122399 66844607555394032647683599)
  ·
    refine ⟨100266911333091048971525399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66844607555394032647683599 100266911333091048971525399)
    ·
      refine ⟨150400366999636573457288099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100266911333091048971525399 150400366999636573457288099)
      ·
        refine ⟨225600550499454860185932149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150400366999636573457288099 225600550499454860185932149)
        ·
          refine ⟨21150051609323893142431139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 225600550499454860185932149 21150051609323893142431139)
          ·
            refine ⟨31725077413985839713646709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21150051609323893142431139 31725077413985839713646709)
            ·
              refine ⟨2974226007561172473154379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31725077413985839713646709 2974226007561172473154379)
              ·
                refine ⟨4461339011341758709731569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2974226007561172473154379 4461339011341758709731569)
                ·
                  refine ⟨3346004258506319032298677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4461339011341758709731569 3346004258506319032298677)
                  ·
                    refine ⟨313687899234967409278001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3346004258506319032298677 313687899234967409278001)
                    ·
                      rfl

theorem cell23_1832715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 1, 2, 5].length) (baseStart_1832715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1832715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1832715 prefixEnd_1832715 := by exact prefixLift 1832715
  have htrace : WordTrace (prefixWord ++ tailWord_1832715) baseStart_1832715 baseEnd_1832715 := by
    simpa [prefixWord, tailWord_1832715, baseEnd_1832715] using wordTrace_append hprefix tailTrace_1832715
  have hstable : (prefixWord ++ tailWord_1832715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832715).length < 2 ^ (prefixWord ++ tailWord_1832715).sum := by decide
  have hdescent : baseEnd_1832715 < baseStart_1832715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832735 : List Nat := [1, 1, 2, 4, 2, 1, 2, 1, 4, 1, 4]
def baseStart_1832735 : Nat := 118140960795 + 1832735 * 2 ^ 59
def prefixEnd_1832735 : Nat := 4983230072969 + 3 ^ 40 * 1832735 * 2
def baseEnd_1832735 : Nat := 941073967317992149583911

theorem tailTrace_1832735 : CollatzResearch.WordTrace tailWord_1832735 prefixEnd_1832735 941073967317992149583911 := by
  unfold tailWord_1832735
  simp only [CollatzResearch.WordTrace]
  refine ⟨66845337015321576063411659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44563558010214384042274439 66845337015321576063411659)
  ·
    refine ⟨100268005522982364095117489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66845337015321576063411659 100268005522982364095117489)
    ·
      refine ⟨75201004142236773071338117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100268005522982364095117489 75201004142236773071338117)
      ·
        refine ⟨14100188276669394950875897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75201004142236773071338117 14100188276669394950875897)
        ·
          refine ⟨10575141207502046213156923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14100188276669394950875897 10575141207502046213156923)
          ·
            refine ⟨15862711811253069319735385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10575141207502046213156923 15862711811253069319735385)
            ·
              refine ⟨11897033858439801989801539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15862711811253069319735385 11897033858439801989801539)
              ·
                refine ⟨17845550787659702984702309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11897033858439801989801539 17845550787659702984702309)
                ·
                  refine ⟨3346040772686194309631683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17845550787659702984702309 3346040772686194309631683)
                  ·
                    refine ⟨5019061159029291464447525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3346040772686194309631683 5019061159029291464447525)
                    ·
                      refine ⟨941073967317992149583911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5019061159029291464447525 941073967317992149583911)
                      ·
                        rfl

theorem cell23_1832735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_1832735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1832735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1832735 prefixEnd_1832735 := by exact prefixLift 1832735
  have htrace : WordTrace (prefixWord ++ tailWord_1832735) baseStart_1832735 baseEnd_1832735 := by
    simpa [prefixWord, tailWord_1832735, baseEnd_1832735] using wordTrace_append hprefix tailTrace_1832735
  have hstable : (prefixWord ++ tailWord_1832735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832735).length < 2 ^ (prefixWord ++ tailWord_1832735).sum := by decide
  have hdescent : baseEnd_1832735 < baseStart_1832735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832762 : List Nat := [3, 1, 1, 1, 5, 1, 2, 2, 3, 4]
def baseStart_1832762 : Nat := 118140960795 + 1832762 * 2 ^ 59
def prefixEnd_1832762 : Nat := 4983230072969 + 3 ^ 40 * 1832762 * 2
def baseEnd_1832762 : Nat := 313695943765221181315429

theorem tailTrace_1832762 : CollatzResearch.WordTrace tailWord_1832762 prefixEnd_1832762 313695943765221181315429 := by
  unfold tailWord_1832762
  simp only [CollatzResearch.WordTrace]
  refine ⟨16711580446555939918661135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44564214524149173116429693 16711580446555939918661135)
  ·
    refine ⟨25067370669833909877991703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16711580446555939918661135 25067370669833909877991703)
    ·
      refine ⟨37601056004750864816987555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25067370669833909877991703 37601056004750864816987555)
      ·
        refine ⟨56401584007126297225481333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37601056004750864816987555 56401584007126297225481333)
        ·
          refine ⟨5287648500668090364888875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56401584007126297225481333 5287648500668090364888875)
          ·
            refine ⟨7931472751002135547333313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5287648500668090364888875 7931472751002135547333313)
            ·
              refine ⟨5948604563251601660499985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7931472751002135547333313 5948604563251601660499985)
              ·
                refine ⟨4461453422438701245374989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5948604563251601660499985 4461453422438701245374989)
                ·
                  refine ⟨1673045033414512967015621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4461453422438701245374989 1673045033414512967015621)
                  ·
                    refine ⟨313695943765221181315429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1673045033414512967015621 313695943765221181315429)
                    ·
                      rfl

theorem cell23_1832762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 2, 3, 4].length) (baseStart_1832762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1832762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1832762 prefixEnd_1832762 := by exact prefixLift 1832762
  have htrace : WordTrace (prefixWord ++ tailWord_1832762) baseStart_1832762 baseEnd_1832762 := by
    simpa [prefixWord, tailWord_1832762, baseEnd_1832762] using wordTrace_append hprefix tailTrace_1832762
  have hstable : (prefixWord ++ tailWord_1832762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832762).length < 2 ^ (prefixWord ++ tailWord_1832762).sum := by decide
  have hdescent : baseEnd_1832762 < baseStart_1832762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832768 : List Nat := [2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 9]
def baseStart_1832768 : Nat := 118140960795 + 1832768 * 2 ^ 59
def prefixEnd_1832768 : Nat := 4983230072969 + 3 ^ 40 * 1832768 * 2
def baseEnd_1832768 : Nat := 941090912179590520471259

theorem tailTrace_1832768 : CollatzResearch.WordTrace tailWord_1832768 prefixEnd_1832768 941090912179590520471259 := by
  unfold tailWord_1832768
  simp only [CollatzResearch.WordTrace]
  refine ⟨33423270312101011349681479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44564360416134681799575305 33423270312101011349681479)
  ·
    refine ⟨50134905468151517024522219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33423270312101011349681479 50134905468151517024522219)
    ·
      refine ⟨75202358202227275536783329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50134905468151517024522219 75202358202227275536783329)
      ·
        refine ⟨56401768651670456652587497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75202358202227275536783329 56401768651670456652587497)
        ·
          refine ⟨42301326488752842489440623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56401768651670456652587497 42301326488752842489440623)
          ·
            refine ⟨63451989733129263734160935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42301326488752842489440623 63451989733129263734160935)
            ·
              refine ⟨95177984599693895601241403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63451989733129263734160935 95177984599693895601241403)
              ·
                refine ⟨142766976899540843401862105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95177984599693895601241403 142766976899540843401862105)
                ·
                  refine ⟨107075232674655632551396579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 142766976899540843401862105 107075232674655632551396579)
                  ·
                    refine ⟨160612849011983448827094869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 107075232674655632551396579 160612849011983448827094869)
                    ·
                      refine ⟨941090912179590520471259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 160612849011983448827094869 941090912179590520471259)
                      ·
                        rfl

theorem cell23_1832768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 9].length) (baseStart_1832768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1832768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1832768 prefixEnd_1832768 := by exact prefixLift 1832768
  have htrace : WordTrace (prefixWord ++ tailWord_1832768) baseStart_1832768 baseEnd_1832768 := by
    simpa [prefixWord, tailWord_1832768, baseEnd_1832768] using wordTrace_append hprefix tailTrace_1832768
  have hstable : (prefixWord ++ tailWord_1832768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832768).length < 2 ^ (prefixWord ++ tailWord_1832768).sum := by decide
  have hdescent : baseEnd_1832768 < baseStart_1832768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832796 : List Nat := [2, 2, 4, 2, 2, 2, 1, 1, 3, 4]
def baseStart_1832796 : Nat := 118140960795 + 1832796 * 2 ^ 59
def prefixEnd_1832796 : Nat := 4983230072969 + 3 ^ 40 * 1832796 * 2
def baseEnd_1832796 : Nat := 313701763212638803640377

theorem tailTrace_1832796 : CollatzResearch.WordTrace tailWord_1832796 prefixEnd_1832796 313701763212638803640377 := by
  unfold tailWord_1832796
  simp only [CollatzResearch.WordTrace]
  refine ⟨33423780934050291740691121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44565041245400388987588161 33423780934050291740691121)
  ·
    refine ⟨25067835700537718805518341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33423780934050291740691121 25067835700537718805518341)
    ·
      refine ⟨4700219193850822276034689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25067835700537718805518341 4700219193850822276034689)
      ·
        refine ⟨3525164395388116707026017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4700219193850822276034689 3525164395388116707026017)
        ·
          refine ⟨2643873296541087530269513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3525164395388116707026017 2643873296541087530269513)
          ·
            refine ⟨1982904972405815647702135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2643873296541087530269513 1982904972405815647702135)
            ·
              refine ⟨2974357458608723471553203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1982904972405815647702135 2974357458608723471553203)
              ·
                refine ⟨4461536187913085207329805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2974357458608723471553203 4461536187913085207329805)
                ·
                  refine ⟨1673076070467406952748677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4461536187913085207329805 1673076070467406952748677)
                  ·
                    refine ⟨313701763212638803640377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1673076070467406952748677 313701763212638803640377)
                    ·
                      rfl

theorem cell23_1832796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_1832796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1832796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1832796 prefixEnd_1832796 := by exact prefixLift 1832796
  have htrace : WordTrace (prefixWord ++ tailWord_1832796) baseStart_1832796 baseEnd_1832796 := by
    simpa [prefixWord, tailWord_1832796, baseEnd_1832796] using wordTrace_append hprefix tailTrace_1832796
  have hstable : (prefixWord ++ tailWord_1832796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832796).length < 2 ^ (prefixWord ++ tailWord_1832796).sum := by decide
  have hdescent : baseEnd_1832796 < baseStart_1832796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832805 : List Nat := [1, 3, 1, 3, 1, 1, 1, 4, 3, 5]
def baseStart_1832805 : Nat := 118140960795 + 1832805 * 2 ^ 59
def prefixEnd_1832805 : Nat := 4983230072969 + 3 ^ 40 * 1832805 * 2
def baseEnd_1832805 : Nat := 313703303654602291902863

theorem tailTrace_1832805 : CollatzResearch.WordTrace tailWord_1832805 prefixEnd_1832805 313703303654602291902863 := by
  unfold tailWord_1832805
  simp only [CollatzResearch.WordTrace]
  refine ⟨66847890125067978018459869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44565260083378652012306579 66847890125067978018459869)
  ·
    refine ⟨25067958796900491756922451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66847890125067978018459869 25067958796900491756922451)
    ·
      refine ⟨37601938195350737635383677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25067958796900491756922451 37601938195350737635383677)
      ·
        refine ⟨14100726823256526613268879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37601938195350737635383677 14100726823256526613268879)
        ·
          refine ⟨21151090234884789919903319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14100726823256526613268879 21151090234884789919903319)
          ·
            refine ⟨31726635352327184879854979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21151090234884789919903319 31726635352327184879854979)
            ·
              refine ⟨47589953028490777319782469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31726635352327184879854979 47589953028490777319782469)
              ·
                refine ⟨8923116192842020747459213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47589953028490777319782469 8923116192842020747459213)
                ·
                  refine ⟨3346168572315757780297205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8923116192842020747459213 3346168572315757780297205)
                  ·
                    refine ⟨313703303654602291902863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3346168572315757780297205 313703303654602291902863)
                    ·
                      rfl

theorem cell23_1832805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 4, 3, 5].length) (baseStart_1832805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1832805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1832805 prefixEnd_1832805 := by exact prefixLift 1832805
  have htrace : WordTrace (prefixWord ++ tailWord_1832805) baseStart_1832805 baseEnd_1832805 := by
    simpa [prefixWord, tailWord_1832805, baseEnd_1832805] using wordTrace_append hprefix tailTrace_1832805
  have hstable : (prefixWord ++ tailWord_1832805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832805).length < 2 ^ (prefixWord ++ tailWord_1832805).sum := by decide
  have hdescent : baseEnd_1832805 < baseStart_1832805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832835 : List Nat := [1, 1, 1, 3, 4, 2, 1, 1, 3, 6]
def baseStart_1832835 : Nat := 118140960795 + 1832835 * 2 ^ 59
def prefixEnd_1832835 : Nat := 4983230072969 + 3 ^ 40 * 1832835 * 2
def baseEnd_1832835 : Nat := 313708438461147252777817

theorem tailTrace_1832835 : CollatzResearch.WordTrace tailWord_1832835 prefixEnd_1832835 313708438461147252777817 := by
  unfold tailWord_1832835
  simp only [CollatzResearch.WordTrace]
  refine ⟨66848984314959293142051959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44565989543306195428034639 66848984314959293142051959)
  ·
    refine ⟨100273476472438939713077939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66848984314959293142051959 100273476472438939713077939)
    ·
      refine ⟨150410214708658409569616909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100273476472438939713077939 150410214708658409569616909)
      ·
        refine ⟨56403830515746903588606341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150410214708658409569616909 56403830515746903588606341)
        ·
          refine ⟨10575718221702544422863689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56403830515746903588606341 10575718221702544422863689)
          ·
            refine ⟨7931788666276908317147767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10575718221702544422863689 7931788666276908317147767)
            ·
              refine ⟨11897682999415362475721651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7931788666276908317147767 11897682999415362475721651)
              ·
                refine ⟨17846524499123043713582477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11897682999415362475721651 17846524499123043713582477)
                ·
                  refine ⟨6692446687171141392593429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17846524499123043713582477 6692446687171141392593429)
                  ·
                    refine ⟨313708438461147252777817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6692446687171141392593429 313708438461147252777817)
                    ·
                      rfl

theorem cell23_1832835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 3, 6].length) (baseStart_1832835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1832835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1832835 prefixEnd_1832835 := by exact prefixLift 1832835
  have htrace : WordTrace (prefixWord ++ tailWord_1832835) baseStart_1832835 baseEnd_1832835 := by
    simpa [prefixWord, tailWord_1832835, baseEnd_1832835] using wordTrace_append hprefix tailTrace_1832835
  have hstable : (prefixWord ++ tailWord_1832835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832835).length < 2 ^ (prefixWord ++ tailWord_1832835).sum := by decide
  have hdescent : baseEnd_1832835 < baseStart_1832835 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832893 : List Nat := [1, 4, 1, 2, 3, 1, 1, 5, 1, 2, 2]
def baseStart_1832893 : Nat := 118140960795 + 1832893 * 2 ^ 59
def prefixEnd_1832893 : Nat := 4983230072969 + 3 ^ 40 * 1832893 * 2
def baseEnd_1832893 : Nat := 941155097261402531408185

theorem tailTrace_1832893 : CollatzResearch.WordTrace tailWord_1832893 prefixEnd_1832893 941155097261402531408185 := by
  unfold tailWord_1832893
  simp only [CollatzResearch.WordTrace]
  refine ⟨66851099748749169047663333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44567399832499446031775555 66851099748749169047663333)
  ·
    refine ⟨12534581202890469196436875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66851099748749169047663333 12534581202890469196436875)
    ·
      refine ⟨18801871804335703794655313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12534581202890469196436875 18801871804335703794655313)
      ·
        refine ⟨14101403853251777845991485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18801871804335703794655313 14101403853251777845991485)
        ·
          refine ⟨5288026444969416692246807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14101403853251777845991485 5288026444969416692246807)
          ·
            refine ⟨7932039667454125038370211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5288026444969416692246807 7932039667454125038370211)
            ·
              refine ⟨11898059501181187557555317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7932039667454125038370211 11898059501181187557555317)
              ·
                refine ⟨1115443078235736333520811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11898059501181187557555317 1115443078235736333520811)
                ·
                  refine ⟨1673164617353604500281217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1115443078235736333520811 1673164617353604500281217)
                  ·
                    refine ⟨1254873463015203375210913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1673164617353604500281217 1254873463015203375210913)
                    ·
                      refine ⟨941155097261402531408185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1254873463015203375210913 941155097261402531408185)
                      ·
                        rfl

theorem cell23_1832893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 5, 1, 2, 2].length) (baseStart_1832893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1832893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1832893 prefixEnd_1832893 := by exact prefixLift 1832893
  have htrace : WordTrace (prefixWord ++ tailWord_1832893) baseStart_1832893 baseEnd_1832893 := by
    simpa [prefixWord, tailWord_1832893, baseEnd_1832893] using wordTrace_append hprefix tailTrace_1832893
  have hstable : (prefixWord ++ tailWord_1832893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832893).length < 2 ^ (prefixWord ++ tailWord_1832893).sum := by decide
  have hdescent : baseEnd_1832893 < baseStart_1832893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832905 : List Nat := [1, 2, 1, 1, 2, 1, 2, 4, 2, 2, 5]
def baseStart_1832905 : Nat := 118140960795 + 1832905 * 2 ^ 59
def prefixEnd_1832905 : Nat := 4983230072969 + 3 ^ 40 * 1832905 * 2
def baseEnd_1832905 : Nat := 941161259029256484458129

theorem tailTrace_1832905 : CollatzResearch.WordTrace tailWord_1832905 prefixEnd_1832905 941161259029256484458129 := by
  unfold tailWord_1832905
  simp only [CollatzResearch.WordTrace]
  refine ⟨66851537424705695097100169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44567691616470463398066779 66851537424705695097100169)
  ·
    refine ⟨50138653068529271322825127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66851537424705695097100169 50138653068529271322825127)
    ·
      refine ⟨75207979602793906984237691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50138653068529271322825127 75207979602793906984237691)
      ·
        refine ⟨112811969404190860476356537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75207979602793906984237691 112811969404190860476356537)
        ·
          refine ⟨84608977053143145357267403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112811969404190860476356537 84608977053143145357267403)
          ·
            refine ⟨126913465579714718035901105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84608977053143145357267403 126913465579714718035901105)
            ·
              refine ⟨95185099184786038526925829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126913465579714718035901105 95185099184786038526925829)
              ·
                refine ⟨17847206097147382223798593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95185099184786038526925829 17847206097147382223798593)
                ·
                  refine ⟨13385404572860536667848945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17847206097147382223798593 13385404572860536667848945)
                  ·
                    refine ⟨10039053429645402500886709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13385404572860536667848945 10039053429645402500886709)
                    ·
                      refine ⟨941161259029256484458129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10039053429645402500886709 941161259029256484458129)
                      ·
                        rfl

theorem cell23_1832905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 2, 2, 5].length) (baseStart_1832905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1832905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1832905 prefixEnd_1832905 := by exact prefixLift 1832905
  have htrace : WordTrace (prefixWord ++ tailWord_1832905) baseStart_1832905 baseEnd_1832905 := by
    simpa [prefixWord, tailWord_1832905, baseEnd_1832905] using wordTrace_append hprefix tailTrace_1832905
  have hstable : (prefixWord ++ tailWord_1832905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832905).length < 2 ^ (prefixWord ++ tailWord_1832905).sum := by decide
  have hdescent : baseEnd_1832905 < baseStart_1832905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832955 : List Nat := [1, 1, 1, 1, 1, 3, 4, 2, 9]
def baseStart_1832955 : Nat := 118140960795 + 1832955 * 2 ^ 59
def prefixEnd_1832955 : Nat := 4983230072969 + 3 ^ 40 * 1832955 * 2
def baseEnd_1832955 : Nat := 104576325895775698759211

theorem tailTrace_1832955 : CollatzResearch.WordTrace tailWord_1832955 prefixEnd_1832955 104576325895775698759211 := by
  unfold tailWord_1832955
  simp only [CollatzResearch.WordTrace]
  refine ⟨66853361074524553636420319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44568907383016369090946879 66853361074524553636420319)
  ·
    refine ⟨100280041611786830454630479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66853361074524553636420319 100280041611786830454630479)
    ·
      refine ⟨150420062417680245681945719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100280041611786830454630479 150420062417680245681945719)
      ·
        refine ⟨225630093626520368522918579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150420062417680245681945719 225630093626520368522918579)
        ·
          refine ⟨338445140439780552784377869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225630093626520368522918579 338445140439780552784377869)
          ·
            refine ⟨126916927664917707294141701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 338445140439780552784377869 126916927664917707294141701)
            ·
              refine ⟨23796923937172070117651569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 126916927664917707294141701 23796923937172070117651569)
              ·
                refine ⟨17847692952879052588238677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23796923937172070117651569 17847692952879052588238677)
                ·
                  refine ⟨104576325895775698759211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 17847692952879052588238677 104576325895775698759211)
                  ·
                    rfl

theorem cell23_1832955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 9].length) (baseStart_1832955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1832955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1832955 prefixEnd_1832955 := by exact prefixLift 1832955
  have htrace : WordTrace (prefixWord ++ tailWord_1832955) baseStart_1832955 baseEnd_1832955 := by
    simpa [prefixWord, tailWord_1832955, baseEnd_1832955] using wordTrace_append hprefix tailTrace_1832955
  have hstable : (prefixWord ++ tailWord_1832955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832955).length < 2 ^ (prefixWord ++ tailWord_1832955).sum := by decide
  have hdescent : baseEnd_1832955 < baseStart_1832955 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833039 : List Nat := [1, 1, 2, 1, 1, 2, 2, 5, 2, 4, 2]
def baseStart_1833039 : Nat := 118140960795 + 1833039 * 2 ^ 59
def prefixEnd_1833039 : Nat := 4983230072969 + 3 ^ 40 * 1833039 * 2
def baseEnd_1833039 : Nat := 941230065436958960182513

theorem tailTrace_1833039 : CollatzResearch.WordTrace tailWord_1833039 prefixEnd_1833039 941230065436958960182513 := by
  unfold tailWord_1833039
  simp only [CollatzResearch.WordTrace]
  refine ⟨66856424806220235982478171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44570949870813490654985447 66856424806220235982478171)
  ·
    refine ⟨100284637209330353973717257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66856424806220235982478171 100284637209330353973717257)
    ·
      refine ⟨75213477906997765480287943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100284637209330353973717257 75213477906997765480287943)
      ·
        refine ⟨112820216860496648220431915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75213477906997765480287943 112820216860496648220431915)
        ·
          refine ⟨169230325290744972330647873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112820216860496648220431915 169230325290744972330647873)
          ·
            refine ⟨126922743968058729247985905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169230325290744972330647873 126922743968058729247985905)
            ·
              refine ⟨95192057976044046935989429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126922743968058729247985905 95192057976044046935989429)
              ·
                refine ⟨8924255435254129400249009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 95192057976044046935989429 8924255435254129400249009)
                ·
                  refine ⟨6693191576440597050186757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8924255435254129400249009 6693191576440597050186757)
                  ·
                    refine ⟨1254973420582611946910017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6693191576440597050186757 1254973420582611946910017)
                    ·
                      refine ⟨941230065436958960182513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1254973420582611946910017 941230065436958960182513)
                      ·
                        rfl

theorem cell23_1833039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 5, 2, 4, 2].length) (baseStart_1833039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1833039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1833039 prefixEnd_1833039 := by exact prefixLift 1833039
  have htrace : WordTrace (prefixWord ++ tailWord_1833039) baseStart_1833039 baseEnd_1833039 := by
    simpa [prefixWord, tailWord_1833039, baseEnd_1833039] using wordTrace_append hprefix tailTrace_1833039
  have hstable : (prefixWord ++ tailWord_1833039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833039).length < 2 ^ (prefixWord ++ tailWord_1833039).sum := by decide
  have hdescent : baseEnd_1833039 < baseStart_1833039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833049 : List Nat := [1, 2, 1, 2, 2, 1, 5, 2, 3, 4]
def baseStart_1833049 : Nat := 118140960795 + 1833049 * 2 ^ 59
def prefixEnd_1833049 : Nat := 4983230072969 + 3 ^ 40 * 1833049 * 2
def baseEnd_1833049 : Nat := 313745066747834640352489

theorem tailTrace_1833049 : CollatzResearch.WordTrace tailWord_1833049 prefixEnd_1833049 313745066747834640352489 := by
  unfold tailWord_1833049
  simp only [CollatzResearch.WordTrace]
  refine ⟨66856789536184007690342201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44571193024122671793561467 66856789536184007690342201)
  ·
    refine ⟨50142592152138005767756651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66856789536184007690342201 50142592152138005767756651)
    ·
      refine ⟨75213888228207008651634977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50142592152138005767756651 75213888228207008651634977)
      ·
        refine ⟨56410416171155256488726233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75213888228207008651634977 56410416171155256488726233)
        ·
          refine ⟨42307812128366442366544675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56410416171155256488726233 42307812128366442366544675)
          ·
            refine ⟨63461718192549663549817013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42307812128366442366544675 63461718192549663549817013)
            ·
              refine ⟨5949536080551530957795345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63461718192549663549817013 5949536080551530957795345)
              ·
                refine ⟨4462152060413648218346509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5949536080551530957795345 4462152060413648218346509)
                ·
                  refine ⟨1673307022655118081879941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4462152060413648218346509 1673307022655118081879941)
                  ·
                    refine ⟨313745066747834640352489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1673307022655118081879941 313745066747834640352489)
                    ·
                      rfl

theorem cell23_1833049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 2, 3, 4].length) (baseStart_1833049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1833049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1833049 prefixEnd_1833049 := by exact prefixLift 1833049
  have htrace : WordTrace (prefixWord ++ tailWord_1833049) baseStart_1833049 baseEnd_1833049 := by
    simpa [prefixWord, tailWord_1833049, baseEnd_1833049] using wordTrace_append hprefix tailTrace_1833049
  have hstable : (prefixWord ++ tailWord_1833049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833049).length < 2 ^ (prefixWord ++ tailWord_1833049).sum := by decide
  have hdescent : baseEnd_1833049 < baseStart_1833049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833053 : List Nat := [1, 4, 4, 1, 1, 3, 1, 1, 2, 5]
def baseStart_1833053 : Nat := 118140960795 + 1833053 * 2 ^ 59
def prefixEnd_1833053 : Nat := 4983230072969 + 3 ^ 40 * 1833053 * 2
def baseEnd_1833053 : Nat := 313745751388707301802483

theorem tailTrace_1833053 : CollatzResearch.WordTrace tailWord_1833053 prefixEnd_1833053 313745751388707301802483 := by
  unfold tailWord_1833053
  simp only [CollatzResearch.WordTrace]
  refine ⟨66856935428169516373487813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44571290285446344248991875 66856935428169516373487813)
  ·
    refine ⟨12535675392781784320028965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66856935428169516373487813 12535675392781784320028965)
    ·
      refine ⟨2350439136146584560005431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12535675392781784320028965 2350439136146584560005431)
      ·
        refine ⟨3525658704219876840008147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2350439136146584560005431 3525658704219876840008147)
        ·
          refine ⟨5288488056329815260012221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3525658704219876840008147 5288488056329815260012221)
          ·
            refine ⟨1983183021123680722504583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5288488056329815260012221 1983183021123680722504583)
            ·
              refine ⟨2974774531685521083756875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1983183021123680722504583 2974774531685521083756875)
              ·
                refine ⟨4462161797528281625635313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2974774531685521083756875 4462161797528281625635313)
                ·
                  refine ⟨3346621348146211219226485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4462161797528281625635313 3346621348146211219226485)
                  ·
                    refine ⟨313745751388707301802483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3346621348146211219226485 313745751388707301802483)
                    ·
                      rfl

theorem cell23_1833053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_1833053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1833053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1833053 prefixEnd_1833053 := by exact prefixLift 1833053
  have htrace : WordTrace (prefixWord ++ tailWord_1833053) baseStart_1833053 baseEnd_1833053 := by
    simpa [prefixWord, tailWord_1833053, baseEnd_1833053] using wordTrace_append hprefix tailTrace_1833053
  have hstable : (prefixWord ++ tailWord_1833053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833053).length < 2 ^ (prefixWord ++ tailWord_1833053).sum := by decide
  have hdescent : baseEnd_1833053 < baseStart_1833053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833056 : List Nat := [2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 4]
def baseStart_1833056 : Nat := 118140960795 + 1833056 * 2 ^ 59
def prefixEnd_1833056 : Nat := 4983230072969 + 3 ^ 40 * 1833056 * 2
def baseEnd_1833056 : Nat := 941238794608085393669935

theorem tailTrace_1833056 : CollatzResearch.WordTrace tailWord_1833056 prefixEnd_1833056 941238794608085393669935 := by
  unfold tailWord_1833056
  simp only [CollatzResearch.WordTrace]
  refine ⟨33428522423579323942923511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44571363231439098590564681 33428522423579323942923511)
  ·
    refine ⟨50142783635368985914385267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33428522423579323942923511 50142783635368985914385267)
    ·
      refine ⟨75214175453053478871577901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50142783635368985914385267 75214175453053478871577901)
      ·
        refine ⟨28205315794895054576841713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75214175453053478871577901 28205315794895054576841713)
        ·
          refine ⟨21153986846171290932631285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28205315794895054576841713 21153986846171290932631285)
          ·
            refine ⟨1983186266828558524934183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21153986846171290932631285 1983186266828558524934183)
            ·
              refine ⟨2974779400242837787401275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1983186266828558524934183 2974779400242837787401275)
              ·
                refine ⟨4462169100364256681101913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2974779400242837787401275 4462169100364256681101913)
                ·
                  refine ⟨3346626825273192510826435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4462169100364256681101913 3346626825273192510826435)
                  ·
                    refine ⟨5019940237909788766239653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3346626825273192510826435 5019940237909788766239653)
                    ·
                      refine ⟨941238794608085393669935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5019940237909788766239653 941238794608085393669935)
                      ·
                        rfl

theorem cell23_1833056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 4].length) (baseStart_1833056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1833056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1833056 prefixEnd_1833056 := by exact prefixLift 1833056
  have htrace : WordTrace (prefixWord ++ tailWord_1833056) baseStart_1833056 baseEnd_1833056 := by
    simpa [prefixWord, tailWord_1833056, baseEnd_1833056] using wordTrace_append hprefix tailTrace_1833056
  have hstable : (prefixWord ++ tailWord_1833056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833056).length < 2 ^ (prefixWord ++ tailWord_1833056).sum := by decide
  have hdescent : baseEnd_1833056 < baseStart_1833056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833079 : List Nat := [1, 1, 3, 1, 1, 5, 3, 2, 6]
def baseStart_1833079 : Nat := 118140960795 + 1833079 * 2 ^ 59
def prefixEnd_1833079 : Nat := 4983230072969 + 3 ^ 40 * 1833079 * 2
def baseEnd_1833079 : Nat := 104583400518126533742481

theorem tailTrace_1833079 : CollatzResearch.WordTrace tailWord_1833079 prefixEnd_1833079 104583400518126533742481 := by
  unfold tailWord_1833079
  simp only [CollatzResearch.WordTrace]
  refine ⟨66857883726075322813934291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44571922484050215209289527 66857883726075322813934291)
  ·
    refine ⟨100286825589112984220901437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66857883726075322813934291 100286825589112984220901437)
    ·
      refine ⟨37607559595917369082838039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100286825589112984220901437 37607559595917369082838039)
      ·
        refine ⟨56411339393876053624257059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37607559595917369082838039 56411339393876053624257059)
        ·
          refine ⟨84617009090814080436385589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56411339393876053624257059 84617009090814080436385589)
          ·
            refine ⟨7932844602263820040911149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84617009090814080436385589 7932844602263820040911149)
            ·
              refine ⟨2974816725848932515341681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7932844602263820040911149 2974816725848932515341681)
              ·
                refine ⟨2231112544386699386506261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2974816725848932515341681 2231112544386699386506261)
                ·
                  refine ⟨104583400518126533742481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2231112544386699386506261 104583400518126533742481)
                  ·
                    rfl

theorem cell23_1833079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 2, 6].length) (baseStart_1833079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1833079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1833079 prefixEnd_1833079 := by exact prefixLift 1833079
  have htrace : WordTrace (prefixWord ++ tailWord_1833079) baseStart_1833079 baseEnd_1833079 := by
    simpa [prefixWord, tailWord_1833079, baseEnd_1833079] using wordTrace_append hprefix tailTrace_1833079
  have hstable : (prefixWord ++ tailWord_1833079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833079).length < 2 ^ (prefixWord ++ tailWord_1833079).sum := by decide
  have hdescent : baseEnd_1833079 < baseStart_1833079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833116 : List Nat := [2, 2, 3, 2, 1, 1, 1, 3, 1, 5, 2]
def baseStart_1833116 : Nat := 118140960795 + 1833116 * 2 ^ 59
def prefixEnd_1833116 : Nat := 4983230072969 + 3 ^ 40 * 1833116 * 2
def baseEnd_1833116 : Nat := 941269603447355158919659

theorem tailTrace_1833116 : CollatzResearch.WordTrace tailWord_1833116 prefixEnd_1833116 941269603447355158919659 := by
  unfold tailWord_1833116
  simp only [CollatzResearch.WordTrace]
  refine ⟨33429616613470639066515601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44572822151294185422020801 33429616613470639066515601)
  ·
    refine ⟨25072212460102979299886701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33429616613470639066515601 25072212460102979299886701)
    ·
      refine ⟨9402079672538617237457513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25072212460102979299886701 9402079672538617237457513)
      ·
        refine ⟨7051559754403962928093135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9402079672538617237457513 7051559754403962928093135)
        ·
          refine ⟨10577339631605944392139703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7051559754403962928093135 10577339631605944392139703)
          ·
            refine ⟨15866009447408916588209555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10577339631605944392139703 15866009447408916588209555)
            ·
              refine ⟨23799014171113374882314333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15866009447408916588209555 23799014171113374882314333)
              ·
                refine ⟨8924630314167515580867875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23799014171113374882314333 8924630314167515580867875)
                ·
                  refine ⟨13386945471251273371301813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8924630314167515580867875 13386945471251273371301813)
                  ·
                    refine ⟨1255026137929806878559545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13386945471251273371301813 1255026137929806878559545)
                    ·
                      refine ⟨941269603447355158919659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1255026137929806878559545 941269603447355158919659)
                      ·
                        rfl

theorem cell23_1833116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 3, 1, 5, 2].length) (baseStart_1833116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1833116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1833116 prefixEnd_1833116 := by exact prefixLift 1833116
  have htrace : WordTrace (prefixWord ++ tailWord_1833116) baseStart_1833116 baseEnd_1833116 := by
    simpa [prefixWord, tailWord_1833116, baseEnd_1833116] using wordTrace_append hprefix tailTrace_1833116
  have hstable : (prefixWord ++ tailWord_1833116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833116).length < 2 ^ (prefixWord ++ tailWord_1833116).sum := by decide
  have hdescent : baseEnd_1833116 < baseStart_1833116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833133 : List Nat := [1, 5, 2, 1, 2, 1, 1, 1, 4, 3, 2]
def baseStart_1833133 : Nat := 118140960795 + 1833133 * 2 ^ 59
def prefixEnd_1833133 : Nat := 4983230072969 + 3 ^ 40 * 1833133 * 2
def baseEnd_1833133 : Nat := 941278332618481592407081

theorem tailTrace_1833133 : CollatzResearch.WordTrace tailWord_1833133 prefixEnd_1833133 941278332618481592407081 := by
  unfold tailWord_1833133
  simp only [CollatzResearch.WordTrace]
  refine ⟨66859853267879690036400053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44573235511919793357600035 66859853267879690036400053)
  ·
    refine ⟨6268111243863720940912505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66859853267879690036400053 6268111243863720940912505)
    ·
      refine ⟨4701083432897790705684379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6268111243863720940912505 4701083432897790705684379)
      ·
        refine ⟨7051625149346686058526569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4701083432897790705684379 7051625149346686058526569)
        ·
          refine ⟨5288718862010014543894927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7051625149346686058526569 5288718862010014543894927)
          ·
            refine ⟨7933078293015021815842391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5288718862010014543894927 7933078293015021815842391)
            ·
              refine ⟨11899617439522532723763587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7933078293015021815842391 11899617439522532723763587)
              ·
                refine ⟨17849426159283799085645381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11899617439522532723763587 17849426159283799085645381)
                ·
                  refine ⟨3346767404865712328558509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17849426159283799085645381 3346767404865712328558509)
                  ·
                    refine ⟨1255037776824642123209441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3346767404865712328558509 1255037776824642123209441)
                    ·
                      refine ⟨941278332618481592407081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1255037776824642123209441 941278332618481592407081)
                      ·
                        rfl

theorem cell23_1833133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 4, 3, 2].length) (baseStart_1833133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1833133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1833133 prefixEnd_1833133 := by exact prefixLift 1833133
  have htrace : WordTrace (prefixWord ++ tailWord_1833133) baseStart_1833133 baseEnd_1833133 := by
    simpa [prefixWord, tailWord_1833133, baseEnd_1833133] using wordTrace_append hprefix tailTrace_1833133
  have hstable : (prefixWord ++ tailWord_1833133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833133).length < 2 ^ (prefixWord ++ tailWord_1833133).sum := by decide
  have hdescent : baseEnd_1833133 < baseStart_1833133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833134 : List Nat := [4, 1, 4, 2, 1, 1, 3, 2, 1, 4]
def baseStart_1833134 : Nat := 118140960795 + 1833134 * 2 ^ 59
def prefixEnd_1833134 : Nat := 4983230072969 + 3 ^ 40 * 1833134 * 2
def baseEnd_1833134 : Nat := 313759615366378696164859

theorem tailTrace_1833134 : CollatzResearch.WordTrace tailWord_1833134 prefixEnd_1833134 313759615366378696164859 := by
  unfold tailWord_1833134
  simp only [CollatzResearch.WordTrace]
  refine ⟨8357486217609508400898307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44573259827250711471457637 8357486217609508400898307)
  ·
    refine ⟨12536229326414262601347461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8357486217609508400898307 12536229326414262601347461)
    ·
      refine ⟨2350542998702674237752649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12536229326414262601347461 2350542998702674237752649)
      ·
        refine ⟨1762907249027005678314487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2350542998702674237752649 1762907249027005678314487)
        ·
          refine ⟨2644360873540508517471731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1762907249027005678314487 2644360873540508517471731)
          ·
            refine ⟨3966541310310762776207597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2644360873540508517471731 3966541310310762776207597)
            ·
              refine ⟨1487452991366536041077849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3966541310310762776207597 1487452991366536041077849)
              ·
                refine ⟨1115589743524902030808387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1487452991366536041077849 1115589743524902030808387)
                ·
                  refine ⟨1673384615287353046212581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1115589743524902030808387 1673384615287353046212581)
                  ·
                    refine ⟨313759615366378696164859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1673384615287353046212581 313759615366378696164859)
                    ·
                      rfl

theorem cell23_1833134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_1833134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1833134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1833134 prefixEnd_1833134 := by exact prefixLift 1833134
  have htrace : WordTrace (prefixWord ++ tailWord_1833134) baseStart_1833134 baseEnd_1833134 := by
    simpa [prefixWord, tailWord_1833134, baseEnd_1833134] using wordTrace_append hprefix tailTrace_1833134
  have hstable : (prefixWord ++ tailWord_1833134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833134).length < 2 ^ (prefixWord ++ tailWord_1833134).sum := by decide
  have hdescent : baseEnd_1833134 < baseStart_1833134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833149 : List Nat := [1, 4, 1, 2, 1, 1, 1, 1, 2, 6, 3]
def baseStart_1833149 : Nat := 118140960795 + 1833149 * 2 ^ 59
def prefixEnd_1833149 : Nat := 4983230072969 + 3 ^ 40 * 1833149 * 2
def baseEnd_1833149 : Nat := 941286548308953529807007

theorem tailTrace_1833149 : CollatzResearch.WordTrace tailWord_1833149 prefixEnd_1833149 941286548308953529807007 := by
  unfold tailWord_1833149
  simp only [CollatzResearch.WordTrace]
  refine ⟨66860436835821724768982501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44573624557214483179321667 66860436835821724768982501)
  ·
    refine ⟨12536331906716573394184219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66860436835821724768982501 12536331906716573394184219)
    ·
      refine ⟨18804497860074860091276329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12536331906716573394184219 18804497860074860091276329)
      ·
        refine ⟨14103373395056145068457247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18804497860074860091276329 14103373395056145068457247)
        ·
          refine ⟨21155060092584217602685871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14103373395056145068457247 21155060092584217602685871)
          ·
            refine ⟨31732590138876326404028807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21155060092584217602685871 31732590138876326404028807)
            ·
              refine ⟨47598885208314489606043211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31732590138876326404028807 47598885208314489606043211)
              ·
                refine ⟨71398327812471734409064817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47598885208314489606043211 71398327812471734409064817)
                ·
                  refine ⟨53548745859353800806798613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71398327812471734409064817 53548745859353800806798613)
                  ·
                    refine ⟨2510097462157209412818685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 53548745859353800806798613 2510097462157209412818685)
                    ·
                      refine ⟨941286548308953529807007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2510097462157209412818685 941286548308953529807007)
                      ·
                        rfl

theorem cell23_1833149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 6, 3].length) (baseStart_1833149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1833149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1833149 prefixEnd_1833149 := by exact prefixLift 1833149
  have htrace : WordTrace (prefixWord ++ tailWord_1833149) baseStart_1833149 baseEnd_1833149 := by
    simpa [prefixWord, tailWord_1833149, baseEnd_1833149] using wordTrace_append hprefix tailTrace_1833149
  have hstable : (prefixWord ++ tailWord_1833149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833149).length < 2 ^ (prefixWord ++ tailWord_1833149).sum := by decide
  have hdescent : baseEnd_1833149 < baseStart_1833149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833176 : List Nat := [2, 1, 2, 2, 4, 2, 1, 2, 1, 2, 4]
def baseStart_1833176 : Nat := 118140960795 + 1833176 * 2 ^ 59
def prefixEnd_1833176 : Nat := 4983230072969 + 3 ^ 40 * 1833176 * 2
def baseEnd_1833176 : Nat := 941300412286624924169383

theorem tailTrace_1833176 : CollatzResearch.WordTrace tailWord_1833176 prefixEnd_1833176 941300412286624924169383 := by
  unfold tailWord_1833176
  simp only [CollatzResearch.WordTrace]
  refine ⟨33430710803361954190107691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44574281071149272253476921 33430710803361954190107691)
  ·
    refine ⟨50146066205042931285161537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33430710803361954190107691 50146066205042931285161537)
    ·
      refine ⟨37609549653782198463871153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50146066205042931285161537 37609549653782198463871153)
      ·
        refine ⟨28207162240336648847903365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37609549653782198463871153 28207162240336648847903365)
        ·
          refine ⟨5288842920063121658981881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28207162240336648847903365 5288842920063121658981881)
          ·
            refine ⟨3966632190047341244236411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5288842920063121658981881 3966632190047341244236411)
            ·
              refine ⟨5949948285071011866354617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3966632190047341244236411 5949948285071011866354617)
              ·
                refine ⟨4462461213803258899765963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5949948285071011866354617 4462461213803258899765963)
                ·
                  refine ⟨6693691820704888349648945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4462461213803258899765963 6693691820704888349648945)
                  ·
                    refine ⟨5020268865528666262236709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6693691820704888349648945 5020268865528666262236709)
                    ·
                      refine ⟨941300412286624924169383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5020268865528666262236709 941300412286624924169383)
                      ·
                        rfl

theorem cell23_1833176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 2, 1, 2, 4].length) (baseStart_1833176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1833176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1833176 prefixEnd_1833176 := by exact prefixLift 1833176
  have htrace : WordTrace (prefixWord ++ tailWord_1833176) baseStart_1833176 baseEnd_1833176 := by
    simpa [prefixWord, tailWord_1833176, baseEnd_1833176] using wordTrace_append hprefix tailTrace_1833176
  have hstable : (prefixWord ++ tailWord_1833176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833176).length < 2 ^ (prefixWord ++ tailWord_1833176).sum := by decide
  have hdescent : baseEnd_1833176 < baseStart_1833176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833179 : List Nat := [1, 1, 1, 1, 1, 1, 1, 7, 3, 3, 3]
def baseStart_1833179 : Nat := 118140960795 + 1833179 * 2 ^ 59
def prefixEnd_1833179 : Nat := 4983230072969 + 3 ^ 40 * 1833179 * 2
def baseEnd_1833179 : Nat := 941301952728588412431869

theorem tailTrace_1833179 : CollatzResearch.WordTrace tailWord_1833179 prefixEnd_1833179 941301952728588412431869 := by
  unfold tailWord_1833179
  simp only [CollatzResearch.WordTrace]
  refine ⟨66861531025713039892574591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44574354017142026595049727 66861531025713039892574591)
  ·
    refine ⟨100292296538569559838861887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66861531025713039892574591 100292296538569559838861887)
    ·
      refine ⟨150438444807854339758292831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100292296538569559838861887 150438444807854339758292831)
      ·
        refine ⟨225657667211781509637439247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150438444807854339758292831 225657667211781509637439247)
        ·
          refine ⟨338486500817672264456158871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225657667211781509637439247 338486500817672264456158871)
          ·
            refine ⟨507729751226508396684238307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 338486500817672264456158871 507729751226508396684238307)
            ·
              refine ⟨761594626839762595026357461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 507729751226508396684238307 761594626839762595026357461)
              ·
                refine ⟨17849874066556935820930253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 761594626839762595026357461 17849874066556935820930253)
                ·
                  refine ⟨6693702774958850932848845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17849874066556935820930253 6693702774958850932848845)
                  ·
                    refine ⟨2510138540609569099818317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6693702774958850932848845 2510138540609569099818317)
                    ·
                      refine ⟨941301952728588412431869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2510138540609569099818317 941301952728588412431869)
                      ·
                        rfl

theorem cell23_1833179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 3, 3, 3].length) (baseStart_1833179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1833179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1833179 prefixEnd_1833179 := by exact prefixLift 1833179
  have htrace : WordTrace (prefixWord ++ tailWord_1833179) baseStart_1833179 baseEnd_1833179 := by
    simpa [prefixWord, tailWord_1833179, baseEnd_1833179] using wordTrace_append hprefix tailTrace_1833179
  have hstable : (prefixWord ++ tailWord_1833179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833179).length < 2 ^ (prefixWord ++ tailWord_1833179).sum := by decide
  have hdescent : baseEnd_1833179 < baseStart_1833179 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833199 : List Nat := [1, 1, 2, 1, 6, 1, 1, 1, 2, 7]
def baseStart_1833199 : Nat := 118140960795 + 1833199 * 2 ^ 59
def prefixEnd_1833199 : Nat := 4983230072969 + 3 ^ 40 * 1833199 * 2
def baseEnd_1833199 : Nat := 313770740780559444727259

theorem tailTrace_1833199 : CollatzResearch.WordTrace tailWord_1833199 prefixEnd_1833199 313770740780559444727259 := by
  unfold tailWord_1833199
  simp only [CollatzResearch.WordTrace]
  refine ⟨66862260485640583308302651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44574840323760388872201767 66862260485640583308302651)
  ·
    refine ⟨100293390728460874962453977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66862260485640583308302651 100293390728460874962453977)
    ·
      refine ⟨75220043046345656221840483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100293390728460874962453977 75220043046345656221840483)
      ·
        refine ⟨112830064569518484332760725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75220043046345656221840483 112830064569518484332760725)
        ·
          refine ⟨5288909276696178953098159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 112830064569518484332760725 5288909276696178953098159)
          ·
            refine ⟨7933363915044268429647239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5288909276696178953098159 7933363915044268429647239)
            ·
              refine ⟨11900045872566402644470859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7933363915044268429647239 11900045872566402644470859)
              ·
                refine ⟨17850068808849603966706289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11900045872566402644470859 17850068808849603966706289)
                ·
                  refine ⟨13387551606637202975029717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17850068808849603966706289 13387551606637202975029717)
                  ·
                    refine ⟨313770740780559444727259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13387551606637202975029717 313770740780559444727259)
                    ·
                      rfl

theorem cell23_1833199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 2, 7].length) (baseStart_1833199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1833199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1833199 prefixEnd_1833199 := by exact prefixLift 1833199
  have htrace : WordTrace (prefixWord ++ tailWord_1833199) baseStart_1833199 baseEnd_1833199 := by
    simpa [prefixWord, tailWord_1833199, baseEnd_1833199] using wordTrace_append hprefix tailTrace_1833199
  have hstable : (prefixWord ++ tailWord_1833199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833199).length < 2 ^ (prefixWord ++ tailWord_1833199).sum := by decide
  have hdescent : baseEnd_1833199 < baseStart_1833199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833219 : List Nat := [1, 1, 1, 3, 2, 3, 1, 2, 2, 3, 4]
def baseStart_1833219 : Nat := 118140960795 + 1833219 * 2 ^ 59
def prefixEnd_1833219 : Nat := 4983230072969 + 3 ^ 40 * 1833219 * 2
def baseEnd_1833219 : Nat := 941322491954768255931685

theorem tailTrace_1833219 : CollatzResearch.WordTrace tailWord_1833219 prefixEnd_1833219 941322491954768255931685 := by
  unfold tailWord_1833219
  simp only [CollatzResearch.WordTrace]
  refine ⟨66862989945568126724030711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44575326630378751149353807 66862989945568126724030711)
  ·
    refine ⟨100294484918352190086046067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66862989945568126724030711 100294484918352190086046067)
    ·
      refine ⟨150441727377528285129069101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100294484918352190086046067 150441727377528285129069101)
      ·
        refine ⟨56415647766573106923400913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150441727377528285129069101 56415647766573106923400913)
        ·
          refine ⟨42311735824929830192550685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56415647766573106923400913 42311735824929830192550685)
          ·
            refine ⟨15866900934348686322206507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42311735824929830192550685 15866900934348686322206507)
            ·
              refine ⟨23800351401523029483309761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15866900934348686322206507 23800351401523029483309761)
              ·
                refine ⟨17850263551142272112482321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23800351401523029483309761 17850263551142272112482321)
                ·
                  refine ⟨13387697663356704084361741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17850263551142272112482321 13387697663356704084361741)
                  ·
                    refine ⟨5020386623758764031635653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13387697663356704084361741 5020386623758764031635653)
                    ·
                      refine ⟨941322491954768255931685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5020386623758764031635653 941322491954768255931685)
                      ·
                        rfl

theorem cell23_1833219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 2, 3, 4].length) (baseStart_1833219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1833219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1833219 prefixEnd_1833219 := by exact prefixLift 1833219
  have htrace : WordTrace (prefixWord ++ tailWord_1833219) baseStart_1833219 baseEnd_1833219 := by
    simpa [prefixWord, tailWord_1833219, baseEnd_1833219] using wordTrace_append hprefix tailTrace_1833219
  have hstable : (prefixWord ++ tailWord_1833219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833219).length < 2 ^ (prefixWord ++ tailWord_1833219).sum := by decide
  have hdescent : baseEnd_1833219 < baseStart_1833219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833316 : List Nat := [2, 3, 1, 1, 3, 1, 3, 1, 1, 2, 5]
def baseStart_1833316 : Nat := 118140960795 + 1833316 * 2 ^ 59
def prefixEnd_1833316 : Nat := 4983230072969 + 3 ^ 40 * 1833316 * 2
def baseEnd_1833316 : Nat := 941372299578254376418739

theorem tailTrace_1833316 : CollatzResearch.WordTrace tailWord_1833316 prefixEnd_1833316 941372299578254376418739 := by
  unfold tailWord_1833316
  simp only [CollatzResearch.WordTrace]
  refine ⟨33433263913108356145155901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44577685217477808193541201 33433263913108356145155901)
  ·
    refine ⟨12537473967415633554433463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33433263913108356145155901 12537473967415633554433463)
    ·
      refine ⟨18806210951123450331650195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12537473967415633554433463 18806210951123450331650195)
      ·
        refine ⟨28209316426685175497475293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18806210951123450331650195 28209316426685175497475293)
        ·
          refine ⟨10578493660006940811553235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28209316426685175497475293 10578493660006940811553235)
          ·
            refine ⟨15867740490010411217329853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10578493660006940811553235 15867740490010411217329853)
            ·
              refine ⟨5950402683753904206498695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15867740490010411217329853 5950402683753904206498695)
              ·
                refine ⟨8925604025630856309748043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5950402683753904206498695 8925604025630856309748043)
                ·
                  refine ⟨13388406038446284464622065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8925604025630856309748043 13388406038446284464622065)
                  ·
                    refine ⟨10041304528834713348466549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13388406038446284464622065 10041304528834713348466549)
                    ·
                      refine ⟨941372299578254376418739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10041304528834713348466549 941372299578254376418739)
                      ·
                        rfl

theorem cell23_1833316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 1, 1, 2, 5].length) (baseStart_1833316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1833316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1833316 prefixEnd_1833316 := by exact prefixLift 1833316
  have htrace : WordTrace (prefixWord ++ tailWord_1833316) baseStart_1833316 baseEnd_1833316 := by
    simpa [prefixWord, tailWord_1833316, baseEnd_1833316] using wordTrace_append hprefix tailTrace_1833316
  have hstable : (prefixWord ++ tailWord_1833316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833316).length < 2 ^ (prefixWord ++ tailWord_1833316).sum := by decide
  have hdescent : baseEnd_1833316 < baseStart_1833316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833377 : List Nat := [1, 2, 3, 5, 1, 1, 1, 1, 2, 4, 2]
def baseStart_1833377 : Nat := 118140960795 + 1833377 * 2 ^ 59
def prefixEnd_1833377 : Nat := 4983230072969 + 3 ^ 40 * 1833377 * 2
def baseEnd_1833377 : Nat := 941403621898178637755959

theorem tailTrace_1833377 : CollatzResearch.WordTrace tailWord_1833377 prefixEnd_1833377 941403621898178637755959 := by
  unfold tailWord_1833377
  simp only [CollatzResearch.WordTrace]
  refine ⟨66868752678995719708282385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44579168452663813138854923 66868752678995719708282385)
  ·
    refine ⟨50151564509246789781211789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66868752678995719708282385 50151564509246789781211789)
    ·
      refine ⟨18806836690967546167954421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50151564509246789781211789 18806836690967546167954421)
      ·
        refine ⟨1763140939778207453245727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18806836690967546167954421 1763140939778207453245727)
        ·
          refine ⟨2644711409667311179868591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1763140939778207453245727 2644711409667311179868591)
          ·
            refine ⟨3967067114500966769802887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2644711409667311179868591 3967067114500966769802887)
            ·
              refine ⟨5950600671751450154704331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3967067114500966769802887 5950600671751450154704331)
              ·
                refine ⟨8925901007627175232056497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5950600671751450154704331 8925901007627175232056497)
                ·
                  refine ⟨6694425755720381424042373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8925901007627175232056497 6694425755720381424042373)
                  ·
                    refine ⟨1255204829197571517007945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6694425755720381424042373 1255204829197571517007945)
                    ·
                      refine ⟨941403621898178637755959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1255204829197571517007945 941403621898178637755959)
                      ·
                        rfl

theorem cell23_1833377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_1833377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1833377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1833377 prefixEnd_1833377 := by exact prefixLift 1833377
  have htrace : WordTrace (prefixWord ++ tailWord_1833377) baseStart_1833377 baseEnd_1833377 := by
    simpa [prefixWord, tailWord_1833377, baseEnd_1833377] using wordTrace_append hprefix tailTrace_1833377
  have hstable : (prefixWord ++ tailWord_1833377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833377).length < 2 ^ (prefixWord ++ tailWord_1833377).sum := by decide
  have hdescent : baseEnd_1833377 < baseStart_1833377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833383 : List Nat := [1, 1, 6, 1, 1, 2, 2, 3, 6]
def baseStart_1833383 : Nat := 118140960795 + 1833383 * 2 ^ 59
def prefixEnd_1833383 : Nat := 4983230072969 + 3 ^ 40 * 1833383 * 2
def baseEnd_1833383 : Nat := 104600744753567290475659

theorem tailTrace_1833383 : CollatzResearch.WordTrace tailWord_1833383 prefixEnd_1833383 104600744753567290475659 := by
  unfold tailWord_1833383
  simp only [CollatzResearch.WordTrace]
  refine ⟨66868971516973982733000803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44579314344649321822000535 66868971516973982733000803)
  ·
    refine ⟨100303457275460974099501205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66868971516973982733000803 100303457275460974099501205)
    ·
      refine ⟨4701724559787233160914119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 100303457275460974099501205 4701724559787233160914119)
      ·
        refine ⟨7052586839680849741371179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4701724559787233160914119 7052586839680849741371179)
        ·
          refine ⟨10578880259521274612056769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7052586839680849741371179 10578880259521274612056769)
          ·
            refine ⟨7934160194640955959042577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10578880259521274612056769 7934160194640955959042577)
            ·
              refine ⟨5950620145980716969281933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7934160194640955959042577 5950620145980716969281933)
              ·
                refine ⟨2231482554742768863480725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5950620145980716969281933 2231482554742768863480725)
                ·
                  refine ⟨104600744753567290475659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2231482554742768863480725 104600744753567290475659)
                  ·
                    rfl

theorem cell23_1833383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 3, 6].length) (baseStart_1833383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1833383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1833383 prefixEnd_1833383 := by exact prefixLift 1833383
  have htrace : WordTrace (prefixWord ++ tailWord_1833383) baseStart_1833383 baseEnd_1833383 := by
    simpa [prefixWord, tailWord_1833383, baseEnd_1833383] using wordTrace_append hprefix tailTrace_1833383
  have hstable : (prefixWord ++ tailWord_1833383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833383).length < 2 ^ (prefixWord ++ tailWord_1833383).sum := by decide
  have hdescent : baseEnd_1833383 < baseStart_1833383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833397 : List Nat := [1, 3, 3, 2, 3, 2, 1, 1, 2, 2, 3]
def baseStart_1833397 : Nat := 118140960795 + 1833397 * 2 ^ 59
def prefixEnd_1833397 : Nat := 4983230072969 + 3 ^ 40 * 1833397 * 2
def baseEnd_1833397 : Nat := 941413891511268559505867

theorem tailTrace_1833397 : CollatzResearch.WordTrace tailWord_1833397 prefixEnd_1833397 941413891511268559505867 := by
  unfold tailWord_1833397
  simp only [CollatzResearch.WordTrace]
  refine ⟨66869482138923263124010445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44579654759282175416006963 66869482138923263124010445)
  ·
    refine ⟨25076055802096223671503917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66869482138923263124010445 25076055802096223671503917)
    ·
      refine ⟨9403520925786083876813969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25076055802096223671503917 9403520925786083876813969)
      ·
        refine ⟨7052640694339562907610477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9403520925786083876813969 7052640694339562907610477)
        ·
          refine ⟨2644740260377336090353929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7052640694339562907610477 2644740260377336090353929)
          ·
            refine ⟨1983555195283002067765447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2644740260377336090353929 1983555195283002067765447)
            ·
              refine ⟨2975332792924503101648171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1983555195283002067765447 2975332792924503101648171)
              ·
                refine ⟨4462999189386754652472257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2975332792924503101648171 4462999189386754652472257)
                ·
                  refine ⟨3347249392040065989354193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4462999189386754652472257 3347249392040065989354193)
                  ·
                    refine ⟨2510437044030049492015645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3347249392040065989354193 2510437044030049492015645)
                    ·
                      refine ⟨941413891511268559505867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2510437044030049492015645 941413891511268559505867)
                      ·
                        rfl

theorem cell23_1833397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_1833397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1833397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1833397 prefixEnd_1833397 := by exact prefixLift 1833397
  have htrace : WordTrace (prefixWord ++ tailWord_1833397) baseStart_1833397 baseEnd_1833397 := by
    simpa [prefixWord, tailWord_1833397, baseEnd_1833397] using wordTrace_append hprefix tailTrace_1833397
  have hstable : (prefixWord ++ tailWord_1833397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833397).length < 2 ^ (prefixWord ++ tailWord_1833397).sum := by decide
  have hdescent : baseEnd_1833397 < baseStart_1833397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833403 : List Nat := [1, 1, 1, 1, 1, 2, 2, 1, 8, 3, 2]
def baseStart_1833403 : Nat := 118140960795 + 1833403 * 2 ^ 59
def prefixEnd_1833403 : Nat := 4983230072969 + 3 ^ 40 * 1833403 * 2
def baseEnd_1833403 : Nat := 941416972395195536030839

theorem tailTrace_1833403 : CollatzResearch.WordTrace tailWord_1833403 prefixEnd_1833403 941416972395195536030839 := by
  unfold tailWord_1833403
  simp only [CollatzResearch.WordTrace]
  refine ⟨66869700976901526148728863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44579800651267684099152575 66869700976901526148728863)
  ·
    refine ⟨100304551465352289223093295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66869700976901526148728863 100304551465352289223093295)
    ·
      refine ⟨150456827198028433834639943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100304551465352289223093295 150456827198028433834639943)
      ·
        refine ⟨225685240797042650751959915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150456827198028433834639943 225685240797042650751959915)
        ·
          refine ⟨338527861195563976127939873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225685240797042650751959915 338527861195563976127939873)
          ·
            refine ⟨253895895896672982095954905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 338527861195563976127939873 253895895896672982095954905)
            ·
              refine ⟨190421921922504736571966179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 253895895896672982095954905 190421921922504736571966179)
              ·
                refine ⟨285632882883757104857949269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190421921922504736571966179 285632882883757104857949269)
                ·
                  refine ⟨3347260346294028572554093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 285632882883757104857949269 3347260346294028572554093)
                  ·
                    refine ⟨1255222629860260714707785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3347260346294028572554093 1255222629860260714707785)
                    ·
                      refine ⟨941416972395195536030839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1255222629860260714707785 941416972395195536030839)
                      ·
                        rfl

theorem cell23_1833403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 8, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 8, 3, 2].length) (baseStart_1833403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1833403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1833403 prefixEnd_1833403 := by exact prefixLift 1833403
  have htrace : WordTrace (prefixWord ++ tailWord_1833403) baseStart_1833403 baseEnd_1833403 := by
    simpa [prefixWord, tailWord_1833403, baseEnd_1833403] using wordTrace_append hprefix tailTrace_1833403
  have hstable : (prefixWord ++ tailWord_1833403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833403).length < 2 ^ (prefixWord ++ tailWord_1833403).sum := by decide
  have hdescent : baseEnd_1833403 < baseStart_1833403 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833450 : List Nat := [3, 1, 3, 1, 3, 1, 1, 4, 1, 1, 4]
def baseStart_1833450 : Nat := 118140960795 + 1833450 * 2 ^ 59
def prefixEnd_1833450 : Nat := 4983230072969 + 3 ^ 40 * 1833450 * 2
def baseEnd_1833450 : Nat := 941441105985956852143123

theorem tailTrace_1833450 : CollatzResearch.WordTrace tailWord_1833450 prefixEnd_1833450 941441105985956852143123 := by
  unfold tailWord_1833450
  simp only [CollatzResearch.WordTrace]
  refine ⟨16717853801932813293922451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44580943471820835450459869 16717853801932813293922451)
  ·
    refine ⟨25076780702899219940883677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16717853801932813293922451 25076780702899219940883677)
    ·
      refine ⟨9403792763587207477831379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25076780702899219940883677 9403792763587207477831379)
      ·
        refine ⟨14105689145380811216747069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9403792763587207477831379 14105689145380811216747069)
        ·
          refine ⟨5289633429517804206280151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14105689145380811216747069 5289633429517804206280151)
          ·
            refine ⟨7934450144276706309420227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5289633429517804206280151 7934450144276706309420227)
            ·
              refine ⟨11901675216415059464130341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7934450144276706309420227 11901675216415059464130341)
              ·
                refine ⟨2231564103077823649524439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11901675216415059464130341 2231564103077823649524439)
                ·
                  refine ⟨3347346154616735474286659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2231564103077823649524439 3347346154616735474286659)
                  ·
                    refine ⟨5021019231925103211429989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3347346154616735474286659 5021019231925103211429989)
                    ·
                      refine ⟨941441105985956852143123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5021019231925103211429989 941441105985956852143123)
                      ·
                        rfl

theorem cell23_1833450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 4, 1, 1, 4].length) (baseStart_1833450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1833450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1833450 prefixEnd_1833450 := by exact prefixLift 1833450
  have htrace : WordTrace (prefixWord ++ tailWord_1833450) baseStart_1833450 baseEnd_1833450 := by
    simpa [prefixWord, tailWord_1833450, baseEnd_1833450] using wordTrace_append hprefix tailTrace_1833450
  have hstable : (prefixWord ++ tailWord_1833450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833450).length < 2 ^ (prefixWord ++ tailWord_1833450).sum := by decide
  have hdescent : baseEnd_1833450 < baseStart_1833450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833456 : List Nat := [2, 1, 1, 1, 3, 3, 3, 9]
def baseStart_1833456 : Nat := 118140960795 + 1833456 * 2 ^ 59
def prefixEnd_1833456 : Nat := 4983230072969 + 3 ^ 40 * 1833456 * 2
def baseEnd_1833456 : Nat := 34868303217403104765485

theorem tailTrace_1833456 : CollatzResearch.WordTrace tailWord_1833456 prefixEnd_1833456 34868303217403104765485 := by
  unfold tailWord_1833456
  simp only [CollatzResearch.WordTrace]
  refine ⟨33435817022854758100204111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44581089363806344133605481 33435817022854758100204111)
  ·
    refine ⟨50153725534282137150306167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33435817022854758100204111 50153725534282137150306167)
    ·
      refine ⟨75230588301423205725459251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50153725534282137150306167 75230588301423205725459251)
      ·
        refine ⟨112845882452134808588188877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75230588301423205725459251 112845882452134808588188877)
        ·
          refine ⟨42317205919550553220570829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112845882452134808588188877 42317205919550553220570829)
          ·
            refine ⟨15868952219831457457714061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42317205919550553220570829 15868952219831457457714061)
            ·
              refine ⟨5950857082436796546642773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15868952219831457457714061 5950857082436796546642773)
              ·
                refine ⟨34868303217403104765485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5950857082436796546642773 34868303217403104765485)
                ·
                  rfl

theorem cell23_1833456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 9].length) (baseStart_1833456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1833456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1833456 prefixEnd_1833456 := by exact prefixLift 1833456
  have htrace : WordTrace (prefixWord ++ tailWord_1833456) baseStart_1833456 baseEnd_1833456 := by
    simpa [prefixWord, tailWord_1833456, baseEnd_1833456] using wordTrace_append hprefix tailTrace_1833456
  have hstable : (prefixWord ++ tailWord_1833456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833456).length < 2 ^ (prefixWord ++ tailWord_1833456).sum := by decide
  have hdescent : baseEnd_1833456 < baseStart_1833456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833473 : List Nat := [1, 2, 4, 1, 3, 3, 9]
def baseStart_1833473 : Nat := 118140960795 + 1833473 * 2 ^ 59
def prefixEnd_1833473 : Nat := 4983230072969 + 3 ^ 40 * 1833473 * 2
def baseEnd_1833473 : Nat := 11622875506679139038957

theorem tailTrace_1833473 : CollatzResearch.WordTrace tailWord_1833473 prefixEnd_1833473 11622875506679139038957 := by
  unfold tailWord_1833473
  simp only [CollatzResearch.WordTrace]
  refine ⟨66872254086647928103777073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44581502724431952069184715 66872254086647928103777073)
  ·
    refine ⟨50154190564985946077832805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66872254086647928103777073 50154190564985946077832805)
    ·
      refine ⟨9403910730934864889593651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50154190564985946077832805 9403910730934864889593651)
      ·
        refine ⟨14105866096402297334390477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9403910730934864889593651 14105866096402297334390477)
        ·
          refine ⟨5289699786150861500396429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14105866096402297334390477 5289699786150861500396429)
          ·
            refine ⟨1983637419806573062648661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5289699786150861500396429 1983637419806573062648661)
            ·
              refine ⟨11622875506679139038957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1983637419806573062648661 11622875506679139038957)
              ·
                rfl

theorem cell23_1833473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 9].length) (baseStart_1833473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1833473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1833473 prefixEnd_1833473 := by exact prefixLift 1833473
  have htrace : WordTrace (prefixWord ++ tailWord_1833473) baseStart_1833473 baseEnd_1833473 := by
    simpa [prefixWord, tailWord_1833473, baseEnd_1833473] using wordTrace_append hprefix tailTrace_1833473
  have hstable : (prefixWord ++ tailWord_1833473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833473).length < 2 ^ (prefixWord ++ tailWord_1833473).sum := by decide
  have hdescent : baseEnd_1833473 < baseStart_1833473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833478 : List Nat := [6, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3]
def baseStart_1833478 : Nat := 118140960795 + 1833478 * 2 ^ 59
def prefixEnd_1833478 : Nat := 4983230072969 + 3 ^ 40 * 1833478 * 2
def baseEnd_1833478 : Nat := 941455483444282742592995

theorem tailTrace_1833478 : CollatzResearch.WordTrace tailWord_1833478 prefixEnd_1833478 941455483444282742592995 := by
  unfold tailWord_1833478
  simp only [CollatzResearch.WordTrace]
  refine ⟨2089763639113431686178409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 44581624301086542638472725 2089763639113431686178409)
  ·
    refine ⟨1567322729335073764633807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2089763639113431686178409 1567322729335073764633807)
    ·
      refine ⟨2350984094002610646950711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1567322729335073764633807 2350984094002610646950711)
      ·
        refine ⟨3526476141003915970426067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2350984094002610646950711 3526476141003915970426067)
        ·
          refine ⟨5289714211505873955639101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3526476141003915970426067 5289714211505873955639101)
          ·
            refine ⟨1983642829314702733364663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5289714211505873955639101 1983642829314702733364663)
            ·
              refine ⟨2975464243972054100046995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1983642829314702733364663 2975464243972054100046995)
              ·
                refine ⟨4463196365958081150070493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2975464243972054100046995 4463196365958081150070493)
                ·
                  refine ⟨1673698637234280431276435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4463196365958081150070493 1673698637234280431276435)
                  ·
                    refine ⟨2510547955851420646914653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1673698637234280431276435 2510547955851420646914653)
                    ·
                      refine ⟨941455483444282742592995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2510547955851420646914653 941455483444282742592995)
                      ·
                        rfl

theorem cell23_1833478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_1833478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1833478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1833478 prefixEnd_1833478 := by exact prefixLift 1833478
  have htrace : WordTrace (prefixWord ++ tailWord_1833478) baseStart_1833478 baseEnd_1833478 := by
    simpa [prefixWord, tailWord_1833478, baseEnd_1833478] using wordTrace_append hprefix tailTrace_1833478
  have hstable : (prefixWord ++ tailWord_1833478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833478).length < 2 ^ (prefixWord ++ tailWord_1833478).sum := by decide
  have hdescent : baseEnd_1833478 < baseStart_1833478 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833484 : List Nat := [2, 2, 1, 2, 4, 3, 1, 1, 3, 2, 2]
def baseStart_1833484 : Nat := 118140960795 + 1833484 * 2 ^ 59
def prefixEnd_1833484 : Nat := 4983230072969 + 3 ^ 40 * 1833484 * 2
def baseEnd_1833484 : Nat := 941458564328209719117967

theorem tailTrace_1833484 : CollatzResearch.WordTrace tailWord_1833484 prefixEnd_1833484 941458564328209719117967 := by
  unfold tailWord_1833484
  simp only [CollatzResearch.WordTrace]
  refine ⟨33436327644804038491213753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44581770193072051321618337 33436327644804038491213753)
  ·
    refine ⟨25077245733603028868410315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33436327644804038491213753 25077245733603028868410315)
    ·
      refine ⟨37615868600404543302615473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25077245733603028868410315 37615868600404543302615473)
      ·
        refine ⟨28211901450303407476961605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37615868600404543302615473 28211901450303407476961605)
        ·
          refine ⟨5289731521931888901930301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28211901450303407476961605 5289731521931888901930301)
          ·
            refine ⟨1983649320724458338223863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5289731521931888901930301 1983649320724458338223863)
            ·
              refine ⟨2975473981086687507335795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1983649320724458338223863 2975473981086687507335795)
              ·
                refine ⟨4463210971630031261003693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2975473981086687507335795 4463210971630031261003693)
                ·
                  refine ⟨1673704114361261722876385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4463210971630031261003693 1673704114361261722876385)
                  ·
                    refine ⟨1255278085770946292157289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1673704114361261722876385 1255278085770946292157289)
                    ·
                      refine ⟨941458564328209719117967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1255278085770946292157289 941458564328209719117967)
                      ·
                        rfl

theorem cell23_1833484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 1, 3, 2, 2].length) (baseStart_1833484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1833484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1833484 prefixEnd_1833484 := by exact prefixLift 1833484
  have htrace : WordTrace (prefixWord ++ tailWord_1833484) baseStart_1833484 baseEnd_1833484 := by
    simpa [prefixWord, tailWord_1833484, baseEnd_1833484] using wordTrace_append hprefix tailTrace_1833484
  have hstable : (prefixWord ++ tailWord_1833484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833484).length < 2 ^ (prefixWord ++ tailWord_1833484).sum := by decide
  have hdescent : baseEnd_1833484 < baseStart_1833484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833504 : List Nat := [2, 1, 1, 6, 2, 2, 1, 2, 1, 2, 3]
def baseStart_1833504 : Nat := 118140960795 + 1833504 * 2 ^ 59
def prefixEnd_1833504 : Nat := 4983230072969 + 3 ^ 40 * 1833504 * 2
def baseEnd_1833504 : Nat := 941468833941299640867875

theorem tailTrace_1833504 : CollatzResearch.WordTrace tailWord_1833504 prefixEnd_1833504 941468833941299640867875 := by
  unfold tailWord_1833504
  simp only [CollatzResearch.WordTrace]
  refine ⟨33436692374767810199077783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44582256499690413598770377 33436692374767810199077783)
  ·
    refine ⟨50155038562151715298616675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33436692374767810199077783 50155038562151715298616675)
    ·
      refine ⟨75232557843227572947925013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50155038562151715298616675 75232557843227572947925013)
      ·
        refine ⟨3526526148901292481933985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 75232557843227572947925013 3526526148901292481933985)
        ·
          refine ⟨2644894611675969361450489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3526526148901292481933985 2644894611675969361450489)
          ·
            refine ⟨1983670958756977021087867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2644894611675969361450489 1983670958756977021087867)
            ·
              refine ⟨2975506438135465531631801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1983670958756977021087867 2975506438135465531631801)
              ·
                refine ⟨2231629828601599148723851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2975506438135465531631801 2231629828601599148723851)
                ·
                  refine ⟨3347444742902398723085777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2231629828601599148723851 3347444742902398723085777)
                  ·
                    refine ⟨2510583557176799042314333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3347444742902398723085777 2510583557176799042314333)
                    ·
                      refine ⟨941468833941299640867875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2510583557176799042314333 941468833941299640867875)
                      ·
                        rfl

theorem cell23_1833504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_1833504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1833504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1833504 prefixEnd_1833504 := by exact prefixLift 1833504
  have htrace : WordTrace (prefixWord ++ tailWord_1833504) baseStart_1833504 baseEnd_1833504 := by
    simpa [prefixWord, tailWord_1833504, baseEnd_1833504] using wordTrace_append hprefix tailTrace_1833504
  have hstable : (prefixWord ++ tailWord_1833504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833504).length < 2 ^ (prefixWord ++ tailWord_1833504).sum := by decide
  have hdescent : baseEnd_1833504 < baseStart_1833504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833553 : List Nat := [1, 2, 2, 1, 3, 3, 1, 1, 1, 4, 4]
def baseStart_1833553 : Nat := 118140960795 + 1833553 * 2 ^ 59
def prefixEnd_1833553 : Nat := 4983230072969 + 3 ^ 40 * 1833553 * 2
def baseEnd_1833553 : Nat := 941493994493369949155149

theorem tailTrace_1833553 : CollatzResearch.WordTrace tailWord_1833553 prefixEnd_1833553 941493994493369949155149 := by
  unfold tailWord_1833553
  simp only [CollatzResearch.WordTrace]
  refine ⟨66875171926358101766689313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44583447950905401177792875 66875171926358101766689313)
  ·
    refine ⟨50156378944768576325016985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66875171926358101766689313 50156378944768576325016985)
    ·
      refine ⟨37617284208576432243762739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50156378944768576325016985 37617284208576432243762739)
      ·
        refine ⟨56425926312864648365644109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37617284208576432243762739 56425926312864648365644109)
        ·
          refine ⟨21159722367324243137116541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56425926312864648365644109 21159722367324243137116541)
          ·
            refine ⟨7934895887746591176418703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21159722367324243137116541 7934895887746591176418703)
            ·
              refine ⟨11902343831619886764628055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7934895887746591176418703 11902343831619886764628055)
              ·
                refine ⟨17853515747429830146942083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11902343831619886764628055 17853515747429830146942083)
                ·
                  refine ⟨26780273621144745220413125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17853515747429830146942083 26780273621144745220413125)
                  ·
                    refine ⟨5021301303964639728827461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26780273621144745220413125 5021301303964639728827461)
                    ·
                      refine ⟨941493994493369949155149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5021301303964639728827461 941493994493369949155149)
                      ·
                        rfl

theorem cell23_1833553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 4, 4].length) (baseStart_1833553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1833553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1833553 prefixEnd_1833553 := by exact prefixLift 1833553
  have htrace : WordTrace (prefixWord ++ tailWord_1833553) baseStart_1833553 baseEnd_1833553 := by
    simpa [prefixWord, tailWord_1833553, baseEnd_1833553] using wordTrace_append hprefix tailTrace_1833553
  have hstable : (prefixWord ++ tailWord_1833553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833553).length < 2 ^ (prefixWord ++ tailWord_1833553).sum := by decide
  have hdescent : baseEnd_1833553 < baseStart_1833553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833580 : List Nat := [2, 2, 1, 1, 3, 1, 3, 5, 5]
def baseStart_1833580 : Nat := 118140960795 + 1833580 * 2 ^ 59
def prefixEnd_1833580 : Nat := 4983230072969 + 3 ^ 40 * 1833580 * 2
def baseEnd_1833580 : Nat := 104611984274560149279725

theorem tailTrace_1833580 : CollatzResearch.WordTrace tailWord_1833580 prefixEnd_1833580 104611984274560149279725 := by
  unfold tailWord_1833580
  simp only [CollatzResearch.WordTrace]
  refine ⟨33438078348630142688961097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44584104464840190251948129 33438078348630142688961097)
  ·
    refine ⟨25078558761472607016720823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33438078348630142688961097 25078558761472607016720823)
    ·
      refine ⟨37617838142208910525081235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25078558761472607016720823 37617838142208910525081235)
      ·
        refine ⟨56426757213313365787621853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37617838142208910525081235 56426757213313365787621853)
        ·
          refine ⟨21160033954992512170358195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56426757213313365787621853 21160033954992512170358195)
          ·
            refine ⟨31740050932488768255537293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21160033954992512170358195 31740050932488768255537293)
            ·
              refine ⟨11902519099683288095826485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31740050932488768255537293 11902519099683288095826485)
              ·
                refine ⟨1115861165595308258983733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11902519099683288095826485 1115861165595308258983733)
                ·
                  refine ⟨104611984274560149279725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1115861165595308258983733 104611984274560149279725)
                  ·
                    rfl

theorem cell23_1833580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 5, 5].length) (baseStart_1833580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1833580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1833580 prefixEnd_1833580 := by exact prefixLift 1833580
  have htrace : WordTrace (prefixWord ++ tailWord_1833580) baseStart_1833580 baseEnd_1833580 := by
    simpa [prefixWord, tailWord_1833580, baseEnd_1833580] using wordTrace_append hprefix tailTrace_1833580
  have hstable : (prefixWord ++ tailWord_1833580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833580).length < 2 ^ (prefixWord ++ tailWord_1833580).sum := by decide
  have hdescent : baseEnd_1833580 < baseStart_1833580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833603 : List Nat := [1, 1, 1, 3, 3, 1, 2, 3, 1, 2, 5]
def baseStart_1833603 : Nat := 118140960795 + 1833603 * 2 ^ 59
def prefixEnd_1833603 : Nat := 4983230072969 + 3 ^ 40 * 1833603 * 2
def baseEnd_1833603 : Nat := 941519668526094753529919

theorem tailTrace_1833603 : CollatzResearch.WordTrace tailWord_1833603 prefixEnd_1833603 941519668526094753529919 := by
  unfold tailWord_1833603
  simp only [CollatzResearch.WordTrace]
  refine ⟨66876995576176960306009463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44584663717451306870672975 66876995576176960306009463)
  ·
    refine ⟨100315493364265440459014195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66876995576176960306009463 100315493364265440459014195)
    ·
      refine ⟨150473240046398160688521293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100315493364265440459014195 150473240046398160688521293)
      ·
        refine ⟨56427465017399310258195485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150473240046398160688521293 56427465017399310258195485)
        ·
          refine ⟨21160299381524741346823307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56427465017399310258195485 21160299381524741346823307)
          ·
            refine ⟨31740449072287112020234961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21160299381524741346823307 31740449072287112020234961)
            ·
              refine ⟨23805336804215334015176221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31740449072287112020234961 23805336804215334015176221)
              ·
                refine ⟨8927001301580750255691083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23805336804215334015176221 8927001301580750255691083)
                ·
                  refine ⟨13390501952371125383536625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8927001301580750255691083 13390501952371125383536625)
                  ·
                    refine ⟨10042876464278344037652469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13390501952371125383536625 10042876464278344037652469)
                    ·
                      refine ⟨941519668526094753529919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10042876464278344037652469 941519668526094753529919)
                      ·
                        rfl

theorem cell23_1833603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 3, 1, 2, 5].length) (baseStart_1833603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1833603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1833603 prefixEnd_1833603 := by exact prefixLift 1833603
  have htrace : WordTrace (prefixWord ++ tailWord_1833603) baseStart_1833603 baseEnd_1833603 := by
    simpa [prefixWord, tailWord_1833603, baseEnd_1833603] using wordTrace_append hprefix tailTrace_1833603
  have hstable : (prefixWord ++ tailWord_1833603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833603).length < 2 ^ (prefixWord ++ tailWord_1833603).sum := by decide
  have hdescent : baseEnd_1833603 < baseStart_1833603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833623 : List Nat := [1, 1, 3, 3, 2, 1, 1, 1, 2, 8]
def baseStart_1833623 : Nat := 118140960795 + 1833623 * 2 ^ 59
def prefixEnd_1833623 : Nat := 4983230072969 + 3 ^ 40 * 1833623 * 2
def baseEnd_1833623 : Nat := 313843312713061558426609

theorem tailTrace_1833623 : CollatzResearch.WordTrace tailWord_1833623 prefixEnd_1833623 313843312713061558426609 := by
  unfold tailWord_1833623
  simp only [CollatzResearch.WordTrace]
  refine ⟨66877725036104503721737523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44585150024069669147825015 66877725036104503721737523)
  ·
    refine ⟨100316587554156755582606285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66877725036104503721737523 100316587554156755582606285)
    ·
      refine ⟨37618720332808783343477357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100316587554156755582606285 37618720332808783343477357)
      ·
        refine ⟨14107020124803293753804009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37618720332808783343477357 14107020124803293753804009)
        ·
          refine ⟨10580265093602470315353007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14107020124803293753804009 10580265093602470315353007)
          ·
            refine ⟨15870397640403705473029511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10580265093602470315353007 15870397640403705473029511)
            ·
              refine ⟨23805596460605558209544267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15870397640403705473029511 23805596460605558209544267)
              ·
                refine ⟨35708394690908337314316401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23805596460605558209544267 35708394690908337314316401)
                ·
                  refine ⟨26781296018181252985737301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35708394690908337314316401 26781296018181252985737301)
                  ·
                    refine ⟨313843312713061558426609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 26781296018181252985737301 313843312713061558426609)
                    ·
                      rfl

theorem cell23_1833623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 8].length) (baseStart_1833623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1833623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1833623 prefixEnd_1833623 := by exact prefixLift 1833623
  have htrace : WordTrace (prefixWord ++ tailWord_1833623) baseStart_1833623 baseEnd_1833623 := by
    simpa [prefixWord, tailWord_1833623, baseEnd_1833623] using wordTrace_append hprefix tailTrace_1833623
  have hstable : (prefixWord ++ tailWord_1833623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833623).length < 2 ^ (prefixWord ++ tailWord_1833623).sum := by decide
  have hdescent : baseEnd_1833623 < baseStart_1833623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833654 : List Nat := [5, 1, 3, 1, 2, 1, 1, 1, 1, 2, 5]
def baseStart_1833654 : Nat := 118140960795 + 1833654 * 2 ^ 59
def prefixEnd_1833654 : Nat := 4983230072969 + 3 ^ 40 * 1833654 * 2
def baseEnd_1833654 : Nat := 941545856039474053992185

theorem tailTrace_1833654 : CollatzResearch.WordTrace tailWord_1833654 prefixEnd_1833654 941545856039474053992185 := by
  unfold tailWord_1833654
  simp only [CollatzResearch.WordTrace]
  refine ⟨4179928481187012251007251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44585903799328130677410677 4179928481187012251007251)
  ·
    refine ⟨6269892721780518376510877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4179928481187012251007251 6269892721780518376510877)
    ·
      refine ⟨2351209770667694391191579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6269892721780518376510877 2351209770667694391191579)
      ·
        refine ⟨3526814656001541586787369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2351209770667694391191579 3526814656001541586787369)
        ·
          refine ⟨2645110992001156190090527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3526814656001541586787369 2645110992001156190090527)
          ·
            refine ⟨3967666488001734285135791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2645110992001156190090527 3967666488001734285135791)
            ·
              refine ⟨5951499732002601427703687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3967666488001734285135791 5951499732002601427703687)
              ·
                refine ⟨8927249598003902141555531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5951499732002601427703687 8927249598003902141555531)
                ·
                  refine ⟨13390874397005853212333297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8927249598003902141555531 13390874397005853212333297)
                  ·
                    refine ⟨10043155797754389909249973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13390874397005853212333297 10043155797754389909249973)
                    ·
                      refine ⟨941545856039474053992185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10043155797754389909249973 941545856039474053992185)
                      ·
                        rfl

theorem cell23_1833654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_1833654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1833654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1833654 prefixEnd_1833654 := by exact prefixLift 1833654
  have htrace : WordTrace (prefixWord ++ tailWord_1833654) baseStart_1833654 baseEnd_1833654 := by
    simpa [prefixWord, tailWord_1833654, baseEnd_1833654] using wordTrace_append hprefix tailTrace_1833654
  have hstable : (prefixWord ++ tailWord_1833654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833654).length < 2 ^ (prefixWord ++ tailWord_1833654).sum := by decide
  have hdescent : baseEnd_1833654 < baseStart_1833654 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833720 : List Nat := [2, 1, 2, 1, 1, 2, 3, 1, 5, 1, 4]
def baseStart_1833720 : Nat := 118140960795 + 1833720 * 2 ^ 59
def prefixEnd_1833720 : Nat := 4983230072969 + 3 ^ 40 * 1833720 * 2
def baseEnd_1833720 : Nat := 941579745762670795766881

theorem tailTrace_1833720 : CollatzResearch.WordTrace tailWord_1833720 prefixEnd_1833720 941579745762670795766881 := by
  unfold tailWord_1833720
  simp only [CollatzResearch.WordTrace]
  refine ⟨33440631458376544644009307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44587508611168726192012409 33440631458376544644009307)
  ·
    refine ⟨50160947187564816966013961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33440631458376544644009307 50160947187564816966013961)
    ·
      refine ⟨37620710390673612724510471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50160947187564816966013961 37620710390673612724510471)
      ·
        refine ⟨56431065586010419086765707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37620710390673612724510471 56431065586010419086765707)
        ·
          refine ⟨84646598379015628630148561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56431065586010419086765707 84646598379015628630148561)
          ·
            refine ⟨63484948784261721472611421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84646598379015628630148561 63484948784261721472611421)
            ·
              refine ⟨23806855794098145552229283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63484948784261721472611421 23806855794098145552229283)
              ·
                refine ⟨35710283691147218328343925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23806855794098145552229283 35710283691147218328343925)
                ·
                  refine ⟨3347839096045051718282243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35710283691147218328343925 3347839096045051718282243)
                  ·
                    refine ⟨5021758644067577577423365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3347839096045051718282243 5021758644067577577423365)
                    ·
                      refine ⟨941579745762670795766881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5021758644067577577423365 941579745762670795766881)
                      ·
                        rfl

theorem cell23_1833720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 5, 1, 4].length) (baseStart_1833720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1833720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1833720 prefixEnd_1833720 := by exact prefixLift 1833720
  have htrace : WordTrace (prefixWord ++ tailWord_1833720) baseStart_1833720 baseEnd_1833720 := by
    simpa [prefixWord, tailWord_1833720, baseEnd_1833720] using wordTrace_append hprefix tailTrace_1833720
  have hstable : (prefixWord ++ tailWord_1833720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833720).length < 2 ^ (prefixWord ++ tailWord_1833720).sum := by decide
  have hdescent : baseEnd_1833720 < baseStart_1833720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833751 : List Nat := [1, 1, 3, 4, 3, 2, 2, 1, 1, 5]
def baseStart_1833751 : Nat := 118140960795 + 1833751 * 2 ^ 59
def prefixEnd_1833751 : Nat := 4983230072969 + 3 ^ 40 * 1833751 * 2
def baseEnd_1833751 : Nat := 313865221220986724826413

theorem tailTrace_1833751 : CollatzResearch.WordTrace tailWord_1833751 prefixEnd_1833751 313865221220986724826413 := by
  unfold tailWord_1833751
  simp only [CollatzResearch.WordTrace]
  refine ⟨66882393579640781582397107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44588262386427187721598071 66882393579640781582397107)
  ·
    refine ⟨100323590369461172373595661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66882393579640781582397107 100323590369461172373595661)
    ·
      refine ⟨37621346388547939640098373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100323590369461172373595661 37621346388547939640098373)
      ·
        refine ⟨7054002447852738682518445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37621346388547939640098373 7054002447852738682518445)
        ·
          refine ⟨2645250917944777005944417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7054002447852738682518445 2645250917944777005944417)
          ·
            refine ⟨1983938188458582754458313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2645250917944777005944417 1983938188458582754458313)
            ·
              refine ⟨1487953641343937065843735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1983938188458582754458313 1487953641343937065843735)
              ·
                refine ⟨2231930462015905598765603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1487953641343937065843735 2231930462015905598765603)
                ·
                  refine ⟨3347895693023858398148405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2231930462015905598765603 3347895693023858398148405)
                  ·
                    refine ⟨313865221220986724826413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3347895693023858398148405 313865221220986724826413)
                    ·
                      rfl

theorem cell23_1833751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 2, 1, 1, 5].length) (baseStart_1833751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1833751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1833751 prefixEnd_1833751 := by exact prefixLift 1833751
  have htrace : WordTrace (prefixWord ++ tailWord_1833751) baseStart_1833751 baseEnd_1833751 := by
    simpa [prefixWord, tailWord_1833751, baseEnd_1833751] using wordTrace_append hprefix tailTrace_1833751
  have hstable : (prefixWord ++ tailWord_1833751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833751).length < 2 ^ (prefixWord ++ tailWord_1833751).sum := by decide
  have hdescent : baseEnd_1833751 < baseStart_1833751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833754 : List Nat := [3, 1, 1, 3, 2, 1, 1, 2, 5, 2, 2]
def baseStart_1833754 : Nat := 118140960795 + 1833754 * 2 ^ 59
def prefixEnd_1833754 : Nat := 4983230072969 + 3 ^ 40 * 1833754 * 2
def baseEnd_1833754 : Nat := 941597204104923662741725

theorem tailTrace_1833754 : CollatzResearch.WordTrace tailWord_1833754 prefixEnd_1833754 941597204104923662741725 := by
  unfold tailWord_1833754
  simp only [CollatzResearch.WordTrace]
  refine ⟨16720625749657478273689079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44588335332419942063170877 16720625749657478273689079)
  ·
    refine ⟨25080938624486217410533619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16720625749657478273689079 25080938624486217410533619)
    ·
      refine ⟨37621407936729326115800429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25080938624486217410533619 37621407936729326115800429)
      ·
        refine ⟨14108027976273497293425161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37621407936729326115800429 14108027976273497293425161)
        ·
          refine ⟨10581020982205122970068871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14108027976273497293425161 10581020982205122970068871)
          ·
            refine ⟨15871531473307684455103307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10581020982205122970068871 15871531473307684455103307)
            ·
              refine ⟨23807297209961526682654961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15871531473307684455103307 23807297209961526682654961)
              ·
                refine ⟨17855472907471145011991221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23807297209961526682654961 17855472907471145011991221)
                ·
                  refine ⟨1673950585075419844874177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17855472907471145011991221 1673950585075419844874177)
                  ·
                    refine ⟨1255462938806564883655633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1673950585075419844874177 1255462938806564883655633)
                    ·
                      refine ⟨941597204104923662741725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1255462938806564883655633 941597204104923662741725)
                      ·
                        rfl

theorem cell23_1833754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 5, 2, 2].length) (baseStart_1833754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1833754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1833754 prefixEnd_1833754 := by exact prefixLift 1833754
  have htrace : WordTrace (prefixWord ++ tailWord_1833754) baseStart_1833754 baseEnd_1833754 := by
    simpa [prefixWord, tailWord_1833754, baseEnd_1833754] using wordTrace_append hprefix tailTrace_1833754
  have hstable : (prefixWord ++ tailWord_1833754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833754).length < 2 ^ (prefixWord ++ tailWord_1833754).sum := by decide
  have hdescent : baseEnd_1833754 < baseStart_1833754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833760 : List Nat := [2, 1, 1, 5, 1, 3, 10]
def baseStart_1833760 : Nat := 118140960795 + 1833760 * 2 ^ 59
def prefixEnd_1833760 : Nat := 4983230072969 + 3 ^ 40 * 1833760 * 2
def baseEnd_1833760 : Nat := 11624694876405563447737

theorem tailTrace_1833760 : CollatzResearch.WordTrace tailWord_1833760 prefixEnd_1833760 11624694876405563447737 := by
  unfold tailWord_1833760
  simp only [CollatzResearch.WordTrace]
  refine ⟨33441360918304088059737367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44588481224405450746316489 33441360918304088059737367)
  ·
    refine ⟨50162041377456132089606051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33441360918304088059737367 50162041377456132089606051)
    ·
      refine ⟨75243062066184198134409077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50162041377456132089606051 75243062066184198134409077)
      ·
        refine ⟨7054037068704768575100851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 75243062066184198134409077 7054037068704768575100851)
        ·
          refine ⟨10581055603057152862651277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7054037068704768575100851 10581055603057152862651277)
          ·
            refine ⟨3967895851146432323494229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10581055603057152862651277 3967895851146432323494229)
            ·
              refine ⟨11624694876405563447737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3967895851146432323494229 11624694876405563447737)
              ·
                rfl

theorem cell23_1833760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 10].length) (baseStart_1833760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1833760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1833760 prefixEnd_1833760 := by exact prefixLift 1833760
  have htrace : WordTrace (prefixWord ++ tailWord_1833760) baseStart_1833760 baseEnd_1833760 := by
    simpa [prefixWord, tailWord_1833760, baseEnd_1833760] using wordTrace_append hprefix tailTrace_1833760
  have hstable : (prefixWord ++ tailWord_1833760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833760).length < 2 ^ (prefixWord ++ tailWord_1833760).sum := by decide
  have hdescent : baseEnd_1833760 < baseStart_1833760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833764 : List Nat := [2, 3, 1, 3, 3, 1, 1, 1, 4, 4]
def baseStart_1833764 : Nat := 118140960795 + 1833764 * 2 ^ 59
def prefixEnd_1833764 : Nat := 4983230072969 + 3 ^ 40 * 1833764 * 2
def baseEnd_1833764 : Nat := 313867446303822874538893

theorem tailTrace_1833764 : CollatzResearch.WordTrace tailWord_1833764 prefixEnd_1833764 313867446303822874538893 := by
  unfold tailWord_1833764
  simp only [CollatzResearch.WordTrace]
  refine ⟨33441433864296842401310173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44588578485729123201746897 33441433864296842401310173)
  ·
    refine ⟨12540537699111315900491315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33441433864296842401310173 12540537699111315900491315)
    ·
      refine ⟨18810806548666973850736973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12540537699111315900491315 18810806548666973850736973)
      ·
        refine ⟨7054052455750115194026365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18810806548666973850736973 7054052455750115194026365)
        ·
          refine ⟨2645269670906293197759887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7054052455750115194026365 2645269670906293197759887)
          ·
            refine ⟨3967904506359439796639831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2645269670906293197759887 3967904506359439796639831)
            ·
              refine ⟨5951856759539159694959747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3967904506359439796639831 5951856759539159694959747)
              ·
                refine ⟨8927785139308739542439621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5951856759539159694959747 8927785139308739542439621)
                ·
                  refine ⟨1673959713620388664207429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8927785139308739542439621 1673959713620388664207429)
                  ·
                    refine ⟨313867446303822874538893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1673959713620388664207429 313867446303822874538893)
                    ·
                      rfl

theorem cell23_1833764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 1, 4, 4].length) (baseStart_1833764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1833764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1833764 prefixEnd_1833764 := by exact prefixLift 1833764
  have htrace : WordTrace (prefixWord ++ tailWord_1833764) baseStart_1833764 baseEnd_1833764 := by
    simpa [prefixWord, tailWord_1833764, baseEnd_1833764] using wordTrace_append hprefix tailTrace_1833764
  have hstable : (prefixWord ++ tailWord_1833764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833764).length < 2 ^ (prefixWord ++ tailWord_1833764).sum := by decide
  have hdescent : baseEnd_1833764 < baseStart_1833764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833774 : List Nat := [4, 1, 3, 2, 1, 2, 1, 2, 1, 1, 5]
def baseStart_1833774 : Nat := 118140960795 + 1833774 * 2 ^ 59
def prefixEnd_1833774 : Nat := 4983230072969 + 3 ^ 40 * 1833774 * 2
def baseEnd_1833774 : Nat := 941607473718013584491633

theorem tailTrace_1833774 : CollatzResearch.WordTrace tailWord_1833774 prefixEnd_1833774 941607473718013584491633 := by
  unfold tailWord_1833774
  simp only [CollatzResearch.WordTrace]
  refine ⟨8360404057319682063810547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44588821639038304340322917 8360404057319682063810547)
  ·
    refine ⟨12540606085979523095715821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8360404057319682063810547 12540606085979523095715821)
    ·
      refine ⟨4702727282242321160893433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12540606085979523095715821 4702727282242321160893433)
      ·
        refine ⟨3527045461681740870670075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4702727282242321160893433 3527045461681740870670075)
        ·
          refine ⟨5290568192522611306005113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3527045461681740870670075 5290568192522611306005113)
          ·
            refine ⟨3967926144391958479503835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5290568192522611306005113 3967926144391958479503835)
            ·
              refine ⟨5951889216587937719255753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3967926144391958479503835 5951889216587937719255753)
              ·
                refine ⟨4463916912440953289441815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5951889216587937719255753 4463916912440953289441815)
                ·
                  refine ⟨6695875368661429934162723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4463916912440953289441815 6695875368661429934162723)
                  ·
                    refine ⟨10043813052992144901244085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6695875368661429934162723 10043813052992144901244085)
                    ·
                      refine ⟨941607473718013584491633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10043813052992144901244085 941607473718013584491633)
                      ·
                        rfl

theorem cell23_1833774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_1833774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1833774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1833774 prefixEnd_1833774 := by exact prefixLift 1833774
  have htrace : WordTrace (prefixWord ++ tailWord_1833774) baseStart_1833774 baseEnd_1833774 := by
    simpa [prefixWord, tailWord_1833774, baseEnd_1833774] using wordTrace_append hprefix tailTrace_1833774
  have hstable : (prefixWord ++ tailWord_1833774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833774).length < 2 ^ (prefixWord ++ tailWord_1833774).sum := by decide
  have hdescent : baseEnd_1833774 < baseStart_1833774 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833781 : List Nat := [1, 3, 3, 1, 3, 2, 3, 1, 2, 4]
def baseStart_1833781 : Nat := 118140960795 + 1833781 * 2 ^ 59
def prefixEnd_1833781 : Nat := 4983230072969 + 3 ^ 40 * 1833781 * 2
def baseEnd_1833781 : Nat := 313870356027531685701367

theorem tailTrace_1833781 : CollatzResearch.WordTrace tailWord_1833781 prefixEnd_1833781 313870356027531685701367 := by
  unfold tailWord_1833781
  simp only [CollatzResearch.WordTrace]
  refine ⟨66883487769532096705989197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44588991846354731137326131 66883487769532096705989197)
  ·
    refine ⟨25081307913574536264745949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66883487769532096705989197 25081307913574536264745949)
    ·
      refine ⟨9405490467590451099279731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25081307913574536264745949 9405490467590451099279731)
      ·
        refine ⟨14108235701385676648919597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9405490467590451099279731 14108235701385676648919597)
        ·
          refine ⟨5290588388019628743344849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14108235701385676648919597 5290588388019628743344849)
          ·
            refine ⟨3967941291014721557508637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5290588388019628743344849 3967941291014721557508637)
            ·
              refine ⟨1487977984130520584065739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3967941291014721557508637 1487977984130520584065739)
              ·
                refine ⟨2231966976195780876098609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1487977984130520584065739 2231966976195780876098609)
                ·
                  refine ⟨1673975232146835657073957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2231966976195780876098609 1673975232146835657073957)
                  ·
                    refine ⟨313870356027531685701367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1673975232146835657073957 313870356027531685701367)
                    ·
                      rfl

theorem cell23_1833781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 3, 1, 2, 4].length) (baseStart_1833781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1833781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1833781 prefixEnd_1833781 := by exact prefixLift 1833781
  have htrace : WordTrace (prefixWord ++ tailWord_1833781) baseStart_1833781 baseEnd_1833781 := by
    simpa [prefixWord, tailWord_1833781, baseEnd_1833781] using wordTrace_append hprefix tailTrace_1833781
  have hstable : (prefixWord ++ tailWord_1833781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833781).length < 2 ^ (prefixWord ++ tailWord_1833781).sum := by decide
  have hdescent : baseEnd_1833781 < baseStart_1833781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833800 : List Nat := [2, 1, 3, 1, 1, 3, 1, 1, 1, 4, 5]
def baseStart_1833800 : Nat := 118140960795 + 1833800 * 2 ^ 59
def prefixEnd_1833800 : Nat := 4983230072969 + 3 ^ 40 * 1833800 * 2
def baseEnd_1833800 : Nat := 941620824215030482766513

theorem tailTrace_1833800 : CollatzResearch.WordTrace tailWord_1833800 prefixEnd_1833800 941620824215030482766513 := by
  unfold tailWord_1833800
  simp only [CollatzResearch.WordTrace]
  refine ⟨33442090378231631475465427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44589453837642175300620569 33442090378231631475465427)
  ·
    refine ⟨50163135567347447213198141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33442090378231631475465427 50163135567347447213198141)
    ·
      refine ⟨18811175837755292704949303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50163135567347447213198141 18811175837755292704949303)
      ·
        refine ⟨28216763756632939057423955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18811175837755292704949303 28216763756632939057423955)
        ·
          refine ⟨42325145634949408586135933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28216763756632939057423955 42325145634949408586135933)
          ·
            refine ⟨15871929613106028219800975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42325145634949408586135933 15871929613106028219800975)
            ·
              refine ⟨23807894419659042329701463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15871929613106028219800975 23807894419659042329701463)
              ·
                refine ⟨35711841629488563494552195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23807894419659042329701463 35711841629488563494552195)
                ·
                  refine ⟨53567762444232845241828293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35711841629488563494552195 53567762444232845241828293)
                  ·
                    refine ⟨10043955458293658482842805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53567762444232845241828293 10043955458293658482842805)
                    ·
                      refine ⟨941620824215030482766513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10043955458293658482842805 941620824215030482766513)
                      ·
                        rfl

theorem cell23_1833800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 1, 4, 5].length) (baseStart_1833800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1833800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1833800 prefixEnd_1833800 := by exact prefixLift 1833800
  have htrace : WordTrace (prefixWord ++ tailWord_1833800) baseStart_1833800 baseEnd_1833800 := by
    simpa [prefixWord, tailWord_1833800, baseEnd_1833800] using wordTrace_append hprefix tailTrace_1833800
  have hstable : (prefixWord ++ tailWord_1833800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833800).length < 2 ^ (prefixWord ++ tailWord_1833800).sum := by decide
  have hdescent : baseEnd_1833800 < baseStart_1833800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833804 : List Nat := [2, 2, 1, 3, 3, 1, 1, 2, 4, 1, 3]
def baseStart_1833804 : Nat := 118140960795 + 1833804 * 2 ^ 59
def prefixEnd_1833804 : Nat := 4983230072969 + 3 ^ 40 * 1833804 * 2
def baseEnd_1833804 : Nat := 941622878137648467116495

theorem tailTrace_1833804 : CollatzResearch.WordTrace tailWord_1833804 prefixEnd_1833804 941622878137648467116495 := by
  unfold tailWord_1833804
  simp only [CollatzResearch.WordTrace]
  refine ⟨33442163324224385817038233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44589551098965847756050977 33442163324224385817038233)
  ·
    refine ⟨25081622493168289362778675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33442163324224385817038233 25081622493168289362778675)
    ·
      refine ⟨37622433739752434044168013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25081622493168289362778675 37622433739752434044168013)
      ·
        refine ⟨14108412652407162766563005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37622433739752434044168013 14108412652407162766563005)
        ·
          refine ⟨5290654744652686037461127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14108412652407162766563005 5290654744652686037461127)
          ·
            refine ⟨7935982116979029056191691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5290654744652686037461127 7935982116979029056191691)
            ·
              refine ⟨11903973175468543584287537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7935982116979029056191691 11903973175468543584287537)
              ·
                refine ⟨8927979881601407688215653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11903973175468543584287537 8927979881601407688215653)
                ·
                  refine ⟨1673996227800263941540435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8927979881601407688215653 1673996227800263941540435)
                  ·
                    refine ⟨2510994341700395912310653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1673996227800263941540435 2510994341700395912310653)
                    ·
                      refine ⟨941622878137648467116495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2510994341700395912310653 941622878137648467116495)
                      ·
                        rfl

theorem cell23_1833804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 2, 4, 1, 3].length) (baseStart_1833804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1833804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1833804 prefixEnd_1833804 := by exact prefixLift 1833804
  have htrace : WordTrace (prefixWord ++ tailWord_1833804) baseStart_1833804 baseEnd_1833804 := by
    simpa [prefixWord, tailWord_1833804, baseEnd_1833804] using wordTrace_append hprefix tailTrace_1833804
  have hstable : (prefixWord ++ tailWord_1833804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833804).length < 2 ^ (prefixWord ++ tailWord_1833804).sum := by decide
  have hdescent : baseEnd_1833804 < baseStart_1833804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833838 : List Nat := [4, 1, 2, 3, 2, 1, 1, 3, 2, 1, 3]
def baseStart_1833838 : Nat := 118140960795 + 1833838 * 2 ^ 59
def prefixEnd_1833838 : Nat := 4983230072969 + 3 ^ 40 * 1833838 * 2
def baseEnd_1833838 : Nat := 941640336479901334091339

theorem tailTrace_1833838 : CollatzResearch.WordTrace tailWord_1833838 prefixEnd_1833838 941640336479901334091339 := by
  unfold tailWord_1833838
  simp only [CollatzResearch.WordTrace]
  refine ⟨8360695841290699430101771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44590377820217063627209445 8360695841290699430101771)
  ·
    refine ⟨12541043761936049145152657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8360695841290699430101771 12541043761936049145152657)
    ·
      refine ⟨9405782821452036858864493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12541043761936049145152657 9405782821452036858864493)
      ·
        refine ⟨3527168558044513822074185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9405782821452036858864493 3527168558044513822074185)
        ·
          refine ⟨2645376418533385366555639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3527168558044513822074185 2645376418533385366555639)
          ·
            refine ⟨3968064627800078049833459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2645376418533385366555639 3968064627800078049833459)
            ·
              refine ⟨5952096941700117074750189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3968064627800078049833459 5952096941700117074750189)
              ·
                refine ⟨2232036353137543903031321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5952096941700117074750189 2232036353137543903031321)
                ·
                  refine ⟨1674027264853157927273491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2232036353137543903031321 1674027264853157927273491)
                  ·
                    refine ⟨2511040897279736890910237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1674027264853157927273491 2511040897279736890910237)
                    ·
                      refine ⟨941640336479901334091339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2511040897279736890910237 941640336479901334091339)
                      ·
                        rfl

theorem cell23_1833838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_1833838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1833838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1833838 prefixEnd_1833838 := by exact prefixLift 1833838
  have htrace : WordTrace (prefixWord ++ tailWord_1833838) baseStart_1833838 baseEnd_1833838 := by
    simpa [prefixWord, tailWord_1833838, baseEnd_1833838] using wordTrace_append hprefix tailTrace_1833838
  have hstable : (prefixWord ++ tailWord_1833838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833838).length < 2 ^ (prefixWord ++ tailWord_1833838).sum := by decide
  have hdescent : baseEnd_1833838 < baseStart_1833838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
