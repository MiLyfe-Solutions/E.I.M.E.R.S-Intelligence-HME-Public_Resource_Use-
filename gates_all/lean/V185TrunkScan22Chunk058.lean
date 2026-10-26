import V185TrunkScan22Chunk057

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_521045 : List Nat := [1, 3, 2, 2, 2, 1, 2, 4, 5]
def baseStart_521045 : Nat := 118140960795 + 521045 * 2 ^ 59
def prefixEnd_521045 : Nat := 4983230072969 + 3 ^ 40 * 521045 * 2
def baseEnd_521045 : Nat := 59454783916004253942503

theorem tailTrace_521045 : CollatzResearch.WordTrace tailWord_521045 prefixEnd_521045 59454783916004253942503 := by
  unfold tailWord_521045
  simp only [CollatzResearch.WordTrace]
  refine ⟨19004072397350427246460589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12669381598233618164307059 19004072397350427246460589)
  ·
    refine ⟨7126527149006410217422721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19004072397350427246460589 7126527149006410217422721)
    ·
      refine ⟨5344895361754807663067041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7126527149006410217422721 5344895361754807663067041)
      ·
        refine ⟨4008671521316105747300281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5344895361754807663067041 4008671521316105747300281)
        ·
          refine ⟨3006503640987079310475211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4008671521316105747300281 3006503640987079310475211)
          ·
            refine ⟨4509755461480618965712817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3006503640987079310475211 4509755461480618965712817)
            ·
              refine ⟨3382316596110464224284613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4509755461480618965712817 3382316596110464224284613)
              ·
                refine ⟨634184361770712042053365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3382316596110464224284613 634184361770712042053365)
                ·
                  refine ⟨59454783916004253942503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 634184361770712042053365 59454783916004253942503)
                  ·
                    rfl

theorem cell22_521045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 4, 5].length) (baseStart_521045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_521045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_521045 prefixEnd_521045 := by exact prefixLift 521045
  have htrace : WordTrace (prefixWord ++ tailWord_521045) baseStart_521045 baseEnd_521045 := by
    simpa [prefixWord, tailWord_521045, baseEnd_521045] using wordTrace_append hprefix tailTrace_521045
  have hstable : (prefixWord ++ tailWord_521045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521045).length < 2 ^ (prefixWord ++ tailWord_521045).sum := by decide
  have hdescent : baseEnd_521045 < baseStart_521045 := by decide
  rcases family_descends (prefixWord ++ tailWord_521045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521120 : List Nat := [2, 1, 1, 4, 1, 1, 2, 2, 4, 4]
def baseStart_521120 : Nat := 118140960795 + 521120 * 2 ^ 59
def prefixEnd_521120 : Nat := 4983230072969 + 3 ^ 40 * 521120 * 2
def baseEnd_521120 : Nat := 178390025780737566202279

theorem tailTrace_521120 : CollatzResearch.WordTrace tailWord_521120 prefixEnd_521120 178390025780737566202279 := by
  unfold tailWord_521120
  simp only [CollatzResearch.WordTrace]
  refine ⟨9503403936039357527720407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12671205248052476703627209 9503403936039357527720407)
  ·
    refine ⟨14255105904059036291580611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9503403936039357527720407 14255105904059036291580611)
    ·
      refine ⟨21382658856088554437370917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14255105904059036291580611 21382658856088554437370917)
      ·
        refine ⟨4009248535516603957007047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21382658856088554437370917 4009248535516603957007047)
        ·
          refine ⟨6013872803274905935510571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4009248535516603957007047 6013872803274905935510571)
          ·
            refine ⟨9020809204912358903265857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6013872803274905935510571 9020809204912358903265857)
            ·
              refine ⟨6765606903684269177449393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9020809204912358903265857 6765606903684269177449393)
              ·
                refine ⟨5074205177763201883087045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6765606903684269177449393 5074205177763201883087045)
                ·
                  refine ⟨951413470830600353078821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5074205177763201883087045 951413470830600353078821)
                  ·
                    refine ⟨178390025780737566202279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 951413470830600353078821 178390025780737566202279)
                    ·
                      rfl

theorem cell22_521120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 4, 4].length) (baseStart_521120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_521120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_521120 prefixEnd_521120 := by exact prefixLift 521120
  have htrace : WordTrace (prefixWord ++ tailWord_521120) baseStart_521120 baseEnd_521120 := by
    simpa [prefixWord, tailWord_521120, baseEnd_521120] using wordTrace_append hprefix tailTrace_521120
  have hstable : (prefixWord ++ tailWord_521120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521120).length < 2 ^ (prefixWord ++ tailWord_521120).sum := by decide
  have hdescent : baseEnd_521120 < baseStart_521120 := by decide
  rcases family_descends (prefixWord ++ tailWord_521120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521122 : List Nat := [3, 3, 1, 2, 2, 1, 1, 3, 1, 5]
def baseStart_521122 : Nat := 118140960795 + 521122 * 2 ^ 59
def prefixEnd_521122 : Nat := 4983230072969 + 3 ^ 40 * 521122 * 2
def baseEnd_521122 : Nat := 178390710421610227652273

theorem tailTrace_521122 : CollatzResearch.WordTrace tailWord_521122 prefixEnd_521122 178390710421610227652273 := by
  unfold tailWord_521122
  simp only [CollatzResearch.WordTrace]
  refine ⟨4751720204517867349253405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12671253878714312931342413 4751720204517867349253405)
  ·
    refine ⟨1781895076694200255970027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4751720204517867349253405 1781895076694200255970027)
    ·
      refine ⟨2672842615041300383955041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1781895076694200255970027 2672842615041300383955041)
      ·
        refine ⟨2004631961280975287966281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2672842615041300383955041 2004631961280975287966281)
        ·
          refine ⟨1503473970960731465974711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2004631961280975287966281 1503473970960731465974711)
          ·
            refine ⟨2255210956441097198962067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1503473970960731465974711 2255210956441097198962067)
            ·
              refine ⟨3382816434661645798443101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2255210956441097198962067 3382816434661645798443101)
              ·
                refine ⟨1268556162998117174416163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3382816434661645798443101 1268556162998117174416163)
                ·
                  refine ⟨1902834244497175761624245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1268556162998117174416163 1902834244497175761624245)
                  ·
                    refine ⟨178390710421610227652273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1902834244497175761624245 178390710421610227652273)
                    ·
                      rfl

theorem cell22_521122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_521122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_521122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_521122 prefixEnd_521122 := by exact prefixLift 521122
  have htrace : WordTrace (prefixWord ++ tailWord_521122) baseStart_521122 baseEnd_521122 := by
    simpa [prefixWord, tailWord_521122, baseEnd_521122] using wordTrace_append hprefix tailTrace_521122
  have hstable : (prefixWord ++ tailWord_521122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521122).length < 2 ^ (prefixWord ++ tailWord_521122).sum := by decide
  have hdescent : baseEnd_521122 < baseStart_521122 := by decide
  rcases family_descends (prefixWord ++ tailWord_521122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521137 : List Nat := [1, 2, 2, 4, 3, 1, 1, 1, 1, 6]
def baseStart_521137 : Nat := 118140960795 + 521137 * 2 ^ 59
def prefixEnd_521137 : Nat := 4983230072969 + 3 ^ 40 * 521137 * 2
def baseEnd_521137 : Nat := 178395845228155188527227

theorem tailTrace_521137 : CollatzResearch.WordTrace tailWord_521137 prefixEnd_521137 178395845228155188527227 := by
  unfold tailWord_521137
  simp only [CollatzResearch.WordTrace]
  refine ⟨19007427913017126958809665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12671618608678084639206443 19007427913017126958809665)
  ·
    refine ⟨14255570934762845219107249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19007427913017126958809665 14255570934762845219107249)
    ·
      refine ⟨10691678201072133914330437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14255570934762845219107249 10691678201072133914330437)
      ·
        refine ⟨2004689662701025108936957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10691678201072133914330437 2004689662701025108936957)
        ·
          refine ⟨751758623512884415851359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2004689662701025108936957 751758623512884415851359)
          ·
            refine ⟨1127637935269326623777039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 751758623512884415851359 1127637935269326623777039)
            ·
              refine ⟨1691456902903989935665559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1127637935269326623777039 1691456902903989935665559)
              ·
                refine ⟨2537185354355984903498339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1691456902903989935665559 2537185354355984903498339)
                ·
                  refine ⟨3805778031533977355247509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2537185354355984903498339 3805778031533977355247509)
                  ·
                    refine ⟨178395845228155188527227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3805778031533977355247509 178395845228155188527227)
                    ·
                      rfl

theorem cell22_521137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 1, 1, 6].length) (baseStart_521137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_521137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_521137 prefixEnd_521137 := by exact prefixLift 521137
  have htrace : WordTrace (prefixWord ++ tailWord_521137) baseStart_521137 baseEnd_521137 := by
    simpa [prefixWord, tailWord_521137, baseEnd_521137] using wordTrace_append hprefix tailTrace_521137
  have hstable : (prefixWord ++ tailWord_521137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521137).length < 2 ^ (prefixWord ++ tailWord_521137).sum := by decide
  have hdescent : baseEnd_521137 < baseStart_521137 := by decide
  rcases family_descends (prefixWord ++ tailWord_521137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521156 : List Nat := [2, 3, 3, 3, 1, 1, 1, 1, 4, 3]
def baseStart_521156 : Nat := 118140960795 + 521156 * 2 ^ 59
def prefixEnd_521156 : Nat := 4983230072969 + 3 ^ 40 * 521156 * 2
def baseEnd_521156 : Nat := 178402349316445472302169

theorem tailTrace_521156 : CollatzResearch.WordTrace tailWord_521156 prefixEnd_521156 178402349316445472302169 := by
  unfold tailWord_521156
  simp only [CollatzResearch.WordTrace]
  refine ⟨9504060449974146601875661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12672080599965528802500881 9504060449974146601875661)
  ·
    refine ⟨3564022668740304975703373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9504060449974146601875661 3564022668740304975703373)
    ·
      refine ⟨1336508500777614365888765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3564022668740304975703373 1336508500777614365888765)
      ·
        refine ⟨501190687791605387208287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1336508500777614365888765 501190687791605387208287)
        ·
          refine ⟨751786031687408080812431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 501190687791605387208287 751786031687408080812431)
          ·
            refine ⟨1127679047531112121218647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 751786031687408080812431 1127679047531112121218647)
            ·
              refine ⟨1691518571296668181827971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1127679047531112121218647 1691518571296668181827971)
              ·
                refine ⟨2537277856945002272741957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1691518571296668181827971 2537277856945002272741957)
                ·
                  refine ⟨475739598177187926139117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2537277856945002272741957 475739598177187926139117)
                  ·
                    refine ⟨178402349316445472302169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 475739598177187926139117 178402349316445472302169)
                    ·
                      rfl

theorem cell22_521156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_521156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_521156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_521156 prefixEnd_521156 := by exact prefixLift 521156
  have htrace : WordTrace (prefixWord ++ tailWord_521156) baseStart_521156 baseEnd_521156 := by
    simpa [prefixWord, tailWord_521156, baseEnd_521156] using wordTrace_append hprefix tailTrace_521156
  have hstable : (prefixWord ++ tailWord_521156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521156).length < 2 ^ (prefixWord ++ tailWord_521156).sum := by decide
  have hdescent : baseEnd_521156 < baseStart_521156 := by decide
  rcases family_descends (prefixWord ++ tailWord_521156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521167 : List Nat := [1, 1, 2, 1, 1, 6, 1, 3, 3, 3]
def baseStart_521167 : Nat := 118140960795 + 521167 * 2 ^ 59
def prefixEnd_521167 : Nat := 4983230072969 + 3 ^ 40 * 521167 * 2
def baseEnd_521167 : Nat := 178406114841245110277135

theorem tailTrace_521167 : CollatzResearch.WordTrace tailWord_521167 prefixEnd_521167 178406114841245110277135 := by
  unfold tailWord_521167
  simp only [CollatzResearch.WordTrace]
  refine ⟨19008522102908442082401755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12672348068605628054934503 19008522102908442082401755)
  ·
    refine ⟨28512783154362663123602633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19008522102908442082401755 28512783154362663123602633)
    ·
      refine ⟨21384587365771997342701975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28512783154362663123602633 21384587365771997342701975)
      ·
        refine ⟨32076881048657996014052963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21384587365771997342701975 32076881048657996014052963)
        ·
          refine ⟨48115321572986994021079445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32076881048657996014052963 48115321572986994021079445)
          ·
            refine ⟨2255405698733765344738099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 48115321572986994021079445 2255405698733765344738099)
            ·
              refine ⟨3383108548100648017107149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2255405698733765344738099 3383108548100648017107149)
              ·
                refine ⟨1268665705537743006415181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3383108548100648017107149 1268665705537743006415181)
                ·
                  refine ⟨475749639576653627405693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1268665705537743006415181 475749639576653627405693)
                  ·
                    refine ⟨178406114841245110277135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 475749639576653627405693 178406114841245110277135)
                    ·
                      rfl

theorem cell22_521167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 3, 3, 3].length) (baseStart_521167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_521167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_521167 prefixEnd_521167 := by exact prefixLift 521167
  have htrace : WordTrace (prefixWord ++ tailWord_521167) baseStart_521167 baseEnd_521167 := by
    simpa [prefixWord, tailWord_521167, baseEnd_521167] using wordTrace_append hprefix tailTrace_521167
  have hstable : (prefixWord ++ tailWord_521167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521167).length < 2 ^ (prefixWord ++ tailWord_521167).sum := by decide
  have hdescent : baseEnd_521167 < baseStart_521167 := by decide
  rcases family_descends (prefixWord ++ tailWord_521167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521186 : List Nat := [3, 3, 3, 1, 1, 3, 2, 6]
def baseStart_521186 : Nat := 118140960795 + 521186 * 2 ^ 59
def prefixEnd_521186 : Nat := 4983230072969 + 3 ^ 40 * 521186 * 2
def baseEnd_521186 : Nat := 19823624325503932672453

theorem tailTrace_521186 : CollatzResearch.WordTrace tailWord_521186 prefixEnd_521186 19823624325503932672453 := by
  unfold tailWord_521186
  simp only [CollatzResearch.WordTrace]
  refine ⟨4752303772459902081835853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12672810059893072218228941 4752303772459902081835853)
  ·
    refine ⟨1782113914672463280688445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4752303772459902081835853 1782113914672463280688445)
    ·
      refine ⟨668292718002173730258167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1782113914672463280688445 668292718002173730258167)
      ·
        refine ⟨1002439077003260595387251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 668292718002173730258167 1002439077003260595387251)
        ·
          refine ⟨1503658615504890893080877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1002439077003260595387251 1503658615504890893080877)
          ·
            refine ⟨563871980814334084905329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1503658615504890893080877 563871980814334084905329)
            ·
              refine ⟨422903985610750563678997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 563871980814334084905329 422903985610750563678997)
              ·
                refine ⟨19823624325503932672453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 422903985610750563678997 19823624325503932672453)
                ·
                  rfl

theorem cell22_521186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 2, 6].length) (baseStart_521186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_521186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_521186 prefixEnd_521186 := by exact prefixLift 521186
  have htrace : WordTrace (prefixWord ++ tailWord_521186) baseStart_521186 baseEnd_521186 := by
    simpa [prefixWord, tailWord_521186, baseEnd_521186] using wordTrace_append hprefix tailTrace_521186
  have hstable : (prefixWord ++ tailWord_521186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521186).length < 2 ^ (prefixWord ++ tailWord_521186).sum := by decide
  have hdescent : baseEnd_521186 < baseStart_521186 := by decide
  rcases family_descends (prefixWord ++ tailWord_521186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521201 : List Nat := [1, 2, 2, 2, 4, 1, 3, 3, 1, 3]
def baseStart_521201 : Nat := 118140960795 + 521201 * 2 ^ 59
def prefixEnd_521201 : Nat := 4983230072969 + 3 ^ 40 * 521201 * 2
def baseEnd_521201 : Nat := 178417753736080354927031

theorem tailTrace_521201 : CollatzResearch.WordTrace tailWord_521201 prefixEnd_521201 178417753736080354927031 := by
  unfold tailWord_521201
  simp only [CollatzResearch.WordTrace]
  refine ⟨19009762184785265889139457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12673174789856843926092971 19009762184785265889139457)
  ·
    refine ⟨14257321638588949416854593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19009762184785265889139457 14257321638588949416854593)
    ·
      refine ⟨10692991228941712062640945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14257321638588949416854593 10692991228941712062640945)
      ·
        refine ⟨8019743421706284046980709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10692991228941712062640945 8019743421706284046980709)
        ·
          refine ⟨1503701891569928258808883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8019743421706284046980709 1503701891569928258808883)
          ·
            refine ⟨2255552837354892388213325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1503701891569928258808883 2255552837354892388213325)
            ·
              refine ⟨845832314008084645579997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2255552837354892388213325 845832314008084645579997)
              ·
                refine ⟨317187117753031742092499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 845832314008084645579997 317187117753031742092499)
                ·
                  refine ⟨475780676629547613138749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 317187117753031742092499 475780676629547613138749)
                  ·
                    refine ⟨178417753736080354927031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 475780676629547613138749 178417753736080354927031)
                    ·
                      rfl

theorem cell22_521201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 3, 1, 3].length) (baseStart_521201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_521201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_521201 prefixEnd_521201 := by exact prefixLift 521201
  have htrace : WordTrace (prefixWord ++ tailWord_521201) baseStart_521201 baseEnd_521201 := by
    simpa [prefixWord, tailWord_521201, baseEnd_521201] using wordTrace_append hprefix tailTrace_521201
  have hstable : (prefixWord ++ tailWord_521201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521201).length < 2 ^ (prefixWord ++ tailWord_521201).sum := by decide
  have hdescent : baseEnd_521201 < baseStart_521201 := by decide
  rcases family_descends (prefixWord ++ tailWord_521201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521244 : List Nat := [2, 2, 3, 1, 4, 1, 1, 1, 3, 4]
def baseStart_521244 : Nat := 118140960795 + 521244 * 2 ^ 59
def prefixEnd_521244 : Nat := 4983230072969 + 3 ^ 40 * 521244 * 2
def baseEnd_521244 : Nat := 178432473514842576101899

theorem tailTrace_521244 : CollatzResearch.WordTrace tailWord_521244 prefixEnd_521244 178432473514842576101899 := by
  unfold tailWord_521244
  simp only [CollatzResearch.WordTrace]
  refine ⟨9505665261814742116477393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12674220349086322821969857 9505665261814742116477393)
  ·
    refine ⟨7129248946361056587358045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9505665261814742116477393 7129248946361056587358045)
    ·
      refine ⟨2673468354885396220259267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7129248946361056587358045 2673468354885396220259267)
      ·
        refine ⟨4010202532328094330388901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2673468354885396220259267 4010202532328094330388901)
        ·
          refine ⟨751912974811517686947919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4010202532328094330388901 751912974811517686947919)
          ·
            refine ⟨1127869462217276530421879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 751912974811517686947919 1127869462217276530421879)
            ·
              refine ⟨1691804193325914795632819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1127869462217276530421879 1691804193325914795632819)
              ·
                refine ⟨2537706289988872193449229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1691804193325914795632819 2537706289988872193449229)
                ·
                  refine ⟨951639858745827072543461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2537706289988872193449229 951639858745827072543461)
                  ·
                    refine ⟨178432473514842576101899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 951639858745827072543461 178432473514842576101899)
                    ·
                      rfl

theorem cell22_521244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_521244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_521244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_521244 prefixEnd_521244 := by exact prefixLift 521244
  have htrace : WordTrace (prefixWord ++ tailWord_521244) baseStart_521244 baseEnd_521244 := by
    simpa [prefixWord, tailWord_521244, baseEnd_521244] using wordTrace_append hprefix tailTrace_521244
  have hstable : (prefixWord ++ tailWord_521244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521244).length < 2 ^ (prefixWord ++ tailWord_521244).sum := by decide
  have hdescent : baseEnd_521244 < baseStart_521244 := by decide
  rcases family_descends (prefixWord ++ tailWord_521244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521274 : List Nat := [3, 1, 1, 1, 3, 1, 3, 4, 2, 3]
def baseStart_521274 : Nat := 118140960795 + 521274 * 2 ^ 59
def prefixEnd_521274 : Nat := 4983230072969 + 3 ^ 40 * 521274 * 2
def baseEnd_521274 : Nat := 178442743127932497851807

theorem tailTrace_521274 : CollatzResearch.WordTrace tailWord_521274 prefixEnd_521274 178442743127932497851807 := by
  unfold tailWord_521274
  simp only [CollatzResearch.WordTrace]
  refine ⟨4753106178380199839136719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12674949809013866237697917 4753106178380199839136719)
  ·
    refine ⟨7129659267570299758705079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4753106178380199839136719 7129659267570299758705079)
    ·
      refine ⟨10694488901355449638057619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7129659267570299758705079 10694488901355449638057619)
      ·
        refine ⟨16041733352033174457086429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10694488901355449638057619 16041733352033174457086429)
        ·
          refine ⟨6015650007012440421407411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16041733352033174457086429 6015650007012440421407411)
          ·
            refine ⟨9023475010518660632111117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6015650007012440421407411 9023475010518660632111117)
            ·
              refine ⟨3383803128944497737041669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9023475010518660632111117 3383803128944497737041669)
              ·
                refine ⟨634463086677093325695313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3383803128944497737041669 634463086677093325695313)
                ·
                  refine ⟨475847315007819994271485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 634463086677093325695313 475847315007819994271485)
                  ·
                    refine ⟨178442743127932497851807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 475847315007819994271485 178442743127932497851807)
                    ·
                      rfl

theorem cell22_521274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 4, 2, 3].length) (baseStart_521274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_521274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_521274 prefixEnd_521274 := by exact prefixLift 521274
  have htrace : WordTrace (prefixWord ++ tailWord_521274) baseStart_521274 baseEnd_521274 := by
    simpa [prefixWord, tailWord_521274, baseEnd_521274] using wordTrace_append hprefix tailTrace_521274
  have hstable : (prefixWord ++ tailWord_521274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521274).length < 2 ^ (prefixWord ++ tailWord_521274).sum := by decide
  have hdescent : baseEnd_521274 < baseStart_521274 := by decide
  rcases family_descends (prefixWord ++ tailWord_521274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521276 : List Nat := [2, 2, 2, 2, 2, 2, 4, 2, 4]
def baseStart_521276 : Nat := 118140960795 + 521276 * 2 ^ 59
def prefixEnd_521276 : Nat := 4983230072969 + 3 ^ 40 * 521276 * 2
def baseEnd_521276 : Nat := 59481142589601719767267

theorem tailTrace_521276 : CollatzResearch.WordTrace tailWord_521276 prefixEnd_521276 59481142589601719767267 := by
  unfold tailWord_521276
  simp only [CollatzResearch.WordTrace]
  refine ⟨9506248829756776849059841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12674998439675702465413121 9506248829756776849059841)
  ·
    refine ⟨7129686622317582636794881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9506248829756776849059841 7129686622317582636794881)
    ·
      refine ⟨5347264966738186977596161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7129686622317582636794881 5347264966738186977596161)
      ·
        refine ⟨4010448725053640233197121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5347264966738186977596161 4010448725053640233197121)
        ·
          refine ⟨3007836543790230174897841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4010448725053640233197121 3007836543790230174897841)
          ·
            refine ⟨2255877407842672631173381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3007836543790230174897841 2255877407842672631173381)
            ·
              refine ⟨422977013970501118345009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2255877407842672631173381 422977013970501118345009)
              ·
                refine ⟨317232760477875838758757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 422977013970501118345009 317232760477875838758757)
                ·
                  refine ⟨59481142589601719767267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 317232760477875838758757 59481142589601719767267)
                  ·
                    rfl

theorem cell22_521276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 4, 2, 4].length) (baseStart_521276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_521276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_521276 prefixEnd_521276 := by exact prefixLift 521276
  have htrace : WordTrace (prefixWord ++ tailWord_521276) baseStart_521276 baseEnd_521276 := by
    simpa [prefixWord, tailWord_521276, baseEnd_521276] using wordTrace_append hprefix tailTrace_521276
  have hstable : (prefixWord ++ tailWord_521276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521276).length < 2 ^ (prefixWord ++ tailWord_521276).sum := by decide
  have hdescent : baseEnd_521276 < baseStart_521276 := by decide
  rcases family_descends (prefixWord ++ tailWord_521276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521287 : List Nat := [1, 1, 4, 1, 3, 2, 3, 7]
def baseStart_521287 : Nat := 118140960795 + 521287 * 2 ^ 59
def prefixEnd_521287 : Nat := 4983230072969 + 3 ^ 40 * 521287 * 2
def baseEnd_521287 : Nat := 19827465921511644141863

theorem tailTrace_521287 : CollatzResearch.WordTrace tailWord_521287 prefixEnd_521287 19827465921511644141863 := by
  unfold tailWord_521287
  simp only [CollatzResearch.WordTrace]
  refine ⟨19012898862473702576770115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12675265908315801717846743 19012898862473702576770115)
  ·
    refine ⟨28519348293710553865155173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19012898862473702576770115 28519348293710553865155173)
    ·
      refine ⟨5347377805070728849716595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28519348293710553865155173 5347377805070728849716595)
      ·
        refine ⟨8021066707606093274574893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5347377805070728849716595 8021066707606093274574893)
        ·
          refine ⟨3007900015352284977965585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8021066707606093274574893 3007900015352284977965585)
          ·
            refine ⟨2255925011514213733474189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3007900015352284977965585 2255925011514213733474189)
            ·
              refine ⟨845971879317830150052821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2255925011514213733474189 845971879317830150052821)
              ·
                refine ⟨19827465921511644141863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 845971879317830150052821 19827465921511644141863)
                ·
                  rfl

theorem cell22_521287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 7].length) (baseStart_521287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_521287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_521287 prefixEnd_521287 := by exact prefixLift 521287
  have htrace : WordTrace (prefixWord ++ tailWord_521287) baseStart_521287 baseEnd_521287 := by
    simpa [prefixWord, tailWord_521287, baseEnd_521287] using wordTrace_append hprefix tailTrace_521287
  have hstable : (prefixWord ++ tailWord_521287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521287).length < 2 ^ (prefixWord ++ tailWord_521287).sum := by decide
  have hdescent : baseEnd_521287 < baseStart_521287 := by decide
  rcases family_descends (prefixWord ++ tailWord_521287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521310 : List Nat := [4, 4, 1, 1, 1, 2, 2, 3, 4]
def baseStart_521310 : Nat := 118140960795 + 521310 * 2 ^ 59
def prefixEnd_521310 : Nat := 4983230072969 + 3 ^ 40 * 521310 * 2
def baseEnd_521310 : Nat := 59485022221213467983899

theorem tailTrace_521310 : CollatzResearch.WordTrace tailWord_521310 prefixEnd_521310 59485022221213467983899 := by
  unfold tailWord_521310
  simp only [CollatzResearch.WordTrace]
  refine ⟨2376717217673797188107173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12675825160926918336571589 2376717217673797188107173)
  ·
    refine ⟨445634478313836972770095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2376717217673797188107173 445634478313836972770095)
    ·
      refine ⟨668451717470755459155143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445634478313836972770095 668451717470755459155143)
      ·
        refine ⟨1002677576206133188732715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 668451717470755459155143 1002677576206133188732715)
        ·
          refine ⟨1504016364309199783099073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1002677576206133188732715 1504016364309199783099073)
          ·
            refine ⟨1128012273231899837324305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1504016364309199783099073 1128012273231899837324305)
            ·
              refine ⟨846009204923924877993229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1128012273231899837324305 846009204923924877993229)
              ·
                refine ⟨317253451846471829247461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 846009204923924877993229 317253451846471829247461)
                ·
                  refine ⟨59485022221213467983899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 317253451846471829247461 59485022221213467983899)
                  ·
                    rfl

theorem cell22_521310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_521310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_521310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_521310 prefixEnd_521310 := by exact prefixLift 521310
  have htrace : WordTrace (prefixWord ++ tailWord_521310) baseStart_521310 baseEnd_521310 := by
    simpa [prefixWord, tailWord_521310, baseEnd_521310] using wordTrace_append hprefix tailTrace_521310
  have hstable : (prefixWord ++ tailWord_521310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521310).length < 2 ^ (prefixWord ++ tailWord_521310).sum := by decide
  have hdescent : baseEnd_521310 < baseStart_521310 := by decide
  rcases family_descends (prefixWord ++ tailWord_521310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521336 : List Nat := [2, 1, 2, 1, 1, 1, 6, 4, 1, 3]
def baseStart_521336 : Nat := 118140960795 + 521336 * 2 ^ 59
def prefixEnd_521336 : Nat := 4983230072969 + 3 ^ 40 * 521336 * 2
def baseEnd_521336 : Nat := 178463966994985002801617

theorem tailTrace_521336 : CollatzResearch.WordTrace tailWord_521336 prefixEnd_521336 178463966994985002801617 := by
  unfold tailWord_521336
  simp only [CollatzResearch.WordTrace]
  refine ⟨9507343019648091972651931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12676457359530789296869241 9507343019648091972651931)
  ·
    refine ⟨14261014529472137958977897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9507343019648091972651931 14261014529472137958977897)
    ·
      refine ⟨10695760897104103469233423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14261014529472137958977897 10695760897104103469233423)
      ·
        refine ⟨16043641345656155203850135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10695760897104103469233423 16043641345656155203850135)
        ·
          refine ⟨24065462018484232805775203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16043641345656155203850135 24065462018484232805775203)
          ·
            refine ⟨36098193027726349208662805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24065462018484232805775203 36098193027726349208662805)
            ·
              refine ⟨1692102798174672619156069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 36098193027726349208662805 1692102798174672619156069)
              ·
                refine ⟨317269274657751116091763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1692102798174672619156069 317269274657751116091763)
                ·
                  refine ⟨475903911986626674137645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 317269274657751116091763 475903911986626674137645)
                  ·
                    refine ⟨178463966994985002801617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 475903911986626674137645 178463966994985002801617)
                    ·
                      rfl

theorem cell22_521336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 4, 1, 3].length) (baseStart_521336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_521336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_521336 prefixEnd_521336 := by exact prefixLift 521336
  have htrace : WordTrace (prefixWord ++ tailWord_521336) baseStart_521336 baseEnd_521336 := by
    simpa [prefixWord, tailWord_521336, baseEnd_521336] using wordTrace_append hprefix tailTrace_521336
  have hstable : (prefixWord ++ tailWord_521336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521336).length < 2 ^ (prefixWord ++ tailWord_521336).sum := by decide
  have hdescent : baseEnd_521336 < baseStart_521336 := by decide
  rcases family_descends (prefixWord ++ tailWord_521336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521342 : List Nat := [4, 2, 4, 1, 2, 1, 1, 1, 1, 5]
def baseStart_521342 : Nat := 118140960795 + 521342 * 2 ^ 59
def prefixEnd_521342 : Nat := 4983230072969 + 3 ^ 40 * 521342 * 2
def baseEnd_521342 : Nat := 178466020917602987151599

theorem tailTrace_521342 : CollatzResearch.WordTrace tailWord_521342 prefixEnd_521342 178466020917602987151599 := by
  unfold tailWord_521342
  simp only [CollatzResearch.WordTrace]
  refine ⟨2376863109659305871252785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12676603251516297980014853 2376863109659305871252785)
  ·
    refine ⟨1782647332244479403439589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2376863109659305871252785 1782647332244479403439589)
    ·
      refine ⟨334246374795839888144923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1782647332244479403439589 334246374795839888144923)
      ·
        refine ⟨501369562193759832217385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334246374795839888144923 501369562193759832217385)
        ·
          refine ⟨376027171645319874163039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 501369562193759832217385 376027171645319874163039)
          ·
            refine ⟨564040757467979811244559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376027171645319874163039 564040757467979811244559)
            ·
              refine ⟨846061136201969716866839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 564040757467979811244559 846061136201969716866839)
              ·
                refine ⟨1269091704302954575300259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 846061136201969716866839 1269091704302954575300259)
                ·
                  refine ⟨1903637556454431862950389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1269091704302954575300259 1903637556454431862950389)
                  ·
                    refine ⟨178466020917602987151599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1903637556454431862950389 178466020917602987151599)
                    ·
                      rfl

theorem cell22_521342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_521342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_521342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_521342 prefixEnd_521342 := by exact prefixLift 521342
  have htrace : WordTrace (prefixWord ++ tailWord_521342) baseStart_521342 baseEnd_521342 := by
    simpa [prefixWord, tailWord_521342, baseEnd_521342] using wordTrace_append hprefix tailTrace_521342
  have hstable : (prefixWord ++ tailWord_521342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521342).length < 2 ^ (prefixWord ++ tailWord_521342).sum := by decide
  have hdescent : baseEnd_521342 < baseStart_521342 := by decide
  rcases family_descends (prefixWord ++ tailWord_521342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521347 : List Nat := [1, 1, 1, 3, 3, 2, 1, 3, 2, 5]
def baseStart_521347 : Nat := 118140960795 + 521347 * 2 ^ 59
def prefixEnd_521347 : Nat := 4983230072969 + 3 ^ 40 * 521347 * 2
def baseEnd_521347 : Nat := 178467732519784640776583

theorem tailTrace_521347 : CollatzResearch.WordTrace tailWord_521347 prefixEnd_521347 178467732519784640776583 := by
  unfold tailWord_521347
  simp only [CollatzResearch.WordTrace]
  refine ⟨19015087242256332823954295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12676724828170888549302863 19015087242256332823954295)
  ·
    refine ⟨28522630863384499235931443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19015087242256332823954295 28522630863384499235931443)
    ·
      refine ⟨42783946295076748853897165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28522630863384499235931443 42783946295076748853897165)
      ·
        refine ⟨16043979860653780820211437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42783946295076748853897165 16043979860653780820211437)
        ·
          refine ⟨6016492447745167807579289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16043979860653780820211437 6016492447745167807579289)
          ·
            refine ⟨4512369335808875855684467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6016492447745167807579289 4512369335808875855684467)
            ·
              refine ⟨6768554003713313783526701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4512369335808875855684467 6768554003713313783526701)
              ·
                refine ⟨2538207751392492668822513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6768554003713313783526701 2538207751392492668822513)
                ·
                  refine ⟨1903655813544369501616885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2538207751392492668822513 1903655813544369501616885)
                  ·
                    refine ⟨178467732519784640776583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1903655813544369501616885 178467732519784640776583)
                    ·
                      rfl

theorem cell22_521347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 3, 2, 5].length) (baseStart_521347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_521347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_521347 prefixEnd_521347 := by exact prefixLift 521347
  have htrace : WordTrace (prefixWord ++ tailWord_521347) baseStart_521347 baseEnd_521347 := by
    simpa [prefixWord, tailWord_521347, baseEnd_521347] using wordTrace_append hprefix tailTrace_521347
  have hstable : (prefixWord ++ tailWord_521347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521347).length < 2 ^ (prefixWord ++ tailWord_521347).sum := by decide
  have hdescent : baseEnd_521347 < baseStart_521347 := by decide
  rcases family_descends (prefixWord ++ tailWord_521347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521370 : List Nat := [3, 1, 1, 5, 1, 3, 1, 3, 1, 3]
def baseStart_521370 : Nat := 118140960795 + 521370 * 2 ^ 59
def prefixEnd_521370 : Nat := 4983230072969 + 3 ^ 40 * 521370 * 2
def baseEnd_521370 : Nat := 178475605889820247451513

theorem tailTrace_521370 : CollatzResearch.WordTrace tailWord_521370 prefixEnd_521370 178475605889820247451513 := by
  unfold tailWord_521370
  simp only [CollatzResearch.WordTrace]
  refine ⟨4753981530293251938010391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12677284080782005168027709 4753981530293251938010391)
  ·
    refine ⟨7130972295439877907015587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4753981530293251938010391 7130972295439877907015587)
    ·
      refine ⟨10696458443159816860523381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7130972295439877907015587 10696458443159816860523381)
      ·
        refine ⟨1002792979046232830674067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10696458443159816860523381 1002792979046232830674067)
        ·
          refine ⟨1504189468569349246011101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1002792979046232830674067 1504189468569349246011101)
          ·
            refine ⟨564071050713505967254163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1504189468569349246011101 564071050713505967254163)
            ·
              refine ⟨846106576070258950881245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 564071050713505967254163 846106576070258950881245)
              ·
                refine ⟨317289966026347106580467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 846106576070258950881245 317289966026347106580467)
                ·
                  refine ⟨475934949039520659870701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 317289966026347106580467 475934949039520659870701)
                  ·
                    refine ⟨178475605889820247451513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 475934949039520659870701 178475605889820247451513)
                    ·
                      rfl

theorem cell22_521370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 3, 1, 3].length) (baseStart_521370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_521370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_521370 prefixEnd_521370 := by exact prefixLift 521370
  have htrace : WordTrace (prefixWord ++ tailWord_521370) baseStart_521370 baseEnd_521370 := by
    simpa [prefixWord, tailWord_521370, baseEnd_521370] using wordTrace_append hprefix tailTrace_521370
  have hstable : (prefixWord ++ tailWord_521370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521370).length < 2 ^ (prefixWord ++ tailWord_521370).sum := by decide
  have hdescent : baseEnd_521370 < baseStart_521370 := by decide
  rcases family_descends (prefixWord ++ tailWord_521370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521392 : List Nat := [2, 1, 1, 1, 2, 1, 2, 4, 3, 5]
def baseStart_521392 : Nat := 118140960795 + 521392 * 2 ^ 59
def prefixEnd_521392 : Nat := 4983230072969 + 3 ^ 40 * 521392 * 2
def baseEnd_521392 : Nat := 178483136939419523401445

theorem tailTrace_521392 : CollatzResearch.WordTrace tailWord_521392 prefixEnd_521392 178483136939419523401445 := by
  unfold tailWord_521392
  simp only [CollatzResearch.WordTrace]
  refine ⟨9508364263546652754671215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12677819018062203672894953 9508364263546652754671215)
  ·
    refine ⟨14262546395319979132006823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9508364263546652754671215 14262546395319979132006823)
    ·
      refine ⟨21393819592979968698010235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14262546395319979132006823 21393819592979968698010235)
      ·
        refine ⟨32090729389469953047015353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21393819592979968698010235 32090729389469953047015353)
        ·
          refine ⟨24068047042102464785261515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32090729389469953047015353 24068047042102464785261515)
          ·
            refine ⟨36102070563153697177892273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24068047042102464785261515 36102070563153697177892273)
            ·
              refine ⟨27076552922365272883419205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36102070563153697177892273 27076552922365272883419205)
              ·
                refine ⟨5076853672943488665641101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27076552922365272883419205 5076853672943488665641101)
                ·
                  refine ⟨1903820127353808249615413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5076853672943488665641101 1903820127353808249615413)
                  ·
                    refine ⟨178483136939419523401445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1903820127353808249615413 178483136939419523401445)
                    ·
                      rfl

theorem cell22_521392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 3, 5].length) (baseStart_521392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_521392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_521392 prefixEnd_521392 := by exact prefixLift 521392
  have htrace : WordTrace (prefixWord ++ tailWord_521392) baseStart_521392 baseEnd_521392 := by
    simpa [prefixWord, tailWord_521392, baseEnd_521392] using wordTrace_append hprefix tailTrace_521392
  have hstable : (prefixWord ++ tailWord_521392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521392).length < 2 ^ (prefixWord ++ tailWord_521392).sum := by decide
  have hdescent : baseEnd_521392 < baseStart_521392 := by decide
  rcases family_descends (prefixWord ++ tailWord_521392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521394 : List Nat := [3, 2, 1, 1, 1, 4, 3, 1, 6]
def baseStart_521394 : Nat := 118140960795 + 521394 * 2 ^ 59
def prefixEnd_521394 : Nat := 4983230072969 + 3 ^ 40 * 521394 * 2
def baseEnd_521394 : Nat := 59494607193430728283813

theorem tailTrace_521394 : CollatzResearch.WordTrace tailWord_521394 prefixEnd_521394 59494607193430728283813 := by
  unfold tailWord_521394
  simp only [CollatzResearch.WordTrace]
  refine ⟨4754200368271514962728809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12677867648724039900610157 4754200368271514962728809)
  ·
    refine ⟨3565650276203636222046607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4754200368271514962728809 3565650276203636222046607)
    ·
      refine ⟨5348475414305454333069911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3565650276203636222046607 5348475414305454333069911)
      ·
        refine ⟨8022713121458181499604867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5348475414305454333069911 8022713121458181499604867)
        ·
          refine ⟨12034069682187272249407301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8022713121458181499604867 12034069682187272249407301)
          ·
            refine ⟨2256388065410113546763869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12034069682187272249407301 2256388065410113546763869)
            ·
              refine ⟨846145524528792580036451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2256388065410113546763869 846145524528792580036451)
              ·
                refine ⟨1269218286793188870054677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 846145524528792580036451 1269218286793188870054677)
                ·
                  refine ⟨59494607193430728283813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1269218286793188870054677 59494607193430728283813)
                  ·
                    rfl

theorem cell22_521394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 1, 6].length) (baseStart_521394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_521394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_521394 prefixEnd_521394 := by exact prefixLift 521394
  have htrace : WordTrace (prefixWord ++ tailWord_521394) baseStart_521394 baseEnd_521394 := by
    simpa [prefixWord, tailWord_521394, baseEnd_521394] using wordTrace_append hprefix tailTrace_521394
  have hstable : (prefixWord ++ tailWord_521394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521394).length < 2 ^ (prefixWord ++ tailWord_521394).sum := by decide
  have hdescent : baseEnd_521394 < baseStart_521394 := by decide
  rcases family_descends (prefixWord ++ tailWord_521394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521407 : List Nat := [1, 1, 2, 2, 2, 2, 2, 1, 3, 6]
def baseStart_521407 : Nat := 118140960795 + 521407 * 2 ^ 59
def prefixEnd_521407 : Nat := 4983230072969 + 3 ^ 40 * 521407 * 2
def baseEnd_521407 : Nat := 178488271745964484276399

theorem tailTrace_521407 : CollatzResearch.WordTrace tailWord_521407 prefixEnd_521407 178488271745964484276399 := by
  unfold tailWord_521407
  simp only [CollatzResearch.WordTrace]
  refine ⟨19017275622038963071138475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12678183748025975380758983 19017275622038963071138475)
  ·
    refine ⟨28525913433058444606707713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19017275622038963071138475 28525913433058444606707713)
    ·
      refine ⟨21394435074793833455030785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28525913433058444606707713 21394435074793833455030785)
      ·
        refine ⟨16045826306095375091273089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21394435074793833455030785 16045826306095375091273089)
        ·
          refine ⟨12034369729571531318454817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16045826306095375091273089 12034369729571531318454817)
          ·
            refine ⟨9025777297178648488841113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12034369729571531318454817 9025777297178648488841113)
            ·
              refine ⟨6769332972883986366630835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9025777297178648488841113 6769332972883986366630835)
              ·
                refine ⟨10153999459325979549946253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6769332972883986366630835 10153999459325979549946253)
                ·
                  refine ⟨3807749797247242331229845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10153999459325979549946253 3807749797247242331229845)
                  ·
                    refine ⟨178488271745964484276399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3807749797247242331229845 178488271745964484276399)
                    ·
                      rfl

theorem cell22_521407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 3, 6].length) (baseStart_521407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_521407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_521407 prefixEnd_521407 := by exact prefixLift 521407
  have htrace : WordTrace (prefixWord ++ tailWord_521407) baseStart_521407 baseEnd_521407 := by
    simpa [prefixWord, tailWord_521407, baseEnd_521407] using wordTrace_append hprefix tailTrace_521407
  have hstable : (prefixWord ++ tailWord_521407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521407).length < 2 ^ (prefixWord ++ tailWord_521407).sum := by decide
  have hdescent : baseEnd_521407 < baseStart_521407 := by decide
  rcases family_descends (prefixWord ++ tailWord_521407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521445 : List Nat := [1, 3, 1, 4, 3, 2, 2, 2, 4]
def baseStart_521445 : Nat := 118140960795 + 521445 * 2 ^ 59
def prefixEnd_521445 : Nat := 4983230072969 + 3 ^ 40 * 521445 * 2
def baseEnd_521445 : Nat := 59500426640848350608761

theorem tailTrace_521445 : CollatzResearch.WordTrace tailWord_521445 prefixEnd_521445 59500426640848350608761 := by
  unfold tailWord_521445
  simp only [CollatzResearch.WordTrace]
  refine ⟨19018661595901295561021789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12679107730600863707347859 19018661595901295561021789)
  ·
    refine ⟨7131998098462985835383171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19018661595901295561021789 7131998098462985835383171)
    ·
      refine ⟨10697997147694478753074757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7131998098462985835383171 10697997147694478753074757)
      ·
        refine ⟨2005874465192714766201517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10697997147694478753074757 2005874465192714766201517)
        ·
          refine ⟨752202924447268037325569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2005874465192714766201517 752202924447268037325569)
          ·
            refine ⟨564152193335451027994177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 752202924447268037325569 564152193335451027994177)
            ·
              refine ⟨423114145001588270995633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 564152193335451027994177 423114145001588270995633)
              ·
                refine ⟨317335608751191203246725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 423114145001588270995633 317335608751191203246725)
                ·
                  refine ⟨59500426640848350608761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 317335608751191203246725 59500426640848350608761)
                  ·
                    rfl

theorem cell22_521445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 2, 2, 4].length) (baseStart_521445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_521445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_521445 prefixEnd_521445 := by exact prefixLift 521445
  have htrace : WordTrace (prefixWord ++ tailWord_521445) baseStart_521445 baseEnd_521445 := by
    simpa [prefixWord, tailWord_521445, baseEnd_521445] using wordTrace_append hprefix tailTrace_521445
  have hstable : (prefixWord ++ tailWord_521445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521445).length < 2 ^ (prefixWord ++ tailWord_521445).sum := by decide
  have hdescent : baseEnd_521445 < baseStart_521445 := by decide
  rcases family_descends (prefixWord ++ tailWord_521445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521471 : List Nat := [1, 1, 2, 2, 1, 6, 1, 2, 3, 3]
def baseStart_521471 : Nat := 118140960795 + 521471 * 2 ^ 59
def prefixEnd_521471 : Nat := 4983230072969 + 3 ^ 40 * 521471 * 2
def baseEnd_521471 : Nat := 178510180253889650676203

theorem tailTrace_521471 : CollatzResearch.WordTrace tailWord_521471 prefixEnd_521471 178510180253889650676203 := by
  unfold tailWord_521471
  simp only [CollatzResearch.WordTrace]
  refine ⟨19019609893807102001468267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12679739929204734667645511 19019609893807102001468267)
  ·
    refine ⟨28529414840710653002202401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19019609893807102001468267 28529414840710653002202401)
    ·
      refine ⟨21397061130532989751651801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28529414840710653002202401 21397061130532989751651801)
      ·
        refine ⟨16047795847899742313738851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21397061130532989751651801 16047795847899742313738851)
        ·
          refine ⟨24071693771849613470608277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16047795847899742313738851 24071693771849613470608277)
          ·
            refine ⟨1128360645555450631434763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 24071693771849613470608277 1128360645555450631434763)
            ·
              refine ⟨1692540968333175947152145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1128360645555450631434763 1692540968333175947152145)
              ·
                refine ⟨1269405726249881960364109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1692540968333175947152145 1269405726249881960364109)
                ·
                  refine ⟨476027147343705735136541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1269405726249881960364109 476027147343705735136541)
                  ·
                    refine ⟨178510180253889650676203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 476027147343705735136541 178510180253889650676203)
                    ·
                      rfl

theorem cell22_521471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 2, 3, 3].length) (baseStart_521471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_521471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_521471 prefixEnd_521471 := by exact prefixLift 521471
  have htrace : WordTrace (prefixWord ++ tailWord_521471) baseStart_521471 baseEnd_521471 := by
    simpa [prefixWord, tailWord_521471, baseEnd_521471] using wordTrace_append hprefix tailTrace_521471
  have hstable : (prefixWord ++ tailWord_521471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521471).length < 2 ^ (prefixWord ++ tailWord_521471).sum := by decide
  have hdescent : baseEnd_521471 < baseStart_521471 := by decide
  rcases family_descends (prefixWord ++ tailWord_521471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521501 : List Nat := [1, 4, 2, 3, 1, 2, 1, 1, 7]
def baseStart_521501 : Nat := 118140960795 + 521501 * 2 ^ 59
def prefixEnd_521501 : Nat := 4983230072969 + 3 ^ 40 * 521501 * 2
def baseEnd_521501 : Nat := 59506816622326524142037

theorem tailTrace_521501 : CollatzResearch.WordTrace tailWord_521501 prefixEnd_521501 59506816622326524142037 := by
  unfold tailWord_521501
  simp only [CollatzResearch.WordTrace]
  refine ⟨19020704083698417125060357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12680469389132278083373571 19020704083698417125060357)
  ·
    refine ⟨3566382015693453210948817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19020704083698417125060357 3566382015693453210948817)
    ·
      refine ⟨2674786511770089908211613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3566382015693453210948817 2674786511770089908211613)
      ·
        refine ⟨1003044941913783715579355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2674786511770089908211613 1003044941913783715579355)
        ·
          refine ⟨1504567412870675573369033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1003044941913783715579355 1504567412870675573369033)
          ·
            refine ⟨1128425559653006680026775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1504567412870675573369033 1128425559653006680026775)
            ·
              refine ⟨1692638339479510020040163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1128425559653006680026775 1692638339479510020040163)
              ·
                refine ⟨2538957509219265030060245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1692638339479510020040163 2538957509219265030060245)
                ·
                  refine ⟨59506816622326524142037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2538957509219265030060245 59506816622326524142037)
                  ·
                    rfl

theorem cell22_521501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 1, 7].length) (baseStart_521501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_521501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_521501 prefixEnd_521501 := by exact prefixLift 521501
  have htrace : WordTrace (prefixWord ++ tailWord_521501) baseStart_521501 baseEnd_521501 := by
    simpa [prefixWord, tailWord_521501, baseEnd_521501] using wordTrace_append hprefix tailTrace_521501
  have hstable : (prefixWord ++ tailWord_521501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521501).length < 2 ^ (prefixWord ++ tailWord_521501).sum := by decide
  have hdescent : baseEnd_521501 < baseStart_521501 := by decide
  rcases family_descends (prefixWord ++ tailWord_521501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521544 : List Nat := [2, 1, 3, 1, 1, 2, 1, 3, 3, 5]
def baseStart_521544 : Nat := 118140960795 + 521544 * 2 ^ 59
def prefixEnd_521544 : Nat := 4983230072969 + 3 ^ 40 * 521544 * 2
def baseEnd_521544 : Nat := 178535169645741793600979

theorem tailTrace_521544 : CollatzResearch.WordTrace tailWord_521544 prefixEnd_521544 178535169645741793600979 := by
  unfold tailWord_521544
  simp only [CollatzResearch.WordTrace]
  refine ⟨9511136211271317734437843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12681514948361756979250457 9511136211271317734437843)
  ·
    refine ⟨14266704316906976601656765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9511136211271317734437843 14266704316906976601656765)
    ·
      refine ⟨5350014118840116225621287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14266704316906976601656765 5350014118840116225621287)
      ·
        refine ⟨8025021178260174338431931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5350014118840116225621287 8025021178260174338431931)
        ·
          refine ⟨12037531767390261507647897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8025021178260174338431931 12037531767390261507647897)
          ·
            refine ⟨9028148825542696130735923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12037531767390261507647897 9028148825542696130735923)
            ·
              refine ⟨13542223238314044196103885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9028148825542696130735923 13542223238314044196103885)
              ·
                refine ⟨5078333714367766573538957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13542223238314044196103885 5078333714367766573538957)
                ·
                  refine ⟨1904375142887912465077109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5078333714367766573538957 1904375142887912465077109)
                  ·
                    refine ⟨178535169645741793600979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1904375142887912465077109 178535169645741793600979)
                    ·
                      rfl

theorem cell22_521544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 3, 5].length) (baseStart_521544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_521544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_521544 prefixEnd_521544 := by exact prefixLift 521544
  have htrace : WordTrace (prefixWord ++ tailWord_521544) baseStart_521544 baseEnd_521544 := by
    simpa [prefixWord, tailWord_521544, baseEnd_521544] using wordTrace_append hprefix tailTrace_521544
  have hstable : (prefixWord ++ tailWord_521544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521544).length < 2 ^ (prefixWord ++ tailWord_521544).sum := by decide
  have hdescent : baseEnd_521544 < baseStart_521544 := by decide
  rcases family_descends (prefixWord ++ tailWord_521544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521561 : List Nat := [1, 2, 1, 2, 2, 2, 4, 1, 4, 3]
def baseStart_521561 : Nat := 118140960795 + 521561 * 2 ^ 59
def prefixEnd_521561 : Nat := 4983230072969 + 3 ^ 40 * 521561 * 2
def baseEnd_521561 : Nat := 178540989093159415925927

theorem tailTrace_521561 : CollatzResearch.WordTrace tailWord_521561 prefixEnd_521561 178540989093159415925927 := by
  unfold tailWord_521561
  simp only [CollatzResearch.WordTrace]
  refine ⟨19022892463481047372244537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12681928308987364914829691 19022892463481047372244537)
  ·
    refine ⟨14267169347610785529183403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19022892463481047372244537 14267169347610785529183403)
    ·
      refine ⟨21400754021416178293775105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14267169347610785529183403 21400754021416178293775105)
      ·
        refine ⟨16050565516062133720331329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21400754021416178293775105 16050565516062133720331329)
        ·
          refine ⟨12037924137046600290248497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16050565516062133720331329 12037924137046600290248497)
          ·
            refine ⟨9028443102784950217686373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12037924137046600290248497 9028443102784950217686373)
            ·
              refine ⟨1692833081772178165816195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9028443102784950217686373 1692833081772178165816195)
              ·
                refine ⟨2539249622658267248724293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1692833081772178165816195 2539249622658267248724293)
                ·
                  refine ⟨476109304248425109135805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2539249622658267248724293 476109304248425109135805)
                  ·
                    refine ⟨178540989093159415925927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 476109304248425109135805 178540989093159415925927)
                    ·
                      rfl

theorem cell22_521561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 1, 4, 3].length) (baseStart_521561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_521561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_521561 prefixEnd_521561 := by exact prefixLift 521561
  have htrace : WordTrace (prefixWord ++ tailWord_521561) baseStart_521561 baseEnd_521561 := by
    simpa [prefixWord, tailWord_521561, baseEnd_521561] using wordTrace_append hprefix tailTrace_521561
  have hstable : (prefixWord ++ tailWord_521561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521561).length < 2 ^ (prefixWord ++ tailWord_521561).sum := by decide
  have hdescent : baseEnd_521561 < baseStart_521561 := by decide
  rcases family_descends (prefixWord ++ tailWord_521561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521582 : List Nat := [4, 1, 2, 4, 1, 2, 1, 2, 1, 4]
def baseStart_521582 : Nat := 118140960795 + 521582 * 2 ^ 59
def prefixEnd_521582 : Nat := 4983230072969 + 3 ^ 40 * 521582 * 2
def baseEnd_521582 : Nat := 178548177822322361150863

theorem tailTrace_521582 : CollatzResearch.WordTrace tailWord_521582 prefixEnd_521582 178548177822322361150863 := by
  unfold tailWord_521582
  simp only [CollatzResearch.WordTrace]
  refine ⟨2377957299550620994844875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12682438930936645305839333 2377957299550620994844875)
  ·
    refine ⟨3566935949325931492267313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2377957299550620994844875 3566935949325931492267313)
    ·
      refine ⟨2675201961994448619200485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3566935949325931492267313 2675201961994448619200485)
      ·
        refine ⟨501600367873959116100091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2675201961994448619200485 501600367873959116100091)
        ·
          refine ⟨752400551810938674150137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 501600367873959116100091 752400551810938674150137)
          ·
            refine ⟨564300413858204005612603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 752400551810938674150137 564300413858204005612603)
            ·
              refine ⟨846450620787306008418905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 564300413858204005612603 846450620787306008418905)
              ·
                refine ⟨634837965590479506314179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 846450620787306008418905 634837965590479506314179)
                ·
                  refine ⟨952256948385719259471269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 634837965590479506314179 952256948385719259471269)
                  ·
                    refine ⟨178548177822322361150863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 952256948385719259471269 178548177822322361150863)
                    ·
                      rfl

theorem cell22_521582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 2, 1, 4].length) (baseStart_521582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_521582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_521582 prefixEnd_521582 := by exact prefixLift 521582
  have htrace : WordTrace (prefixWord ++ tailWord_521582) baseStart_521582 baseEnd_521582 := by
    simpa [prefixWord, tailWord_521582, baseEnd_521582] using wordTrace_append hprefix tailTrace_521582
  have hstable : (prefixWord ++ tailWord_521582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521582).length < 2 ^ (prefixWord ++ tailWord_521582).sum := by decide
  have hdescent : baseEnd_521582 < baseStart_521582 := by decide
  rcases family_descends (prefixWord ++ tailWord_521582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521614 : List Nat := [4, 1, 1, 4, 3, 1, 2, 2, 4]
def baseStart_521614 : Nat := 118140960795 + 521614 * 2 ^ 59
def prefixEnd_521614 : Nat := 4983230072969 + 3 ^ 40 * 521614 * 2
def baseEnd_521614 : Nat := 59519710692094981450255

theorem tailTrace_521614 : CollatzResearch.WordTrace tailWord_521614 prefixEnd_521614 59519710692094981450255 := by
  unfold tailWord_521614
  simp only [CollatzResearch.WordTrace]
  refine ⟨2378103191536129677990487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12683217021526024949282597 2378103191536129677990487)
  ·
    refine ⟨3567154787304194516985731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2378103191536129677990487 3567154787304194516985731)
    ·
      refine ⟨5350732180956291775478597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3567154787304194516985731 5350732180956291775478597)
      ·
        refine ⟨1003262283929304707902237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5350732180956291775478597 1003262283929304707902237)
        ·
          refine ⟨376223356473489265463339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1003262283929304707902237 376223356473489265463339)
          ·
            refine ⟨564335034710233898195009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376223356473489265463339 564335034710233898195009)
            ·
              refine ⟨423251276032675423646257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 564335034710233898195009 423251276032675423646257)
              ·
                refine ⟨317438457024506567734693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 423251276032675423646257 317438457024506567734693)
                ·
                  refine ⟨59519710692094981450255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 317438457024506567734693 59519710692094981450255)
                  ·
                    rfl

theorem cell22_521614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 2, 2, 4].length) (baseStart_521614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_521614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_521614 prefixEnd_521614 := by exact prefixLift 521614
  have htrace : WordTrace (prefixWord ++ tailWord_521614) baseStart_521614 baseEnd_521614 := by
    simpa [prefixWord, tailWord_521614, baseEnd_521614] using wordTrace_append hprefix tailTrace_521614
  have hstable : (prefixWord ++ tailWord_521614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521614).length < 2 ^ (prefixWord ++ tailWord_521614).sum := by decide
  have hdescent : baseEnd_521614 < baseStart_521614 := by decide
  rcases family_descends (prefixWord ++ tailWord_521614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521657 : List Nat := [1, 2, 1, 4, 4, 1, 2, 3, 1, 3]
def baseStart_521657 : Nat := 118140960795 + 521657 * 2 ^ 59
def prefixEnd_521657 : Nat := 4983230072969 + 3 ^ 40 * 521657 * 2
def baseEnd_521657 : Nat := 178573851855047165525633

theorem tailTrace_521657 : CollatzResearch.WordTrace tailWord_521657 prefixEnd_521657 178573851855047165525633 := by
  unfold tailWord_521657
  simp only [CollatzResearch.WordTrace]
  refine ⟨19026393871133255767739225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12684262580755503845159483 19026393871133255767739225)
  ·
    refine ⟨14269795403349941825804419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19026393871133255767739225 14269795403349941825804419)
    ·
      refine ⟨21404693105024912738706629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14269795403349941825804419 21404693105024912738706629)
      ·
        refine ⟨4013379957192171138507493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21404693105024912738706629 4013379957192171138507493)
        ·
          refine ⟨752508741973532088470155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4013379957192171138507493 752508741973532088470155)
          ·
            refine ⟨1128763112960298132705233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 752508741973532088470155 1128763112960298132705233)
            ·
              refine ⟨846572334720223599528925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1128763112960298132705233 846572334720223599528925)
              ·
                refine ⟨317464625520083849823347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 846572334720223599528925 317464625520083849823347)
                ·
                  refine ⟨476196938280125774735021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 317464625520083849823347 476196938280125774735021)
                  ·
                    refine ⟨178573851855047165525633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 476196938280125774735021 178573851855047165525633)
                    ·
                      rfl

theorem cell22_521657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 3, 1, 3].length) (baseStart_521657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_521657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_521657 prefixEnd_521657 := by exact prefixLift 521657
  have htrace : WordTrace (prefixWord ++ tailWord_521657) baseStart_521657 baseEnd_521657 := by
    simpa [prefixWord, tailWord_521657, baseEnd_521657] using wordTrace_append hprefix tailTrace_521657
  have hstable : (prefixWord ++ tailWord_521657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521657).length < 2 ^ (prefixWord ++ tailWord_521657).sum := by decide
  have hdescent : baseEnd_521657 < baseStart_521657 := by decide
  rcases family_descends (prefixWord ++ tailWord_521657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521668 : List Nat := [2, 3, 3, 2, 1, 1, 1, 2, 2, 5]
def baseStart_521668 : Nat := 118140960795 + 521668 * 2 ^ 59
def prefixEnd_521668 : Nat := 4983230072969 + 3 ^ 40 * 521668 * 2
def baseEnd_521668 : Nat := 178577617379846803500599

theorem tailTrace_521668 : CollatzResearch.WordTrace tailWord_521668 prefixEnd_521668 178577617379846803500599 := by
  unfold tailWord_521668
  simp only [CollatzResearch.WordTrace]
  refine ⟨9513397537046702323194829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12684530049395603097593105 9513397537046702323194829)
  ·
    refine ⟨3567524076392513371198061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9513397537046702323194829 3567524076392513371198061)
    ·
      refine ⟨1337821528647192514199273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3567524076392513371198061 1337821528647192514199273)
      ·
        refine ⟨1003366146485394385649455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1337821528647192514199273 1003366146485394385649455)
        ·
          refine ⟨1505049219728091578474183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1003366146485394385649455 1505049219728091578474183)
          ·
            refine ⟨2257573829592137367711275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1505049219728091578474183 2257573829592137367711275)
            ·
              refine ⟨3386360744388206051566913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2257573829592137367711275 3386360744388206051566913)
              ·
                refine ⟨2539770558291154538675185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3386360744388206051566913 2539770558291154538675185)
                ·
                  refine ⟨1904827918718365904006389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2539770558291154538675185 1904827918718365904006389)
                  ·
                    refine ⟨178577617379846803500599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1904827918718365904006389 178577617379846803500599)
                    ·
                      rfl

theorem cell22_521668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_521668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_521668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_521668 prefixEnd_521668 := by exact prefixLift 521668
  have htrace : WordTrace (prefixWord ++ tailWord_521668) baseStart_521668 baseEnd_521668 := by
    simpa [prefixWord, tailWord_521668, baseEnd_521668] using wordTrace_append hprefix tailTrace_521668
  have hstable : (prefixWord ++ tailWord_521668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521668).length < 2 ^ (prefixWord ++ tailWord_521668).sum := by decide
  have hdescent : baseEnd_521668 < baseStart_521668 := by decide
  rcases family_descends (prefixWord ++ tailWord_521668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521696 : List Nat := [2, 1, 1, 3, 1, 1, 2, 5, 1, 5]
def baseStart_521696 : Nat := 118140960795 + 521696 * 2 ^ 59
def prefixEnd_521696 : Nat := 4983230072969 + 3 ^ 40 * 521696 * 2
def baseEnd_521696 : Nat := 178587202352064063800513

theorem tailTrace_521696 : CollatzResearch.WordTrace tailWord_521696 prefixEnd_521696 178587202352064063800513 := by
  unfold tailWord_521696
  simp only [CollatzResearch.WordTrace]
  refine ⟨9513908158995982714204471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12685210878661310285605961 9513908158995982714204471)
  ·
    refine ⟨14270862238493974071306707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9513908158995982714204471 14270862238493974071306707)
    ·
      refine ⟨21406293357740961106960061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14270862238493974071306707 21406293357740961106960061)
      ·
        refine ⟨8027360009152860415110023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21406293357740961106960061 8027360009152860415110023)
        ·
          refine ⟨12041040013729290622665035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8027360009152860415110023 12041040013729290622665035)
          ·
            refine ⟨18061560020593935933997553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12041040013729290622665035 18061560020593935933997553)
            ·
              refine ⟨13546170015445451950498165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18061560020593935933997553 13546170015445451950498165)
              ·
                refine ⟨1269953438948011120359203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13546170015445451950498165 1269953438948011120359203)
                ·
                  refine ⟨1904930158422016680538805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1269953438948011120359203 1904930158422016680538805)
                  ·
                    refine ⟨178587202352064063800513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1904930158422016680538805 178587202352064063800513)
                    ·
                      rfl

theorem cell22_521696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 5, 1, 5].length) (baseStart_521696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_521696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_521696 prefixEnd_521696 := by exact prefixLift 521696
  have htrace : WordTrace (prefixWord ++ tailWord_521696) baseStart_521696 baseEnd_521696 := by
    simpa [prefixWord, tailWord_521696, baseEnd_521696] using wordTrace_append hprefix tailTrace_521696
  have hstable : (prefixWord ++ tailWord_521696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521696).length < 2 ^ (prefixWord ++ tailWord_521696).sum := by decide
  have hdescent : baseEnd_521696 < baseStart_521696 := by decide
  rcases family_descends (prefixWord ++ tailWord_521696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521711 : List Nat := [1, 1, 2, 1, 4, 1, 4, 1, 1, 6]
def baseStart_521711 : Nat := 118140960795 + 521711 * 2 ^ 59
def prefixEnd_521711 : Nat := 4983230072969 + 3 ^ 40 * 521711 * 2
def baseEnd_521711 : Nat := 178592337158609024675467

theorem tailTrace_521711 : CollatzResearch.WordTrace tailWord_521711 prefixEnd_521711 178592337158609024675467 := by
  unfold tailWord_521711
  simp only [CollatzResearch.WordTrace]
  refine ⟨19028363412937622990204987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12685575608625081993469991 19028363412937622990204987)
  ·
    refine ⟨28542545119406434485307481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19028363412937622990204987 28542545119406434485307481)
    ·
      refine ⟨21406908839554825863980611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28542545119406434485307481 21406908839554825863980611)
      ·
        refine ⟨32110363259332238795970917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21406908839554825863980611 32110363259332238795970917)
        ·
          refine ⟨6020693111124794774244547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32110363259332238795970917 6020693111124794774244547)
          ·
            refine ⟨9031039666687192161366821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6020693111124794774244547 9031039666687192161366821)
            ·
              refine ⟨1693319937503848530256279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9031039666687192161366821 1693319937503848530256279)
              ·
                refine ⟨2539979906255772795384419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1693319937503848530256279 2539979906255772795384419)
                ·
                  refine ⟨3809969859383659193076629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2539979906255772795384419 3809969859383659193076629)
                  ·
                    refine ⟨178592337158609024675467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3809969859383659193076629 178592337158609024675467)
                    ·
                      rfl

theorem cell22_521711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 1, 1, 6].length) (baseStart_521711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_521711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_521711 prefixEnd_521711 := by exact prefixLift 521711
  have htrace : WordTrace (prefixWord ++ tailWord_521711) baseStart_521711 baseEnd_521711 := by
    simpa [prefixWord, tailWord_521711, baseEnd_521711] using wordTrace_append hprefix tailTrace_521711
  have hstable : (prefixWord ++ tailWord_521711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521711).length < 2 ^ (prefixWord ++ tailWord_521711).sum := by decide
  have hdescent : baseEnd_521711 < baseStart_521711 := by decide
  rcases family_descends (prefixWord ++ tailWord_521711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521713 : List Nat := [1, 2, 2, 2, 3, 2, 1, 2, 4, 3]
def baseStart_521713 : Nat := 118140960795 + 521713 * 2 ^ 59
def prefixEnd_521713 : Nat := 4983230072969 + 3 ^ 40 * 521713 * 2
def baseEnd_521713 : Nat := 178593021799481686125461

theorem tailTrace_521713 : CollatzResearch.WordTrace tailWord_521713 prefixEnd_521713 178593021799481686125461 := by
  unfold tailWord_521713
  simp only [CollatzResearch.WordTrace]
  refine ⟨19028436358930377331777793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12685624239286918221185195 19028436358930377331777793)
  ·
    refine ⟨14271327269197782998833345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19028436358930377331777793 14271327269197782998833345)
    ·
      refine ⟨10703495451898337249125009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14271327269197782998833345 10703495451898337249125009)
      ·
        refine ⟨8027621588923752936843757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10703495451898337249125009 8027621588923752936843757)
        ·
          refine ⟨3010358095846407351316409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8027621588923752936843757 3010358095846407351316409)
          ·
            refine ⟨2257768571884805513487307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3010358095846407351316409 2257768571884805513487307)
            ·
              refine ⟨3386652857827208270230961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2257768571884805513487307 3386652857827208270230961)
              ·
                refine ⟨2539989643370406202673221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3386652857827208270230961 2539989643370406202673221)
                ·
                  refine ⟨476248058131951163001229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2539989643370406202673221 476248058131951163001229)
                  ·
                    refine ⟨178593021799481686125461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 476248058131951163001229 178593021799481686125461)
                    ·
                      rfl

theorem cell22_521713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 2, 4, 3].length) (baseStart_521713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_521713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_521713 prefixEnd_521713 := by exact prefixLift 521713
  have htrace : WordTrace (prefixWord ++ tailWord_521713) baseStart_521713 baseEnd_521713 := by
    simpa [prefixWord, tailWord_521713, baseEnd_521713] using wordTrace_append hprefix tailTrace_521713
  have hstable : (prefixWord ++ tailWord_521713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521713).length < 2 ^ (prefixWord ++ tailWord_521713).sum := by decide
  have hdescent : baseEnd_521713 < baseStart_521713 := by decide
  rcases family_descends (prefixWord ++ tailWord_521713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521732 : List Nat := [2, 3, 2, 3, 3, 1, 1, 1, 6]
def baseStart_521732 : Nat := 118140960795 + 521732 * 2 ^ 59
def prefixEnd_521732 : Nat := 4983230072969 + 3 ^ 40 * 521732 * 2
def baseEnd_521732 : Nat := 59533175295923989966801

theorem tailTrace_521732 : CollatzResearch.WordTrace tailWord_521732 prefixEnd_521732 59533175295923989966801 := by
  unfold tailWord_521732
  simp only [CollatzResearch.WordTrace]
  refine ⟨9514564672930771788359725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12686086230574362384479633 9514564672930771788359725)
  ·
    refine ⟨3567961752349039420634897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9514564672930771788359725 3567961752349039420634897)
    ·
      refine ⟨2675971314261779565476173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3567961752349039420634897 2675971314261779565476173)
      ·
        refine ⟨1003489242848167337053565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2675971314261779565476173 1003489242848167337053565)
        ·
          refine ⟨376308466068062751395087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1003489242848167337053565 376308466068062751395087)
          ·
            refine ⟨564462699102094127092631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376308466068062751395087 564462699102094127092631)
            ·
              refine ⟨846694048653141190638947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 564462699102094127092631 846694048653141190638947)
              ·
                refine ⟨1270041072979711785958421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 846694048653141190638947 1270041072979711785958421)
                ·
                  refine ⟨59533175295923989966801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1270041072979711785958421 59533175295923989966801)
                  ·
                    rfl

theorem cell22_521732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 1, 6].length) (baseStart_521732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_521732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_521732 prefixEnd_521732 := by exact prefixLift 521732
  have htrace : WordTrace (prefixWord ++ tailWord_521732) baseStart_521732 baseEnd_521732 := by
    simpa [prefixWord, tailWord_521732, baseEnd_521732] using wordTrace_append hprefix tailTrace_521732
  have hstable : (prefixWord ++ tailWord_521732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521732).length < 2 ^ (prefixWord ++ tailWord_521732).sum := by decide
  have hdescent : baseEnd_521732 < baseStart_521732 := by decide
  rcases family_descends (prefixWord ++ tailWord_521732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521747 : List Nat := [1, 1, 1, 2, 1, 8, 2, 1, 2, 3]
def baseStart_521747 : Nat := 118140960795 + 521747 * 2 ^ 59
def prefixEnd_521747 : Nat := 4983230072969 + 3 ^ 40 * 521747 * 2
def baseEnd_521747 : Nat := 178604660694316930775357

theorem tailTrace_521747 : CollatzResearch.WordTrace tailWord_521747 prefixEnd_521747 178604660694316930775357 := by
  unfold tailWord_521747
  simp only [CollatzResearch.WordTrace]
  refine ⟨19029676440807201138515495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12686450960538134092343663 19029676440807201138515495)
  ·
    refine ⟨28544514661210801707773243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19029676440807201138515495 28544514661210801707773243)
    ·
      refine ⟨42816771991816202561659865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28544514661210801707773243 42816771991816202561659865)
      ·
        refine ⟨32112578993862151921244899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42816771991816202561659865 32112578993862151921244899)
        ·
          refine ⟨48168868490793227881867349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32112578993862151921244899 48168868490793227881867349)
          ·
            refine ⟨564478927626483139240633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 48168868490793227881867349 564478927626483139240633)
            ·
              refine ⟨423359195719862354430475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 564478927626483139240633 423359195719862354430475)
              ·
                refine ⟨635038793579793531645713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 423359195719862354430475 635038793579793531645713)
                ·
                  refine ⟨476279095184845148734285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 635038793579793531645713 476279095184845148734285)
                  ·
                    refine ⟨178604660694316930775357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 476279095184845148734285 178604660694316930775357)
                    ·
                      rfl

theorem cell22_521747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 2, 1, 2, 3].length) (baseStart_521747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_521747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_521747 prefixEnd_521747 := by exact prefixLift 521747
  have htrace : WordTrace (prefixWord ++ tailWord_521747) baseStart_521747 baseEnd_521747 := by
    simpa [prefixWord, tailWord_521747, baseEnd_521747] using wordTrace_append hprefix tailTrace_521747
  have hstable : (prefixWord ++ tailWord_521747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521747).length < 2 ^ (prefixWord ++ tailWord_521747).sum := by decide
  have hdescent : baseEnd_521747 < baseStart_521747 := by decide
  rcases family_descends (prefixWord ++ tailWord_521747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521863 : List Nat := [1, 1, 4, 2, 1, 3, 1, 2, 1, 6]
def baseStart_521863 : Nat := 118140960795 + 521863 * 2 ^ 59
def prefixEnd_521863 : Nat := 4983230072969 + 3 ^ 40 * 521863 * 2
def baseEnd_521863 : Nat := 178644369864931294875001

theorem tailTrace_521863 : CollatzResearch.WordTrace tailWord_521863 prefixEnd_521863 178644369864931294875001 := by
  unfold tailWord_521863
  simp only [CollatzResearch.WordTrace]
  refine ⟨19033907308386952949738243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12689271538924635299825495 19033907308386952949738243)
  ·
    refine ⟨28550860962580429424607365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19033907308386952949738243 28550860962580429424607365)
    ·
      refine ⟨5353286430483830517113881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28550860962580429424607365 5353286430483830517113881)
      ·
        refine ⟨4014964822862872887835411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5353286430483830517113881 4014964822862872887835411)
        ·
          refine ⟨6022447234294309331753117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4014964822862872887835411 6022447234294309331753117)
          ·
            refine ⟨2258417712860365999407419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6022447234294309331753117 2258417712860365999407419)
            ·
              refine ⟨3387626569290548999111129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2258417712860365999407419 3387626569290548999111129)
              ·
                refine ⟨2540719926967911749333347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3387626569290548999111129 2540719926967911749333347)
                ·
                  refine ⟨3811079890451867624000021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2540719926967911749333347 3811079890451867624000021)
                  ·
                    refine ⟨178644369864931294875001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3811079890451867624000021 178644369864931294875001)
                    ·
                      rfl

theorem cell22_521863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 2, 1, 6].length) (baseStart_521863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_521863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_521863 prefixEnd_521863 := by exact prefixLift 521863
  have htrace : WordTrace (prefixWord ++ tailWord_521863) baseStart_521863 baseEnd_521863 := by
    simpa [prefixWord, tailWord_521863, baseEnd_521863] using wordTrace_append hprefix tailTrace_521863
  have hstable : (prefixWord ++ tailWord_521863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521863).length < 2 ^ (prefixWord ++ tailWord_521863).sum := by decide
  have hdescent : baseEnd_521863 < baseStart_521863 := by decide
  rcases family_descends (prefixWord ++ tailWord_521863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521865 : List Nat := [1, 2, 1, 1, 4, 1, 2, 5, 2, 3]
def baseStart_521865 : Nat := 118140960795 + 521865 * 2 ^ 59
def prefixEnd_521865 : Nat := 4983230072969 + 3 ^ 40 * 521865 * 2
def baseEnd_521865 : Nat := 178645054505803956324995

theorem tailTrace_521865 : CollatzResearch.WordTrace tailWord_521865 prefixEnd_521865 178645054505803956324995 := by
  unfold tailWord_521865
  simp only [CollatzResearch.WordTrace]
  refine ⟨19033980254379707291311049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12689320169586471527540699 19033980254379707291311049)
  ·
    refine ⟨14275485190784780468483287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19033980254379707291311049 14275485190784780468483287)
    ·
      refine ⟨21413227786177170702724931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14275485190784780468483287 21413227786177170702724931)
      ·
        refine ⟨32119841679265756054087397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21413227786177170702724931 32119841679265756054087397)
        ·
          refine ⟨6022470314862329260141387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32119841679265756054087397 6022470314862329260141387)
          ·
            refine ⟨9033705472293493890212081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6022470314862329260141387 9033705472293493890212081)
            ·
              refine ⟨6775279104220120417659061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9033705472293493890212081 6775279104220120417659061)
              ·
                refine ⟨635182416020636289155537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6775279104220120417659061 635182416020636289155537)
                ·
                  refine ⟨476386812015477216866653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 635182416020636289155537 476386812015477216866653)
                  ·
                    refine ⟨178645054505803956324995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 476386812015477216866653 178645054505803956324995)
                    ·
                      rfl

theorem cell22_521865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 5, 2, 3].length) (baseStart_521865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_521865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_521865 prefixEnd_521865 := by exact prefixLift 521865
  have htrace : WordTrace (prefixWord ++ tailWord_521865) baseStart_521865 baseEnd_521865 := by
    simpa [prefixWord, tailWord_521865, baseEnd_521865] using wordTrace_append hprefix tailTrace_521865
  have hstable : (prefixWord ++ tailWord_521865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521865).length < 2 ^ (prefixWord ++ tailWord_521865).sum := by decide
  have hdescent : baseEnd_521865 < baseStart_521865 := by decide
  rcases family_descends (prefixWord ++ tailWord_521865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521884 : List Nat := [2, 2, 3, 2, 3, 2, 1, 3, 4]
def baseStart_521884 : Nat := 118140960795 + 521884 * 2 ^ 59
def prefixEnd_521884 : Nat := 4983230072969 + 3 ^ 40 * 521884 * 2
def baseEnd_521884 : Nat := 59550519531364746699979

theorem tailTrace_521884 : CollatzResearch.WordTrace tailWord_521884 prefixEnd_521884 59550519531364746699979 := by
  unfold tailWord_521884
  simp only [CollatzResearch.WordTrace]
  refine ⟨9517336620655436768126353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12689782160873915690835137 9517336620655436768126353)
  ·
    refine ⟨7138002465491577576094765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9517336620655436768126353 7138002465491577576094765)
    ·
      refine ⟨2676750924559341591035537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7138002465491577576094765 2676750924559341591035537)
      ·
        refine ⟨2007563193419506193276653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2676750924559341591035537 2007563193419506193276653)
        ·
          refine ⟨752836197532314822478745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2007563193419506193276653 752836197532314822478745)
          ·
            refine ⟨564627148149236116859059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 752836197532314822478745 564627148149236116859059)
            ·
              refine ⟨846940722223854175288589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 564627148149236116859059 846940722223854175288589)
              ·
                refine ⟨317602770833945315733221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 846940722223854175288589 317602770833945315733221)
                ·
                  refine ⟨59550519531364746699979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 317602770833945315733221 59550519531364746699979)
                  ·
                    rfl

theorem cell22_521884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 3, 4].length) (baseStart_521884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_521884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_521884 prefixEnd_521884 := by exact prefixLift 521884
  have htrace : WordTrace (prefixWord ++ tailWord_521884) baseStart_521884 baseEnd_521884 := by
    simpa [prefixWord, tailWord_521884, baseEnd_521884] using wordTrace_append hprefix tailTrace_521884
  have hstable : (prefixWord ++ tailWord_521884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521884).length < 2 ^ (prefixWord ++ tailWord_521884).sum := by decide
  have hdescent : baseEnd_521884 < baseStart_521884 := by decide
  rcases family_descends (prefixWord ++ tailWord_521884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521970 : List Nat := [3, 2, 1, 3, 1, 1, 1, 1, 5, 4]
def baseStart_521970 : Nat := 118140960795 + 521970 * 2 ^ 59
def prefixEnd_521970 : Nat := 4983230072969 + 3 ^ 40 * 521970 * 2
def baseEnd_521970 : Nat := 178680998151618682449673

theorem tailTrace_521970 : CollatzResearch.WordTrace tailWord_521970 prefixEnd_521970 178680998151618682449673 := by
  unfold tailWord_521970
  simp only [CollatzResearch.WordTrace]
  refine ⟨4759452479749827555970841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12691873279332873482588909 4759452479749827555970841)
  ·
    refine ⟨3569589359812370666978131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4759452479749827555970841 3569589359812370666978131)
    ·
      refine ⟨5354384039718556000467197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3569589359812370666978131 5354384039718556000467197)
      ·
        refine ⟨2007894014894458500175199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5354384039718556000467197 2007894014894458500175199)
        ·
          refine ⟨3011841022341687750262799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2007894014894458500175199 3011841022341687750262799)
          ·
            refine ⟨4517761533512531625394199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3011841022341687750262799 4517761533512531625394199)
            ·
              refine ⟨6776642300268797438091299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4517761533512531625394199 6776642300268797438091299)
              ·
                refine ⟨10164963450403196157136949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6776642300268797438091299 10164963450403196157136949)
                ·
                  refine ⟨952965323475299639731589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10164963450403196157136949 952965323475299639731589)
                  ·
                    refine ⟨178680998151618682449673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 952965323475299639731589 178680998151618682449673)
                    ·
                      rfl

theorem cell22_521970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 5, 4].length) (baseStart_521970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_521970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_521970 prefixEnd_521970 := by exact prefixLift 521970
  have htrace : WordTrace (prefixWord ++ tailWord_521970) baseStart_521970 baseEnd_521970 := by
    simpa [prefixWord, tailWord_521970, baseEnd_521970] using wordTrace_append hprefix tailTrace_521970
  have hstable : (prefixWord ++ tailWord_521970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521970).length < 2 ^ (prefixWord ++ tailWord_521970).sum := by decide
  have hdescent : baseEnd_521970 < baseStart_521970 := by decide
  rcases family_descends (prefixWord ++ tailWord_521970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522015 : List Nat := [1, 1, 2, 4, 2, 1, 2, 1, 4, 4]
def baseStart_522015 : Nat := 118140960795 + 522015 * 2 ^ 59
def prefixEnd_522015 : Nat := 4983230072969 + 3 ^ 40 * 522015 * 2
def baseEnd_522015 : Nat := 178696402571253565074535

theorem tailTrace_522015 : CollatzResearch.WordTrace tailWord_522015 prefixEnd_522015 178696402571253565074535 := by
  unfold tailWord_522015
  simp only [CollatzResearch.WordTrace]
  refine ⟨19039451203836282909271499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12692967469224188606180999 19039451203836282909271499)
  ·
    refine ⟨28559176805754424363907249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19039451203836282909271499 28559176805754424363907249)
    ·
      refine ⟨21419382604315818272930437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28559176805754424363907249 21419382604315818272930437)
      ·
        refine ⟨4016134238309215926174457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21419382604315818272930437 4016134238309215926174457)
        ·
          refine ⟨3012100678731911944630843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4016134238309215926174457 3012100678731911944630843)
          ·
            refine ⟨4518151018097867916946265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3012100678731911944630843 4518151018097867916946265)
            ·
              refine ⟨3388613263573400937709699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4518151018097867916946265 3388613263573400937709699)
              ·
                refine ⟨5082919895360101406564549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3388613263573400937709699 5082919895360101406564549)
                ·
                  refine ⟨953047480380019013730853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5082919895360101406564549 953047480380019013730853)
                  ·
                    refine ⟨178696402571253565074535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 953047480380019013730853 178696402571253565074535)
                    ·
                      rfl

theorem cell22_522015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 4, 4].length) (baseStart_522015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_522015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_522015 prefixEnd_522015 := by exact prefixLift 522015
  have htrace : WordTrace (prefixWord ++ tailWord_522015) baseStart_522015 baseEnd_522015 := by
    simpa [prefixWord, tailWord_522015, baseEnd_522015] using wordTrace_append hprefix tailTrace_522015
  have hstable : (prefixWord ++ tailWord_522015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522015).length < 2 ^ (prefixWord ++ tailWord_522015).sum := by decide
  have hdescent : baseEnd_522015 < baseStart_522015 := by decide
  rcases family_descends (prefixWord ++ tailWord_522015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522017 : List Nat := [1, 2, 3, 2, 1, 4, 1, 1, 4, 3]
def baseStart_522017 : Nat := 118140960795 + 522017 * 2 ^ 59
def prefixEnd_522017 : Nat := 4983230072969 + 3 ^ 40 * 522017 * 2
def baseEnd_522017 : Nat := 178697087212126226524529

theorem tailTrace_522017 : CollatzResearch.WordTrace tailWord_522017 prefixEnd_522017 178697087212126226524529 := by
  unfold tailWord_522017
  simp only [CollatzResearch.WordTrace]
  refine ⟨19039524149829037250844305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12693016099886024833896203 19039524149829037250844305)
  ·
    refine ⟨14279643112371777938133229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19039524149829037250844305 14279643112371777938133229)
    ·
      refine ⟨5354866167139416726799961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14279643112371777938133229 5354866167139416726799961)
      ·
        refine ⟨4016149625354562545099971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5354866167139416726799961 4016149625354562545099971)
        ·
          refine ⟨6024224438031843817649957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4016149625354562545099971 6024224438031843817649957)
          ·
            refine ⟨1129542082130970715809367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6024224438031843817649957 1129542082130970715809367)
            ·
              refine ⟨1694313123196456073714051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1129542082130970715809367 1694313123196456073714051)
              ·
                refine ⟨2541469684794684110571077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1694313123196456073714051 2541469684794684110571077)
                ·
                  refine ⟨476525565899003270732077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2541469684794684110571077 476525565899003270732077)
                  ·
                    refine ⟨178697087212126226524529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 476525565899003270732077 178697087212126226524529)
                    ·
                      rfl

theorem cell22_522017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 1, 4, 3].length) (baseStart_522017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_522017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_522017 prefixEnd_522017 := by exact prefixLift 522017
  have htrace : WordTrace (prefixWord ++ tailWord_522017) baseStart_522017 baseEnd_522017 := by
    simpa [prefixWord, tailWord_522017, baseEnd_522017] using wordTrace_append hprefix tailTrace_522017
  have hstable : (prefixWord ++ tailWord_522017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522017).length < 2 ^ (prefixWord ++ tailWord_522017).sum := by decide
  have hdescent : baseEnd_522017 < baseStart_522017 := by decide
  rcases family_descends (prefixWord ++ tailWord_522017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522079 : List Nat := [1, 1, 2, 3, 1, 6, 1, 1, 3, 3]
def baseStart_522079 : Nat := 118140960795 + 522079 * 2 ^ 59
def prefixEnd_522079 : Nat := 4983230072969 + 3 ^ 40 * 522079 * 2
def baseEnd_522079 : Nat := 178718311079178731474339

theorem tailTrace_522079 : CollatzResearch.WordTrace tailWord_522079 prefixEnd_522079 178718311079178731474339 := by
  unfold tailWord_522079
  simp only [CollatzResearch.WordTrace]
  refine ⟨19041785475604421839601291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12694523650402947893067527 19041785475604421839601291)
  ·
    refine ⟨28562678213406632759401937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19041785475604421839601291 28562678213406632759401937)
    ·
      refine ⟨21422008660054974569551453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28562678213406632759401937 21422008660054974569551453)
      ·
        refine ⟨8033253247520615463581795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21422008660054974569551453 8033253247520615463581795)
        ·
          refine ⟨12049879871280923195372693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8033253247520615463581795 12049879871280923195372693)
          ·
            refine ⟨564838118966293274783095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 12049879871280923195372693 564838118966293274783095)
            ·
              refine ⟨847257178449439912174643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 564838118966293274783095 847257178449439912174643)
              ·
                refine ⟨1270885767674159868261965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 847257178449439912174643 1270885767674159868261965)
                ·
                  refine ⟨476582162877809950598237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1270885767674159868261965 476582162877809950598237)
                  ·
                    refine ⟨178718311079178731474339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 476582162877809950598237 178718311079178731474339)
                    ·
                      rfl

theorem cell22_522079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 1, 3, 3].length) (baseStart_522079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_522079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_522079 prefixEnd_522079 := by exact prefixLift 522079
  have htrace : WordTrace (prefixWord ++ tailWord_522079) baseStart_522079 baseEnd_522079 := by
    simpa [prefixWord, tailWord_522079, baseEnd_522079] using wordTrace_append hprefix tailTrace_522079
  have hstable : (prefixWord ++ tailWord_522079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522079).length < 2 ^ (prefixWord ++ tailWord_522079).sum := by decide
  have hdescent : baseEnd_522079 < baseStart_522079 := by decide
  rcases family_descends (prefixWord ++ tailWord_522079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522092 : List Nat := [2, 2, 1, 1, 4, 3, 1, 3, 5]
def baseStart_522092 : Nat := 118140960795 + 522092 * 2 ^ 59
def prefixEnd_522092 : Nat := 4983230072969 + 3 ^ 40 * 522092 * 2
def baseEnd_522092 : Nat := 59574253748283676966433

theorem tailTrace_522092 : CollatzResearch.WordTrace tailWord_522092 prefixEnd_522092 59574253748283676966433 := by
  unfold tailWord_522092
  simp only [CollatzResearch.WordTrace]
  refine ⟨9521129812278662529912265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12694839749704883373216353 9521129812278662529912265)
  ·
    refine ⟨7140847359208996897434199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9521129812278662529912265 7140847359208996897434199)
    ·
      refine ⟨10711271038813495346151299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7140847359208996897434199 10711271038813495346151299)
      ·
        refine ⟨16066906558220243019226949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10711271038813495346151299 16066906558220243019226949)
        ·
          refine ⟨3012544979666295566105053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16066906558220243019226949 3012544979666295566105053)
          ·
            refine ⟨1129704367374860837289395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3012544979666295566105053 1129704367374860837289395)
            ·
              refine ⟨1694556551062291255934093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1129704367374860837289395 1694556551062291255934093)
              ·
                refine ⟨635458706648359220975285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1694556551062291255934093 635458706648359220975285)
                ·
                  refine ⟨59574253748283676966433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 635458706648359220975285 59574253748283676966433)
                  ·
                    rfl

theorem cell22_522092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 5].length) (baseStart_522092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_522092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_522092 prefixEnd_522092 := by exact prefixLift 522092
  have htrace : WordTrace (prefixWord ++ tailWord_522092) baseStart_522092 baseEnd_522092 := by
    simpa [prefixWord, tailWord_522092, baseEnd_522092] using wordTrace_append hprefix tailTrace_522092
  have hstable : (prefixWord ++ tailWord_522092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522092).length < 2 ^ (prefixWord ++ tailWord_522092).sum := by decide
  have hdescent : baseEnd_522092 < baseStart_522092 := by decide
  rcases family_descends (prefixWord ++ tailWord_522092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522126 : List Nat := [4, 1, 1, 5, 1, 1, 2, 2, 5]
def baseStart_522126 : Nat := 118140960795 + 522126 * 2 ^ 59
def prefixEnd_522126 : Nat := 4983230072969 + 3 ^ 40 * 522126 * 2
def baseEnd_522126 : Nat := 59578133379895425183065

theorem tailTrace_522126 : CollatzResearch.WordTrace tailWord_522126 prefixEnd_522126 59578133379895425183065 := by
  unfold tailWord_522126
  simp only [CollatzResearch.WordTrace]
  refine ⟨2380437463304268608320279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12695666470956099244374821 2380437463304268608320279)
  ·
    refine ⟨3570656194956402912480419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2380437463304268608320279 3570656194956402912480419)
    ·
      refine ⟨5355984292434604368720629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3570656194956402912480419 5355984292434604368720629)
      ·
        refine ⟨502123527415744159567559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5355984292434604368720629 502123527415744159567559)
        ·
          refine ⟨753185291123616239351339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 502123527415744159567559 753185291123616239351339)
          ·
            refine ⟨1129777936685424359027009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 753185291123616239351339 1129777936685424359027009)
            ·
              refine ⟨847333452514068269270257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1129777936685424359027009 847333452514068269270257)
              ·
                refine ⟨635500089385551201952693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 847333452514068269270257 635500089385551201952693)
                ·
                  refine ⟨59578133379895425183065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 635500089385551201952693 59578133379895425183065)
                  ·
                    rfl

theorem cell22_522126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 2, 5].length) (baseStart_522126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_522126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_522126 prefixEnd_522126 := by exact prefixLift 522126
  have htrace : WordTrace (prefixWord ++ tailWord_522126) baseStart_522126 baseEnd_522126 := by
    simpa [prefixWord, tailWord_522126, baseEnd_522126] using wordTrace_append hprefix tailTrace_522126
  have hstable : (prefixWord ++ tailWord_522126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522126).length < 2 ^ (prefixWord ++ tailWord_522126).sum := by decide
  have hdescent : baseEnd_522126 < baseStart_522126 := by decide
  rcases family_descends (prefixWord ++ tailWord_522126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522130 : List Nat := [3, 2, 3, 2, 1, 3, 2, 2, 1, 3]
def baseStart_522130 : Nat := 118140960795 + 522130 * 2 ^ 59
def prefixEnd_522130 : Nat := 4983230072969 + 3 ^ 40 * 522130 * 2
def baseEnd_522130 : Nat := 178735769421431598449183

theorem tailTrace_522130 : CollatzResearch.WordTrace tailWord_522130 prefixEnd_522130 178735769421431598449183 := by
  unfold tailWord_522130
  simp only [CollatzResearch.WordTrace]
  refine ⟨4760911399604914387426961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12695763732279771699805229 4760911399604914387426961)
  ·
    refine ⟨3570683549703685790570221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4760911399604914387426961 3570683549703685790570221)
    ·
      refine ⟨1339006331138882171463833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3570683549703685790570221 1339006331138882171463833)
      ·
        refine ⟨1004254748354161628597875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1339006331138882171463833 1004254748354161628597875)
        ·
          refine ⟨1506382122531242442896813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1004254748354161628597875 1506382122531242442896813)
          ·
            refine ⟨564893295949215916086305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1506382122531242442896813 564893295949215916086305)
            ·
              refine ⟨423669971961911937064729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 564893295949215916086305 423669971961911937064729)
              ·
                refine ⟨317752478971433952798547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 423669971961911937064729 317752478971433952798547)
                ·
                  refine ⟨476628718457150929197821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 317752478971433952798547 476628718457150929197821)
                  ·
                    refine ⟨178735769421431598449183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 476628718457150929197821 178735769421431598449183)
                    ·
                      rfl

theorem cell22_522130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_522130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_522130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_522130 prefixEnd_522130 := by exact prefixLift 522130
  have htrace : WordTrace (prefixWord ++ tailWord_522130) baseStart_522130 baseEnd_522130 := by
    simpa [prefixWord, tailWord_522130, baseEnd_522130] using wordTrace_append hprefix tailTrace_522130
  have hstable : (prefixWord ++ tailWord_522130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522130).length < 2 ^ (prefixWord ++ tailWord_522130).sum := by decide
  have hdescent : baseEnd_522130 < baseStart_522130 := by decide
  rcases family_descends (prefixWord ++ tailWord_522130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522248 : List Nat := [2, 1, 3, 2, 1, 2, 5, 2, 1, 3]
def baseStart_522248 : Nat := 118140960795 + 522248 * 2 ^ 59
def prefixEnd_522248 : Nat := 4983230072969 + 3 ^ 40 * 522248 * 2
def baseEnd_522248 : Nat := 178776163232918623998821

theorem tailTrace_522248 : CollatzResearch.WordTrace tailWord_522248 prefixEnd_522248 178776163232918623998821 := by
  unfold tailWord_522248
  simp only [CollatzResearch.WordTrace]
  refine ⟨9523974705996081851251699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12698632941328109135002265 9523974705996081851251699)
  ·
    refine ⟨14285962058994122776877549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9523974705996081851251699 14285962058994122776877549)
    ·
      refine ⟨5357235772122796041329081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14285962058994122776877549 5357235772122796041329081)
      ·
        refine ⟨4017926829092097030996811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5357235772122796041329081 4017926829092097030996811)
        ·
          refine ⟨6026890243638145546495217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4017926829092097030996811 6026890243638145546495217)
          ·
            refine ⟨4520167682728609159871413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6026890243638145546495217 4520167682728609159871413)
            ·
              refine ⟨423765720255807108737945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4520167682728609159871413 423765720255807108737945)
              ·
                refine ⟨317824290191855331553459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 423765720255807108737945 317824290191855331553459)
                ·
                  refine ⟨476736435287782997330189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 317824290191855331553459 476736435287782997330189)
                  ·
                    refine ⟨178776163232918623998821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 476736435287782997330189 178776163232918623998821)
                    ·
                      rfl

theorem cell22_522248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 5, 2, 1, 3].length) (baseStart_522248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_522248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_522248 prefixEnd_522248 := by exact prefixLift 522248
  have htrace : WordTrace (prefixWord ++ tailWord_522248) baseStart_522248 baseEnd_522248 := by
    simpa [prefixWord, tailWord_522248, baseEnd_522248] using wordTrace_append hprefix tailTrace_522248
  have hstable : (prefixWord ++ tailWord_522248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522248).length < 2 ^ (prefixWord ++ tailWord_522248).sum := by decide
  have hdescent : baseEnd_522248 < baseStart_522248 := by decide
  rcases family_descends (prefixWord ++ tailWord_522248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522274 : List Nat := [3, 3, 1, 1, 1, 2, 3, 1, 3, 4]
def baseStart_522274 : Nat := 118140960795 + 522274 * 2 ^ 59
def prefixEnd_522274 : Nat := 4983230072969 + 3 ^ 40 * 522274 * 2
def baseEnd_522274 : Nat := 178785063564263222848741

theorem tailTrace_522274 : CollatzResearch.WordTrace tailWord_522274 prefixEnd_522274 178785063564263222848741 := by
  unfold tailWord_522274
  simp only [CollatzResearch.WordTrace]
  refine ⟨4762224427474492535737469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12699265139931980095299917 4762224427474492535737469)
  ·
    refine ⟨1785834160302934700901551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4762224427474492535737469 1785834160302934700901551)
    ·
      refine ⟨2678751240454402051352327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1785834160302934700901551 2678751240454402051352327)
      ·
        refine ⟨4018126860681603077028491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2678751240454402051352327 4018126860681603077028491)
        ·
          refine ⟨6027190291022404615542737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4018126860681603077028491 6027190291022404615542737)
          ·
            refine ⟨4520392718266803461657053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6027190291022404615542737 4520392718266803461657053)
            ·
              refine ⟨1695147269350051298121395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4520392718266803461657053 1695147269350051298121395)
              ·
                refine ⟨2542720904025076947182093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1695147269350051298121395 2542720904025076947182093)
                ·
                  refine ⟨953520339009403855193285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2542720904025076947182093 953520339009403855193285)
                  ·
                    refine ⟨178785063564263222848741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 953520339009403855193285 178785063564263222848741)
                    ·
                      rfl

theorem cell22_522274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_522274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_522274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_522274 prefixEnd_522274 := by exact prefixLift 522274
  have htrace : WordTrace (prefixWord ++ tailWord_522274) baseStart_522274 baseEnd_522274 := by
    simpa [prefixWord, tailWord_522274, baseEnd_522274] using wordTrace_append hprefix tailTrace_522274
  have hstable : (prefixWord ++ tailWord_522274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522274).length < 2 ^ (prefixWord ++ tailWord_522274).sum := by decide
  have hdescent : baseEnd_522274 < baseStart_522274 := by decide
  rcases family_descends (prefixWord ++ tailWord_522274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522336 : List Nat := [2, 1, 1, 3, 2, 5, 1, 1, 2, 4]
def baseStart_522336 : Nat := 118140960795 + 522336 * 2 ^ 59
def prefixEnd_522336 : Nat := 4983230072969 + 3 ^ 40 * 522336 * 2
def baseEnd_522336 : Nat := 178806287431315727798551

theorem tailTrace_522336 : CollatzResearch.WordTrace tailWord_522336 prefixEnd_522336 178806287431315727798551 := by
  unfold tailWord_522336
  simp only [CollatzResearch.WordTrace]
  refine ⟨9525579517836677365853431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12700772690448903154471241 9525579517836677365853431)
  ·
    refine ⟨14288369276755016048780147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9525579517836677365853431 14288369276755016048780147)
    ·
      refine ⟨21432553915132524073170221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14288369276755016048780147 21432553915132524073170221)
      ·
        refine ⟨8037207718174696527438833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21432553915132524073170221 8037207718174696527438833)
        ·
          refine ⟨6027905788631022395579125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8037207718174696527438833 6027905788631022395579125)
          ·
            refine ⟨565116167684158349585543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6027905788631022395579125 565116167684158349585543)
            ·
              refine ⟨847674251526237524378315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 565116167684158349585543 847674251526237524378315)
              ·
                refine ⟨1271511377289356286567473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 847674251526237524378315 1271511377289356286567473)
                ·
                  refine ⟨953633532967017214925605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1271511377289356286567473 953633532967017214925605)
                  ·
                    refine ⟨178806287431315727798551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 953633532967017214925605 178806287431315727798551)
                    ·
                      rfl

theorem cell22_522336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 1, 2, 4].length) (baseStart_522336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_522336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_522336 prefixEnd_522336 := by exact prefixLift 522336
  have htrace : WordTrace (prefixWord ++ tailWord_522336) baseStart_522336 baseEnd_522336 := by
    simpa [prefixWord, tailWord_522336, baseEnd_522336] using wordTrace_append hprefix tailTrace_522336
  have hstable : (prefixWord ++ tailWord_522336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522336).length < 2 ^ (prefixWord ++ tailWord_522336).sum := by decide
  have hdescent : baseEnd_522336 < baseStart_522336 := by decide
  rcases family_descends (prefixWord ++ tailWord_522336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522400 : List Nat := [2, 1, 1, 4, 2, 4, 1, 3, 1, 3]
def baseStart_522400 : Nat := 118140960795 + 522400 * 2 ^ 59
def prefixEnd_522400 : Nat := 4983230072969 + 3 ^ 40 * 522400 * 2
def baseEnd_522400 : Nat := 178828195939240894198355

theorem tailTrace_522400 : CollatzResearch.WordTrace tailWord_522400 prefixEnd_522400 178828195939240894198355 := by
  unfold tailWord_522400
  simp only [CollatzResearch.WordTrace]
  refine ⟨9526746653720746831018327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12702328871627662441357769 9526746653720746831018327)
  ·
    refine ⟨14290119980581120246527491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9526746653720746831018327 14290119980581120246527491)
    ·
      refine ⟨21435179970871680369791237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14290119980581120246527491 21435179970871680369791237)
      ·
        refine ⟨4019096244538440069335857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21435179970871680369791237 4019096244538440069335857)
        ·
          refine ⟨3014322183403830052001893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4019096244538440069335857 3014322183403830052001893)
          ·
            refine ⟨565185409388218134750355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3014322183403830052001893 565185409388218134750355)
            ·
              refine ⟨847778114082327202125533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 565185409388218134750355 847778114082327202125533)
              ·
                refine ⟨317916792780872700797075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 847778114082327202125533 317916792780872700797075)
                ·
                  refine ⟨476875189171309051195613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 317916792780872700797075 476875189171309051195613)
                  ·
                    refine ⟨178828195939240894198355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 476875189171309051195613 178828195939240894198355)
                    ·
                      rfl

theorem cell22_522400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 3, 1, 3].length) (baseStart_522400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_522400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_522400 prefixEnd_522400 := by exact prefixLift 522400
  have htrace : WordTrace (prefixWord ++ tailWord_522400) baseStart_522400 baseEnd_522400 := by
    simpa [prefixWord, tailWord_522400, baseEnd_522400] using wordTrace_append hprefix tailTrace_522400
  have hstable : (prefixWord ++ tailWord_522400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522400).length < 2 ^ (prefixWord ++ tailWord_522400).sum := by decide
  have hdescent : baseEnd_522400 < baseStart_522400 := by decide
  rcases family_descends (prefixWord ++ tailWord_522400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522417 : List Nat := [1, 2, 2, 5, 2, 1, 3, 2, 1, 3]
def baseStart_522417 : Nat := 118140960795 + 522417 * 2 ^ 59
def prefixEnd_522417 : Nat := 4983230072969 + 3 ^ 40 * 522417 * 2
def baseEnd_522417 : Nat := 178834015386658516523303

theorem tailTrace_522417 : CollatzResearch.WordTrace tailWord_522417 prefixEnd_522417 178834015386658516523303 := by
  unfold tailWord_522417
  simp only [CollatzResearch.WordTrace]
  refine ⟨19054113348379905565405505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12702742232253270376937003 19054113348379905565405505)
  ·
    refine ⟨14290585011284929174054129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19054113348379905565405505 14290585011284929174054129)
    ·
      refine ⟨10717938758463696880540597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14290585011284929174054129 10717938758463696880540597)
      ·
        refine ⟨1004806758605971582550681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10717938758463696880540597 1004806758605971582550681)
        ·
          refine ⟨753605068954478686913011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1004806758605971582550681 753605068954478686913011)
          ·
            refine ⟨1130407603431718030369517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 753605068954478686913011 1130407603431718030369517)
            ·
              refine ⟨423902851286894261388569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1130407603431718030369517 423902851286894261388569)
              ·
                refine ⟨317927138465170696041427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 423902851286894261388569 317927138465170696041427)
                ·
                  refine ⟨476890707697756044062141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 317927138465170696041427 476890707697756044062141)
                  ·
                    refine ⟨178834015386658516523303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 476890707697756044062141 178834015386658516523303)
                    ·
                      rfl

theorem cell22_522417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 3, 2, 1, 3].length) (baseStart_522417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_522417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_522417 prefixEnd_522417 := by exact prefixLift 522417
  have htrace : WordTrace (prefixWord ++ tailWord_522417) baseStart_522417 baseEnd_522417 := by
    simpa [prefixWord, tailWord_522417, baseEnd_522417] using wordTrace_append hprefix tailTrace_522417
  have hstable : (prefixWord ++ tailWord_522417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522417).length < 2 ^ (prefixWord ++ tailWord_522417).sum := by decide
  have hdescent : baseEnd_522417 < baseStart_522417 := by decide
  rcases family_descends (prefixWord ++ tailWord_522417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522430 : List Nat := [4, 2, 1, 1, 4, 2, 2, 1, 5]
def baseStart_522430 : Nat := 118140960795 + 522430 * 2 ^ 59
def prefixEnd_522430 : Nat := 4983230072969 + 3 ^ 40 * 522430 * 2
def baseEnd_522430 : Nat := 59612821850776938649421

theorem tailTrace_522430 : CollatzResearch.WordTrace tailWord_522430 prefixEnd_522430 59612821850776938649421 := by
  unfold tailWord_522430
  simp only [CollatzResearch.WordTrace]
  refine ⟨2381823437166601098203593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12703058331555205857085829 2381823437166601098203593)
  ·
    refine ⟨1786367577874950823652695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2381823437166601098203593 1786367577874950823652695)
    ·
      refine ⟨2679551366812426235479043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1786367577874950823652695 2679551366812426235479043)
      ·
        refine ⟨4019327050218639353218565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2679551366812426235479043 4019327050218639353218565)
        ·
          refine ⟨753623821915994878728481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4019327050218639353218565 753623821915994878728481)
          ·
            refine ⟨565217866436996159046361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 753623821915994878728481 565217866436996159046361)
            ·
              refine ⟨423913399827747119284771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 565217866436996159046361 423913399827747119284771)
              ·
                refine ⟨635870099741620678927157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 423913399827747119284771 635870099741620678927157)
                ·
                  refine ⟨59612821850776938649421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 635870099741620678927157 59612821850776938649421)
                  ·
                    rfl

theorem cell22_522430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 2, 1, 5].length) (baseStart_522430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_522430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_522430 prefixEnd_522430 := by exact prefixLift 522430
  have htrace : WordTrace (prefixWord ++ tailWord_522430) baseStart_522430 baseEnd_522430 := by
    simpa [prefixWord, tailWord_522430, baseEnd_522430] using wordTrace_append hprefix tailTrace_522430
  have hstable : (prefixWord ++ tailWord_522430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522430).length < 2 ^ (prefixWord ++ tailWord_522430).sum := by decide
  have hdescent : baseEnd_522430 < baseStart_522430 := by decide
  rcases family_descends (prefixWord ++ tailWord_522430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522456 : List Nat := [2, 1, 2, 2, 4, 2, 1, 2, 1, 5]
def baseStart_522456 : Nat := 118140960795 + 522456 * 2 ^ 59
def prefixEnd_522456 : Nat := 4983230072969 + 3 ^ 40 * 522456 * 2
def baseEnd_522456 : Nat := 178847365883675414798183

theorem tailTrace_522456 : CollatzResearch.WordTrace tailWord_522456 prefixEnd_522456 178847365883675414798183 := by
  unfold tailWord_522456
  simp only [CollatzResearch.WordTrace]
  refine ⟨9527767897619307613037611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12703690530159076817383481 9527767897619307613037611)
  ·
    refine ⟨14291651846428961419556417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9527767897619307613037611 14291651846428961419556417)
    ·
      refine ⟨10718738884821721064667313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14291651846428961419556417 10718738884821721064667313)
      ·
        refine ⟨8039054163616290798500485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10718738884821721064667313 8039054163616290798500485)
        ·
          refine ⟨1507322655678054524718841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8039054163616290798500485 1507322655678054524718841)
          ·
            refine ⟨1130491991758540893539131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1507322655678054524718841 1130491991758540893539131)
            ·
              refine ⟨1695737987637811340308697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1130491991758540893539131 1695737987637811340308697)
              ·
                refine ⟨1271803490728358505231523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1695737987637811340308697 1271803490728358505231523)
                ·
                  refine ⟨1907705236092537757847285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1271803490728358505231523 1907705236092537757847285)
                  ·
                    refine ⟨178847365883675414798183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1907705236092537757847285 178847365883675414798183)
                    ·
                      rfl

theorem cell22_522456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 2, 1, 5].length) (baseStart_522456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_522456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_522456 prefixEnd_522456 := by exact prefixLift 522456
  have htrace : WordTrace (prefixWord ++ tailWord_522456) baseStart_522456 baseEnd_522456 := by
    simpa [prefixWord, tailWord_522456, baseEnd_522456] using wordTrace_append hprefix tailTrace_522456
  have hstable : (prefixWord ++ tailWord_522456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522456).length < 2 ^ (prefixWord ++ tailWord_522456).sum := by decide
  have hdescent : baseEnd_522456 < baseStart_522456 := by decide
  rcases family_descends (prefixWord ++ tailWord_522456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522469 : List Nat := [1, 3, 1, 4, 2, 11]
def baseStart_522469 : Nat := 118140960795 + 522469 * 2 ^ 59
def prefixEnd_522469 : Nat := 4983230072969 + 3 ^ 40 * 522469 * 2
def baseEnd_522469 : Nat := 2208047111720342150903

theorem tailTrace_522469 : CollatzResearch.WordTrace tailWord_522469 prefixEnd_522469 2208047111720342150903 := by
  unfold tailWord_522469
  simp only [CollatzResearch.WordTrace]
  refine ⟨19056009944191518446298461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12704006629461012297532307 19056009944191518446298461)
  ·
    refine ⟨7146003729071819417361923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19056009944191518446298461 7146003729071819417361923)
    ·
      refine ⟨10719005593607729126042885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7146003729071819417361923 10719005593607729126042885)
      ·
        refine ⟨2009813548801449211133041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10719005593607729126042885 2009813548801449211133041)
        ·
          refine ⟨1507360161601086908349781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2009813548801449211133041 1507360161601086908349781)
          ·
            refine ⟨2208047111720342150903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 1507360161601086908349781 2208047111720342150903)
            ·
              rfl

theorem cell22_522469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 11].length) (baseStart_522469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_522469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_522469 prefixEnd_522469 := by exact prefixLift 522469
  have htrace : WordTrace (prefixWord ++ tailWord_522469) baseStart_522469 baseEnd_522469 := by
    simpa [prefixWord, tailWord_522469, baseEnd_522469] using wordTrace_append hprefix tailTrace_522469
  have hstable : (prefixWord ++ tailWord_522469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522469).length < 2 ^ (prefixWord ++ tailWord_522469).sum := by decide
  have hdescent : baseEnd_522469 < baseStart_522469 := by decide
  rcases family_descends (prefixWord ++ tailWord_522469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522486 : List Nat := [5, 1, 1, 1, 1, 1, 5, 7]
def baseStart_522486 : Nat := 118140960795 + 522486 * 2 ^ 59
def prefixEnd_522486 : Nat := 4983230072969 + 3 ^ 40 * 522486 * 2
def baseEnd_522486 : Nat := 19873070610751704060899

theorem tailTrace_522486 : CollatzResearch.WordTrace tailWord_522486 prefixEnd_522486 19873070610751704060899 := by
  unfold tailWord_522486
  simp only [CollatzResearch.WordTrace]
  refine ⟨1191039374070620646854207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12704419990086620233111541 1191039374070620646854207)
  ·
    refine ⟨1786559061105930970281311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1191039374070620646854207 1786559061105930970281311)
    ·
      refine ⟨2679838591658896455421967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1786559061105930970281311 2679838591658896455421967)
      ·
        refine ⟨4019757887488344683132951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2679838591658896455421967 4019757887488344683132951)
        ·
          refine ⟨6029636831232517024699427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4019757887488344683132951 6029636831232517024699427)
          ·
            refine ⟨9044455246848775537049141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6029636831232517024699427 9044455246848775537049141)
            ·
              refine ⟨847917679392072706598357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9044455246848775537049141 847917679392072706598357)
              ·
                refine ⟨19873070610751704060899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 847917679392072706598357 19873070610751704060899)
                ·
                  rfl

theorem cell22_522486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 7].length) (baseStart_522486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_522486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_522486 prefixEnd_522486 := by exact prefixLift 522486
  have htrace : WordTrace (prefixWord ++ tailWord_522486) baseStart_522486 baseEnd_522486 := by
    simpa [prefixWord, tailWord_522486, baseEnd_522486] using wordTrace_append hprefix tailTrace_522486
  have hstable : (prefixWord ++ tailWord_522486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522486).length < 2 ^ (prefixWord ++ tailWord_522486).sum := by decide
  have hdescent : baseEnd_522486 < baseStart_522486 := by decide
  rcases family_descends (prefixWord ++ tailWord_522486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522499 : List Nat := [1, 1, 1, 3, 2, 3, 1, 2, 2, 6]
def baseStart_522499 : Nat := 118140960795 + 522499 * 2 ^ 59
def prefixEnd_522499 : Nat := 4983230072969 + 3 ^ 40 * 522499 * 2
def baseEnd_522499 : Nat := 178862085662437635973051

theorem tailTrace_522499 : CollatzResearch.WordTrace tailWord_522499 prefixEnd_522499 178862085662437635973051 := by
  unfold tailWord_522499
  simp only [CollatzResearch.WordTrace]
  refine ⟨19057104134082833569890551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12704736089388555713260367 19057104134082833569890551)
  ·
    refine ⟨28585656201124250354835827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19057104134082833569890551 28585656201124250354835827)
    ·
      refine ⟨42878484301686375532253741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28585656201124250354835827 42878484301686375532253741)
      ·
        refine ⟨16079431613132390824595153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42878484301686375532253741 16079431613132390824595153)
        ·
          refine ⟨12059573709849293118446365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16079431613132390824595153 12059573709849293118446365)
          ·
            refine ⟨4522340141193484919417387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12059573709849293118446365 4522340141193484919417387)
            ·
              refine ⟨6783510211790227379126081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4522340141193484919417387 6783510211790227379126081)
              ·
                refine ⟨5087632658842670534344561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6783510211790227379126081 5087632658842670534344561)
                ·
                  refine ⟨3815724494132002900758421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5087632658842670534344561 3815724494132002900758421)
                  ·
                    refine ⟨178862085662437635973051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3815724494132002900758421 178862085662437635973051)
                    ·
                      rfl

theorem cell22_522499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 2, 6].length) (baseStart_522499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_522499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_522499 prefixEnd_522499 := by exact prefixLift 522499
  have htrace : WordTrace (prefixWord ++ tailWord_522499) baseStart_522499 baseEnd_522499 := by
    simpa [prefixWord, tailWord_522499, baseEnd_522499] using wordTrace_append hprefix tailTrace_522499
  have hstable : (prefixWord ++ tailWord_522499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522499).length < 2 ^ (prefixWord ++ tailWord_522499).sum := by decide
  have hdescent : baseEnd_522499 < baseStart_522499 := by decide
  rcases family_descends (prefixWord ++ tailWord_522499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522544 : List Nat := [2, 1, 1, 1, 2, 2, 2, 1, 2, 8]
def baseStart_522544 : Nat := 118140960795 + 522544 * 2 ^ 59
def prefixEnd_522544 : Nat := 4983230072969 + 3 ^ 40 * 522544 * 2
def baseEnd_522544 : Nat := 178877490082072518597913

theorem tailTrace_522544 : CollatzResearch.WordTrace tailWord_522544 prefixEnd_522544 178877490082072518597913 := by
  unfold tailWord_522544
  simp only [CollatzResearch.WordTrace]
  refine ⟨9529372709459903127639343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12705830279279870836852457 9529372709459903127639343)
  ·
    refine ⟨14294059064189854691459015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9529372709459903127639343 14294059064189854691459015)
    ·
      refine ⟨21441088596284782037188523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14294059064189854691459015 21441088596284782037188523)
      ·
        refine ⟨32161632894427173055782785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21441088596284782037188523 32161632894427173055782785)
        ·
          refine ⟨24121224670820379791837089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32161632894427173055782785 24121224670820379791837089)
          ·
            refine ⟨18090918503115284843877817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24121224670820379791837089 18090918503115284843877817)
            ·
              refine ⟨13568188877336463632908363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18090918503115284843877817 13568188877336463632908363)
              ·
                refine ⟨20352283316004695449362545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13568188877336463632908363 20352283316004695449362545)
                ·
                  refine ⟨15264212487003521587021909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20352283316004695449362545 15264212487003521587021909)
                  ·
                    refine ⟨178877490082072518597913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 15264212487003521587021909 178877490082072518597913)
                    ·
                      rfl

theorem cell22_522544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 2, 8].length) (baseStart_522544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_522544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_522544 prefixEnd_522544 := by exact prefixLift 522544
  have htrace : WordTrace (prefixWord ++ tailWord_522544) baseStart_522544 baseEnd_522544 := by
    simpa [prefixWord, tailWord_522544, baseEnd_522544] using wordTrace_append hprefix tailTrace_522544
  have hstable : (prefixWord ++ tailWord_522544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522544).length < 2 ^ (prefixWord ++ tailWord_522544).sum := by decide
  have hdescent : baseEnd_522544 < baseStart_522544 := by decide
  rcases family_descends (prefixWord ++ tailWord_522544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522578 : List Nat := [3, 2, 2, 1, 1, 1, 4, 3, 1, 4]
def baseStart_522578 : Nat := 118140960795 + 522578 * 2 ^ 59
def prefixEnd_522578 : Nat := 4983230072969 + 3 ^ 40 * 522578 * 2
def baseEnd_522578 : Nat := 178889128976907763247809

theorem tailTrace_522578 : CollatzResearch.WordTrace tailWord_522578 prefixEnd_522578 178889128976907763247809 := by
  unfold tailWord_522578
  simp only [CollatzResearch.WordTrace]
  refine ⟨4764996375199157515504097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12706657000531086708010925 4764996375199157515504097)
  ·
    refine ⟨3573747281399368136628073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4764996375199157515504097 3573747281399368136628073)
    ·
      refine ⟨2680310461049526102471055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3573747281399368136628073 2680310461049526102471055)
      ·
        refine ⟨4020465691574289153706583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2680310461049526102471055 4020465691574289153706583)
        ·
          refine ⟨6030698537361433730559875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4020465691574289153706583 6030698537361433730559875)
          ·
            refine ⟨9046047806042150595839813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6030698537361433730559875 9046047806042150595839813)
            ·
              refine ⟨1696133963632903236719965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9046047806042150595839813 1696133963632903236719965)
              ·
                refine ⟨636050236362338713769987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1696133963632903236719965 636050236362338713769987)
                ·
                  refine ⟨954075354543508070654981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 636050236362338713769987 954075354543508070654981)
                  ·
                    refine ⟨178889128976907763247809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 954075354543508070654981 178889128976907763247809)
                    ·
                      rfl

theorem cell22_522578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_522578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_522578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_522578 prefixEnd_522578 := by exact prefixLift 522578
  have htrace : WordTrace (prefixWord ++ tailWord_522578) baseStart_522578 baseEnd_522578 := by
    simpa [prefixWord, tailWord_522578, baseEnd_522578] using wordTrace_append hprefix tailTrace_522578
  have hstable : (prefixWord ++ tailWord_522578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522578).length < 2 ^ (prefixWord ++ tailWord_522578).sum := by decide
  have hdescent : baseEnd_522578 < baseStart_522578 := by decide
  rcases family_descends (prefixWord ++ tailWord_522578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522621 : List Nat := [1, 4, 1, 1, 2, 3, 2, 8]
def baseStart_522621 : Nat := 118140960795 + 522621 * 2 ^ 59
def prefixEnd_522621 : Nat := 4983230072969 + 3 ^ 40 * 522621 * 2
def baseEnd_522621 : Nat := 19878205417296664935853

theorem tailTrace_522621 : CollatzResearch.WordTrace tailWord_522621 prefixEnd_522621 19878205417296664935853 := by
  unfold tailWord_522621
  simp only [CollatzResearch.WordTrace]
  refine ⟨19061553839640848405831717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12707702559760565603887811 19061553839640848405831717)
  ·
    refine ⟨3574041344932659076093447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19061553839640848405831717 3574041344932659076093447)
    ·
      refine ⟨5361062017398988614140171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3574041344932659076093447 5361062017398988614140171)
      ·
        refine ⟨8041593026098482921210257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5361062017398988614140171 8041593026098482921210257)
        ·
          refine ⟨6031194769573862190907693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8041593026098482921210257 6031194769573862190907693)
          ·
            refine ⟨2261698038590198321590385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6031194769573862190907693 2261698038590198321590385)
            ·
              refine ⟨1696273528942648741192789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2261698038590198321590385 1696273528942648741192789)
              ·
                refine ⟨19878205417296664935853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1696273528942648741192789 19878205417296664935853)
                ·
                  rfl

theorem cell22_522621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 8].length) (baseStart_522621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_522621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_522621 prefixEnd_522621 := by exact prefixLift 522621
  have htrace : WordTrace (prefixWord ++ tailWord_522621) baseStart_522621 baseEnd_522621 := by
    simpa [prefixWord, tailWord_522621, baseEnd_522621] using wordTrace_append hprefix tailTrace_522621
  have hstable : (prefixWord ++ tailWord_522621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522621).length < 2 ^ (prefixWord ++ tailWord_522621).sum := by decide
  have hdescent : baseEnd_522621 < baseStart_522621 := by decide
  rcases family_descends (prefixWord ++ tailWord_522621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522644 : List Nat := [2, 4, 2, 1, 3, 2, 2, 2, 4]
def baseStart_522644 : Nat := 118140960795 + 522644 * 2 ^ 59
def prefixEnd_522644 : Nat := 4983230072969 + 3 ^ 40 * 522644 * 2
def baseEnd_522644 : Nat := 59637240708568530365869

theorem tailTrace_522644 : CollatzResearch.WordTrace tailWord_522644 prefixEnd_522644 59637240708568530365869 := by
  unfold tailWord_522644
  simp only [CollatzResearch.WordTrace]
  refine ⟨9531196359278761666959493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12708261812371682222612657 9531196359278761666959493)
  ·
    refine ⟨1787099317364767812554905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9531196359278761666959493 1787099317364767812554905)
    ·
      refine ⟨1340324488023575859416179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1787099317364767812554905 1340324488023575859416179)
      ·
        refine ⟨2010486732035363789124269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1340324488023575859416179 2010486732035363789124269)
        ·
          refine ⟨753932524513261420921601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2010486732035363789124269 753932524513261420921601)
          ·
            refine ⟨565449393384946065691201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 753932524513261420921601 565449393384946065691201)
            ·
              refine ⟨424087045038709549268401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 565449393384946065691201 424087045038709549268401)
              ·
                refine ⟨318065283779032161951301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 424087045038709549268401 318065283779032161951301)
                ·
                  refine ⟨59637240708568530365869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 318065283779032161951301 59637240708568530365869)
                  ·
                    rfl

theorem cell22_522644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 2, 2, 4].length) (baseStart_522644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_522644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_522644 prefixEnd_522644 := by exact prefixLift 522644
  have htrace : WordTrace (prefixWord ++ tailWord_522644) baseStart_522644 baseEnd_522644 := by
    simpa [prefixWord, tailWord_522644, baseEnd_522644] using wordTrace_append hprefix tailTrace_522644
  have hstable : (prefixWord ++ tailWord_522644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522644).length < 2 ^ (prefixWord ++ tailWord_522644).sum := by decide
  have hdescent : baseEnd_522644 < baseStart_522644 := by decide
  rcases family_descends (prefixWord ++ tailWord_522644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522728 : List Nat := [2, 1, 4, 1, 1, 3, 2, 2, 6]
def baseStart_522728 : Nat := 118140960795 + 522728 * 2 ^ 59
def prefixEnd_522728 : Nat := 4983230072969 + 3 ^ 40 * 522728 * 2
def baseEnd_522728 : Nat := 59646825680785790665783

theorem tailTrace_522728 : CollatzResearch.WordTrace tailWord_522728 prefixEnd_522728 59646825680785790665783 := by
  unfold tailWord_522728
  simp only [CollatzResearch.WordTrace]
  refine ⟨9532728225126602839988419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12710304300168803786651225 9532728225126602839988419)
  ·
    refine ⟨14299092337689904259982629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9532728225126602839988419 14299092337689904259982629)
    ·
      refine ⟨2681079813316857048746743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14299092337689904259982629 2681079813316857048746743)
      ·
        refine ⟨4021619719975285573120115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2681079813316857048746743 4021619719975285573120115)
        ·
          refine ⟨6032429579962928359680173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4021619719975285573120115 6032429579962928359680173)
          ·
            refine ⟨2262161092486098134880065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6032429579962928359680173 2262161092486098134880065)
            ·
              refine ⟨1696620819364573601160049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2262161092486098134880065 1696620819364573601160049)
              ·
                refine ⟨1272465614523430200870037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1696620819364573601160049 1272465614523430200870037)
                ·
                  refine ⟨59646825680785790665783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1272465614523430200870037 59646825680785790665783)
                  ·
                    rfl

theorem cell22_522728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 2, 6].length) (baseStart_522728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_522728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_522728 prefixEnd_522728 := by exact prefixLift 522728
  have htrace : WordTrace (prefixWord ++ tailWord_522728) baseStart_522728 baseEnd_522728 := by
    simpa [prefixWord, tailWord_522728, baseEnd_522728] using wordTrace_append hprefix tailTrace_522728
  have hstable : (prefixWord ++ tailWord_522728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522728).length < 2 ^ (prefixWord ++ tailWord_522728).sum := by decide
  have hdescent : baseEnd_522728 < baseStart_522728 := by decide
  rcases family_descends (prefixWord ++ tailWord_522728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522730 : List Nat := [3, 1, 3, 1, 3, 1, 1, 4, 1, 4]
def baseStart_522730 : Nat := 118140960795 + 522730 * 2 ^ 59
def prefixEnd_522730 : Nat := 4983230072969 + 3 ^ 40 * 522730 * 2
def baseEnd_522730 : Nat := 178941161683230033447343

theorem tailTrace_522730 : CollatzResearch.WordTrace tailWord_522730 prefixEnd_522730 178941161683230033447343 := by
  unfold tailWord_522730
  simp only [CollatzResearch.WordTrace]
  refine ⟨4766382349061490005387411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12710352930830640014366429 4766382349061490005387411)
  ·
    refine ⟨7149573523592235008081117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4766382349061490005387411 7149573523592235008081117)
    ·
      refine ⟨2681090071347088128030419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7149573523592235008081117 2681090071347088128030419)
      ·
        refine ⟨4021635107020632192045629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2681090071347088128030419 4021635107020632192045629)
        ·
          refine ⟨1508113165132737072017111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4021635107020632192045629 1508113165132737072017111)
          ·
            refine ⟨2262169747699105608025667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1508113165132737072017111 2262169747699105608025667)
            ·
              refine ⟨3393254621548658412038501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2262169747699105608025667 3393254621548658412038501)
              ·
                refine ⟨636235241540373452257219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3393254621548658412038501 636235241540373452257219)
                ·
                  refine ⟨954352862310560178385829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 636235241540373452257219 954352862310560178385829)
                  ·
                    refine ⟨178941161683230033447343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 954352862310560178385829 178941161683230033447343)
                    ·
                      rfl

theorem cell22_522730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_522730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_522730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_522730 prefixEnd_522730 := by exact prefixLift 522730
  have htrace : WordTrace (prefixWord ++ tailWord_522730) baseStart_522730 baseEnd_522730 := by
    simpa [prefixWord, tailWord_522730, baseEnd_522730] using wordTrace_append hprefix tailTrace_522730
  have hstable : (prefixWord ++ tailWord_522730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522730).length < 2 ^ (prefixWord ++ tailWord_522730).sum := by decide
  have hdescent : baseEnd_522730 < baseStart_522730 := by decide
  rcases family_descends (prefixWord ++ tailWord_522730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522745 : List Nat := [1, 2, 1, 3, 1, 2, 5, 3, 4]
def baseStart_522745 : Nat := 118140960795 + 522745 * 2 ^ 59
def prefixEnd_522745 : Nat := 4983230072969 + 3 ^ 40 * 522745 * 2
def baseEnd_522745 : Nat := 59648765496591664774099

theorem tailTrace_522745 : CollatzResearch.WordTrace tailWord_522745 prefixEnd_522745 59648765496591664774099 := by
  unfold tailWord_522745
  simp only [CollatzResearch.WordTrace]
  refine ⟨19066076491191617583345689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12710717660794411722230459 19066076491191617583345689)
  ·
    refine ⟨14299557368393713187509267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19066076491191617583345689 14299557368393713187509267)
    ·
      refine ⟨21449336052590569781263901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14299557368393713187509267 21449336052590569781263901)
      ·
        refine ⟨8043501019721463667973963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21449336052590569781263901 8043501019721463667973963)
        ·
          refine ⟨12065251529582195501960945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8043501019721463667973963 12065251529582195501960945)
          ·
            refine ⟨9048938647186646626470709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12065251529582195501960945 9048938647186646626470709)
            ·
              refine ⟨848337998173748121231629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9048938647186646626470709 848337998173748121231629)
              ·
                refine ⟨318126749315155545461861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 848337998173748121231629 318126749315155545461861)
                ·
                  refine ⟨59648765496591664774099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 318126749315155545461861 59648765496591664774099)
                  ·
                    rfl

theorem cell22_522745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 3, 4].length) (baseStart_522745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_522745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_522745 prefixEnd_522745 := by exact prefixLift 522745
  have htrace : WordTrace (prefixWord ++ tailWord_522745) baseStart_522745 baseEnd_522745 := by
    simpa [prefixWord, tailWord_522745, baseEnd_522745] using wordTrace_append hprefix tailTrace_522745
  have hstable : (prefixWord ++ tailWord_522745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522745).length < 2 ^ (prefixWord ++ tailWord_522745).sum := by decide
  have hdescent : baseEnd_522745 < baseStart_522745 := by decide
  rcases family_descends (prefixWord ++ tailWord_522745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522760 : List Nat := [2, 1, 3, 2, 1, 1, 1, 6, 2, 3]
def baseStart_522760 : Nat := 118140960795 + 522760 * 2 ^ 59
def prefixEnd_522760 : Nat := 4983230072969 + 3 ^ 40 * 522760 * 2
def baseEnd_522760 : Nat := 178951431296319955197251

theorem tailTrace_522760 : CollatzResearch.WordTrace tailWord_522760 prefixEnd_522760 178951431296319955197251 := by
  unfold tailWord_522760
  simp only [CollatzResearch.WordTrace]
  refine ⟨9533311793068637572570867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12711082390758183430094489 9533311793068637572570867)
  ·
    refine ⟨14299967689602956358856301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9533311793068637572570867 14299967689602956358856301)
    ·
      refine ⟨5362487883601108634571113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14299967689602956358856301 5362487883601108634571113)
      ·
        refine ⟨4021865912700831475928335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5362487883601108634571113 4021865912700831475928335)
        ·
          refine ⟨6032798869051247213892503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4021865912700831475928335 6032798869051247213892503)
          ·
            refine ⟨9049198303576870820838755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6032798869051247213892503 9049198303576870820838755)
            ·
              refine ⟨13573797455365306231258133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9049198303576870820838755 13573797455365306231258133)
              ·
                refine ⟨636271755720248729590225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13573797455365306231258133 636271755720248729590225)
                ·
                  refine ⟨477203816790186547192669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 636271755720248729590225 477203816790186547192669)
                  ·
                    refine ⟨178951431296319955197251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 477203816790186547192669 178951431296319955197251)
                    ·
                      rfl

theorem cell22_522760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 6, 2, 3].length) (baseStart_522760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_522760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_522760 prefixEnd_522760 := by exact prefixLift 522760
  have htrace : WordTrace (prefixWord ++ tailWord_522760) baseStart_522760 baseEnd_522760 := by
    simpa [prefixWord, tailWord_522760, baseEnd_522760] using wordTrace_append hprefix tailTrace_522760
  have hstable : (prefixWord ++ tailWord_522760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522760).length < 2 ^ (prefixWord ++ tailWord_522760).sum := by decide
  have hdescent : baseEnd_522760 < baseStart_522760 := by decide
  rcases family_descends (prefixWord ++ tailWord_522760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522762 : List Nat := [3, 1, 2, 2, 2, 1, 5, 2, 4]
def baseStart_522762 : Nat := 118140960795 + 522762 * 2 ^ 59
def prefixEnd_522762 : Nat := 4983230072969 + 3 ^ 40 * 522762 * 2
def baseEnd_522762 : Nat := 59650705312397538882415

theorem tailTrace_522762 : CollatzResearch.WordTrace tailWord_522762 prefixEnd_522762 59650705312397538882415 := by
  unfold tailWord_522762
  simp only [CollatzResearch.WordTrace]
  refine ⟨4766674133032507371678635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12711131021420019657809693 4766674133032507371678635)
  ·
    refine ⟨7150011199548761057517953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4766674133032507371678635 7150011199548761057517953)
    ·
      refine ⟨5362508399661570793138465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7150011199548761057517953 5362508399661570793138465)
      ·
        refine ⟨4021881299746178094853849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5362508399661570793138465 4021881299746178094853849)
        ·
          refine ⟨3016410974809633571140387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4021881299746178094853849 3016410974809633571140387)
          ·
            refine ⟨4524616462214450356710581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3016410974809633571140387 4524616462214450356710581)
            ·
              refine ⟨424182793332604720941617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4524616462214450356710581 424182793332604720941617)
              ·
                refine ⟨318137094999453540706213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 424182793332604720941617 318137094999453540706213)
                ·
                  refine ⟨59650705312397538882415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 318137094999453540706213 59650705312397538882415)
                  ·
                    rfl

theorem cell22_522762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 5, 2, 4].length) (baseStart_522762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_522762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_522762 prefixEnd_522762 := by exact prefixLift 522762
  have htrace : WordTrace (prefixWord ++ tailWord_522762) baseStart_522762 baseEnd_522762 := by
    simpa [prefixWord, tailWord_522762, baseEnd_522762] using wordTrace_append hprefix tailTrace_522762
  have hstable : (prefixWord ++ tailWord_522762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522762).length < 2 ^ (prefixWord ++ tailWord_522762).sum := by decide
  have hdescent : baseEnd_522762 < baseStart_522762 := by decide
  rcases family_descends (prefixWord ++ tailWord_522762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522773 : List Nat := [1, 3, 2, 1, 3, 1, 4, 7]
def baseStart_522773 : Nat := 118140960795 + 522773 * 2 ^ 59
def prefixEnd_522773 : Nat := 4983230072969 + 3 ^ 40 * 522773 * 2
def baseEnd_522773 : Nat := 19883986829110250513579

theorem tailTrace_522773 : CollatzResearch.WordTrace tailWord_522773 prefixEnd_522773 19883986829110250513579 := by
  unfold tailWord_522773
  simp only [CollatzResearch.WordTrace]
  refine ⟨19067097735090178365364973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12711398490060118910243315 19067097735090178365364973)
  ·
    refine ⟨7150161650658816887011865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19067097735090178365364973 7150161650658816887011865)
    ·
      refine ⟨5362621237994112665258899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7150161650658816887011865 5362621237994112665258899)
      ·
        refine ⟨8043931856991168997888349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5362621237994112665258899 8043931856991168997888349)
        ·
          refine ⟨3016474446371688374208131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8043931856991168997888349 3016474446371688374208131)
          ·
            refine ⟨4524711669557532561312197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3016474446371688374208131 4524711669557532561312197)
            ·
              refine ⟨848383438042037355246037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4524711669557532561312197 848383438042037355246037)
              ·
                refine ⟨19883986829110250513579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 848383438042037355246037 19883986829110250513579)
                ·
                  rfl

theorem cell22_522773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 7].length) (baseStart_522773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_522773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_522773 prefixEnd_522773 := by exact prefixLift 522773
  have htrace : WordTrace (prefixWord ++ tailWord_522773) baseStart_522773 baseEnd_522773 := by
    simpa [prefixWord, tailWord_522773, baseEnd_522773] using wordTrace_append hprefix tailTrace_522773
  have hstable : (prefixWord ++ tailWord_522773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522773).length < 2 ^ (prefixWord ++ tailWord_522773).sum := by decide
  have hdescent : baseEnd_522773 < baseStart_522773 := by decide
  rcases family_descends (prefixWord ++ tailWord_522773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522792 : List Nat := [2, 1, 5, 2, 1, 2, 2, 1, 2, 4]
def baseStart_522792 : Nat := 118140960795 + 522792 * 2 ^ 59
def prefixEnd_522792 : Nat := 4983230072969 + 3 ^ 40 * 522792 * 2
def baseEnd_522792 : Nat := 178962385550282538397153

theorem tailTrace_522792 : CollatzResearch.WordTrace tailWord_522792 prefixEnd_522792 178962385550282538397153 := by
  unfold tailWord_522792
  simp only [CollatzResearch.WordTrace]
  refine ⟨9533895361010672305153315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12711860481347563073537753 9533895361010672305153315)
  ·
    refine ⟨14300843041516008457729973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9533895361010672305153315 14300843041516008457729973)
    ·
      refine ⟨1340704035142125792912185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14300843041516008457729973 1340704035142125792912185)
      ·
        refine ⟨1005528026356594344684139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1340704035142125792912185 1005528026356594344684139)
        ·
          refine ⟨1508292039534891517026209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1005528026356594344684139 1508292039534891517026209)
          ·
            refine ⟨1131219029651168637769657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1508292039534891517026209 1131219029651168637769657)
            ·
              refine ⟨848414272238376478327243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1131219029651168637769657 848414272238376478327243)
              ·
                refine ⟨1272621408357564717490865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 848414272238376478327243 1272621408357564717490865)
                ·
                  refine ⟨954466056268173538118149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1272621408357564717490865 954466056268173538118149)
                  ·
                    refine ⟨178962385550282538397153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 954466056268173538118149 178962385550282538397153)
                    ·
                      rfl

theorem cell22_522792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_522792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_522792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_522792 prefixEnd_522792 := by exact prefixLift 522792
  have htrace : WordTrace (prefixWord ++ tailWord_522792) baseStart_522792 baseEnd_522792 := by
    simpa [prefixWord, tailWord_522792, baseEnd_522792] using wordTrace_append hprefix tailTrace_522792
  have hstable : (prefixWord ++ tailWord_522792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522792).length < 2 ^ (prefixWord ++ tailWord_522792).sum := by decide
  have hdescent : baseEnd_522792 < baseStart_522792 := by decide
  rcases family_descends (prefixWord ++ tailWord_522792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522833 : List Nat := [1, 2, 2, 1, 3, 3, 1, 1, 1, 7]
def baseStart_522833 : Nat := 118140960795 + 522833 * 2 ^ 59
def prefixEnd_522833 : Nat := 4983230072969 + 3 ^ 40 * 522833 * 2
def baseEnd_522833 : Nat := 178976420688172098122027

theorem tailTrace_522833 : CollatzResearch.WordTrace tailWord_522833 prefixEnd_522833 178976420688172098122027 := by
  unfold tailWord_522833
  simp only [CollatzResearch.WordTrace]
  refine ⟨19069286114872808612549153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12712857409915205741699435 19069286114872808612549153)
  ·
    refine ⟨14301964586154606459411865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19069286114872808612549153 14301964586154606459411865)
    ·
      refine ⟨10726473439615954844558899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14301964586154606459411865 10726473439615954844558899)
      ·
        refine ⟨16089710159423932266838349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10726473439615954844558899 16089710159423932266838349)
        ·
          refine ⟨6033641309783974600064381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16089710159423932266838349 6033641309783974600064381)
          ·
            refine ⟨2262615491168990475024143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6033641309783974600064381 2262615491168990475024143)
            ·
              refine ⟨3393923236753485712536215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2262615491168990475024143 3393923236753485712536215)
              ·
                refine ⟨5090884855130228568804323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3393923236753485712536215 5090884855130228568804323)
                ·
                  refine ⟨7636327282695342853206485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5090884855130228568804323 7636327282695342853206485)
                  ·
                    refine ⟨178976420688172098122027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7636327282695342853206485 178976420688172098122027)
                    ·
                      rfl

theorem cell22_522833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 7].length) (baseStart_522833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_522833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_522833 prefixEnd_522833 := by exact prefixLift 522833
  have htrace : WordTrace (prefixWord ++ tailWord_522833) baseStart_522833 baseEnd_522833 := by
    simpa [prefixWord, tailWord_522833, baseEnd_522833] using wordTrace_append hprefix tailTrace_522833
  have hstable : (prefixWord ++ tailWord_522833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522833).length < 2 ^ (prefixWord ++ tailWord_522833).sum := by decide
  have hdescent : baseEnd_522833 < baseStart_522833 := by decide
  rcases family_descends (prefixWord ++ tailWord_522833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522856 : List Nat := [2, 1, 4, 3, 2, 1, 2, 3, 1, 3]
def baseStart_522856 : Nat := 118140960795 + 522856 * 2 ^ 59
def prefixEnd_522856 : Nat := 4983230072969 + 3 ^ 40 * 522856 * 2
def baseEnd_522856 : Nat := 178984294058207704796957

theorem tailTrace_522856 : CollatzResearch.WordTrace tailWord_522856 prefixEnd_522856 178984294058207704796957 := by
  unfold tailWord_522856
  simp only [CollatzResearch.WordTrace]
  refine ⟨9535062496894741770318211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12713416662526322360424281 9535062496894741770318211)
  ·
    refine ⟨14302593745342112655477317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9535062496894741770318211 14302593745342112655477317)
    ·
      refine ⟨2681736327251646122901997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14302593745342112655477317 2681736327251646122901997)
      ·
        refine ⟨1005651122719367296088249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2681736327251646122901997 1005651122719367296088249)
        ·
          refine ⟨754238342039525472066187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1005651122719367296088249 754238342039525472066187)
          ·
            refine ⟨1131357513059288208099281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 754238342039525472066187 1131357513059288208099281)
            ·
              refine ⟨848518134794466156074461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1131357513059288208099281 848518134794466156074461)
              ·
                refine ⟨318194300547924808527923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 848518134794466156074461 318194300547924808527923)
                ·
                  refine ⟨477291450821887212791885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 318194300547924808527923 477291450821887212791885)
                  ·
                    refine ⟨178984294058207704796957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 477291450821887212791885 178984294058207704796957)
                    ·
                      rfl

theorem cell22_522856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 3, 1, 3].length) (baseStart_522856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_522856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_522856 prefixEnd_522856 := by exact prefixLift 522856
  have htrace : WordTrace (prefixWord ++ tailWord_522856) baseStart_522856 baseEnd_522856 := by
    simpa [prefixWord, tailWord_522856, baseEnd_522856] using wordTrace_append hprefix tailTrace_522856
  have hstable : (prefixWord ++ tailWord_522856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522856).length < 2 ^ (prefixWord ++ tailWord_522856).sum := by decide
  have hdescent : baseEnd_522856 < baseStart_522856 := by decide
  rcases family_descends (prefixWord ++ tailWord_522856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522869 : List Nat := [1, 3, 4, 2, 2, 2, 1, 2, 5]
def baseStart_522869 : Nat := 118140960795 + 522869 * 2 ^ 59
def prefixEnd_522869 : Nat := 4983230072969 + 3 ^ 40 * 522869 * 2
def baseEnd_522869 : Nat := 59662914741293334740639

theorem tailTrace_522869 : CollatzResearch.WordTrace tailWord_522869 prefixEnd_522869 59662914741293334740639 := by
  unfold tailWord_522869
  simp only [CollatzResearch.WordTrace]
  refine ⟨19070599142742386760859661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12713732761828257840573107 19070599142742386760859661)
  ·
    refine ⟨7151474678528395035322373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19070599142742386760859661 7151474678528395035322373)
    ·
      refine ⟨1340901502224074069122945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7151474678528395035322373 1340901502224074069122945)
      ·
        refine ⟨1005676126668055551842209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1340901502224074069122945 1005676126668055551842209)
        ·
          refine ⟨754257095001041663881657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1005676126668055551842209 754257095001041663881657)
          ·
            refine ⟨565692821250781247911243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 754257095001041663881657 565692821250781247911243)
            ·
              refine ⟨848539231876171871866865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 565692821250781247911243 848539231876171871866865)
              ·
                refine ⟨636404423907128903900149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 848539231876171871866865 636404423907128903900149)
                ·
                  refine ⟨59662914741293334740639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 636404423907128903900149 59662914741293334740639)
                  ·
                    rfl

theorem cell22_522869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 2, 5].length) (baseStart_522869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_522869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_522869 prefixEnd_522869 := by exact prefixLift 522869
  have htrace : WordTrace (prefixWord ++ tailWord_522869) baseStart_522869 baseEnd_522869 := by
    simpa [prefixWord, tailWord_522869, baseEnd_522869] using wordTrace_append hprefix tailTrace_522869
  have hstable : (prefixWord ++ tailWord_522869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522869).length < 2 ^ (prefixWord ++ tailWord_522869).sum := by decide
  have hdescent : baseEnd_522869 < baseStart_522869 := by decide
  rcases family_descends (prefixWord ++ tailWord_522869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522880 : List Nat := [2, 1, 1, 2, 1, 6, 2, 1, 6]
def baseStart_522880 : Nat := 118140960795 + 522880 * 2 ^ 59
def prefixEnd_522880 : Nat := 4983230072969 + 3 ^ 40 * 522880 * 2
def baseEnd_522880 : Nat := 59664169916226547398961

theorem tailTrace_522880 : CollatzResearch.WordTrace tailWord_522880 prefixEnd_522880 59664169916226547398961 := by
  unfold tailWord_522880
  simp only [CollatzResearch.WordTrace]
  refine ⟨9535500172851267819755047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12714000230468357093006729 9535500172851267819755047)
  ·
    refine ⟨14303250259276901729632571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9535500172851267819755047 14303250259276901729632571)
    ·
      refine ⟨21454875388915352594448857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14303250259276901729632571 21454875388915352594448857)
      ·
        refine ⟨16091156541686514445836643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21454875388915352594448857 16091156541686514445836643)
        ·
          refine ⟨24136734812529771668754965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16091156541686514445836643 24136734812529771668754965)
          ·
            refine ⟨1131409444337333046972889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 24136734812529771668754965 1131409444337333046972889)
            ·
              refine ⟨848557083252999785229667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1131409444337333046972889 848557083252999785229667)
              ·
                refine ⟨1272835624879499677844501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 848557083252999785229667 1272835624879499677844501)
                ·
                  refine ⟨59664169916226547398961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1272835624879499677844501 59664169916226547398961)
                  ·
                    rfl

theorem cell22_522880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 1, 6].length) (baseStart_522880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_522880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_522880 prefixEnd_522880 := by exact prefixLift 522880
  have htrace : WordTrace (prefixWord ++ tailWord_522880) baseStart_522880 baseEnd_522880 := by
    simpa [prefixWord, tailWord_522880, baseEnd_522880] using wordTrace_append hprefix tailTrace_522880
  have hstable : (prefixWord ++ tailWord_522880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522880).length < 2 ^ (prefixWord ++ tailWord_522880).sum := by decide
  have hdescent : baseEnd_522880 < baseStart_522880 := by decide
  rcases family_descends (prefixWord ++ tailWord_522880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522925 : List Nat := [1, 5, 2, 1, 1, 2, 10]
def baseStart_522925 : Nat := 118140960795 + 522925 * 2 ^ 59
def prefixEnd_522925 : Nat := 4983230072969 + 3 ^ 40 * 522925 * 2
def baseEnd_522925 : Nat := 6629922746974612030435

theorem tailTrace_522925 : CollatzResearch.WordTrace tailWord_522925 prefixEnd_522925 6629922746974612030435 := by
  unfold tailWord_522925
  simp only [CollatzResearch.WordTrace]
  refine ⟨19072641630539508324898229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12715094420359672216598819 19072641630539508324898229)
  ·
    refine ⟨1788060152863078905459209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19072641630539508324898229 1788060152863078905459209)
    ·
      refine ⟨1341045114647309179094407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1788060152863078905459209 1341045114647309179094407)
      ·
        refine ⟨2011567671970963768641611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1341045114647309179094407 2011567671970963768641611)
        ·
          refine ⟨3017351507956445652962417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2011567671970963768641611 3017351507956445652962417)
          ·
            refine ⟨2263013630967334239721813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3017351507956445652962417 2263013630967334239721813)
            ·
              refine ⟨6629922746974612030435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2263013630967334239721813 6629922746974612030435)
              ·
                rfl

theorem cell22_522925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 10].length) (baseStart_522925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_522925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_522925 prefixEnd_522925 := by exact prefixLift 522925
  have htrace : WordTrace (prefixWord ++ tailWord_522925) baseStart_522925 baseEnd_522925 := by
    simpa [prefixWord, tailWord_522925, baseEnd_522925] using wordTrace_append hprefix tailTrace_522925
  have hstable : (prefixWord ++ tailWord_522925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522925).length < 2 ^ (prefixWord ++ tailWord_522925).sum := by decide
  have hdescent : baseEnd_522925 < baseStart_522925 := by decide
  rcases family_descends (prefixWord ++ tailWord_522925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522950 : List Nat := [6, 1, 2, 1, 3, 1, 1, 2, 1, 4]
def baseStart_522950 : Nat := 118140960795 + 522950 * 2 ^ 59
def prefixEnd_522950 : Nat := 4983230072969 + 3 ^ 40 * 522950 * 2
def baseEnd_522950 : Nat := 179016472179222792946669

theorem tailTrace_522950 : CollatzResearch.WordTrace tailWord_522950 prefixEnd_522950 179016472179222792946669 := by
  unfold tailWord_522950
  simp only [CollatzResearch.WordTrace]
  refine ⟨596048545482779299829947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 12715702303632625063038869 596048545482779299829947)
  ·
    refine ⟨894072818224168949744921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 596048545482779299829947 894072818224168949744921)
    ·
      refine ⟨670554613668126712308691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 894072818224168949744921 670554613668126712308691)
      ·
        refine ⟨1005831920502190068463037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 670554613668126712308691 1005831920502190068463037)
        ·
          refine ⟨377186970188321275673639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1005831920502190068463037 377186970188321275673639)
          ·
            refine ⟨565780455282481913510459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 377186970188321275673639 565780455282481913510459)
            ·
              refine ⟨848670682923722870265689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 565780455282481913510459 848670682923722870265689)
              ·
                refine ⟨636503012192792152699267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 848670682923722870265689 636503012192792152699267)
                ·
                  refine ⟨954754518289188229048901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 636503012192792152699267 954754518289188229048901)
                  ·
                    refine ⟨179016472179222792946669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 954754518289188229048901 179016472179222792946669)
                    ·
                      rfl

theorem cell22_522950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_522950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_522950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_522950 prefixEnd_522950 := by exact prefixLift 522950
  have htrace : WordTrace (prefixWord ++ tailWord_522950) baseStart_522950 baseEnd_522950 := by
    simpa [prefixWord, tailWord_522950, baseEnd_522950] using wordTrace_append hprefix tailTrace_522950
  have hstable : (prefixWord ++ tailWord_522950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522950).length < 2 ^ (prefixWord ++ tailWord_522950).sum := by decide
  have hdescent : baseEnd_522950 < baseStart_522950 := by decide
  rcases family_descends (prefixWord ++ tailWord_522950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522991 : List Nat := [1, 1, 2, 1, 5, 2, 4, 2, 1, 3]
def baseStart_522991 : Nat := 118140960795 + 522991 * 2 ^ 59
def prefixEnd_522991 : Nat := 4983230072969 + 3 ^ 40 * 522991 * 2
def baseEnd_522991 : Nat := 179030507317112352671543

theorem tailTrace_522991 : CollatzResearch.WordTrace tailWord_522991 prefixEnd_522991 179030507317112352671543 := by
  unfold tailWord_522991
  simp only [CollatzResearch.WordTrace]
  refine ⟨19075048848300401596800827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12716699232200267731200551 19075048848300401596800827)
  ·
    refine ⟨28612573272450602395201241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19075048848300401596800827 28612573272450602395201241)
    ·
      refine ⟨21459429954337951796400931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28612573272450602395201241 21459429954337951796400931)
      ·
        refine ⟨32189144931506927694601397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21459429954337951796400931 32189144931506927694601397)
        ·
          refine ⟨3017732337328774471368881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32189144931506927694601397 3017732337328774471368881)
          ·
            refine ⟨2263299252996580853526661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3017732337328774471368881 2263299252996580853526661)
            ·
              refine ⟨424368609936858910036249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2263299252996580853526661 424368609936858910036249)
              ·
                refine ⟨318276457452644182527187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 424368609936858910036249 318276457452644182527187)
                ·
                  refine ⟨477414686178966273790781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 318276457452644182527187 477414686178966273790781)
                  ·
                    refine ⟨179030507317112352671543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 477414686178966273790781 179030507317112352671543)
                    ·
                      rfl

theorem cell22_522991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 4, 2, 1, 3].length) (baseStart_522991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_522991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_522991 prefixEnd_522991 := by exact prefixLift 522991
  have htrace : WordTrace (prefixWord ++ tailWord_522991) baseStart_522991 baseEnd_522991 := by
    simpa [prefixWord, tailWord_522991, baseEnd_522991] using wordTrace_append hprefix tailTrace_522991
  have hstable : (prefixWord ++ tailWord_522991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522991).length < 2 ^ (prefixWord ++ tailWord_522991).sum := by decide
  have hdescent : baseEnd_522991 < baseStart_522991 := by decide
  rcases family_descends (prefixWord ++ tailWord_522991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523000 : List Nat := [2, 1, 2, 1, 1, 2, 3, 1, 5, 4]
def baseStart_523000 : Nat := 118140960795 + 523000 * 2 ^ 59
def prefixEnd_523000 : Nat := 4983230072969 + 3 ^ 40 * 523000 * 2
def baseEnd_523000 : Nat := 179033588201039329196515

theorem tailTrace_523000 : CollatzResearch.WordTrace tailWord_523000 prefixEnd_523000 179033588201039329196515 := by
  unfold tailWord_523000
  simp only [CollatzResearch.WordTrace]
  refine ⟨9537688552633898066939227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12716918070178530755918969 9537688552633898066939227)
  ·
    refine ⟨14306532828950847100408841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9537688552633898066939227 14306532828950847100408841)
    ·
      refine ⟨10729899621713135325306631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14306532828950847100408841 10729899621713135325306631)
      ·
        refine ⟨16094849432569702987959947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10729899621713135325306631 16094849432569702987959947)
        ·
          refine ⟨24142274148854554481939921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16094849432569702987959947 24142274148854554481939921)
          ·
            refine ⟨18106705611640915861454941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24142274148854554481939921 18106705611640915861454941)
            ·
              refine ⟨6790014604365343448045603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18106705611640915861454941 6790014604365343448045603)
              ·
                refine ⟨10185021906548015172068405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6790014604365343448045603 10185021906548015172068405)
                ·
                  refine ⟨954845803738876422381413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10185021906548015172068405 954845803738876422381413)
                  ·
                    refine ⟨179033588201039329196515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 954845803738876422381413 179033588201039329196515)
                    ·
                      rfl

theorem cell22_523000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 5, 4].length) (baseStart_523000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_523000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_523000 prefixEnd_523000 := by exact prefixLift 523000
  have htrace : WordTrace (prefixWord ++ tailWord_523000) baseStart_523000 baseEnd_523000 := by
    simpa [prefixWord, tailWord_523000, baseEnd_523000] using wordTrace_append hprefix tailTrace_523000
  have hstable : (prefixWord ++ tailWord_523000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523000).length < 2 ^ (prefixWord ++ tailWord_523000).sum := by decide
  have hdescent : baseEnd_523000 < baseStart_523000 := by decide
  rcases family_descends (prefixWord ++ tailWord_523000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523075 : List Nat := [1, 1, 1, 3, 1, 4, 1, 1, 2, 7]
def baseStart_523075 : Nat := 118140960795 + 523075 * 2 ^ 59
def prefixEnd_523075 : Nat := 4983230072969 + 3 ^ 40 * 523075 * 2
def baseEnd_523075 : Nat := 179059262233764133571285

theorem tailTrace_523075 : CollatzResearch.WordTrace tailWord_523075 prefixEnd_523075 179059262233764133571285 := by
  unfold tailWord_523075
  simp only [CollatzResearch.WordTrace]
  refine ⟨19078112579996083942858679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12718741719997389295239119 19078112579996083942858679)
  ·
    refine ⟨28617168869994125914288019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19078112579996083942858679 28617168869994125914288019)
    ·
      refine ⟨42925753304991188871432029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28617168869994125914288019 42925753304991188871432029)
      ·
        refine ⟨16097157489371695826787011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42925753304991188871432029 16097157489371695826787011)
        ·
          refine ⟨24145736234057543740180517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16097157489371695826787011 24145736234057543740180517)
          ·
            refine ⟨4527325543885789451283847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24145736234057543740180517 4527325543885789451283847)
            ·
              refine ⟨6790988315828684176925771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4527325543885789451283847 6790988315828684176925771)
              ·
                refine ⟨10186482473743026265388657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6790988315828684176925771 10186482473743026265388657)
                ·
                  refine ⟨7639861855307269699041493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10186482473743026265388657 7639861855307269699041493)
                  ·
                    refine ⟨179059262233764133571285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7639861855307269699041493 179059262233764133571285)
                    ·
                      rfl

theorem cell22_523075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 7].length) (baseStart_523075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_523075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_523075 prefixEnd_523075 := by exact prefixLift 523075
  have htrace : WordTrace (prefixWord ++ tailWord_523075) baseStart_523075 baseEnd_523075 := by
    simpa [prefixWord, tailWord_523075, baseEnd_523075] using wordTrace_append hprefix tailTrace_523075
  have hstable : (prefixWord ++ tailWord_523075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523075).length < 2 ^ (prefixWord ++ tailWord_523075).sum := by decide
  have hdescent : baseEnd_523075 < baseStart_523075 := by decide
  rcases family_descends (prefixWord ++ tailWord_523075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523109 : List Nat := [1, 3, 1, 3, 1, 1, 5, 1, 3, 3]
def baseStart_523109 : Nat := 118140960795 + 523109 * 2 ^ 59
def prefixEnd_523109 : Nat := 4983230072969 + 3 ^ 40 * 523109 * 2
def baseEnd_523109 : Nat := 179070901128599378221181

theorem tailTrace_523109 : CollatzResearch.WordTrace tailWord_523109 prefixEnd_523109 179070901128599378221181 := by
  unfold tailWord_523109
  simp only [CollatzResearch.WordTrace]
  refine ⟨19079352661872907749596381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12719568441248605166397587 19079352661872907749596381)
  ·
    refine ⟨7154757248202340406098643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19079352661872907749596381 7154757248202340406098643)
    ·
      refine ⟨10732135872303510609147965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7154757248202340406098643 10732135872303510609147965)
      ·
        refine ⟨4024550952113816478430487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10732135872303510609147965 4024550952113816478430487)
        ·
          refine ⟨6036826428170724717645731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4024550952113816478430487 6036826428170724717645731)
          ·
            refine ⟨9055239642256087076468597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6036826428170724717645731 9055239642256087076468597)
            ·
              refine ⟨848928716461508163418931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9055239642256087076468597 848928716461508163418931)
              ·
                refine ⟨1273393074692262245128397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 848928716461508163418931 1273393074692262245128397)
                ·
                  refine ⟨477522403009598341923149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1273393074692262245128397 477522403009598341923149)
                  ·
                    refine ⟨179070901128599378221181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 477522403009598341923149 179070901128599378221181)
                    ·
                      rfl

theorem cell22_523109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 1, 3, 3].length) (baseStart_523109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_523109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_523109 prefixEnd_523109 := by exact prefixLift 523109
  have htrace : WordTrace (prefixWord ++ tailWord_523109) baseStart_523109 baseEnd_523109 := by
    simpa [prefixWord, tailWord_523109, baseEnd_523109] using wordTrace_append hprefix tailTrace_523109
  have hstable : (prefixWord ++ tailWord_523109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523109).length < 2 ^ (prefixWord ++ tailWord_523109).sum := by decide
  have hdescent : baseEnd_523109 < baseStart_523109 := by decide
  rcases family_descends (prefixWord ++ tailWord_523109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523169 : List Nat := [1, 2, 3, 4, 1, 1, 1, 2, 3, 4]
def baseStart_523169 : Nat := 118140960795 + 523169 * 2 ^ 59
def prefixEnd_523169 : Nat := 4983230072969 + 3 ^ 40 * 523169 * 2
def baseEnd_523169 : Nat := 179091440354779221720997

theorem tailTrace_523169 : CollatzResearch.WordTrace tailWord_523169 prefixEnd_523169 179091440354779221720997 := by
  unfold tailWord_523169
  simp only [CollatzResearch.WordTrace]
  refine ⟨19081541041655537996780561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12721027361103691997853707 19081541041655537996780561)
  ·
    refine ⟨14311155781241653497585421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19081541041655537996780561 14311155781241653497585421)
    ·
      refine ⟨5366683417965620061594533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14311155781241653497585421 5366683417965620061594533)
      ·
        refine ⟨1006253140868553761548975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5366683417965620061594533 1006253140868553761548975)
        ·
          refine ⟨1509379711302830642323463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1006253140868553761548975 1509379711302830642323463)
          ·
            refine ⟨2264069566954245963485195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1509379711302830642323463 2264069566954245963485195)
            ·
              refine ⟨3396104350431368945227793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2264069566954245963485195 3396104350431368945227793)
              ·
                refine ⟨2547078262823526708920845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3396104350431368945227793 2547078262823526708920845)
                ·
                  refine ⟨955154348558822515845317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2547078262823526708920845 955154348558822515845317)
                  ·
                    refine ⟨179091440354779221720997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 955154348558822515845317 179091440354779221720997)
                    ·
                      rfl

theorem cell22_523169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 2, 3, 4].length) (baseStart_523169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_523169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_523169 prefixEnd_523169 := by exact prefixLift 523169
  have htrace : WordTrace (prefixWord ++ tailWord_523169) baseStart_523169 baseEnd_523169 := by
    simpa [prefixWord, tailWord_523169, baseEnd_523169] using wordTrace_append hprefix tailTrace_523169
  have hstable : (prefixWord ++ tailWord_523169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523169).length < 2 ^ (prefixWord ++ tailWord_523169).sum := by decide
  have hdescent : baseEnd_523169 < baseStart_523169 := by decide
  rcases family_descends (prefixWord ++ tailWord_523169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523212 : List Nat := [2, 2, 1, 4, 1, 1, 11]
def baseStart_523212 : Nat := 118140960795 + 523212 * 2 ^ 59
def prefixEnd_523212 : Nat := 4983230072969 + 3 ^ 40 * 523212 * 2
def baseEnd_523212 : Nat := 6633561486427460847995

theorem tailTrace_523212 : CollatzResearch.WordTrace tailWord_523212 prefixEnd_523212 6633561486427460847995 := by
  unfold tailWord_523212
  simp only [CollatzResearch.WordTrace]
  refine ⟨9541554690249878170297945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12722072920333170893730593 9541554690249878170297945)
  ·
    refine ⟨7156166017687408627723459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9541554690249878170297945 7156166017687408627723459)
    ·
      refine ⟨10734249026531112941585189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7156166017687408627723459 10734249026531112941585189)
      ·
        refine ⟨2012671692474583676547223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10734249026531112941585189 2012671692474583676547223)
        ·
          refine ⟨3019007538711875514820835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2012671692474583676547223 3019007538711875514820835)
          ·
            refine ⟨4528511308067813272231253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3019007538711875514820835 4528511308067813272231253)
            ·
              refine ⟨6633561486427460847995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 4528511308067813272231253 6633561486427460847995)
              ·
                rfl

theorem cell22_523212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 11].length) (baseStart_523212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_523212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_523212 prefixEnd_523212 := by exact prefixLift 523212
  have htrace : WordTrace (prefixWord ++ tailWord_523212) baseStart_523212 baseEnd_523212 := by
    simpa [prefixWord, tailWord_523212, baseEnd_523212] using wordTrace_append hprefix tailTrace_523212
  have hstable : (prefixWord ++ tailWord_523212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523212).length < 2 ^ (prefixWord ++ tailWord_523212).sum := by decide
  have hdescent : baseEnd_523212 < baseStart_523212 := by decide
  rcases family_descends (prefixWord ++ tailWord_523212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523257 : List Nat := [1, 2, 1, 3, 1, 3, 1, 1, 9]
def baseStart_523257 : Nat := 118140960795 + 523257 * 2 ^ 59
def prefixEnd_523257 : Nat := 4983230072969 + 3 ^ 40 * 523257 * 2
def baseEnd_523257 : Nat := 59707188184392108506909

theorem tailTrace_523257 : CollatzResearch.WordTrace tailWord_523257 prefixEnd_523257 59707188184392108506909 := by
  unfold tailWord_523257
  simp only [CollatzResearch.WordTrace]
  refine ⟨19084750665336729025984025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12723167110224486017322683 19084750665336729025984025)
  ·
    refine ⟨14313562999002546769488019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19084750665336729025984025 14313562999002546769488019)
    ·
      refine ⟨21470344498503820154232029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14313562999002546769488019 21470344498503820154232029)
      ·
        refine ⟨8051379186938932557837011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21470344498503820154232029 8051379186938932557837011)
        ·
          refine ⟨12077068780408398836755517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8051379186938932557837011 12077068780408398836755517)
          ·
            refine ⟨4528900792653149563783319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12077068780408398836755517 4528900792653149563783319)
            ·
              refine ⟨6793351188979724345674979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4528900792653149563783319 6793351188979724345674979)
              ·
                refine ⟨10190026783469586518512469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6793351188979724345674979 10190026783469586518512469)
                ·
                  refine ⟨59707188184392108506909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 10190026783469586518512469 59707188184392108506909)
                  ·
                    rfl

theorem cell22_523257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 9].length) (baseStart_523257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_523257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_523257 prefixEnd_523257 := by exact prefixLift 523257
  have htrace : WordTrace (prefixWord ++ tailWord_523257) baseStart_523257 baseEnd_523257 := by
    simpa [prefixWord, tailWord_523257, baseEnd_523257] using wordTrace_append hprefix tailTrace_523257
  have hstable : (prefixWord ++ tailWord_523257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523257).length < 2 ^ (prefixWord ++ tailWord_523257).sum := by decide
  have hdescent : baseEnd_523257 < baseStart_523257 := by decide
  rcases family_descends (prefixWord ++ tailWord_523257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523274 : List Nat := [3, 1, 2, 2, 3, 1, 2, 1, 7]
def baseStart_523274 : Nat := 118140960795 + 523274 * 2 ^ 59
def prefixEnd_523274 : Nat := 4983230072969 + 3 ^ 40 * 523274 * 2
def baseEnd_523274 : Nat := 59709128000197982615225

theorem tailTrace_523274 : CollatzResearch.WordTrace tailWord_523274 prefixEnd_523274 59709128000197982615225 := by
  unfold tailWord_523274
  simp only [CollatzResearch.WordTrace]
  refine ⟨4771342676568785232338219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12723580470850093952901917 4771342676568785232338219)
  ·
    refine ⟨7157014014853177848507329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4771342676568785232338219 7157014014853177848507329)
    ·
      refine ⟨5367760511139883386380497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7157014014853177848507329 5367760511139883386380497)
      ·
        refine ⟨4025820383354912539785373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5367760511139883386380497 4025820383354912539785373)
        ·
          refine ⟨1509682643758092202419515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4025820383354912539785373 1509682643758092202419515)
          ·
            refine ⟨2264523965637138303629273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1509682643758092202419515 2264523965637138303629273)
            ·
              refine ⟨1698392974227853727721955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2264523965637138303629273 1698392974227853727721955)
              ·
                refine ⟨2547589461341780591582933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1698392974227853727721955 2547589461341780591582933)
                ·
                  refine ⟨59709128000197982615225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2547589461341780591582933 59709128000197982615225)
                  ·
                    rfl

theorem cell22_523274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 1, 7].length) (baseStart_523274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_523274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_523274 prefixEnd_523274 := by exact prefixLift 523274
  have htrace : WordTrace (prefixWord ++ tailWord_523274) baseStart_523274 baseEnd_523274 := by
    simpa [prefixWord, tailWord_523274, baseEnd_523274] using wordTrace_append hprefix tailTrace_523274
  have hstable : (prefixWord ++ tailWord_523274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523274).length < 2 ^ (prefixWord ++ tailWord_523274).sum := by decide
  have hdescent : baseEnd_523274 < baseStart_523274 := by decide
  rcases family_descends (prefixWord ++ tailWord_523274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523278 : List Nat := [4, 1, 1, 2, 2, 4, 1, 1, 3, 3]
def baseStart_523278 : Nat := 118140960795 + 523278 * 2 ^ 59
def prefixEnd_523278 : Nat := 4983230072969 + 3 ^ 40 * 523278 * 2
def baseEnd_523278 : Nat := 179128753282339270745663

theorem tailTrace_523278 : CollatzResearch.WordTrace tailWord_523278 prefixEnd_523278 179128753282339270745663 := by
  unfold tailWord_523278
  simp only [CollatzResearch.WordTrace]
  refine ⟨2385689574782581201562311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12723677732173766408332325 2385689574782581201562311)
  ·
    refine ⟨3578534362173871802343467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2385689574782581201562311 3578534362173871802343467)
    ·
      refine ⟨5367801543260807703515201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3578534362173871802343467 5367801543260807703515201)
      ·
        refine ⟨4025851157445605777636401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5367801543260807703515201 4025851157445605777636401)
        ·
          refine ⟨3019388368084204333227301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4025851157445605777636401 3019388368084204333227301)
          ·
            refine ⟨566135319015788312480119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3019388368084204333227301 566135319015788312480119)
            ·
              refine ⟨849202978523682468720179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 566135319015788312480119 849202978523682468720179)
              ·
                refine ⟨1273804467785523703080269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 849202978523682468720179 1273804467785523703080269)
                ·
                  refine ⟨477676675419571388655101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1273804467785523703080269 477676675419571388655101)
                  ·
                    refine ⟨179128753282339270745663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 477676675419571388655101 179128753282339270745663)
                    ·
                      rfl

theorem cell22_523278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 1, 3, 3].length) (baseStart_523278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_523278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_523278 prefixEnd_523278 := by exact prefixLift 523278
  have htrace : WordTrace (prefixWord ++ tailWord_523278) baseStart_523278 baseEnd_523278 := by
    simpa [prefixWord, tailWord_523278, baseEnd_523278] using wordTrace_append hprefix tailTrace_523278
  have hstable : (prefixWord ++ tailWord_523278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523278).length < 2 ^ (prefixWord ++ tailWord_523278).sum := by decide
  have hdescent : baseEnd_523278 < baseStart_523278 := by decide
  rcases family_descends (prefixWord ++ tailWord_523278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523329 : List Nat := [1, 2, 5, 1, 4, 1, 2, 2, 1, 3]
def baseStart_523329 : Nat := 118140960795 + 523329 * 2 ^ 59
def prefixEnd_523329 : Nat := 4983230072969 + 3 ^ 40 * 523329 * 2
def baseEnd_523329 : Nat := 179146211624592137720507

theorem tailTrace_523329 : CollatzResearch.WordTrace tailWord_523329 prefixEnd_523329 179146211624592137720507 := by
  unfold tailWord_523329
  simp only [CollatzResearch.WordTrace]
  refine ⟨19087376721075885322605041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12724917814050590215070027 19087376721075885322605041)
  ·
    refine ⟨14315532540806913991953781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19087376721075885322605041 14315532540806913991953781)
    ·
      refine ⟨1342081175700648186745667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14315532540806913991953781 1342081175700648186745667)
      ·
        refine ⟨2013121763550972280118501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1342081175700648186745667 2013121763550972280118501)
        ·
          refine ⟨377460330665807302522219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2013121763550972280118501 377460330665807302522219)
          ·
            refine ⟨566190495998710953783329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 377460330665807302522219 566190495998710953783329)
            ·
              refine ⟨424642871999033215337497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 566190495998710953783329 424642871999033215337497)
              ·
                refine ⟨318482153999274911503123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 424642871999033215337497 318482153999274911503123)
                ·
                  refine ⟨477723230998912367254685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 318482153999274911503123 477723230998912367254685)
                  ·
                    refine ⟨179146211624592137720507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 477723230998912367254685 179146211624592137720507)
                    ·
                      rfl

theorem cell22_523329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_523329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_523329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_523329 prefixEnd_523329 := by exact prefixLift 523329
  have htrace : WordTrace (prefixWord ++ tailWord_523329) baseStart_523329 baseEnd_523329 := by
    simpa [prefixWord, tailWord_523329, baseEnd_523329] using wordTrace_append hprefix tailTrace_523329
  have hstable : (prefixWord ++ tailWord_523329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523329).length < 2 ^ (prefixWord ++ tailWord_523329).sum := by decide
  have hdescent : baseEnd_523329 < baseStart_523329 := by decide
  rcases family_descends (prefixWord ++ tailWord_523329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523336 : List Nat := [2, 1, 3, 1, 1, 1, 5, 4, 4]
def baseStart_523336 : Nat := 118140960795 + 523336 * 2 ^ 59
def prefixEnd_523336 : Nat := 4983230072969 + 3 ^ 40 * 523336 * 2
def baseEnd_523336 : Nat := 59716202622548817598495

theorem tailTrace_523336 : CollatzResearch.WordTrace tailWord_523336 prefixEnd_523336 59716202622548817598495 := by
  unfold tailWord_523336
  simp only [CollatzResearch.WordTrace]
  refine ⟨9543816016025262759054931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12725088021367017012073241 9543816016025262759054931)
  ·
    refine ⟨14315724024037894138582397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9543816016025262759054931 14315724024037894138582397)
    ·
      refine ⟨5368396509014210301968399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14315724024037894138582397 5368396509014210301968399)
      ·
        refine ⟨8052594763521315452952599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5368396509014210301968399 8052594763521315452952599)
        ·
          refine ⟨12078892145281973179428899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8052594763521315452952599 12078892145281973179428899)
          ·
            refine ⟨18118338217922959769143349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12078892145281973179428899 18118338217922959769143349)
            ·
              refine ⟨1698594207930277478357189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18118338217922959769143349 1698594207930277478357189)
              ·
                refine ⟨318486413986927027191973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1698594207930277478357189 318486413986927027191973)
                ·
                  refine ⟨59716202622548817598495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 318486413986927027191973 59716202622548817598495)
                  ·
                    rfl

theorem cell22_523336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 4, 4].length) (baseStart_523336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_523336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_523336 prefixEnd_523336 := by exact prefixLift 523336
  have htrace : WordTrace (prefixWord ++ tailWord_523336) baseStart_523336 baseEnd_523336 := by
    simpa [prefixWord, tailWord_523336, baseEnd_523336] using wordTrace_append hprefix tailTrace_523336
  have hstable : (prefixWord ++ tailWord_523336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523336).length < 2 ^ (prefixWord ++ tailWord_523336).sum := by decide
  have hdescent : baseEnd_523336 < baseStart_523336 := by decide
  rcases family_descends (prefixWord ++ tailWord_523336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523349 : List Nat := [1, 3, 2, 2, 1, 2, 2, 2, 1, 6]
def baseStart_523349 : Nat := 118140960795 + 523349 * 2 ^ 59
def prefixEnd_523349 : Nat := 4983230072969 + 3 ^ 40 * 523349 * 2
def baseEnd_523349 : Nat := 179153058033318752220445

theorem tailTrace_523349 : CollatzResearch.WordTrace tailWord_523349 prefixEnd_523349 179153058033318752220445 := by
  unfold tailWord_523349
  simp only [CollatzResearch.WordTrace]
  refine ⟨19088106181003428738333101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12725404120668952492222067 19088106181003428738333101)
  ·
    refine ⟨7158039817876285776874913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19088106181003428738333101 7158039817876285776874913)
    ·
      refine ⟨5368529863407214332656185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7158039817876285776874913 5368529863407214332656185)
      ·
        refine ⟨4026397397555410749492139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5368529863407214332656185 4026397397555410749492139)
        ·
          refine ⟨6039596096333116124238209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4026397397555410749492139 6039596096333116124238209)
          ·
            refine ⟨4529697072249837093178657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6039596096333116124238209 4529697072249837093178657)
            ·
              refine ⟨3397272804187377819883993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4529697072249837093178657 3397272804187377819883993)
              ·
                refine ⟨2547954603140533364912995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3397272804187377819883993 2547954603140533364912995)
                ·
                  refine ⟨3821931904710800047369493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2547954603140533364912995 3821931904710800047369493)
                  ·
                    refine ⟨179153058033318752220445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3821931904710800047369493 179153058033318752220445)
                    ·
                      rfl

theorem cell22_523349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 2, 1, 6].length) (baseStart_523349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_523349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_523349 prefixEnd_523349 := by exact prefixLift 523349
  have htrace : WordTrace (prefixWord ++ tailWord_523349) baseStart_523349 baseEnd_523349 := by
    simpa [prefixWord, tailWord_523349, baseEnd_523349] using wordTrace_append hprefix tailTrace_523349
  have hstable : (prefixWord ++ tailWord_523349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523349).length < 2 ^ (prefixWord ++ tailWord_523349).sum := by decide
  have hdescent : baseEnd_523349 < baseStart_523349 := by decide
  rcases family_descends (prefixWord ++ tailWord_523349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523385 : List Nat := [1, 2, 1, 3, 5, 2, 1, 2, 2, 3]
def baseStart_523385 : Nat := 118140960795 + 523385 * 2 ^ 59
def prefixEnd_523385 : Nat := 4983230072969 + 3 ^ 40 * 523385 * 2
def baseEnd_523385 : Nat := 179165381569026658320335

theorem tailTrace_523385 : CollatzResearch.WordTrace tailWord_523385 prefixEnd_523385 179165381569026658320335 := by
  unfold tailWord_523385
  simp only [CollatzResearch.WordTrace]
  refine ⟨19089419208873006886643609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12726279472582004591095739 19089419208873006886643609)
  ·
    refine ⟨14317064406654755164982707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19089419208873006886643609 14317064406654755164982707)
    ·
      refine ⟨21475596609982132747474061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14317064406654755164982707 21475596609982132747474061)
      ·
        refine ⟨8053348728743299780302773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21475596609982132747474061 8053348728743299780302773)
        ·
          refine ⟨755001443319684354403385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8053348728743299780302773 755001443319684354403385)
          ·
            refine ⟨566251082489763265802539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 755001443319684354403385 566251082489763265802539)
            ·
              refine ⟨849376623734644898703809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 566251082489763265802539 849376623734644898703809)
              ·
                refine ⟨637032467800983674027857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 849376623734644898703809 637032467800983674027857)
                ·
                  refine ⟨477774350850737755520893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 637032467800983674027857 477774350850737755520893)
                  ·
                    refine ⟨179165381569026658320335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 477774350850737755520893 179165381569026658320335)
                    ·
                      rfl

theorem cell22_523385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 2, 2, 3].length) (baseStart_523385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_523385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_523385 prefixEnd_523385 := by exact prefixLift 523385
  have htrace : WordTrace (prefixWord ++ tailWord_523385) baseStart_523385 baseEnd_523385 := by
    simpa [prefixWord, tailWord_523385, baseEnd_523385] using wordTrace_append hprefix tailTrace_523385
  have hstable : (prefixWord ++ tailWord_523385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523385).length < 2 ^ (prefixWord ++ tailWord_523385).sum := by decide
  have hdescent : baseEnd_523385 < baseStart_523385 := by decide
  rcases family_descends (prefixWord ++ tailWord_523385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523499 : List Nat := [1, 1, 1, 1, 2, 16]
def baseStart_523499 : Nat := 118140960795 + 523499 * 2 ^ 59
def prefixEnd_523499 : Nat := 4983230072969 + 3 ^ 40 * 523499 * 2
def baseEnd_523499 : Nat := 2212400075293436555185

theorem tailTrace_523499 : CollatzResearch.WordTrace tailWord_523499 prefixEnd_523499 2212400075293436555185 := by
  unfold tailWord_523499
  simp only [CollatzResearch.WordTrace]
  refine ⟨19093577130460004356293551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12729051420306669570862367 19093577130460004356293551)
  ·
    refine ⟨28640365695690006534440327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19093577130460004356293551 28640365695690006534440327)
    ·
      refine ⟨42960548543535009801660491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28640365695690006534440327 42960548543535009801660491)
      ·
        refine ⟨64440822815302514702490737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42960548543535009801660491 64440822815302514702490737)
        ·
          refine ⟨48330617111476886026868053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64440822815302514702490737 48330617111476886026868053)
          ·
            refine ⟨2212400075293436555185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 16 48330617111476886026868053 2212400075293436555185)
            ·
              rfl

theorem cell22_523499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 16].length) (baseStart_523499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_523499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_523499 prefixEnd_523499 := by exact prefixLift 523499
  have htrace : WordTrace (prefixWord ++ tailWord_523499) baseStart_523499 baseEnd_523499 := by
    simpa [prefixWord, tailWord_523499, baseEnd_523499] using wordTrace_append hprefix tailTrace_523499
  have hstable : (prefixWord ++ tailWord_523499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523499).length < 2 ^ (prefixWord ++ tailWord_523499).sum := by decide
  have hdescent : baseEnd_523499 < baseStart_523499 := by decide
  rcases family_descends (prefixWord ++ tailWord_523499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523550 : List Nat := [4, 3, 2, 1, 2, 1, 9]
def baseStart_523550 : Nat := 118140960795 + 523550 * 2 ^ 59
def prefixEnd_523550 : Nat := 4983230072969 + 3 ^ 40 * 523550 * 2
def baseEnd_523550 : Nat := 6637846831148934368327

theorem tailTrace_523550 : CollatzResearch.WordTrace tailWord_523550 prefixEnd_523550 6637846831148934368327 := by
  unfold tailWord_523550
  simp only [CollatzResearch.WordTrace]
  refine ⟨2386929656659405008300013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12730291502183493377600069 2386929656659405008300013)
  ·
    refine ⟨895098621247276878112505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2386929656659405008300013 895098621247276878112505)
    ·
      refine ⟨671323965935457658584379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 895098621247276878112505 671323965935457658584379)
      ·
        refine ⟨1006985948903186487876569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 671323965935457658584379 1006985948903186487876569)
        ·
          refine ⟨755239461677389865907427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1006985948903186487876569 755239461677389865907427)
          ·
            refine ⟨1132859192516084798861141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 755239461677389865907427 1132859192516084798861141)
            ·
              refine ⟨6637846831148934368327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1132859192516084798861141 6637846831148934368327)
              ·
                rfl

theorem cell22_523550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 9].length) (baseStart_523550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_523550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_523550 prefixEnd_523550 := by exact prefixLift 523550
  have htrace : WordTrace (prefixWord ++ tailWord_523550) baseStart_523550 baseEnd_523550 := by
    simpa [prefixWord, tailWord_523550, baseEnd_523550] using wordTrace_append hprefix tailTrace_523550
  have hstable : (prefixWord ++ tailWord_523550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523550).length < 2 ^ (prefixWord ++ tailWord_523550).sum := by decide
  have hdescent : baseEnd_523550 < baseStart_523550 := by decide
  rcases family_descends (prefixWord ++ tailWord_523550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523554 : List Nat := [3, 3, 1, 1, 5, 1, 1, 2, 2, 3]
def baseStart_523554 : Nat := 118140960795 + 523554 * 2 ^ 59
def prefixEnd_523554 : Nat := 4983230072969 + 3 ^ 40 * 523554 * 2
def baseEnd_523554 : Nat := 179223233722766550844817

theorem tailTrace_523554 : CollatzResearch.WordTrace tailWord_523554 prefixEnd_523554 179223233722766550844817 := by
  unfold tailWord_523554
  simp only [CollatzResearch.WordTrace]
  refine ⟨4773895786315187187386429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12730388763507165833030477 4773895786315187187386429)
  ·
    refine ⟨1790210919868195195269911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4773895786315187187386429 1790210919868195195269911)
    ·
      refine ⟨2685316379802292792904867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1790210919868195195269911 2685316379802292792904867)
      ·
        refine ⟨4027974569703439189357301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2685316379802292792904867 4027974569703439189357301)
        ·
          refine ⟨377622615909697424002247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4027974569703439189357301 377622615909697424002247)
          ·
            refine ⟨566433923864546136003371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 377622615909697424002247 566433923864546136003371)
            ·
              refine ⟨849650885796819204005057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 566433923864546136003371 849650885796819204005057)
              ·
                refine ⟨637238164347614403003793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 849650885796819204005057 637238164347614403003793)
                ·
                  refine ⟨477928623260710802252845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 637238164347614403003793 477928623260710802252845)
                  ·
                    refine ⟨179223233722766550844817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 477928623260710802252845 179223233722766550844817)
                    ·
                      rfl

theorem cell22_523554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 2, 2, 3].length) (baseStart_523554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_523554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_523554 prefixEnd_523554 := by exact prefixLift 523554
  have htrace : WordTrace (prefixWord ++ tailWord_523554) baseStart_523554 baseEnd_523554 := by
    simpa [prefixWord, tailWord_523554, baseEnd_523554] using wordTrace_append hprefix tailTrace_523554
  have hstable : (prefixWord ++ tailWord_523554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523554).length < 2 ^ (prefixWord ++ tailWord_523554).sum := by decide
  have hdescent : baseEnd_523554 < baseStart_523554 := by decide
  rcases family_descends (prefixWord ++ tailWord_523554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523608 : List Nat := [2, 1, 2, 2, 1, 1, 3, 5, 1, 4]
def baseStart_523608 : Nat := 118140960795 + 523608 * 2 ^ 59
def prefixEnd_523608 : Nat := 4983230072969 + 3 ^ 40 * 523608 * 2
def baseEnd_523608 : Nat := 179241719026328409994651

theorem tailTrace_523608 : CollatzResearch.WordTrace tailWord_523608 prefixEnd_523608 179241719026328409994651 := by
  unfold tailWord_523608
  simp only [CollatzResearch.WordTrace]
  refine ⟨9548776343532557986005739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12731701791376743981340985 9548776343532557986005739)
  ·
    refine ⟨14323164515298836979008609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9548776343532557986005739 14323164515298836979008609)
    ·
      refine ⟨10742373386474127734256457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14323164515298836979008609 10742373386474127734256457)
      ·
        refine ⟨8056780039855595800692343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10742373386474127734256457 8056780039855595800692343)
        ·
          refine ⟨12085170059783393701038515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8056780039855595800692343 12085170059783393701038515)
          ·
            refine ⟨18127755089675090551557773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12085170059783393701038515 18127755089675090551557773)
            ·
              refine ⟨6797908158628158956834165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18127755089675090551557773 6797908158628158956834165)
              ·
                refine ⟨637303889871389902203203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6797908158628158956834165 637303889871389902203203)
                ·
                  refine ⟨955955834807084853304805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 637303889871389902203203 955955834807084853304805)
                  ·
                    refine ⟨179241719026328409994651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 955955834807084853304805 179241719026328409994651)
                    ·
                      rfl

theorem cell22_523608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 5, 1, 4].length) (baseStart_523608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_523608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_523608 prefixEnd_523608 := by exact prefixLift 523608
  have htrace : WordTrace (prefixWord ++ tailWord_523608) baseStart_523608 baseEnd_523608 := by
    simpa [prefixWord, tailWord_523608, baseEnd_523608] using wordTrace_append hprefix tailTrace_523608
  have hstable : (prefixWord ++ tailWord_523608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523608).length < 2 ^ (prefixWord ++ tailWord_523608).sum := by decide
  have hdescent : baseEnd_523608 < baseStart_523608 := by decide
  rcases family_descends (prefixWord ++ tailWord_523608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523653 : List Nat := [1, 3, 1, 1, 3, 1, 3, 3, 2, 4]
def baseStart_523653 : Nat := 118140960795 + 523653 * 2 ^ 59
def prefixEnd_523653 : Nat := 4983230072969 + 3 ^ 40 * 523653 * 2
def baseEnd_523653 : Nat := 179257123445963292619513

theorem tailTrace_523653 : CollatzResearch.WordTrace tailWord_523653 prefixEnd_523653 179257123445963292619513 := by
  unfold tailWord_523653
  simp only [CollatzResearch.WordTrace]
  refine ⟨19099193971902088657399613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12732795981268059104933075 19099193971902088657399613)
  ·
    refine ⟨7162197739463283246524855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19099193971902088657399613 7162197739463283246524855)
    ·
      refine ⟨10743296609194924869787283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7162197739463283246524855 10743296609194924869787283)
      ·
        refine ⟨16114944913792387304680925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10743296609194924869787283 16114944913792387304680925)
        ·
          refine ⟨6043104342672145239255347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16114944913792387304680925 6043104342672145239255347)
          ·
            refine ⟨9064656514008217858883021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6043104342672145239255347 9064656514008217858883021)
            ·
              refine ⟨3399246192753081697081133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9064656514008217858883021 3399246192753081697081133)
              ·
                refine ⟨1274717322282405636405425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3399246192753081697081133 1274717322282405636405425)
                ·
                  refine ⟨956037991711804227304069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1274717322282405636405425 956037991711804227304069)
                  ·
                    refine ⟨179257123445963292619513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 956037991711804227304069 179257123445963292619513)
                    ·
                      rfl

theorem cell22_523653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 3, 2, 4].length) (baseStart_523653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_523653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_523653 prefixEnd_523653 := by exact prefixLift 523653
  have htrace : WordTrace (prefixWord ++ tailWord_523653) baseStart_523653 baseEnd_523653 := by
    simpa [prefixWord, tailWord_523653, baseEnd_523653] using wordTrace_append hprefix tailTrace_523653
  have hstable : (prefixWord ++ tailWord_523653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523653).length < 2 ^ (prefixWord ++ tailWord_523653).sum := by decide
  have hdescent : baseEnd_523653 < baseStart_523653 := by decide
  rcases family_descends (prefixWord ++ tailWord_523653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523668 : List Nat := [2, 4, 2, 1, 2, 11]
def baseStart_523668 : Nat := 118140960795 + 523668 * 2 ^ 59
def prefixEnd_523668 : Nat := 4983230072969 + 3 ^ 40 * 523668 * 2
def baseEnd_523668 : Nat := 2213114299413682141907

theorem tailTrace_523668 : CollatzResearch.WordTrace tailWord_523668 prefixEnd_523668 2213114299413682141907 := by
  unfold tailWord_523668
  simp only [CollatzResearch.WordTrace]
  refine ⟨9549870533423873109597829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12733160711231830812797105 9549870533423873109597829)
  ·
    refine ⟨1790600725016976208049593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9549870533423873109597829 1790600725016976208049593)
    ·
      refine ⟨1342950543762732156037195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1790600725016976208049593 1342950543762732156037195)
      ·
        refine ⟨2014425815644098234055793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1342950543762732156037195 2014425815644098234055793)
        ·
          refine ⟨1510819361733073675541845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2014425815644098234055793 1510819361733073675541845)
          ·
            refine ⟨2213114299413682141907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 1510819361733073675541845 2213114299413682141907)
            ·
              rfl

theorem cell22_523668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 11].length) (baseStart_523668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_523668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_523668 prefixEnd_523668 := by exact prefixLift 523668
  have htrace : WordTrace (prefixWord ++ tailWord_523668) baseStart_523668 baseEnd_523668 := by
    simpa [prefixWord, tailWord_523668, baseEnd_523668] using wordTrace_append hprefix tailTrace_523668
  have hstable : (prefixWord ++ tailWord_523668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523668).length < 2 ^ (prefixWord ++ tailWord_523668).sum := by decide
  have hdescent : baseEnd_523668 < baseStart_523668 := by decide
  rcases family_descends (prefixWord ++ tailWord_523668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523734 : List Nat := [5, 2, 1, 1, 1, 3, 2, 1, 3, 3]
def baseStart_523734 : Nat := 118140960795 + 523734 * 2 ^ 59
def prefixEnd_523734 : Nat := 4983230072969 + 3 ^ 40 * 523734 * 2
def baseEnd_523734 : Nat := 179284851401306081344265

theorem tailTrace_523734 : CollatzResearch.WordTrace tailWord_523734 prefixEnd_523734 179284851401306081344265 := by
  unfold tailWord_523734
  simp only [CollatzResearch.WordTrace]
  refine ⟨1193884267788039968193641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12734765523072426327398837 1193884267788039968193641)
  ·
    refine ⟨895413200841029976145231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1193884267788039968193641 895413200841029976145231)
    ·
      refine ⟨1343119801261544964217847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 895413200841029976145231 1343119801261544964217847)
      ·
        refine ⟨2014679701892317446326771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1343119801261544964217847 2014679701892317446326771)
        ·
          refine ⟨3022019552838476169490157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2014679701892317446326771 3022019552838476169490157)
          ·
            refine ⟨1133257332314428563558809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3022019552838476169490157 1133257332314428563558809)
            ·
              refine ⟨849942999235821422669107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1133257332314428563558809 849942999235821422669107)
              ·
                refine ⟨1274914498853732134003661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 849942999235821422669107 1274914498853732134003661)
                ·
                  refine ⟨478092937070149550251373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1274914498853732134003661 478092937070149550251373)
                  ·
                    refine ⟨179284851401306081344265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 478092937070149550251373 179284851401306081344265)
                    ·
                      rfl

theorem cell22_523734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_523734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_523734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_523734 prefixEnd_523734 := by exact prefixLift 523734
  have htrace : WordTrace (prefixWord ++ tailWord_523734) baseStart_523734 baseEnd_523734 := by
    simpa [prefixWord, tailWord_523734, baseEnd_523734] using wordTrace_append hprefix tailTrace_523734
  have hstable : (prefixWord ++ tailWord_523734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523734).length < 2 ^ (prefixWord ++ tailWord_523734).sum := by decide
  have hdescent : baseEnd_523734 < baseStart_523734 := by decide
  rcases family_descends (prefixWord ++ tailWord_523734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523747 : List Nat := [1, 1, 1, 6, 2, 2, 3, 1, 5]
def baseStart_523747 : Nat := 118140960795 + 523747 * 2 ^ 59
def prefixEnd_523747 : Nat := 4983230072969 + 3 ^ 40 * 523747 * 2
def baseEnd_523747 : Nat := 59763100522326126923075

theorem tailTrace_523747 : CollatzResearch.WordTrace tailWord_523747 prefixEnd_523747 59763100522326126923075 := by
  unfold tailWord_523747
  simp only [CollatzResearch.WordTrace]
  refine ⟨19102622433561542711321495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12735081622374361807547663 19102622433561542711321495)
  ·
    refine ⟨28653933650342314066982243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19102622433561542711321495 28653933650342314066982243)
    ·
      refine ⟨42980900475513471100473365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28653933650342314066982243 42980900475513471100473365)
      ·
        refine ⟨2014729709789693957834689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 42980900475513471100473365 2014729709789693957834689)
        ·
          refine ⟨1511047282342270468376017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2014729709789693957834689 1511047282342270468376017)
          ·
            refine ⟨1133285461756702851282013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1511047282342270468376017 1133285461756702851282013)
            ·
              refine ⟨424982048158763569230755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1133285461756702851282013 424982048158763569230755)
              ·
                refine ⟨637473072238145353846133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 424982048158763569230755 637473072238145353846133)
                ·
                  refine ⟨59763100522326126923075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 637473072238145353846133 59763100522326126923075)
                  ·
                    rfl

theorem cell22_523747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 3, 1, 5].length) (baseStart_523747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_523747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_523747 prefixEnd_523747 := by exact prefixLift 523747
  have htrace : WordTrace (prefixWord ++ tailWord_523747) baseStart_523747 baseEnd_523747 := by
    simpa [prefixWord, tailWord_523747, baseEnd_523747] using wordTrace_append hprefix tailTrace_523747
  have hstable : (prefixWord ++ tailWord_523747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523747).length < 2 ^ (prefixWord ++ tailWord_523747).sum := by decide
  have hdescent : baseEnd_523747 < baseStart_523747 := by decide
  rcases family_descends (prefixWord ++ tailWord_523747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523760 : List Nat := [2, 1, 1, 1, 3, 4, 1, 4, 1, 4]
def baseStart_523760 : Nat := 118140960795 + 523760 * 2 ^ 59
def prefixEnd_523760 : Nat := 4983230072969 + 3 ^ 40 * 523760 * 2
def baseEnd_523760 : Nat := 179293751732650680194185

theorem tailTrace_523760 : CollatzResearch.WordTrace tailWord_523760 prefixEnd_523760 179293751732650680194185 := by
  unfold tailWord_523760
  simp only [CollatzResearch.WordTrace]
  refine ⟨9551548291257222965772367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12735397721676297287696489 9551548291257222965772367)
  ·
    refine ⟨14327322436885834448658551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9551548291257222965772367 14327322436885834448658551)
    ·
      refine ⟨21490983655328751672987827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14327322436885834448658551 21490983655328751672987827)
      ·
        refine ⟨32236475482993127509481741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21490983655328751672987827 32236475482993127509481741)
        ·
          refine ⟨12088678306122422816055653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32236475482993127509481741 12088678306122422816055653)
          ·
            refine ⟨2266627182397954278010435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12088678306122422816055653 2266627182397954278010435)
            ·
              refine ⟨3399940773596931417015653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2266627182397954278010435 3399940773596931417015653)
              ·
                refine ⟨637488895049424640690435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3399940773596931417015653 637488895049424640690435)
                ·
                  refine ⟨956233342574136961035653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 637488895049424640690435 956233342574136961035653)
                  ·
                    refine ⟨179293751732650680194185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 956233342574136961035653 179293751732650680194185)
                    ·
                      rfl

theorem cell22_523760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 4, 1, 4].length) (baseStart_523760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_523760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_523760 prefixEnd_523760 := by exact prefixLift 523760
  have htrace : WordTrace (prefixWord ++ tailWord_523760) baseStart_523760 baseEnd_523760 := by
    simpa [prefixWord, tailWord_523760, baseEnd_523760] using wordTrace_append hprefix tailTrace_523760
  have hstable : (prefixWord ++ tailWord_523760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523760).length < 2 ^ (prefixWord ++ tailWord_523760).sum := by decide
  have hdescent : baseEnd_523760 < baseStart_523760 := by decide
  rcases family_descends (prefixWord ++ tailWord_523760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523775 : List Nat := [1, 1, 2, 2, 1, 2, 2, 7, 4]
def baseStart_523775 : Nat := 118140960795 + 523775 * 2 ^ 59
def prefixEnd_523775 : Nat := 4983230072969 + 3 ^ 40 * 523775 * 2
def baseEnd_523775 : Nat := 59766295513065213689713

theorem tailTrace_523775 : CollatzResearch.WordTrace tailWord_523775 prefixEnd_523775 59766295513065213689713 := by
  unfold tailWord_523775
  simp only [CollatzResearch.WordTrace]
  refine ⟨19103643677460103493340779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12735762451640068995560519 19103643677460103493340779)
  ·
    refine ⟨28655465516190155240011169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19103643677460103493340779 28655465516190155240011169)
    ·
      refine ⟨21491599137142616430008377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28655465516190155240011169 21491599137142616430008377)
      ·
        refine ⟨16118699352856962322506283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21491599137142616430008377 16118699352856962322506283)
        ·
          refine ⟨24178049029285443483759425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16118699352856962322506283 24178049029285443483759425)
          ·
            refine ⟨18133536771964082612819569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24178049029285443483759425 18133536771964082612819569)
            ·
              refine ⟨13600152578973061959614677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18133536771964082612819569 13600152578973061959614677)
              ·
                refine ⟨318753576069681139678469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 13600152578973061959614677 318753576069681139678469)
                ·
                  refine ⟨59766295513065213689713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 318753576069681139678469 59766295513065213689713)
                  ·
                    rfl

theorem cell22_523775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 7, 4].length) (baseStart_523775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_523775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_523775 prefixEnd_523775 := by exact prefixLift 523775
  have htrace : WordTrace (prefixWord ++ tailWord_523775) baseStart_523775 baseEnd_523775 := by
    simpa [prefixWord, tailWord_523775, baseEnd_523775] using wordTrace_append hprefix tailTrace_523775
  have hstable : (prefixWord ++ tailWord_523775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523775).length < 2 ^ (prefixWord ++ tailWord_523775).sum := by decide
  have hdescent : baseEnd_523775 < baseStart_523775 := by decide
  rcases family_descends (prefixWord ++ tailWord_523775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523805 : List Nat := [1, 4, 2, 2, 1, 1, 1, 2, 4, 4]
def baseStart_523805 : Nat := 118140960795 + 523805 * 2 ^ 59
def prefixEnd_523805 : Nat := 4983230072969 + 3 ^ 40 * 523805 * 2
def baseEnd_523805 : Nat := 179309156152285562819047

theorem tailTrace_523805 : CollatzResearch.WordTrace tailWord_523805 prefixEnd_523805 179309156152285562819047 := by
  unfold tailWord_523805
  simp only [CollatzResearch.WordTrace]
  refine ⟨19104737867351418616932869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12736491911567612411288579 19104737867351418616932869)
  ·
    refine ⟨3582138350128390990674913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19104737867351418616932869 3582138350128390990674913)
    ·
      refine ⟨2686603762596293243006185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3582138350128390990674913 2686603762596293243006185)
      ·
        refine ⟨2014952821947219932254639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2686603762596293243006185 2014952821947219932254639)
        ·
          refine ⟨3022429232920829898381959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2014952821947219932254639 3022429232920829898381959)
          ·
            refine ⟨4533643849381244847572939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3022429232920829898381959 4533643849381244847572939)
            ·
              refine ⟨6800465774071867271359409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4533643849381244847572939 6800465774071867271359409)
              ·
                refine ⟨5100349330553900453519557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6800465774071867271359409 5100349330553900453519557)
                ·
                  refine ⟨956315499478856335034917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5100349330553900453519557 956315499478856335034917)
                  ·
                    refine ⟨179309156152285562819047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 956315499478856335034917 179309156152285562819047)
                    ·
                      rfl

theorem cell22_523805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_523805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_523805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_523805 prefixEnd_523805 := by exact prefixLift 523805
  have htrace : WordTrace (prefixWord ++ tailWord_523805) baseStart_523805 baseEnd_523805 := by
    simpa [prefixWord, tailWord_523805, baseEnd_523805] using wordTrace_append hprefix tailTrace_523805
  have hstable : (prefixWord ++ tailWord_523805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523805).length < 2 ^ (prefixWord ++ tailWord_523805).sum := by decide
  have hdescent : baseEnd_523805 < baseStart_523805 := by decide
  rcases family_descends (prefixWord ++ tailWord_523805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523822 : List Nat := [4, 1, 3, 1, 2, 1, 1, 3, 2, 4]
def baseStart_523822 : Nat := 118140960795 + 523822 * 2 ^ 59
def prefixEnd_523822 : Nat := 4983230072969 + 3 ^ 40 * 523822 * 2
def baseEnd_523822 : Nat := 179314975599703185143995

theorem tailTrace_523822 : CollatzResearch.WordTrace tailWord_523822 prefixEnd_523822 179314975599703185143995 := by
  unfold tailWord_523822
  simp only [CollatzResearch.WordTrace]
  refine ⟨2388169738536228815037715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12736905272193220346867813 2388169738536228815037715)
  ·
    refine ⟨3582254607804343222556573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2388169738536228815037715 3582254607804343222556573)
    ·
      refine ⟨1343345477926628708458715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3582254607804343222556573 1343345477926628708458715)
      ·
        refine ⟨2015018216889943062688073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1343345477926628708458715 2015018216889943062688073)
        ·
          refine ⟨1511263662667457297016055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2015018216889943062688073 1511263662667457297016055)
          ·
            refine ⟨2266895494001185945524083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1511263662667457297016055 2266895494001185945524083)
            ·
              refine ⟨3400343241001778918286125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2266895494001185945524083 3400343241001778918286125)
              ·
                refine ⟨1275128715375667094357297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3400343241001778918286125 1275128715375667094357297)
                ·
                  refine ⟨956346536531750320767973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1275128715375667094357297 956346536531750320767973)
                  ·
                    refine ⟨179314975599703185143995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 956346536531750320767973 179314975599703185143995)
                    ·
                      rfl

theorem cell22_523822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_523822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_523822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_523822 prefixEnd_523822 := by exact prefixLift 523822
  have htrace : WordTrace (prefixWord ++ tailWord_523822) baseStart_523822 baseEnd_523822 := by
    simpa [prefixWord, tailWord_523822, baseEnd_523822] using wordTrace_append hprefix tailTrace_523822
  have hstable : (prefixWord ++ tailWord_523822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523822).length < 2 ^ (prefixWord ++ tailWord_523822).sum := by decide
  have hdescent : baseEnd_523822 < baseStart_523822 := by decide
  rcases family_descends (prefixWord ++ tailWord_523822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523972 : List Nat := [2, 3, 3, 1, 1, 1, 4, 7]
def baseStart_523972 : Nat := 118140960795 + 523972 * 2 ^ 59
def prefixEnd_523972 : Nat := 4983230072969 + 3 ^ 40 * 523972 * 2
def baseEnd_523972 : Nat := 19929591518350310432615

theorem tailTrace_523972 : CollatzResearch.WordTrace tailWord_523972 prefixEnd_523972 19929591518350310432615 := by
  unfold tailWord_523972
  simp only [CollatzResearch.WordTrace]
  refine ⟨9555414428873203069131085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12740552571830937425508113 9555414428873203069131085)
  ·
    refine ⟨3583280410827451150924157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9555414428873203069131085 3583280410827451150924157)
    ·
      refine ⟨1343730154060294181596559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3583280410827451150924157 1343730154060294181596559)
      ·
        refine ⟨2015595231090441272394839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1343730154060294181596559 2015595231090441272394839)
        ·
          refine ⟨3023392846635661908592259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2015595231090441272394839 3023392846635661908592259)
          ·
            refine ⟨4535089269953492862888389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3023392846635661908592259 4535089269953492862888389)
            ·
              refine ⟨850329238116279911791573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4535089269953492862888389 850329238116279911791573)
              ·
                refine ⟨19929591518350310432615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 850329238116279911791573 19929591518350310432615)
                ·
                  rfl

theorem cell22_523972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 7].length) (baseStart_523972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_523972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_523972 prefixEnd_523972 := by exact prefixLift 523972
  have htrace : WordTrace (prefixWord ++ tailWord_523972) baseStart_523972 baseEnd_523972 := by
    simpa [prefixWord, tailWord_523972, baseEnd_523972] using wordTrace_append hprefix tailTrace_523972
  have hstable : (prefixWord ++ tailWord_523972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523972).length < 2 ^ (prefixWord ++ tailWord_523972).sum := by decide
  have hdescent : baseEnd_523972 < baseStart_523972 := by decide
  rcases family_descends (prefixWord ++ tailWord_523972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524000 : List Nat := [2, 1, 1, 3, 1, 2, 2, 1, 9]
def baseStart_524000 : Nat := 118140960795 + 524000 * 2 ^ 59
def prefixEnd_524000 : Nat := 4983230072969 + 3 ^ 40 * 524000 * 2
def baseEnd_524000 : Nat := 59791969545790018064483

theorem tailTrace_524000 : CollatzResearch.WordTrace tailWord_524000 prefixEnd_524000 59791969545790018064483 := by
  unfold tailWord_524000
  simp only [CollatzResearch.WordTrace]
  refine ⟨9555925050822483460140727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12741233401096644613520969 9555925050822483460140727)
  ·
    refine ⟨14333887576233725190211091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9555925050822483460140727 14333887576233725190211091)
    ·
      refine ⟨21500831364350587785316637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14333887576233725190211091 21500831364350587785316637)
      ·
        refine ⟨8062811761631470419493739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21500831364350587785316637 8062811761631470419493739)
        ·
          refine ⟨12094217642447205629240609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8062811761631470419493739 12094217642447205629240609)
          ·
            refine ⟨9070663231835404221930457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12094217642447205629240609 9070663231835404221930457)
            ·
              refine ⟨6802997423876553166447843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9070663231835404221930457 6802997423876553166447843)
              ·
                refine ⟨10204496135814829749671765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6802997423876553166447843 10204496135814829749671765)
                ·
                  refine ⟨59791969545790018064483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 10204496135814829749671765 59791969545790018064483)
                  ·
                    rfl

theorem cell22_524000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 9].length) (baseStart_524000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_524000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_524000 prefixEnd_524000 := by exact prefixLift 524000
  have htrace : WordTrace (prefixWord ++ tailWord_524000) baseStart_524000 baseEnd_524000 := by
    simpa [prefixWord, tailWord_524000, baseEnd_524000] using wordTrace_append hprefix tailTrace_524000
  have hstable : (prefixWord ++ tailWord_524000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524000).length < 2 ^ (prefixWord ++ tailWord_524000).sum := by decide
  have hdescent : baseEnd_524000 < baseStart_524000 := by decide
  rcases family_descends (prefixWord ++ tailWord_524000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524017 : List Nat := [1, 2, 2, 2, 2, 3, 1, 4, 5]
def baseStart_524017 : Nat := 118140960795 + 524017 * 2 ^ 59
def prefixEnd_524017 : Nat := 4983230072969 + 3 ^ 40 * 524017 * 2
def baseEnd_524017 : Nat := 59793909361595892172799

theorem tailTrace_524017 : CollatzResearch.WordTrace tailWord_524017 prefixEnd_524017 59793909361595892172799 := by
  unfold tailWord_524017
  simp only [CollatzResearch.WordTrace]
  refine ⟨19112470142583378823650305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12741646761722252549100203 19112470142583378823650305)
  ·
    refine ⟨14334352606937534117737729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19112470142583378823650305 14334352606937534117737729)
    ·
      refine ⟨10750764455203150588303297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14334352606937534117737729 10750764455203150588303297)
      ·
        refine ⟨8063073341402362941227473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10750764455203150588303297 8063073341402362941227473)
        ·
          refine ⟨6047305006051772205920605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8063073341402362941227473 6047305006051772205920605)
          ·
            refine ⟨2267739377269414577220227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6047305006051772205920605 2267739377269414577220227)
            ·
              refine ⟨3401609065904121865830341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2267739377269414577220227 3401609065904121865830341)
              ·
                refine ⟨637801699857022849843189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3401609065904121865830341 637801699857022849843189)
                ·
                  refine ⟨59793909361595892172799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 637801699857022849843189 59793909361595892172799)
                  ·
                    rfl

theorem cell22_524017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 4, 5].length) (baseStart_524017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_524017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_524017 prefixEnd_524017 := by exact prefixLift 524017
  have htrace : WordTrace (prefixWord ++ tailWord_524017) baseStart_524017 baseEnd_524017 := by
    simpa [prefixWord, tailWord_524017, baseEnd_524017] using wordTrace_append hprefix tailTrace_524017
  have hstable : (prefixWord ++ tailWord_524017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524017).length < 2 ^ (prefixWord ++ tailWord_524017).sum := by decide
  have hdescent : baseEnd_524017 < baseStart_524017 := by decide
  rcases family_descends (prefixWord ++ tailWord_524017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524034 : List Nat := [3, 4, 1, 1, 1, 1, 1, 5, 5]
def baseStart_524034 : Nat := 118140960795 + 524034 * 2 ^ 59
def prefixEnd_524034 : Nat := 4983230072969 + 3 ^ 40 * 524034 * 2
def baseEnd_524034 : Nat := 59795849177401766281115

theorem tailTrace_524034 : CollatzResearch.WordTrace tailWord_524034 prefixEnd_524034 59795849177401766281115 := by
  unfold tailWord_524034
  simp only [CollatzResearch.WordTrace]
  refine ⟨4778272545880447681754789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12742060122347860484679437 4778272545880447681754789)
  ·
    refine ⟨895926102352583940329023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4778272545880447681754789 895926102352583940329023)
    ·
      refine ⟨1343889153528875910493535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 895926102352583940329023 1343889153528875910493535)
      ·
        refine ⟨2015833730293313865740303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1343889153528875910493535 2015833730293313865740303)
        ·
          refine ⟨3023750595439970798610455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2015833730293313865740303 3023750595439970798610455)
          ·
            refine ⟨4535625893159956197915683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3023750595439970798610455 4535625893159956197915683)
            ·
              refine ⟨6803438839739934296873525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4535625893159956197915683 6803438839739934296873525)
              ·
                refine ⟨637822391225618840331893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6803438839739934296873525 637822391225618840331893)
                ·
                  refine ⟨59795849177401766281115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 637822391225618840331893 59795849177401766281115)
                  ·
                    rfl

theorem cell22_524034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_524034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_524034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_524034 prefixEnd_524034 := by exact prefixLift 524034
  have htrace : WordTrace (prefixWord ++ tailWord_524034) baseStart_524034 baseEnd_524034 := by
    simpa [prefixWord, tailWord_524034, baseEnd_524034] using wordTrace_append hprefix tailTrace_524034
  have hstable : (prefixWord ++ tailWord_524034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524034).length < 2 ^ (prefixWord ++ tailWord_524034).sum := by decide
  have hdescent : baseEnd_524034 < baseStart_524034 := by decide
  rcases family_descends (prefixWord ++ tailWord_524034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524064 : List Nat := [2, 1, 1, 5, 1, 1, 3, 3, 1, 4]
def baseStart_524064 : Nat := 118140960795 + 524064 * 2 ^ 59
def prefixEnd_524064 : Nat := 4983230072969 + 3 ^ 40 * 524064 * 2
def baseEnd_524064 : Nat := 179397817145295220593253

theorem tailTrace_524064 : CollatzResearch.WordTrace tailWord_524064 prefixEnd_524064 179397817145295220593253 := by
  unfold tailWord_524064
  simp only [CollatzResearch.WordTrace]
  refine ⟨9557092186706552925305623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12742789582275403900407497 9557092186706552925305623)
  ·
    refine ⟨14335638280059829387958435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9557092186706552925305623 14335638280059829387958435)
    ·
      refine ⟨21503457420089744081937653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14335638280059829387958435 21503457420089744081937653)
      ·
        refine ⟨2015949133133413507681655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21503457420089744081937653 2015949133133413507681655)
        ·
          refine ⟨3023923699700120261522483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2015949133133413507681655 3023923699700120261522483)
          ·
            refine ⟨4535885549550180392283725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3023923699700120261522483 4535885549550180392283725)
            ·
              refine ⟨1700957081081317647106397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4535885549550180392283725 1700957081081317647106397)
              ·
                refine ⟨637858905405494117664899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1700957081081317647106397 637858905405494117664899)
                ·
                  refine ⟨956788358108241176497349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 637858905405494117664899 956788358108241176497349)
                  ·
                    refine ⟨179397817145295220593253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 956788358108241176497349 179397817145295220593253)
                    ·
                      rfl

theorem cell22_524064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 3, 1, 4].length) (baseStart_524064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_524064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_524064 prefixEnd_524064 := by exact prefixLift 524064
  have htrace : WordTrace (prefixWord ++ tailWord_524064) baseStart_524064 baseEnd_524064 := by
    simpa [prefixWord, tailWord_524064, baseEnd_524064] using wordTrace_append hprefix tailTrace_524064
  have hstable : (prefixWord ++ tailWord_524064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524064).length < 2 ^ (prefixWord ++ tailWord_524064).sum := by decide
  have hdescent : baseEnd_524064 < baseStart_524064 := by decide
  rcases family_descends (prefixWord ++ tailWord_524064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524092 : List Nat := [2, 2, 2, 2, 1, 1, 3, 2, 1, 6]
def baseStart_524092 : Nat := 118140960795 + 524092 * 2 ^ 59
def prefixEnd_524092 : Nat := 4983230072969 + 3 ^ 40 * 524092 * 2
def baseEnd_524092 : Nat := 179407402117512480893167

theorem tailTrace_524092 : CollatzResearch.WordTrace tailWord_524092 prefixEnd_524092 179407402117512480893167 := by
  unfold tailWord_524092
  simp only [CollatzResearch.WordTrace]
  refine ⟨9557602808655833316315265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12743470411541111088420353 9557602808655833316315265)
  ·
    refine ⟨7168202106491874987236449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9557602808655833316315265 7168202106491874987236449)
    ·
      refine ⟨5376151579868906240427337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7168202106491874987236449 5376151579868906240427337)
      ·
        refine ⟨4032113684901679680320503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5376151579868906240427337 4032113684901679680320503)
        ·
          refine ⟨6048170527352519520480755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4032113684901679680320503 6048170527352519520480755)
          ·
            refine ⟨9072255791028779280721133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6048170527352519520480755 9072255791028779280721133)
            ·
              refine ⟨3402095921635792230270425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9072255791028779280721133 3402095921635792230270425)
              ·
                refine ⟨2551571941226844172702819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3402095921635792230270425 2551571941226844172702819)
                ·
                  refine ⟨3827357911840266259054229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2551571941226844172702819 3827357911840266259054229)
                  ·
                    refine ⟨179407402117512480893167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3827357911840266259054229 179407402117512480893167)
                    ·
                      rfl

theorem cell22_524092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 2, 1, 6].length) (baseStart_524092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_524092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_524092 prefixEnd_524092 := by exact prefixLift 524092
  have htrace : WordTrace (prefixWord ++ tailWord_524092) baseStart_524092 baseEnd_524092 := by
    simpa [prefixWord, tailWord_524092, baseEnd_524092] using wordTrace_append hprefix tailTrace_524092
  have hstable : (prefixWord ++ tailWord_524092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524092).length < 2 ^ (prefixWord ++ tailWord_524092).sum := by decide
  have hdescent : baseEnd_524092 < baseStart_524092 := by decide
  rcases family_descends (prefixWord ++ tailWord_524092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524186 : List Nat := [3, 1, 1, 4, 2, 2, 2, 2, 5]
def baseStart_524186 : Nat := 118140960795 + 524186 * 2 ^ 59
def prefixEnd_524186 : Nat := 4983230072969 + 3 ^ 40 * 524186 * 2
def baseEnd_524186 : Nat := 59813193412842523014293

theorem tailTrace_524186 : CollatzResearch.WordTrace tailWord_524186 prefixEnd_524186 59813193412842523014293 := by
  unfold tailWord_524186
  simp only [CollatzResearch.WordTrace]
  refine ⟨4779658519742780171638103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12745756052647413791034941 4779658519742780171638103)
  ·
    refine ⟨7169487779614170257457155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4779658519742780171638103 7169487779614170257457155)
    ·
      refine ⟨10754231669421255386185733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7169487779614170257457155 10754231669421255386185733)
      ·
        refine ⟨2016418438016485384909825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10754231669421255386185733 2016418438016485384909825)
        ·
          refine ⟨1512313828512364038682369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2016418438016485384909825 1512313828512364038682369)
          ·
            refine ⟨1134235371384273029011777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1512313828512364038682369 1134235371384273029011777)
            ·
              refine ⟨850676528538204771758833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1134235371384273029011777 850676528538204771758833)
              ·
                refine ⟨638007396403653578819125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 850676528538204771758833 638007396403653578819125)
                ·
                  refine ⟨59813193412842523014293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 638007396403653578819125 59813193412842523014293)
                  ·
                    rfl

theorem cell22_524186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 2, 5].length) (baseStart_524186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_524186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_524186 prefixEnd_524186 := by exact prefixLift 524186
  have htrace : WordTrace (prefixWord ++ tailWord_524186) baseStart_524186 baseEnd_524186 := by
    simpa [prefixWord, tailWord_524186, baseEnd_524186] using wordTrace_append hprefix tailTrace_524186
  have hstable : (prefixWord ++ tailWord_524186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524186).length < 2 ^ (prefixWord ++ tailWord_524186).sum := by decide
  have hdescent : baseEnd_524186 < baseStart_524186 := by decide
  rcases family_descends (prefixWord ++ tailWord_524186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524197 : List Nat := [1, 3, 1, 2, 1, 1, 1, 2, 10]
def baseStart_524197 : Nat := 118140960795 + 524197 * 2 ^ 59
def prefixEnd_524197 : Nat := 4983230072969 + 3 ^ 40 * 524197 * 2
def baseEnd_524197 : Nat := 59814448587775735672615

theorem tailTrace_524197 : CollatzResearch.WordTrace tailWord_524197 prefixEnd_524197 59814448587775735672615 := by
  unfold tailWord_524197
  simp only [CollatzResearch.WordTrace]
  refine ⟨19119035281931269565202845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12746023521287513043468563 19119035281931269565202845)
  ·
    refine ⟨7169638230724226086951067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19119035281931269565202845 7169638230724226086951067)
    ·
      refine ⟨10754457346086339130426601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7169638230724226086951067 10754457346086339130426601)
      ·
        refine ⟨8065843009564754347819951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10754457346086339130426601 8065843009564754347819951)
        ·
          refine ⟨12098764514347131521729927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8065843009564754347819951 12098764514347131521729927)
          ·
            refine ⟨18148146771520697282594891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12098764514347131521729927 18148146771520697282594891)
            ·
              refine ⟨27222220157281045923892337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18148146771520697282594891 27222220157281045923892337)
              ·
                refine ⟨20416665117960784442919253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27222220157281045923892337 20416665117960784442919253)
                ·
                  refine ⟨59814448587775735672615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 20416665117960784442919253 59814448587775735672615)
                  ·
                    rfl

theorem cell22_524197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 10].length) (baseStart_524197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_524197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_524197 prefixEnd_524197 := by exact prefixLift 524197
  have htrace : WordTrace (prefixWord ++ tailWord_524197) baseStart_524197 baseEnd_524197 := by
    simpa [prefixWord, tailWord_524197, baseEnd_524197] using wordTrace_append hprefix tailTrace_524197
  have hstable : (prefixWord ++ tailWord_524197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524197).length < 2 ^ (prefixWord ++ tailWord_524197).sum := by decide
  have hdescent : baseEnd_524197 < baseStart_524197 := by decide
  rcases family_descends (prefixWord ++ tailWord_524197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524263 : List Nat := [1, 1, 5, 2, 3, 2, 1, 1, 1, 5]
def baseStart_524263 : Nat := 118140960795 + 524263 * 2 ^ 59
def prefixEnd_524263 : Nat := 4983230072969 + 3 ^ 40 * 524263 * 2
def baseEnd_524263 : Nat := 179465938912125034867643

theorem tailTrace_524263 : CollatzResearch.WordTrace tailWord_524263 prefixEnd_524263 179465938912125034867643 := by
  unfold tailWord_524263
  simp only [CollatzResearch.WordTrace]
  refine ⟨19121442499692162837105443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12747628333128108558070295 19121442499692162837105443)
  ·
    refine ⟨28682163749538244255658165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19121442499692162837105443 28682163749538244255658165)
    ·
      refine ⟨2688952851519210398967953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28682163749538244255658165 2688952851519210398967953)
      ·
        refine ⟨2016714638639407799225965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2688952851519210398967953 2016714638639407799225965)
        ·
          refine ⟨756267989489777924709737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2016714638639407799225965 756267989489777924709737)
          ·
            refine ⟨567200992117333443532303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 756267989489777924709737 567200992117333443532303)
            ·
              refine ⟨850801488176000165298455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 567200992117333443532303 850801488176000165298455)
              ·
                refine ⟨1276202232264000247947683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 850801488176000165298455 1276202232264000247947683)
                ·
                  refine ⟨1914303348396000371921525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1276202232264000247947683 1914303348396000371921525)
                  ·
                    refine ⟨179465938912125034867643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1914303348396000371921525 179465938912125034867643)
                    ·
                      rfl

theorem cell22_524263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 1, 1, 5].length) (baseStart_524263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_524263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_524263 prefixEnd_524263 := by exact prefixLift 524263
  have htrace : WordTrace (prefixWord ++ tailWord_524263) baseStart_524263 baseEnd_524263 := by
    simpa [prefixWord, tailWord_524263, baseEnd_524263] using wordTrace_append hprefix tailTrace_524263
  have hstable : (prefixWord ++ tailWord_524263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524263).length < 2 ^ (prefixWord ++ tailWord_524263).sum := by decide
  have hdescent : baseEnd_524263 < baseStart_524263 := by decide
  rcases family_descends (prefixWord ++ tailWord_524263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524319 : List Nat := [1, 1, 2, 4, 1, 2, 2, 1, 1, 7]
def baseStart_524319 : Nat := 118140960795 + 524319 * 2 ^ 59
def prefixEnd_524319 : Nat := 4983230072969 + 3 ^ 40 * 524319 * 2
def baseEnd_524319 : Nat := 179485108856559555467471

theorem tailTrace_524319 : CollatzResearch.WordTrace tailWord_524319 prefixEnd_524319 179485108856559555467471 := by
  unfold tailWord_524319
  simp only [CollatzResearch.WordTrace]
  refine ⟨19123484987489284401144011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12748989991659522934096007 19123484987489284401144011)
  ·
    refine ⟨28685227481233926601716017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19123484987489284401144011 28685227481233926601716017)
    ·
      refine ⟨21513920610925444951287013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28685227481233926601716017 21513920610925444951287013)
      ·
        refine ⟨4033860114548520928366315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21513920610925444951287013 4033860114548520928366315)
        ·
          refine ⟨6050790171822781392549473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4033860114548520928366315 6050790171822781392549473)
          ·
            refine ⟨4538092628867086044412105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6050790171822781392549473 4538092628867086044412105)
            ·
              refine ⟨3403569471650314533309079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4538092628867086044412105 3403569471650314533309079)
              ·
                refine ⟨5105354207475471799963619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3403569471650314533309079 5105354207475471799963619)
                ·
                  refine ⟨7658031311213207699945429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5105354207475471799963619 7658031311213207699945429)
                  ·
                    refine ⟨179485108856559555467471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7658031311213207699945429 179485108856559555467471)
                    ·
                      rfl

theorem cell22_524319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 7].length) (baseStart_524319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_524319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_524319 prefixEnd_524319 := by exact prefixLift 524319
  have htrace : WordTrace (prefixWord ++ tailWord_524319) baseStart_524319 baseEnd_524319 := by
    simpa [prefixWord, tailWord_524319, baseEnd_524319] using wordTrace_append hprefix tailTrace_524319
  have hstable : (prefixWord ++ tailWord_524319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524319).length < 2 ^ (prefixWord ++ tailWord_524319).sum := by decide
  have hdescent : baseEnd_524319 < baseStart_524319 := by decide
  rcases family_descends (prefixWord ++ tailWord_524319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524351 : List Nat := [1, 1, 2, 2, 3, 1, 2, 5, 1, 4]
def baseStart_524351 : Nat := 118140960795 + 524351 * 2 ^ 59
def prefixEnd_524351 : Nat := 4983230072969 + 3 ^ 40 * 524351 * 2
def baseEnd_524351 : Nat := 179496063110522138667373

theorem tailTrace_524351 : CollatzResearch.WordTrace tailWord_524351 prefixEnd_524351 179496063110522138667373 := by
  unfold tailWord_524351
  simp only [CollatzResearch.WordTrace]
  refine ⟨19124652123373353866308907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12749768082248902577539271 19124652123373353866308907)
  ·
    refine ⟨28686978185060030799463361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19124652123373353866308907 28686978185060030799463361)
    ·
      refine ⟨21515233638795023099597521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28686978185060030799463361 21515233638795023099597521)
      ·
        refine ⟨16136425229096267324698141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21515233638795023099597521 16136425229096267324698141)
        ·
          refine ⟨6051159460911100246761803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16136425229096267324698141 6051159460911100246761803)
          ·
            refine ⟨9076739191366650370142705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6051159460911100246761803 9076739191366650370142705)
            ·
              refine ⟨6807554393524987777607029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9076739191366650370142705 6807554393524987777607029)
              ·
                refine ⟨638208224392967604150659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6807554393524987777607029 638208224392967604150659)
                ·
                  refine ⟨957312336589451406225989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 638208224392967604150659 957312336589451406225989)
                  ·
                    refine ⟨179496063110522138667373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 957312336589451406225989 179496063110522138667373)
                    ·
                      rfl

theorem cell22_524351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 5, 1, 4].length) (baseStart_524351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_524351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_524351 prefixEnd_524351 := by exact prefixLift 524351
  have htrace : WordTrace (prefixWord ++ tailWord_524351) baseStart_524351 baseEnd_524351 := by
    simpa [prefixWord, tailWord_524351, baseEnd_524351] using wordTrace_append hprefix tailTrace_524351
  have hstable : (prefixWord ++ tailWord_524351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524351).length < 2 ^ (prefixWord ++ tailWord_524351).sum := by decide
  have hdescent : baseEnd_524351 < baseStart_524351 := by decide
  rcases family_descends (prefixWord ++ tailWord_524351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524396 : List Nat := [2, 2, 1, 1, 3, 4, 1, 1, 1, 6]
def baseStart_524396 : Nat := 118140960795 + 524396 * 2 ^ 59
def prefixEnd_524396 : Nat := 4983230072969 + 3 ^ 40 * 524396 * 2
def baseEnd_524396 : Nat := 179511467530157021292235

theorem tailTrace_524396 : CollatzResearch.WordTrace tailWord_524396 prefixEnd_524396 179511467530157021292235 := by
  unfold tailWord_524396
  simp only [CollatzResearch.WordTrace]
  refine ⟨9563146704105163275848521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12750862272140217701131361 9563146704105163275848521)
  ·
    refine ⟨7172360028078872456886391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9563146704105163275848521 7172360028078872456886391)
    ·
      refine ⟨10758540042118308685329587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7172360028078872456886391 10758540042118308685329587)
      ·
        refine ⟨16137810063177463027994381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10758540042118308685329587 16137810063177463027994381)
        ·
          refine ⟨6051678773691548635497893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16137810063177463027994381 6051678773691548635497893)
          ·
            refine ⟨1134689770067165369155855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6051678773691548635497893 1134689770067165369155855)
            ·
              refine ⟨1702034655100748053733783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1134689770067165369155855 1702034655100748053733783)
              ·
                refine ⟨2553051982651122080600675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1702034655100748053733783 2553051982651122080600675)
                ·
                  refine ⟨3829577973976683120901013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2553051982651122080600675 3829577973976683120901013)
                  ·
                    refine ⟨179511467530157021292235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3829577973976683120901013 179511467530157021292235)
                    ·
                      rfl

theorem cell22_524396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 6].length) (baseStart_524396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_524396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_524396 prefixEnd_524396 := by exact prefixLift 524396
  have htrace : WordTrace (prefixWord ++ tailWord_524396) baseStart_524396 baseEnd_524396 := by
    simpa [prefixWord, tailWord_524396, baseEnd_524396] using wordTrace_append hprefix tailTrace_524396
  have hstable : (prefixWord ++ tailWord_524396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524396).length < 2 ^ (prefixWord ++ tailWord_524396).sum := by decide
  have hdescent : baseEnd_524396 < baseStart_524396 := by decide
  rcases family_descends (prefixWord ++ tailWord_524396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524398 : List Nat := [4, 1, 2, 2, 1, 1, 2, 2, 4, 3]
def baseStart_524398 : Nat := 118140960795 + 524398 * 2 ^ 59
def prefixEnd_524398 : Nat := 4983230072969 + 3 ^ 40 * 524398 * 2
def baseEnd_524398 : Nat := 179512152171029682742229

theorem tailTrace_524398 : CollatzResearch.WordTrace tailWord_524398 prefixEnd_524398 179512152171029682742229 := by
  unfold tailWord_524398
  simp only [CollatzResearch.WordTrace]
  refine ⟨2390795794275385111658731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12750910902802053928846565 2390795794275385111658731)
  ·
    refine ⟨3586193691413077667488097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2390795794275385111658731 3586193691413077667488097)
    ·
      refine ⟨2689645268559808250616073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3586193691413077667488097 2689645268559808250616073)
      ·
        refine ⟨2017233951419856187962055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2689645268559808250616073 2017233951419856187962055)
        ·
          refine ⟨3025850927129784281943083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2017233951419856187962055 3025850927129784281943083)
          ·
            refine ⟨4538776390694676422914625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3025850927129784281943083 4538776390694676422914625)
            ·
              refine ⟨3404082293021007317185969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4538776390694676422914625 3404082293021007317185969)
              ·
                refine ⟨2553061719765755487889477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3404082293021007317185969 2553061719765755487889477)
                ·
                  refine ⟨478699072456079153979277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2553061719765755487889477 478699072456079153979277)
                  ·
                    refine ⟨179512152171029682742229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 478699072456079153979277 179512152171029682742229)
                    ·
                      rfl

theorem cell22_524398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 2, 4, 3].length) (baseStart_524398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_524398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_524398 prefixEnd_524398 := by exact prefixLift 524398
  have htrace : WordTrace (prefixWord ++ tailWord_524398) baseStart_524398 baseEnd_524398 := by
    simpa [prefixWord, tailWord_524398, baseEnd_524398] using wordTrace_append hprefix tailTrace_524398
  have hstable : (prefixWord ++ tailWord_524398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524398).length < 2 ^ (prefixWord ++ tailWord_524398).sum := by decide
  have hdescent : baseEnd_524398 < baseStart_524398 := by decide
  rcases family_descends (prefixWord ++ tailWord_524398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524462 : List Nat := [4, 1, 4, 2, 2, 1, 8]
def baseStart_524462 : Nat := 118140960795 + 524462 * 2 ^ 59
def prefixEnd_524462 : Nat := 4983230072969 + 3 ^ 40 * 524462 * 2
def baseEnd_524462 : Nat := 6649409654776105523779

theorem tailTrace_524462 : CollatzResearch.WordTrace tailWord_524462 prefixEnd_524462 6649409654776105523779 := by
  unfold tailWord_524462
  simp only [CollatzResearch.WordTrace]
  refine ⟨2391087578246402477949955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12752467083980813215733093 2391087578246402477949955)
  ·
    refine ⟨3586631367369603716924933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2391087578246402477949955 3586631367369603716924933)
    ·
      refine ⟨672493381381800696923425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3586631367369603716924933 672493381381800696923425)
      ·
        refine ⟨504370036036350522692569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 672493381381800696923425 504370036036350522692569)
        ·
          refine ⟨378277527027262892019427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 504370036036350522692569 378277527027262892019427)
          ·
            refine ⟨567416290540894338029141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 378277527027262892019427 567416290540894338029141)
            ·
              refine ⟨6649409654776105523779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 567416290540894338029141 6649409654776105523779)
              ·
                rfl

theorem cell22_524462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 8].length) (baseStart_524462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_524462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_524462 prefixEnd_524462 := by exact prefixLift 524462
  have htrace : WordTrace (prefixWord ++ tailWord_524462) baseStart_524462 baseEnd_524462 := by
    simpa [prefixWord, tailWord_524462, baseEnd_524462] using wordTrace_append hprefix tailTrace_524462
  have hstable : (prefixWord ++ tailWord_524462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524462).length < 2 ^ (prefixWord ++ tailWord_524462).sum := by decide
  have hdescent : baseEnd_524462 < baseStart_524462 := by decide
  rcases family_descends (prefixWord ++ tailWord_524462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524584 : List Nat := [2, 1, 5, 1, 3, 2, 1, 2, 2, 3]
def baseStart_524584 : Nat := 118140960795 + 524584 * 2 ^ 59
def prefixEnd_524584 : Nat := 4983230072969 + 3 ^ 40 * 524584 * 2
def baseEnd_524584 : Nat := 179575823772187197591659

theorem tailTrace_524584 : CollatzResearch.WordTrace tailWord_524584 prefixEnd_524584 179575823772187197591659 := by
  unfold tailWord_524584
  simp only [CollatzResearch.WordTrace]
  refine ⟨9566575165764617329770403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12755433554352823106360537 9566575165764617329770403)
  ·
    refine ⟨14349862748646925994655605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9566575165764617329770403 14349862748646925994655605)
    ·
      refine ⟨1345299632685649311998963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14349862748646925994655605 1345299632685649311998963)
      ·
        refine ⟨2017949449028473967998445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1345299632685649311998963 2017949449028473967998445)
        ·
          refine ⟨756731043385677737999417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2017949449028473967998445 756731043385677737999417)
          ·
            refine ⟨567548282539258303499563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 756731043385677737999417 567548282539258303499563)
            ·
              refine ⟨851322423808887455249345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 567548282539258303499563 851322423808887455249345)
              ·
                refine ⟨638491817856665591437009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 851322423808887455249345 638491817856665591437009)
                ·
                  refine ⟨478868863392499193577757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 638491817856665591437009 478868863392499193577757)
                  ·
                    refine ⟨179575823772187197591659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 478868863392499193577757 179575823772187197591659)
                    ·
                      rfl

theorem cell22_524584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_524584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_524584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_524584 prefixEnd_524584 := by exact prefixLift 524584
  have htrace : WordTrace (prefixWord ++ tailWord_524584) baseStart_524584 baseEnd_524584 := by
    simpa [prefixWord, tailWord_524584, baseEnd_524584] using wordTrace_append hprefix tailTrace_524584
  have hstable : (prefixWord ++ tailWord_524584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524584).length < 2 ^ (prefixWord ++ tailWord_524584).sum := by decide
  have hdescent : baseEnd_524584 < baseStart_524584 := by decide
  rcases family_descends (prefixWord ++ tailWord_524584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524595 : List Nat := [1, 1, 1, 2, 5, 1, 4, 1, 3, 3]
def baseStart_524595 : Nat := 118140960795 + 524595 * 2 ^ 59
def prefixEnd_524595 : Nat := 4983230072969 + 3 ^ 40 * 524595 * 2
def baseEnd_524595 : Nat := 179579589296986835566625

theorem tailTrace_524595 : CollatzResearch.WordTrace tailWord_524595 prefixEnd_524595 179579589296986835566625 := by
  unfold tailWord_524595
  simp only [CollatzResearch.WordTrace]
  refine ⟨19133551534489383538191239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12755701022992922358794159 19133551534489383538191239)
  ·
    refine ⟨28700327301734075307286859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19133551534489383538191239 28700327301734075307286859)
    ·
      refine ⟨43050490952601112960930289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28700327301734075307286859 43050490952601112960930289)
      ·
        refine ⟨32287868214450834720697717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43050490952601112960930289 32287868214450834720697717)
        ·
          refine ⟨3026987645104765755065411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32287868214450834720697717 3026987645104765755065411)
          ·
            refine ⟨4540481467657148632598117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3026987645104765755065411 4540481467657148632598117)
            ·
              refine ⟨851340275185715368612147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4540481467657148632598117 851340275185715368612147)
              ·
                refine ⟨1277010412778573052918221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 851340275185715368612147 1277010412778573052918221)
                ·
                  refine ⟨478878904791964894844333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1277010412778573052918221 478878904791964894844333)
                  ·
                    refine ⟨179579589296986835566625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 478878904791964894844333 179579589296986835566625)
                    ·
                      rfl

theorem cell22_524595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 1, 3, 3].length) (baseStart_524595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_524595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_524595 prefixEnd_524595 := by exact prefixLift 524595
  have htrace : WordTrace (prefixWord ++ tailWord_524595) baseStart_524595 baseEnd_524595 := by
    simpa [prefixWord, tailWord_524595, baseEnd_524595] using wordTrace_append hprefix tailTrace_524595
  have hstable : (prefixWord ++ tailWord_524595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524595).length < 2 ^ (prefixWord ++ tailWord_524595).sum := by decide
  have hdescent : baseEnd_524595 < baseStart_524595 := by decide
  rcases family_descends (prefixWord ++ tailWord_524595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524698 : List Nat := [3, 1, 1, 4, 1, 12]
def baseStart_524698 : Nat := 118140960795 + 524698 * 2 ^ 59
def prefixEnd_524698 : Nat := 4983230072969 + 3 ^ 40 * 524698 * 2
def baseEnd_524698 : Nat := 2217467262986776546189

theorem tailTrace_524698 : CollatzResearch.WordTrace tailWord_524698 prefixEnd_524698 2217467262986776546189 := by
  unfold tailWord_524698
  simp only [CollatzResearch.WordTrace]
  refine ⟨4784327063279058032297687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12758205502077488086127165 4784327063279058032297687)
  ·
    refine ⟨7176490594918587048446531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4784327063279058032297687 7176490594918587048446531)
    ·
      refine ⟨10764735892377880572669797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7176490594918587048446531 10764735892377880572669797)
      ·
        refine ⟨2018387979820852607375587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10764735892377880572669797 2018387979820852607375587)
        ·
          refine ⟨3027581969731278911063381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2018387979820852607375587 3027581969731278911063381)
          ·
            refine ⟨2217467262986776546189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 3027581969731278911063381 2217467262986776546189)
            ·
              rfl

theorem cell22_524698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 12].length) (baseStart_524698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_524698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_524698 prefixEnd_524698 := by exact prefixLift 524698
  have htrace : WordTrace (prefixWord ++ tailWord_524698) baseStart_524698 baseEnd_524698 := by
    simpa [prefixWord, tailWord_524698, baseEnd_524698] using wordTrace_append hprefix tailTrace_524698
  have hstable : (prefixWord ++ tailWord_524698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524698).length < 2 ^ (prefixWord ++ tailWord_524698).sum := by decide
  have hdescent : baseEnd_524698 < baseStart_524698 := by decide
  rcases family_descends (prefixWord ++ tailWord_524698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524704 : List Nat := [2, 1, 1, 4, 1, 5, 2, 2, 4]
def baseStart_524704 : Nat := 118140960795 + 524704 * 2 ^ 59
def prefixEnd_524704 : Nat := 4983230072969 + 3 ^ 40 * 524704 * 2
def baseEnd_524704 : Nat := 59872300741515628197097

theorem tailTrace_524704 : CollatzResearch.WordTrace tailWord_524704 prefixEnd_524704 59872300741515628197097 := by
  unfold tailWord_524704
  simp only [CollatzResearch.WordTrace]
  refine ⟨9568763545547247576954583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12758351394062996769272777 9568763545547247576954583)
  ·
    refine ⟨14353145318320871365431875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9568763545547247576954583 14353145318320871365431875)
    ·
      refine ⟨21529717977481307048147813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14353145318320871365431875 21529717977481307048147813)
      ·
        refine ⟨4036822120777745071527715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21529717977481307048147813 4036822120777745071527715)
        ·
          refine ⟨6055233181166617607291573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4036822120777745071527715 6055233181166617607291573)
          ·
            refine ⟨567678110734370400683585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6055233181166617607291573 567678110734370400683585)
            ·
              refine ⟨425758583050777800512689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 567678110734370400683585 425758583050777800512689)
              ·
                refine ⟨319318937288083350384517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 425758583050777800512689 319318937288083350384517)
                ·
                  refine ⟨59872300741515628197097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 319318937288083350384517 59872300741515628197097)
                  ·
                    rfl

theorem cell22_524704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 2, 2, 4].length) (baseStart_524704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_524704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_524704 prefixEnd_524704 := by exact prefixLift 524704
  have htrace : WordTrace (prefixWord ++ tailWord_524704) baseStart_524704 baseEnd_524704 := by
    simpa [prefixWord, tailWord_524704, baseEnd_524704] using wordTrace_append hprefix tailTrace_524704
  have hstable : (prefixWord ++ tailWord_524704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524704).length < 2 ^ (prefixWord ++ tailWord_524704).sum := by decide
  have hdescent : baseEnd_524704 < baseStart_524704 := by decide
  rcases family_descends (prefixWord ++ tailWord_524704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524728 : List Nat := [2, 1, 2, 1, 2, 2, 1, 1, 4, 6]
def baseStart_524728 : Nat := 118140960795 + 524728 * 2 ^ 59
def prefixEnd_524728 : Nat := 4983230072969 + 3 ^ 40 * 524728 * 2
def baseEnd_524728 : Nat := 179625117915018821991217

theorem tailTrace_524728 : CollatzResearch.WordTrace tailWord_524728 prefixEnd_524728 179625117915018821991217 := by
  unfold tailWord_524728
  simp only [CollatzResearch.WordTrace]
  refine ⟨9569201221503773626391419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12758934962005031501855225 9569201221503773626391419)
  ·
    refine ⟨14353801832255660439587129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9569201221503773626391419 14353801832255660439587129)
    ·
      refine ⟨10765351374191745329690347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14353801832255660439587129 10765351374191745329690347)
      ·
        refine ⟨16148027061287617994535521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10765351374191745329690347 16148027061287617994535521)
        ·
          refine ⟨12111020295965713495901641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16148027061287617994535521 12111020295965713495901641)
          ·
            refine ⟨9083265221974285121926231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12111020295965713495901641 9083265221974285121926231)
            ·
              refine ⟨13624897832961427682889347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9083265221974285121926231 13624897832961427682889347)
              ·
                refine ⟨20437346749442141524334021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13624897832961427682889347 20437346749442141524334021)
                ·
                  refine ⟨3832002515520401535812629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20437346749442141524334021 3832002515520401535812629)
                  ·
                    refine ⟨179625117915018821991217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3832002515520401535812629 179625117915018821991217)
                    ·
                      rfl

theorem cell22_524728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 4, 6].length) (baseStart_524728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_524728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_524728 prefixEnd_524728 := by exact prefixLift 524728
  have htrace : WordTrace (prefixWord ++ tailWord_524728) baseStart_524728 baseEnd_524728 := by
    simpa [prefixWord, tailWord_524728, baseEnd_524728] using wordTrace_append hprefix tailTrace_524728
  have hstable : (prefixWord ++ tailWord_524728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524728).length < 2 ^ (prefixWord ++ tailWord_524728).sum := by decide
  have hdescent : baseEnd_524728 < baseStart_524728 := by decide
  rcases family_descends (prefixWord ++ tailWord_524728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524732 : List Nat := [2, 2, 2, 4, 1, 2, 3, 6]
def baseStart_524732 : Nat := 118140960795 + 524732 * 2 ^ 59
def prefixEnd_524732 : Nat := 4983230072969 + 3 ^ 40 * 524732 * 2
def baseEnd_524732 : Nat := 19958498577418238321245

theorem tailTrace_524732 : CollatzResearch.WordTrace tailWord_524732 prefixEnd_524732 19958498577418238321245 := by
  unfold tailWord_524732
  simp only [CollatzResearch.WordTrace]
  refine ⟨9569274167496527967964225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12759032223328703957285633 9569274167496527967964225)
  ·
    refine ⟨7176955625622395975973169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9569274167496527967964225 7176955625622395975973169)
    ·
      refine ⟨5382716719216796981979877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7176955625622395975973169 5382716719216796981979877)
      ·
        refine ⟨1009259384853149434121227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5382716719216796981979877 1009259384853149434121227)
        ·
          refine ⟨1513889077279724151181841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1009259384853149434121227 1513889077279724151181841)
          ·
            refine ⟨1135416807959793113386381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1513889077279724151181841 1135416807959793113386381)
            ·
              refine ⟨425781302984922417519893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1135416807959793113386381 425781302984922417519893)
              ·
                refine ⟨19958498577418238321245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 425781302984922417519893 19958498577418238321245)
                ·
                  rfl

theorem cell22_524732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 3, 6].length) (baseStart_524732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_524732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_524732 prefixEnd_524732 := by exact prefixLift 524732
  have htrace : WordTrace (prefixWord ++ tailWord_524732) baseStart_524732 baseEnd_524732 := by
    simpa [prefixWord, tailWord_524732, baseEnd_524732] using wordTrace_append hprefix tailTrace_524732
  have hstable : (prefixWord ++ tailWord_524732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524732).length < 2 ^ (prefixWord ++ tailWord_524732).sum := by decide
  have hdescent : baseEnd_524732 < baseStart_524732 := by decide
  rcases family_descends (prefixWord ++ tailWord_524732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524775 : List Nat := [1, 1, 5, 2, 1, 1, 1, 3, 2, 5]
def baseStart_524775 : Nat := 118140960795 + 524775 * 2 ^ 59
def prefixEnd_524775 : Nat := 4983230072969 + 3 ^ 40 * 524775 * 2
def baseEnd_524775 : Nat := 179641206975526366066073

theorem tailTrace_524775 : CollatzResearch.WordTrace tailWord_524775 prefixEnd_524775 179641206975526366066073 := by
  unfold tailWord_524775
  simp only [CollatzResearch.WordTrace]
  refine ⟨19140116673837274279743779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12760077782558182853162519 19140116673837274279743779)
  ·
    refine ⟨28710175010755911419615669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19140116673837274279743779 28710175010755911419615669)
    ·
      refine ⟨2691578907258366695588969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28710175010755911419615669 2691578907258366695588969)
      ·
        refine ⟨2018684180443775021691727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2691578907258366695588969 2018684180443775021691727)
        ·
          refine ⟨3028026270665662532537591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2018684180443775021691727 3028026270665662532537591)
          ·
            refine ⟨4542039405998493798806387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3028026270665662532537591 4542039405998493798806387)
            ·
              refine ⟨6813059108997740698209581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4542039405998493798806387 6813059108997740698209581)
              ·
                refine ⟨2554897165874152761828593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6813059108997740698209581 2554897165874152761828593)
                ·
                  refine ⟨1916172874405614571371445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2554897165874152761828593 1916172874405614571371445)
                  ·
                    refine ⟨179641206975526366066073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1916172874405614571371445 179641206975526366066073)
                    ·
                      rfl

theorem cell22_524775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_524775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_524775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_524775 prefixEnd_524775 := by exact prefixLift 524775
  have htrace : WordTrace (prefixWord ++ tailWord_524775) baseStart_524775 baseEnd_524775 := by
    simpa [prefixWord, tailWord_524775, baseEnd_524775] using wordTrace_append hprefix tailTrace_524775
  have hstable : (prefixWord ++ tailWord_524775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524775).length < 2 ^ (prefixWord ++ tailWord_524775).sum := by decide
  have hdescent : baseEnd_524775 < baseStart_524775 := by decide
  rcases family_descends (prefixWord ++ tailWord_524775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524850 : List Nat := [3, 2, 1, 1, 2, 1, 4, 8]
def baseStart_524850 : Nat := 118140960795 + 524850 * 2 ^ 59
def prefixEnd_524850 : Nat := 4983230072969 + 3 ^ 40 * 524850 * 2
def baseEnd_524850 : Nat := 19962986778694574493427

theorem tailTrace_524850 : CollatzResearch.WordTrace tailWord_524850 prefixEnd_524850 19962986778694574493427 := by
  unfold tailWord_524850
  simp only [CollatzResearch.WordTrace]
  refine ⟨4785713037141390522181001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12761901432377041392482669 4785713037141390522181001)
  ·
    refine ⟨3589284777856042891635751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4785713037141390522181001 3589284777856042891635751)
    ·
      refine ⟨5383927166784064337453627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3589284777856042891635751 5383927166784064337453627)
      ·
        refine ⟨8075890750176096506180441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5383927166784064337453627 8075890750176096506180441)
        ·
          refine ⟨6056918062632072379635331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8075890750176096506180441 6056918062632072379635331)
          ·
            refine ⟨9085377093948108569452997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6056918062632072379635331 9085377093948108569452997)
            ·
              refine ⟨1703508205115270356772437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9085377093948108569452997 1703508205115270356772437)
              ·
                refine ⟨19962986778694574493427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1703508205115270356772437 19962986778694574493427)
                ·
                  rfl

theorem cell22_524850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 8].length) (baseStart_524850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_524850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_524850 prefixEnd_524850 := by exact prefixLift 524850
  have htrace : WordTrace (prefixWord ++ tailWord_524850) baseStart_524850 baseEnd_524850 := by
    simpa [prefixWord, tailWord_524850, baseEnd_524850] using wordTrace_append hprefix tailTrace_524850
  have hstable : (prefixWord ++ tailWord_524850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524850).length < 2 ^ (prefixWord ++ tailWord_524850).sum := by decide
  have hdescent : baseEnd_524850 < baseStart_524850 := by decide
  rcases family_descends (prefixWord ++ tailWord_524850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524854 : List Nat := [5, 1, 2, 1, 2, 2, 1, 2, 1, 5]
def baseStart_524854 : Nat := 118140960795 + 524854 * 2 ^ 59
def prefixEnd_524854 : Nat := 4983230072969 + 3 ^ 40 * 524854 * 2
def baseEnd_524854 : Nat := 179668250289996493340831

theorem tailTrace_524854 : CollatzResearch.WordTrace tailWord_524854 prefixEnd_524854 179668250289996493340831 := by
  unfold tailWord_524854
  simp only [CollatzResearch.WordTrace]
  refine ⟨1196437377534441923241851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12761998693700713847913077 1196437377534441923241851)
  ·
    refine ⟨1794656066301662884862777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1196437377534441923241851 1794656066301662884862777)
    ·
      refine ⟨1345992049726247163647083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1794656066301662884862777 1345992049726247163647083)
      ·
        refine ⟨2018988074589370745470625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1345992049726247163647083 2018988074589370745470625)
        ·
          refine ⟨1514241055942028059102969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2018988074589370745470625 1514241055942028059102969)
          ·
            refine ⟨1135680791956521044327227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1514241055942028059102969 1135680791956521044327227)
            ·
              refine ⟨1703521187934781566490841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1135680791956521044327227 1703521187934781566490841)
              ·
                refine ⟨1277640890951086174868131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1703521187934781566490841 1277640890951086174868131)
                ·
                  refine ⟨1916461336426629262302197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1277640890951086174868131 1916461336426629262302197)
                  ·
                    refine ⟨179668250289996493340831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1916461336426629262302197 179668250289996493340831)
                    ·
                      rfl

theorem cell22_524854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_524854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_524854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_524854 prefixEnd_524854 := by exact prefixLift 524854
  have htrace : WordTrace (prefixWord ++ tailWord_524854) baseStart_524854 baseEnd_524854 := by
    simpa [prefixWord, tailWord_524854, baseEnd_524854] using wordTrace_append hprefix tailTrace_524854
  have hstable : (prefixWord ++ tailWord_524854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524854).length < 2 ^ (prefixWord ++ tailWord_524854).sum := by decide
  have hdescent : baseEnd_524854 < baseStart_524854 := by decide
  rcases family_descends (prefixWord ++ tailWord_524854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524946 : List Nat := [3, 2, 3, 1, 2, 2, 3, 1, 5]
def baseStart_524946 : Nat := 118140960795 + 524946 * 2 ^ 59
def prefixEnd_524946 : Nat := 4983230072969 + 3 ^ 40 * 524946 * 2
def baseEnd_524946 : Nat := 59899914590046306680183

theorem tailTrace_524946 : CollatzResearch.WordTrace tailWord_524946 prefixEnd_524946 59899914590046306680183 := by
  unfold tailWord_524946
  simp only [CollatzResearch.WordTrace]
  refine ⟨4786588389054442621054673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12764235704145180322812461 4786588389054442621054673)
  ·
    refine ⟨3589941291790831965791005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4786588389054442621054673 3589941291790831965791005)
    ·
      refine ⟨1346227984421561987171627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3589941291790831965791005 1346227984421561987171627)
      ·
        refine ⟨2019341976632342980757441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1346227984421561987171627 2019341976632342980757441)
        ·
          refine ⟨1514506482474257235568081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2019341976632342980757441 1514506482474257235568081)
          ·
            refine ⟨1135879861855692926676061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1514506482474257235568081 1135879861855692926676061)
            ·
              refine ⟨425954948195884847503523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1135879861855692926676061 425954948195884847503523)
              ·
                refine ⟨638932422293827271255285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 425954948195884847503523 638932422293827271255285)
                ·
                  refine ⟨59899914590046306680183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 638932422293827271255285 59899914590046306680183)
                  ·
                    rfl

theorem cell22_524946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 3, 1, 5].length) (baseStart_524946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_524946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_524946 prefixEnd_524946 := by exact prefixLift 524946
  have htrace : WordTrace (prefixWord ++ tailWord_524946) baseStart_524946 baseEnd_524946 := by
    simpa [prefixWord, tailWord_524946, baseEnd_524946] using wordTrace_append hprefix tailTrace_524946
  have hstable : (prefixWord ++ tailWord_524946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524946).length < 2 ^ (prefixWord ++ tailWord_524946).sum := by decide
  have hdescent : baseEnd_524946 < baseStart_524946 := by decide
  rcases family_descends (prefixWord ++ tailWord_524946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524957 : List Nat := [1, 4, 2, 1, 1, 1, 4, 2, 6]
def baseStart_524957 : Nat := 118140960795 + 524957 * 2 ^ 59
def prefixEnd_524957 : Nat := 4983230072969 + 3 ^ 40 * 524957 * 2
def baseEnd_524957 : Nat := 59901169764979519338505

theorem tailTrace_524957 : CollatzResearch.WordTrace tailWord_524957 prefixEnd_524957 59901169764979519338505 := by
  unfold tailWord_524957
  simp only [CollatzResearch.WordTrace]
  refine ⟨19146754759177919362869125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12764503172785279575246083 19146754759177919362869125)
  ·
    refine ⟨3590016517345859880537961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19146754759177919362869125 3590016517345859880537961)
    ·
      refine ⟨2692512388009394910403471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3590016517345859880537961 2692512388009394910403471)
      ·
        refine ⟨4038768582014092365605207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2692512388009394910403471 4038768582014092365605207)
        ·
          refine ⟨6058152873021138548407811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4038768582014092365605207 6058152873021138548407811)
          ·
            refine ⟨9087229309531707822611717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6058152873021138548407811 9087229309531707822611717)
            ·
              refine ⟨1703855495537195216739697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9087229309531707822611717 1703855495537195216739697)
              ·
                refine ⟨1277891621652896412554773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1703855495537195216739697 1277891621652896412554773)
                ·
                  refine ⟨59901169764979519338505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1277891621652896412554773 59901169764979519338505)
                  ·
                    rfl

theorem cell22_524957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 2, 6].length) (baseStart_524957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_524957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_524957 prefixEnd_524957 := by exact prefixLift 524957
  have htrace : WordTrace (prefixWord ++ tailWord_524957) baseStart_524957 baseEnd_524957 := by
    simpa [prefixWord, tailWord_524957, baseEnd_524957] using wordTrace_append hprefix tailTrace_524957
  have hstable : (prefixWord ++ tailWord_524957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524957).length < 2 ^ (prefixWord ++ tailWord_524957).sum := by decide
  have hdescent : baseEnd_524957 < baseStart_524957 := by decide
  rcases family_descends (prefixWord ++ tailWord_524957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524967 : List Nat := [1, 1, 6, 3, 2, 1, 1, 3, 1, 3]
def baseStart_524967 : Nat := 118140960795 + 524967 * 2 ^ 59
def prefixEnd_524967 : Nat := 4983230072969 + 3 ^ 40 * 524967 * 2
def baseEnd_524967 : Nat := 179706932499301865265485

theorem tailTrace_524967 : CollatzResearch.WordTrace tailWord_524967 prefixEnd_524967 179706932499301865265485 := by
  unfold tailWord_524967
  simp only [CollatzResearch.WordTrace]
  refine ⟨19147119489141691070733155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12764746326094460713822103 19147119489141691070733155)
  ·
    refine ⟨28720679233712536606099733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19147119489141691070733155 28720679233712536606099733)
    ·
      refine ⟨1346281839080275153410925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 28720679233712536606099733 1346281839080275153410925)
      ·
        refine ⟨504855689655103182529097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1346281839080275153410925 504855689655103182529097)
        ·
          refine ⟨378641767241327386896823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 504855689655103182529097 378641767241327386896823)
          ·
            refine ⟨567962650861991080345235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 378641767241327386896823 567962650861991080345235)
            ·
              refine ⟨851943976292986620517853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 567962650861991080345235 851943976292986620517853)
              ·
                refine ⟨319478991109869982694195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 851943976292986620517853 319478991109869982694195)
                ·
                  refine ⟨479218486664804974041293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 319478991109869982694195 479218486664804974041293)
                  ·
                    refine ⟨179706932499301865265485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 479218486664804974041293 179706932499301865265485)
                    ·
                      rfl

theorem cell22_524967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_524967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_524967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_524967 prefixEnd_524967 := by exact prefixLift 524967
  have htrace : WordTrace (prefixWord ++ tailWord_524967) baseStart_524967 baseEnd_524967 := by
    simpa [prefixWord, tailWord_524967, baseEnd_524967] using wordTrace_append hprefix tailTrace_524967
  have hstable : (prefixWord ++ tailWord_524967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524967).length < 2 ^ (prefixWord ++ tailWord_524967).sum := by decide
  have hdescent : baseEnd_524967 < baseStart_524967 := by decide
  rcases family_descends (prefixWord ++ tailWord_524967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524989 : List Nat := [1, 4, 1, 2, 1, 3, 2, 1, 4, 3]
def baseStart_524989 : Nat := 118140960795 + 524989 * 2 ^ 59
def prefixEnd_524989 : Nat := 4983230072969 + 3 ^ 40 * 524989 * 2
def baseEnd_524989 : Nat := 179714463548901141215417

theorem tailTrace_524989 : CollatzResearch.WordTrace tailWord_524989 prefixEnd_524989 179714463548901141215417 := by
  unfold tailWord_524989
  simp only [CollatzResearch.WordTrace]
  refine ⟨19147921895061988828034021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12765281263374659218689347 19147921895061988828034021)
  ·
    refine ⟨3590235355324122905256379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19147921895061988828034021 3590235355324122905256379)
    ·
      refine ⟨5385353032986184357884569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3590235355324122905256379 5385353032986184357884569)
      ·
        refine ⟨4039014774739638268413427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5385353032986184357884569 4039014774739638268413427)
        ·
          refine ⟨6058522162109457402620141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4039014774739638268413427 6058522162109457402620141)
          ·
            refine ⟨2271945810791046525982553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6058522162109457402620141 2271945810791046525982553)
            ·
              refine ⟨1703959358093284894486915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2271945810791046525982553 1703959358093284894486915)
              ·
                refine ⟨2555939037139927341730373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1703959358093284894486915 2555939037139927341730373)
                ·
                  refine ⟨479238569463736376574445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2555939037139927341730373 479238569463736376574445)
                  ·
                    refine ⟨179714463548901141215417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 479238569463736376574445 179714463548901141215417)
                    ·
                      rfl

theorem cell22_524989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 1, 4, 3].length) (baseStart_524989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_524989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_524989 prefixEnd_524989 := by exact prefixLift 524989
  have htrace : WordTrace (prefixWord ++ tailWord_524989) baseStart_524989 baseEnd_524989 := by
    simpa [prefixWord, tailWord_524989, baseEnd_524989] using wordTrace_append hprefix tailTrace_524989
  have hstable : (prefixWord ++ tailWord_524989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524989).length < 2 ^ (prefixWord ++ tailWord_524989).sum := by decide
  have hdescent : baseEnd_524989 < baseStart_524989 := by decide
  rcases family_descends (prefixWord ++ tailWord_524989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524991 : List Nat := [1, 1, 2, 2, 2, 5, 3, 2, 4]
def baseStart_524991 : Nat := 118140960795 + 524991 * 2 ^ 59
def prefixEnd_524991 : Nat := 4983230072969 + 3 ^ 40 * 524991 * 2
def baseEnd_524991 : Nat := 59905049396591267555137

theorem tailTrace_524991 : CollatzResearch.WordTrace tailWord_524991 prefixEnd_524991 59905049396591267555137 := by
  unfold tailWord_524991
  simp only [CollatzResearch.WordTrace]
  refine ⟨19147994841054743169606827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12765329894036495446404551 19147994841054743169606827)
  ·
    refine ⟨28721992261582114754410241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19147994841054743169606827 28721992261582114754410241)
    ·
      refine ⟨21541494196186586065807681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28721992261582114754410241 21541494196186586065807681)
      ·
        refine ⟨16156120647139939549355761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21541494196186586065807681 16156120647139939549355761)
        ·
          refine ⟨12117090485354954662016821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16156120647139939549355761 12117090485354954662016821)
          ·
            refine ⟨1135977233002026999564077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12117090485354954662016821 1135977233002026999564077)
            ·
              refine ⟨425991462375760124836529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1135977233002026999564077 425991462375760124836529)
              ·
                refine ⟨319493596781820093627397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 425991462375760124836529 319493596781820093627397)
                ·
                  refine ⟨59905049396591267555137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 319493596781820093627397 59905049396591267555137)
                  ·
                    rfl

theorem cell22_524991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 3, 2, 4].length) (baseStart_524991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_524991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_524991 prefixEnd_524991 := by exact prefixLift 524991
  have htrace : WordTrace (prefixWord ++ tailWord_524991) baseStart_524991 baseEnd_524991 := by
    simpa [prefixWord, tailWord_524991, baseEnd_524991] using wordTrace_append hprefix tailTrace_524991
  have hstable : (prefixWord ++ tailWord_524991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524991).length < 2 ^ (prefixWord ++ tailWord_524991).sum := by decide
  have hdescent : baseEnd_524991 < baseStart_524991 := by decide
  rcases family_descends (prefixWord ++ tailWord_524991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525002 : List Nat := [3, 1, 2, 1, 4, 1, 1, 9]
def baseStart_525002 : Nat := 118140960795 + 525002 * 2 ^ 59
def prefixEnd_525002 : Nat := 4983230072969 + 3 ^ 40 * 525002 * 2
def baseEnd_525002 : Nat := 19968768190508160071153

theorem tailTrace_525002 : CollatzResearch.WordTrace tailWord_525002 prefixEnd_525002 19968768190508160071153 := by
  unfold tailWord_525002
  simp only [CollatzResearch.WordTrace]
  refine ⟨4787099011003723012064315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12765597362676594698838173 4787099011003723012064315)
  ·
    refine ⟨7180648516505584518096473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4787099011003723012064315 7180648516505584518096473)
    ·
      refine ⟨5385486387379188388572355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7180648516505584518096473 5385486387379188388572355)
      ·
        refine ⟨8078229581068782582858533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5385486387379188388572355 8078229581068782582858533)
        ·
          refine ⟨1514668046450396734285975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8078229581068782582858533 1514668046450396734285975)
          ·
            refine ⟨2272002069675595101428963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1514668046450396734285975 2272002069675595101428963)
            ·
              refine ⟨3408003104513392652143445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2272002069675595101428963 3408003104513392652143445)
              ·
                refine ⟨19968768190508160071153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3408003104513392652143445 19968768190508160071153)
                ·
                  rfl

theorem cell22_525002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 9].length) (baseStart_525002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_525002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_525002 prefixEnd_525002 := by exact prefixLift 525002
  have htrace : WordTrace (prefixWord ++ tailWord_525002) baseStart_525002 baseEnd_525002 := by
    simpa [prefixWord, tailWord_525002, baseEnd_525002] using wordTrace_append hprefix tailTrace_525002
  have hstable : (prefixWord ++ tailWord_525002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525002).length < 2 ^ (prefixWord ++ tailWord_525002).sum := by decide
  have hdescent : baseEnd_525002 < baseStart_525002 := by decide
  rcases family_descends (prefixWord ++ tailWord_525002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525006 : List Nat := [4, 1, 1, 1, 3, 3, 1, 3, 2, 3]
def baseStart_525006 : Nat := 118140960795 + 525006 * 2 ^ 59
def prefixEnd_525006 : Nat := 4983230072969 + 3 ^ 40 * 525006 * 2
def baseEnd_525006 : Nat := 179720282996318763540365

theorem tailTrace_525006 : CollatzResearch.WordTrace tailWord_525006 prefixEnd_525006 179720282996318763540365 := by
  unfold tailWord_525006
  simp only [CollatzResearch.WordTrace]
  refine ⟨2393567742000050091425359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12765694624000267154268581 2393567742000050091425359)
  ·
    refine ⟨3590351613000075137138039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2393567742000050091425359 3590351613000075137138039)
    ·
      refine ⟨5385527419500112705707059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3590351613000075137138039 5385527419500112705707059)
      ·
        refine ⟨8078291129250169058560589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5385527419500112705707059 8078291129250169058560589)
        ·
          refine ⟨3029359173468813396960221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8078291129250169058560589 3029359173468813396960221)
          ·
            refine ⟨1136009690050805023860083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3029359173468813396960221 1136009690050805023860083)
            ·
              refine ⟨1704014535076207535790125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1136009690050805023860083 1704014535076207535790125)
              ·
                refine ⟨639005450653577825921297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1704014535076207535790125 639005450653577825921297)
                ·
                  refine ⟨479254087990183369440973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 639005450653577825921297 479254087990183369440973)
                  ·
                    refine ⟨179720282996318763540365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 479254087990183369440973 179720282996318763540365)
                    ·
                      rfl

theorem cell22_525006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 3, 2, 3].length) (baseStart_525006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_525006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_525006 prefixEnd_525006 := by exact prefixLift 525006
  have htrace : WordTrace (prefixWord ++ tailWord_525006) baseStart_525006 baseEnd_525006 := by
    simpa [prefixWord, tailWord_525006, baseEnd_525006] using wordTrace_append hprefix tailTrace_525006
  have hstable : (prefixWord ++ tailWord_525006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525006).length < 2 ^ (prefixWord ++ tailWord_525006).sum := by decide
  have hdescent : baseEnd_525006 < baseStart_525006 := by decide
  rcases family_descends (prefixWord ++ tailWord_525006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525064 : List Nat := [2, 1, 3, 2, 2, 2, 2, 3, 5]
def baseStart_525064 : Nat := 118140960795 + 525064 * 2 ^ 59
def prefixEnd_525064 : Nat := 4983230072969 + 3 ^ 40 * 525064 * 2
def baseEnd_525064 : Nat := 59913379193875315196729

theorem tailTrace_525064 : CollatzResearch.WordTrace tailWord_525064 prefixEnd_525064 59913379193875315196729 := by
  unfold tailWord_525064
  simp only [CollatzResearch.WordTrace]
  refine ⟨9575328684895138318507123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12767104913193517758009497 9575328684895138318507123)
  ·
    refine ⟨14362993027342707477760685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9575328684895138318507123 14362993027342707477760685)
    ·
      refine ⟨5386122385253515304160257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14362993027342707477760685 5386122385253515304160257)
      ·
        refine ⟨4039591788940136478120193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5386122385253515304160257 4039591788940136478120193)
        ·
          refine ⟨3029693841705102358590145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4039591788940136478120193 3029693841705102358590145)
          ·
            refine ⟨2272270381278826768942609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3029693841705102358590145 2272270381278826768942609)
            ·
              refine ⟨1704202785959120076706957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2272270381278826768942609 1704202785959120076706957)
              ·
                refine ⟨639076044734670028765109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1704202785959120076706957 639076044734670028765109)
                ·
                  refine ⟨59913379193875315196729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 639076044734670028765109 59913379193875315196729)
                  ·
                    rfl

theorem cell22_525064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 3, 5].length) (baseStart_525064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_525064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_525064 prefixEnd_525064 := by exact prefixLift 525064
  have htrace : WordTrace (prefixWord ++ tailWord_525064) baseStart_525064 baseEnd_525064 := by
    simpa [prefixWord, tailWord_525064, baseEnd_525064] using wordTrace_append hprefix tailTrace_525064
  have hstable : (prefixWord ++ tailWord_525064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525064).length < 2 ^ (prefixWord ++ tailWord_525064).sum := by decide
  have hdescent : baseEnd_525064 < baseStart_525064 := by decide
  rcases family_descends (prefixWord ++ tailWord_525064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525109 : List Nat := [1, 3, 3, 1, 3, 1, 1, 3, 6]
def baseStart_525109 : Nat := 118140960795 + 525109 * 2 ^ 59
def prefixEnd_525109 : Nat := 4983230072969 + 3 ^ 40 * 525109 * 2
def baseEnd_525109 : Nat := 59918514000420276071683

theorem tailTrace_525109 : CollatzResearch.WordTrace tailWord_525109 prefixEnd_525109 59918514000420276071683 := by
  unfold tailWord_525109
  simp only [CollatzResearch.WordTrace]
  refine ⟨19152298654627249322402381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12768199103084832881601587 19152298654627249322402381)
  ·
    refine ⟨7182111995485218495900893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19152298654627249322402381 7182111995485218495900893)
    ·
      refine ⟨2693291998306956935962835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7182111995485218495900893 2693291998306956935962835)
      ·
        refine ⟨4039937997460435403944253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2693291998306956935962835 4039937997460435403944253)
        ·
          refine ⟨1514976749047663276479095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4039937997460435403944253 1514976749047663276479095)
          ·
            refine ⟨2272465123571494914718643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1514976749047663276479095 2272465123571494914718643)
            ·
              refine ⟨3408697685357242372077965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2272465123571494914718643 3408697685357242372077965)
              ·
                refine ⟨1278261632008965889529237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3408697685357242372077965 1278261632008965889529237)
                ·
                  refine ⟨59918514000420276071683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1278261632008965889529237 59918514000420276071683)
                  ·
                    rfl

theorem cell22_525109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 3, 6].length) (baseStart_525109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_525109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_525109 prefixEnd_525109 := by exact prefixLift 525109
  have htrace : WordTrace (prefixWord ++ tailWord_525109) baseStart_525109 baseEnd_525109 := by
    simpa [prefixWord, tailWord_525109, baseEnd_525109] using wordTrace_append hprefix tailTrace_525109
  have hstable : (prefixWord ++ tailWord_525109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525109).length < 2 ^ (prefixWord ++ tailWord_525109).sum := by decide
  have hdescent : baseEnd_525109 < baseStart_525109 := by decide
  rcases family_descends (prefixWord ++ tailWord_525109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525143 : List Nat := [1, 1, 3, 2, 4, 3, 1, 3, 4]
def baseStart_525143 : Nat := 118140960795 + 525143 * 2 ^ 59
def prefixEnd_525143 : Nat := 4983230072969 + 3 ^ 40 * 525143 * 2
def baseEnd_525143 : Nat := 59922393632032024288315

theorem tailTrace_525143 : CollatzResearch.WordTrace tailWord_525143 prefixEnd_525143 59922393632032024288315 := by
  unfold tailWord_525143
  simp only [CollatzResearch.WordTrace]
  refine ⟨19153538736504073129140083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12769025824336048752760055 19153538736504073129140083)
  ·
    refine ⟨28730308104756109693710125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19153538736504073129140083 28730308104756109693710125)
    ·
      refine ⟨10773865539283541135141297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28730308104756109693710125 10773865539283541135141297)
      ·
        refine ⟨8080399154462655851355973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10773865539283541135141297 8080399154462655851355973)
        ·
          refine ⟨1515074841461747972129245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8080399154462655851355973 1515074841461747972129245)
          ·
            refine ⟨568153065548155489548467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1515074841461747972129245 568153065548155489548467)
            ·
              refine ⟨852229598322233234322701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 568153065548155489548467 852229598322233234322701)
              ·
                refine ⟨319586099370837462871013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 852229598322233234322701 319586099370837462871013)
                ·
                  refine ⟨59922393632032024288315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 319586099370837462871013 59922393632032024288315)
                  ·
                    rfl

theorem cell22_525143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 3, 4].length) (baseStart_525143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_525143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_525143 prefixEnd_525143 := by exact prefixLift 525143
  have htrace : WordTrace (prefixWord ++ tailWord_525143) baseStart_525143 baseEnd_525143 := by
    simpa [prefixWord, tailWord_525143, baseEnd_525143] using wordTrace_append hprefix tailTrace_525143
  have hstable : (prefixWord ++ tailWord_525143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525143).length < 2 ^ (prefixWord ++ tailWord_525143).sum := by decide
  have hdescent : baseEnd_525143 < baseStart_525143 := by decide
  rcases family_descends (prefixWord ++ tailWord_525143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525156 : List Nat := [2, 3, 1, 1, 4, 2, 1, 2, 2, 4]
def baseStart_525156 : Nat := 118140960795 + 525156 * 2 ^ 59
def prefixEnd_525156 : Nat := 4983230072969 + 3 ^ 40 * 525156 * 2
def baseEnd_525156 : Nat := 179771631061768372289905

theorem tailTrace_525156 : CollatzResearch.WordTrace tailWord_525156 prefixEnd_525156 179771631061768372289905 := by
  unfold tailWord_525156
  simp only [CollatzResearch.WordTrace]
  refine ⟨9577006442728488174681661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12769341923637984232908881 9577006442728488174681661)
  ·
    refine ⟨3591377416023183065505623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9577006442728488174681661 3591377416023183065505623)
    ·
      refine ⟨5387066124034774598258435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3591377416023183065505623 5387066124034774598258435)
      ·
        refine ⟨8080599186052161897387653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5387066124034774598258435 8080599186052161897387653)
        ·
          refine ⟨1515112347384780355760185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8080599186052161897387653 1515112347384780355760185)
          ·
            refine ⟨1136334260538585266820139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1515112347384780355760185 1136334260538585266820139)
            ·
              refine ⟨1704501390807877900230209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1136334260538585266820139 1704501390807877900230209)
              ·
                refine ⟨1278376043105908425172657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1704501390807877900230209 1278376043105908425172657)
                ·
                  refine ⟨958782032329431318879493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1278376043105908425172657 958782032329431318879493)
                  ·
                    refine ⟨179771631061768372289905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 958782032329431318879493 179771631061768372289905)
                    ·
                      rfl

theorem cell22_525156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 2, 2, 4].length) (baseStart_525156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_525156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_525156 prefixEnd_525156 := by exact prefixLift 525156
  have htrace : WordTrace (prefixWord ++ tailWord_525156) baseStart_525156 baseEnd_525156 := by
    simpa [prefixWord, tailWord_525156, baseEnd_525156] using wordTrace_append hprefix tailTrace_525156
  have hstable : (prefixWord ++ tailWord_525156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525156).length < 2 ^ (prefixWord ++ tailWord_525156).sum := by decide
  have hdescent : baseEnd_525156 < baseStart_525156 := by decide
  rcases family_descends (prefixWord ++ tailWord_525156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525246 : List Nat := [4, 2, 1, 1, 1, 2, 1, 3, 3, 4]
def baseStart_525246 : Nat := 118140960795 + 525246 * 2 ^ 59
def prefixEnd_525246 : Nat := 4983230072969 + 3 ^ 40 * 525246 * 2
def baseEnd_525246 : Nat := 179802439901038137539629

theorem tailTrace_525246 : CollatzResearch.WordTrace tailWord_525246 prefixEnd_525246 179802439901038137539629 := by
  unfold tailWord_525246
  simp only [CollatzResearch.WordTrace]
  refine ⟨2394661931891365215017449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12771530303420614480093061 2394661931891365215017449)
  ·
    refine ⟨1795996448918523911263087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2394661931891365215017449 1795996448918523911263087)
    ·
      refine ⟨2693994673377785866894631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1795996448918523911263087 2693994673377785866894631)
      ·
        refine ⟨4040992010066678800341947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2693994673377785866894631 4040992010066678800341947)
        ·
          refine ⟨6061488015100018200512921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4040992010066678800341947 6061488015100018200512921)
          ·
            refine ⟨4546116011325013650384691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6061488015100018200512921 4546116011325013650384691)
            ·
              refine ⟨6819174016987520475577037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4546116011325013650384691 6819174016987520475577037)
              ·
                refine ⟨2557190256370320178341389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6819174016987520475577037 2557190256370320178341389)
                ·
                  refine ⟨958946346138870066878021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2557190256370320178341389 958946346138870066878021)
                  ·
                    refine ⟨179802439901038137539629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 958946346138870066878021 179802439901038137539629)
                    ·
                      rfl

theorem cell22_525246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_525246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_525246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_525246 prefixEnd_525246 := by exact prefixLift 525246
  have htrace : WordTrace (prefixWord ++ tailWord_525246) baseStart_525246 baseEnd_525246 := by
    simpa [prefixWord, tailWord_525246, baseEnd_525246] using wordTrace_append hprefix tailTrace_525246
  have hstable : (prefixWord ++ tailWord_525246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525246).length < 2 ^ (prefixWord ++ tailWord_525246).sum := by decide
  have hdescent : baseEnd_525246 < baseStart_525246 := by decide
  rcases family_descends (prefixWord ++ tailWord_525246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525263 : List Nat := [1, 1, 2, 1, 1, 6, 4, 1, 1, 4]
def baseStart_525263 : Nat := 118140960795 + 525263 * 2 ^ 59
def prefixEnd_525263 : Nat := 4983230072969 + 3 ^ 40 * 525263 * 2
def baseEnd_525263 : Nat := 179808259348455759864577

theorem tailTrace_525263 : CollatzResearch.WordTrace tailWord_525263 prefixEnd_525263 179808259348455759864577 := by
  unfold tailWord_525263
  simp only [CollatzResearch.WordTrace]
  refine ⟨19157915496069333623508443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12771943664046222415672295 19157915496069333623508443)
  ·
    refine ⟨28736873244104000435262665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19157915496069333623508443 28736873244104000435262665)
    ·
      refine ⟨21552654933078000326446999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28736873244104000435262665 21552654933078000326446999)
      ·
        refine ⟨32328982399617000489670499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21552654933078000326446999 32328982399617000489670499)
        ·
          refine ⟨48493473599425500734505749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32328982399617000489670499 48493473599425500734505749)
          ·
            refine ⟨2273131574973070346929957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 48493473599425500734505749 2273131574973070346929957)
            ·
              refine ⟨426212170307450690049367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2273131574973070346929957 426212170307450690049367)
              ·
                refine ⟨639318255461176035074051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 426212170307450690049367 639318255461176035074051)
                ·
                  refine ⟨958977383191764052611077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 639318255461176035074051 958977383191764052611077)
                  ·
                    refine ⟨179808259348455759864577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 958977383191764052611077 179808259348455759864577)
                    ·
                      rfl

theorem cell22_525263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 4, 1, 1, 4].length) (baseStart_525263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_525263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_525263 prefixEnd_525263 := by exact prefixLift 525263
  have htrace : WordTrace (prefixWord ++ tailWord_525263) baseStart_525263 baseEnd_525263 := by
    simpa [prefixWord, tailWord_525263, baseEnd_525263] using wordTrace_append hprefix tailTrace_525263
  have hstable : (prefixWord ++ tailWord_525263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525263).length < 2 ^ (prefixWord ++ tailWord_525263).sum := by decide
  have hdescent : baseEnd_525263 < baseStart_525263 := by decide
  rcases family_descends (prefixWord ++ tailWord_525263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525304 : List Nat := [2, 1, 2, 1, 1, 3, 1, 1, 1, 9]
def baseStart_525304 : Nat := 118140960795 + 525304 * 2 ^ 59
def prefixEnd_525304 : Nat := 4983230072969 + 3 ^ 40 * 525304 * 2
def baseEnd_525304 : Nat := 179822294486345319589451

theorem tailTrace_525304 : CollatzResearch.WordTrace tailWord_525304 prefixEnd_525304 179822294486345319589451 := by
  unfold tailWord_525304
  simp only [CollatzResearch.WordTrace]
  refine ⟨9579705444460398812875483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12772940592613865083833977 9579705444460398812875483)
  ·
    refine ⟨14369558166690598219313225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9579705444460398812875483 14369558166690598219313225)
    ·
      refine ⟨10777168625017948664484919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14369558166690598219313225 10777168625017948664484919)
      ·
        refine ⟨16165752937526922996727379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10777168625017948664484919 16165752937526922996727379)
        ·
          refine ⟨24248629406290384495091069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16165752937526922996727379 24248629406290384495091069)
          ·
            refine ⟨9093236027358894185659151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24248629406290384495091069 9093236027358894185659151)
            ·
              refine ⟨13639854041038341278488727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9093236027358894185659151 13639854041038341278488727)
              ·
                refine ⟨20459781061557511917733091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13639854041038341278488727 20459781061557511917733091)
                ·
                  refine ⟨30689671592336267876599637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20459781061557511917733091 30689671592336267876599637)
                  ·
                    refine ⟨179822294486345319589451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 30689671592336267876599637 179822294486345319589451)
                    ·
                      rfl

theorem cell22_525304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 1, 9].length) (baseStart_525304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_525304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_525304 prefixEnd_525304 := by exact prefixLift 525304
  have htrace : WordTrace (prefixWord ++ tailWord_525304) baseStart_525304 baseEnd_525304 := by
    simpa [prefixWord, tailWord_525304, baseEnd_525304] using wordTrace_append hprefix tailTrace_525304
  have hstable : (prefixWord ++ tailWord_525304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525304).length < 2 ^ (prefixWord ++ tailWord_525304).sum := by decide
  have hdescent : baseEnd_525304 < baseStart_525304 := by decide
  rcases family_descends (prefixWord ++ tailWord_525304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525321 : List Nat := [1, 2, 1, 1, 3, 1, 1, 4, 5, 3]
def baseStart_525321 : Nat := 118140960795 + 525321 * 2 ^ 59
def prefixEnd_525321 : Nat := 4983230072969 + 3 ^ 40 * 525321 * 2
def baseEnd_525321 : Nat := 179828113933762941914399

theorem tailTrace_525321 : CollatzResearch.WordTrace tailWord_525321 prefixEnd_525321 179828113933762941914399 := by
  unfold tailWord_525321
  simp only [CollatzResearch.WordTrace]
  refine ⟨19160030929859209529119817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12773353953239473019413211 19160030929859209529119817)
  ·
    refine ⟨14370023197394407146839863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19160030929859209529119817 14370023197394407146839863)
    ·
      refine ⟨21555034796091610720259795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14370023197394407146839863 21555034796091610720259795)
      ·
        refine ⟨32332552194137416080389693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21555034796091610720259795 32332552194137416080389693)
        ·
          refine ⟨12124707072801531030146135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32332552194137416080389693 12124707072801531030146135)
          ·
            refine ⟨18187060609202296545219203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12124707072801531030146135 18187060609202296545219203)
            ·
              refine ⟨27280590913803444817828805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18187060609202296545219203 27280590913803444817828805)
              ·
                refine ⟨5115110796338145903342901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27280590913803444817828805 5115110796338145903342901)
                ·
                  refine ⟨479541637156701178438397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5115110796338145903342901 479541637156701178438397)
                  ·
                    refine ⟨179828113933762941914399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 479541637156701178438397 179828113933762941914399)
                    ·
                      rfl

theorem cell22_525321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 5, 3].length) (baseStart_525321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_525321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_525321 prefixEnd_525321 := by exact prefixLift 525321
  have htrace : WordTrace (prefixWord ++ tailWord_525321) baseStart_525321 baseEnd_525321 := by
    simpa [prefixWord, tailWord_525321, baseEnd_525321] using wordTrace_append hprefix tailTrace_525321
  have hstable : (prefixWord ++ tailWord_525321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525321).length < 2 ^ (prefixWord ++ tailWord_525321).sum := by decide
  have hdescent : baseEnd_525321 < baseStart_525321 := by decide
  rcases family_descends (prefixWord ++ tailWord_525321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525344 : List Nat := [2, 1, 1, 7, 1, 2, 2, 1, 2, 3]
def baseStart_525344 : Nat := 118140960795 + 525344 * 2 ^ 59
def prefixEnd_525344 : Nat := 4983230072969 + 3 ^ 40 * 525344 * 2
def baseEnd_525344 : Nat := 179835987303798548589329

theorem tailTrace_525344 : CollatzResearch.WordTrace tailWord_525344 prefixEnd_525344 179835987303798548589329 := by
  unfold tailWord_525344
  simp only [CollatzResearch.WordTrace]
  refine ⟨9580434904387942228603543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12773913205850589638138057 9580434904387942228603543)
  ·
    refine ⟨14370652356581913342905315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9580434904387942228603543 14370652356581913342905315)
    ·
      refine ⟨21555978534872870014357973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14370652356581913342905315 21555978534872870014357973)
      ·
        refine ⟨505218246911082890961515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 21555978534872870014357973 505218246911082890961515)
        ·
          refine ⟨757827370366624336442273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 505218246911082890961515 757827370366624336442273)
          ·
            refine ⟨568370527774968252331705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 757827370366624336442273 568370527774968252331705)
            ·
              refine ⟨426277895831226189248779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 568370527774968252331705 426277895831226189248779)
              ·
                refine ⟨639416843746839283873169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 426277895831226189248779 639416843746839283873169)
                ·
                  refine ⟨479562632810129462904877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 639416843746839283873169 479562632810129462904877)
                  ·
                    refine ⟨179835987303798548589329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 479562632810129462904877 179835987303798548589329)
                    ·
                      rfl

theorem cell22_525344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 2, 1, 2, 3].length) (baseStart_525344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_525344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_525344 prefixEnd_525344 := by exact prefixLift 525344
  have htrace : WordTrace (prefixWord ++ tailWord_525344) baseStart_525344 baseEnd_525344 := by
    simpa [prefixWord, tailWord_525344, baseEnd_525344] using wordTrace_append hprefix tailTrace_525344
  have hstable : (prefixWord ++ tailWord_525344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525344).length < 2 ^ (prefixWord ++ tailWord_525344).sum := by decide
  have hdescent : baseEnd_525344 < baseStart_525344 := by decide
  rcases family_descends (prefixWord ++ tailWord_525344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525389 : List Nat := [1, 6, 1, 1, 1, 2, 4, 2, 1, 3]
def baseStart_525389 : Nat := 118140960795 + 525389 * 2 ^ 59
def prefixEnd_525389 : Nat := 4983230072969 + 3 ^ 40 * 525389 * 2
def baseEnd_525389 : Nat := 179851391723433431214191

theorem tailTrace_525389 : CollatzResearch.WordTrace tailWord_525389 prefixEnd_525389 179851391723433431214191 := by
  unfold tailWord_525389
  simp only [CollatzResearch.WordTrace]
  refine ⟨19162511093612857142595221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12775007395741904761730147 19162511093612857142595221)
  ·
    refine ⟨898242707513102678559151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 19162511093612857142595221 898242707513102678559151)
    ·
      refine ⟨1347364061269654017838727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 898242707513102678559151 1347364061269654017838727)
      ·
        refine ⟨2021046091904481026758091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1347364061269654017838727 2021046091904481026758091)
        ·
          refine ⟨3031569137856721540137137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2021046091904481026758091 3031569137856721540137137)
          ·
            refine ⟨2273676853392541155102853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3031569137856721540137137 2273676853392541155102853)
            ·
              refine ⟨426314410011101466581785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2273676853392541155102853 426314410011101466581785)
              ·
                refine ⟨319735807508326099936339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 426314410011101466581785 319735807508326099936339)
                ·
                  refine ⟨479603711262489149904509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 319735807508326099936339 479603711262489149904509)
                  ·
                    refine ⟨179851391723433431214191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 479603711262489149904509 179851391723433431214191)
                    ·
                      rfl

theorem cell22_525389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_525389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_525389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_525389 prefixEnd_525389 := by exact prefixLift 525389
  have htrace : WordTrace (prefixWord ++ tailWord_525389) baseStart_525389 baseEnd_525389 := by
    simpa [prefixWord, tailWord_525389, baseEnd_525389] using wordTrace_append hprefix tailTrace_525389
  have hstable : (prefixWord ++ tailWord_525389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525389).length < 2 ^ (prefixWord ++ tailWord_525389).sum := by decide
  have hdescent : baseEnd_525389 < baseStart_525389 := by decide
  rcases family_descends (prefixWord ++ tailWord_525389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525445 : List Nat := [1, 3, 1, 1, 6, 1, 1, 1, 4, 3]
def baseStart_525445 : Nat := 118140960795 + 525445 * 2 ^ 59
def prefixEnd_525445 : Nat := 4983230072969 + 3 ^ 40 * 525445 * 2
def baseEnd_525445 : Nat := 179870561667867951814019

theorem tailTrace_525445 : CollatzResearch.WordTrace tailWord_525445 prefixEnd_525445 179870561667867951814019 := by
  unfold tailWord_525445
  simp only [CollatzResearch.WordTrace]
  refine ⟨19164553581409978706633789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12776369054273319137755859 19164553581409978706633789)
  ·
    refine ⟨7186707593028742014987671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19164553581409978706633789 7186707593028742014987671)
    ·
      refine ⟨10780061389543113022481507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7186707593028742014987671 10780061389543113022481507)
      ·
        refine ⟨16170092084314669533722261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10780061389543113022481507 16170092084314669533722261)
        ·
          refine ⟨757973066452250134393231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 16170092084314669533722261 757973066452250134393231)
          ·
            refine ⟨1136959599678375201589847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 757973066452250134393231 1136959599678375201589847)
            ·
              refine ⟨1705439399517562802384771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1136959599678375201589847 1705439399517562802384771)
              ·
                refine ⟨2558159099276344203577157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1705439399517562802384771 2558159099276344203577157)
                ·
                  refine ⟨479654831114314538170717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2558159099276344203577157 479654831114314538170717)
                  ·
                    refine ⟨179870561667867951814019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 479654831114314538170717 179870561667867951814019)
                    ·
                      rfl

theorem cell22_525445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 1, 4, 3].length) (baseStart_525445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_525445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_525445 prefixEnd_525445 := by exact prefixLift 525445
  have htrace : WordTrace (prefixWord ++ tailWord_525445) baseStart_525445 baseEnd_525445 := by
    simpa [prefixWord, tailWord_525445, baseEnd_525445] using wordTrace_append hprefix tailTrace_525445
  have hstable : (prefixWord ++ tailWord_525445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525445).length < 2 ^ (prefixWord ++ tailWord_525445).sum := by decide
  have hdescent : baseEnd_525445 < baseStart_525445 := by decide
  rcases family_descends (prefixWord ++ tailWord_525445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525494 : List Nat := [5, 1, 3, 2, 1, 1, 1, 2, 2, 4]
def baseStart_525494 : Nat := 118140960795 + 525494 * 2 ^ 59
def prefixEnd_525494 : Nat := 4983230072969 + 3 ^ 40 * 525494 * 2
def baseEnd_525494 : Nat := 179887335369248157338869

theorem tailTrace_525494 : CollatzResearch.WordTrace tailWord_525494 prefixEnd_525494 179887335369248157338869 := by
  unfold tailWord_525494
  simp only [CollatzResearch.WordTrace]
  refine ⟨1197896297389528754697971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12777560505488306716778357 1197896297389528754697971)
  ·
    refine ⟨1796844446084293132046957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1197896297389528754697971 1796844446084293132046957)
    ·
      refine ⟨673816667281609924517609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1796844446084293132046957 673816667281609924517609)
      ·
        refine ⟨505362500461207443388207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 673816667281609924517609 505362500461207443388207)
        ·
          refine ⟨758043750691811165082311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 505362500461207443388207 758043750691811165082311)
          ·
            refine ⟨1137065626037716747623467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 758043750691811165082311 1137065626037716747623467)
            ·
              refine ⟨1705598439056575121435201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1137065626037716747623467 1705598439056575121435201)
              ·
                refine ⟨1279198829292431341076401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1705598439056575121435201 1279198829292431341076401)
                ·
                  refine ⟨959399121969323505807301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1279198829292431341076401 959399121969323505807301)
                  ·
                    refine ⟨179887335369248157338869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 959399121969323505807301 179887335369248157338869)
                    ·
                      rfl

theorem cell22_525494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_525494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_525494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_525494 prefixEnd_525494 := by exact prefixLift 525494
  have htrace : WordTrace (prefixWord ++ tailWord_525494) baseStart_525494 baseEnd_525494 := by
    simpa [prefixWord, tailWord_525494, baseEnd_525494] using wordTrace_append hprefix tailTrace_525494
  have hstable : (prefixWord ++ tailWord_525494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525494).length < 2 ^ (prefixWord ++ tailWord_525494).sum := by decide
  have hdescent : baseEnd_525494 < baseStart_525494 := by decide
  rcases family_descends (prefixWord ++ tailWord_525494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525550 : List Nat := [4, 1, 2, 1, 1, 1, 2, 5, 1, 4]
def baseStart_525550 : Nat := 118140960795 + 525550 * 2 ^ 59
def prefixEnd_525550 : Nat := 4983230072969 + 3 ^ 40 * 525550 * 2
def baseEnd_525550 : Nat := 179906505313682677938697

theorem tailTrace_525550 : CollatzResearch.WordTrace tailWord_525550 prefixEnd_525550 179906505313682677938697 := by
  unfold tailWord_525550
  simp only [CollatzResearch.WordTrace]
  refine ⟨2396047905753697704900763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12778922164019721092804069 2396047905753697704900763)
  ·
    refine ⟨3594071858630546557351145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2396047905753697704900763 3594071858630546557351145)
    ·
      refine ⟨2695553893972909918013359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3594071858630546557351145 2695553893972909918013359)
      ·
        refine ⟨4043330840959364877020039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2695553893972909918013359 4043330840959364877020039)
        ·
          refine ⟨6064996261439047315530059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4043330840959364877020039 6064996261439047315530059)
          ·
            refine ⟨9097494392158570973295089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6064996261439047315530059 9097494392158570973295089)
            ·
              refine ⟨6823120794118928229971317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9097494392158570973295089 6823120794118928229971317)
              ·
                refine ⟨639667574448649521559811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6823120794118928229971317 639667574448649521559811)
                ·
                  refine ⟨959501361672974282339717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 639667574448649521559811 959501361672974282339717)
                  ·
                    refine ⟨179906505313682677938697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 959501361672974282339717 179906505313682677938697)
                    ·
                      rfl

theorem cell22_525550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_525550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_525550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_525550 prefixEnd_525550 := by exact prefixLift 525550
  have htrace : WordTrace (prefixWord ++ tailWord_525550) baseStart_525550 baseEnd_525550 := by
    simpa [prefixWord, tailWord_525550, baseEnd_525550] using wordTrace_append hprefix tailTrace_525550
  have hstable : (prefixWord ++ tailWord_525550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525550).length < 2 ^ (prefixWord ++ tailWord_525550).sum := by decide
  have hdescent : baseEnd_525550 < baseStart_525550 := by decide
  rcases family_descends (prefixWord ++ tailWord_525550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525578 : List Nat := [3, 1, 2, 2, 1, 1, 1, 4, 1, 6]
def baseStart_525578 : Nat := 118140960795 + 525578 * 2 ^ 59
def prefixEnd_525578 : Nat := 4983230072969 + 3 ^ 40 * 525578 * 2
def baseEnd_525578 : Nat := 179916090285899938238611

theorem tailTrace_525578 : CollatzResearch.WordTrace tailWord_525578 prefixEnd_525578 179916090285899938238611 := by
  unfold tailWord_525578
  simp only [CollatzResearch.WordTrace]
  refine ⟨4792351122482035605306347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12779602993285428280816925 4792351122482035605306347)
  ·
    refine ⟨7188526683723053407959521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4792351122482035605306347 7188526683723053407959521)
    ·
      refine ⟨5391395012792290055969641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7188526683723053407959521 5391395012792290055969641)
      ·
        refine ⟨4043546259594217541977231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5391395012792290055969641 4043546259594217541977231)
        ·
          refine ⟨6065319389391326312965847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4043546259594217541977231 6065319389391326312965847)
          ·
            refine ⟨9097979084086989469448771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6065319389391326312965847 9097979084086989469448771)
            ·
              refine ⟨13646968626130484204173157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9097979084086989469448771 13646968626130484204173157)
              ·
                refine ⟨2558806617399465788282467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13646968626130484204173157 2558806617399465788282467)
                ·
                  refine ⟨3838209926099198682423701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2558806617399465788282467 3838209926099198682423701)
                  ·
                    refine ⟨179916090285899938238611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3838209926099198682423701 179916090285899938238611)
                    ·
                      rfl

theorem cell22_525578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 4, 1, 6].length) (baseStart_525578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_525578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_525578 prefixEnd_525578 := by exact prefixLift 525578
  have htrace : WordTrace (prefixWord ++ tailWord_525578) baseStart_525578 baseEnd_525578 := by
    simpa [prefixWord, tailWord_525578, baseEnd_525578] using wordTrace_append hprefix tailTrace_525578
  have hstable : (prefixWord ++ tailWord_525578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525578).length < 2 ^ (prefixWord ++ tailWord_525578).sum := by decide
  have hdescent : baseEnd_525578 < baseStart_525578 := by decide
  rcases family_descends (prefixWord ++ tailWord_525578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525580 : List Nat := [2, 2, 1, 2, 2, 4, 2, 1, 1, 5]
def baseStart_525580 : Nat := 118140960795 + 525580 * 2 ^ 59
def prefixEnd_525580 : Nat := 4983230072969 + 3 ^ 40 * 525580 * 2
def baseEnd_525580 : Nat := 179916774926772599688605

theorem tailTrace_525580 : CollatzResearch.WordTrace tailWord_525580 prefixEnd_525580 179916774926772599688605 := by
  unfold tailWord_525580
  simp only [CollatzResearch.WordTrace]
  refine ⟨9584738717960448381399097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12779651623947264508532129 9584738717960448381399097)
  ·
    refine ⟨7188554038470336286049323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9584738717960448381399097 7188554038470336286049323)
    ·
      refine ⟨10782831057705504429073985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7188554038470336286049323 10782831057705504429073985)
      ·
        refine ⟨8087123293279128321805489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10782831057705504429073985 8087123293279128321805489)
        ·
          refine ⟨6065342469959346241354117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8087123293279128321805489 6065342469959346241354117)
          ·
            refine ⟨1137251713117377420253897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6065342469959346241354117 1137251713117377420253897)
            ·
              refine ⟨852938784838033065190423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1137251713117377420253897 852938784838033065190423)
              ·
                refine ⟨1279408177257049597785635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 852938784838033065190423 1279408177257049597785635)
                ·
                  refine ⟨1919112265885574396678453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1279408177257049597785635 1919112265885574396678453)
                  ·
                    refine ⟨179916774926772599688605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1919112265885574396678453 179916774926772599688605)
                    ·
                      rfl

theorem cell22_525580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 1, 1, 5].length) (baseStart_525580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_525580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_525580 prefixEnd_525580 := by exact prefixLift 525580
  have htrace : WordTrace (prefixWord ++ tailWord_525580) baseStart_525580 baseEnd_525580 := by
    simpa [prefixWord, tailWord_525580, baseEnd_525580] using wordTrace_append hprefix tailTrace_525580
  have hstable : (prefixWord ++ tailWord_525580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525580).length < 2 ^ (prefixWord ++ tailWord_525580).sum := by decide
  have hdescent : baseEnd_525580 < baseStart_525580 := by decide
  rcases family_descends (prefixWord ++ tailWord_525580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525610 : List Nat := [3, 1, 4, 2, 1, 2, 9]
def baseStart_525610 : Nat := 118140960795 + 525610 * 2 ^ 59
def prefixEnd_525610 : Nat := 4983230072969 + 3 ^ 40 * 525610 * 2
def baseEnd_525610 : Nat := 6663964612587500794019

theorem tailTrace_525610 : CollatzResearch.WordTrace tailWord_525610 prefixEnd_525610 6663964612587500794019 := by
  unfold tailWord_525610
  simp only [CollatzResearch.WordTrace]
  refine ⟨4792642906453052971597571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12780381083874807924260189 4792642906453052971597571)
  ·
    refine ⟨7188964359679579457396357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4792642906453052971597571 7188964359679579457396357)
    ·
      refine ⟨1347930817439921148261817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7188964359679579457396357 1347930817439921148261817)
      ·
        refine ⟨1010948113079940861196363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1347930817439921148261817 1010948113079940861196363)
        ·
          refine ⟨1516422169619911291794545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1010948113079940861196363 1516422169619911291794545)
          ·
            refine ⟨1137316627214933468845909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1516422169619911291794545 1137316627214933468845909)
            ·
              refine ⟨6663964612587500794019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1137316627214933468845909 6663964612587500794019)
              ·
                rfl

theorem cell22_525610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 9].length) (baseStart_525610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_525610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_525610 prefixEnd_525610 := by exact prefixLift 525610
  have htrace : WordTrace (prefixWord ++ tailWord_525610) baseStart_525610 baseEnd_525610 := by
    simpa [prefixWord, tailWord_525610, baseEnd_525610] using wordTrace_append hprefix tailTrace_525610
  have hstable : (prefixWord ++ tailWord_525610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525610).length < 2 ^ (prefixWord ++ tailWord_525610).sum := by decide
  have hdescent : baseEnd_525610 < baseStart_525610 := by decide
  rcases family_descends (prefixWord ++ tailWord_525610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525661 : List Nat := [1, 4, 5, 1, 2, 1, 8]
def baseStart_525661 : Nat := 118140960795 + 525661 * 2 ^ 59
def prefixEnd_525661 : Nat := 4983230072969 + 3 ^ 40 * 525661 * 2
def baseEnd_525661 : Nat := 6664611217856125496791

theorem tailTrace_525661 : CollatzResearch.WordTrace tailWord_525661 prefixEnd_525661 6664611217856125496791 := by
  unfold tailWord_525661
  simp only [CollatzResearch.WordTrace]
  refine ⟨19172431748627447596496837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12781621165751631730997891 19172431748627447596496837)
  ·
    refine ⟨3594830952867646424343157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19172431748627447596496837 3594830952867646424343157)
    ·
      refine ⟨337015401831341852282171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3594830952867646424343157 337015401831341852282171)
      ·
        refine ⟨505523102747012778423257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337015401831341852282171 505523102747012778423257)
        ·
          refine ⟨379142327060259583817443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 505523102747012778423257 379142327060259583817443)
          ·
            refine ⟨568713490590389375726165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 379142327060259583817443 568713490590389375726165)
            ·
              refine ⟨6664611217856125496791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 568713490590389375726165 6664611217856125496791)
              ·
                rfl

theorem cell22_525661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 8].length) (baseStart_525661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_525661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_525661 prefixEnd_525661 := by exact prefixLift 525661
  have htrace : WordTrace (prefixWord ++ tailWord_525661) baseStart_525661 baseEnd_525661 := by
    simpa [prefixWord, tailWord_525661, baseEnd_525661] using wordTrace_append hprefix tailTrace_525661
  have hstable : (prefixWord ++ tailWord_525661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525661).length < 2 ^ (prefixWord ++ tailWord_525661).sum := by decide
  have hdescent : baseEnd_525661 < baseStart_525661 := by decide
  rcases family_descends (prefixWord ++ tailWord_525661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525676 : List Nat := [2, 2, 1, 1, 5, 2, 3, 2, 1, 3]
def baseStart_525676 : Nat := 118140960795 + 525676 * 2 ^ 59
def prefixEnd_525676 : Nat := 4983230072969 + 3 ^ 40 * 525676 * 2
def baseEnd_525676 : Nat := 179949637688660349288311

theorem tailTrace_525676 : CollatzResearch.WordTrace tailWord_525676 prefixEnd_525676 179949637688660349288311 := by
  unfold tailWord_525676
  simp only [CollatzResearch.WordTrace]
  refine ⟨9586489421786552579146441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12781985895715403438861921 9586489421786552579146441)
  ·
    refine ⟨7189867066339914434359831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9586489421786552579146441 7189867066339914434359831)
    ·
      refine ⟨10784800599509871651539747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7189867066339914434359831 10784800599509871651539747)
      ·
        refine ⟨16177200899264807477309621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10784800599509871651539747 16177200899264807477309621)
        ·
          refine ⟨1516612584306075700997777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16177200899264807477309621 1516612584306075700997777)
          ·
            refine ⟨1137459438229556775748333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1516612584306075700997777 1137459438229556775748333)
            ·
              refine ⟨426547289336083790905625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1137459438229556775748333 426547289336083790905625)
              ·
                refine ⟨319910467002062843179219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 426547289336083790905625 319910467002062843179219)
                ·
                  refine ⟨479865700503094264768829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 319910467002062843179219 479865700503094264768829)
                  ·
                    refine ⟨179949637688660349288311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 479865700503094264768829 179949637688660349288311)
                    ·
                      rfl

theorem cell22_525676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 3, 2, 1, 3].length) (baseStart_525676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_525676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_525676 prefixEnd_525676 := by exact prefixLift 525676
  have htrace : WordTrace (prefixWord ++ tailWord_525676) baseStart_525676 baseEnd_525676 := by
    simpa [prefixWord, tailWord_525676, baseEnd_525676] using wordTrace_append hprefix tailTrace_525676
  have hstable : (prefixWord ++ tailWord_525676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525676).length < 2 ^ (prefixWord ++ tailWord_525676).sum := by decide
  have hdescent : baseEnd_525676 < baseStart_525676 := by decide
  rcases family_descends (prefixWord ++ tailWord_525676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525749 : List Nat := [1, 3, 3, 2, 2, 1, 2, 3, 2, 3]
def baseStart_525749 : Nat := 118140960795 + 525749 * 2 ^ 59
def prefixEnd_525749 : Nat := 4983230072969 + 3 ^ 40 * 525749 * 2
def baseEnd_525749 : Nat := 179974627080512492213087

theorem tailTrace_525749 : CollatzResearch.WordTrace tailWord_525749 prefixEnd_525749 179974627080512492213087 := by
  unfold tailWord_525749
  simp only [CollatzResearch.WordTrace]
  refine ⟨19175641372308638625700301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12783760914872425750466867 19175641372308638625700301)
  ·
    refine ⟨7190865514615739484637613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19175641372308638625700301 7190865514615739484637613)
    ·
      refine ⟨2696574567980902306739105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7190865514615739484637613 2696574567980902306739105)
      ·
        refine ⟨2022430925985676730054329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2696574567980902306739105 2022430925985676730054329)
        ·
          refine ⟨1516823194489257547540747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2022430925985676730054329 1516823194489257547540747)
          ·
            refine ⟨2275234791733886321311121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1516823194489257547540747 2275234791733886321311121)
            ·
              refine ⟨1706426093800414740983341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2275234791733886321311121 1706426093800414740983341)
              ·
                refine ⟨639909785175155527868753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1706426093800414740983341 639909785175155527868753)
                ·
                  refine ⟨479932338881366645901565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 639909785175155527868753 479932338881366645901565)
                  ·
                    refine ⟨179974627080512492213087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 479932338881366645901565 179974627080512492213087)
                    ·
                      rfl

theorem cell22_525749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 3, 2, 3].length) (baseStart_525749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_525749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_525749 prefixEnd_525749 := by exact prefixLift 525749
  have htrace : WordTrace (prefixWord ++ tailWord_525749) baseStart_525749 baseEnd_525749 := by
    simpa [prefixWord, tailWord_525749, baseEnd_525749] using wordTrace_append hprefix tailTrace_525749
  have hstable : (prefixWord ++ tailWord_525749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525749).length < 2 ^ (prefixWord ++ tailWord_525749).sum := by decide
  have hdescent : baseEnd_525749 < baseStart_525749 := by decide
  rcases family_descends (prefixWord ++ tailWord_525749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525764 : List Nat := [2, 3, 3, 2, 1, 1, 3, 1, 2, 4]
def baseStart_525764 : Nat := 118140960795 + 525764 * 2 ^ 59
def prefixEnd_525764 : Nat := 4983230072969 + 3 ^ 40 * 525764 * 2
def baseEnd_525764 : Nat := 179979761887057453088041

theorem tailTrace_525764 : CollatzResearch.WordTrace tailWord_525764 prefixEnd_525764 179979761887057453088041 := by
  unfold tailWord_525764
  simp only [CollatzResearch.WordTrace]
  refine ⟨9588094233627148093748173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12784125644836197458330897 9588094233627148093748173)
  ·
    refine ⟨3595535337610180535155565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9588094233627148093748173 3595535337610180535155565)
    ·
      refine ⟨1348325751603817700683337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3595535337610180535155565 1348325751603817700683337)
      ·
        refine ⟨1011244313702863275512503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1348325751603817700683337 1011244313702863275512503)
        ·
          refine ⟨1516866470554294913268755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1011244313702863275512503 1516866470554294913268755)
          ·
            refine ⟨2275299705831442369903133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1516866470554294913268755 2275299705831442369903133)
            ·
              refine ⟨853237389686790888713675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2275299705831442369903133 853237389686790888713675)
              ·
                refine ⟨1279856084530186333070513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 853237389686790888713675 1279856084530186333070513)
                ·
                  refine ⟨959892063397639749802885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1279856084530186333070513 959892063397639749802885)
                  ·
                    refine ⟨179979761887057453088041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 959892063397639749802885 179979761887057453088041)
                    ·
                      rfl

theorem cell22_525764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_525764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_525764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_525764 prefixEnd_525764 := by exact prefixLift 525764
  have htrace : WordTrace (prefixWord ++ tailWord_525764) baseStart_525764 baseEnd_525764 := by
    simpa [prefixWord, tailWord_525764, baseEnd_525764] using wordTrace_append hprefix tailTrace_525764
  have hstable : (prefixWord ++ tailWord_525764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525764).length < 2 ^ (prefixWord ++ tailWord_525764).sum := by decide
  have hdescent : baseEnd_525764 < baseStart_525764 := by decide
  rcases family_descends (prefixWord ++ tailWord_525764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525884 : List Nat := [2, 2, 2, 2, 4, 1, 1, 2, 1, 5]
def baseStart_525884 : Nat := 118140960795 + 525884 * 2 ^ 59
def prefixEnd_525884 : Nat := 4983230072969 + 3 ^ 40 * 525884 * 2
def baseEnd_525884 : Nat := 180020840339417140087673

theorem tailTrace_525884 : CollatzResearch.WordTrace tailWord_525884 prefixEnd_525884 180020840339417140087673 := by
  unfold tailWord_525884
  simp only [CollatzResearch.WordTrace]
  refine ⟨9590282613409778340932353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12787043484546371121243137 9590282613409778340932353)
  ·
    refine ⟨7192711960057333755699265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9590282613409778340932353 7192711960057333755699265)
    ·
      refine ⟨5394533970043000316774449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7192711960057333755699265 5394533970043000316774449)
      ·
        refine ⟨4045900477532250237580837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5394533970043000316774449 4045900477532250237580837)
        ·
          refine ⟨758606339537296919546407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4045900477532250237580837 758606339537296919546407)
          ·
            refine ⟨1137909509305945379319611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 758606339537296919546407 1137909509305945379319611)
            ·
              refine ⟨1706864263958918068979417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1137909509305945379319611 1706864263958918068979417)
              ·
                refine ⟨1280148197969188551734563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1706864263958918068979417 1280148197969188551734563)
                ·
                  refine ⟨1920222296953782827601845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1280148197969188551734563 1920222296953782827601845)
                  ·
                    refine ⟨180020840339417140087673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1920222296953782827601845 180020840339417140087673)
                    ·
                      rfl

theorem cell22_525884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 2, 1, 5].length) (baseStart_525884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_525884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_525884 prefixEnd_525884 := by exact prefixLift 525884
  have htrace : WordTrace (prefixWord ++ tailWord_525884) baseStart_525884 baseEnd_525884 := by
    simpa [prefixWord, tailWord_525884, baseEnd_525884] using wordTrace_append hprefix tailTrace_525884
  have hstable : (prefixWord ++ tailWord_525884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525884).length < 2 ^ (prefixWord ++ tailWord_525884).sum := by decide
  have hdescent : baseEnd_525884 < baseStart_525884 := by decide
  rcases family_descends (prefixWord ++ tailWord_525884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525933 : List Nat := [1, 5, 1, 1, 5, 1, 1, 1, 2, 4]
def baseStart_525933 : Nat := 118140960795 + 525933 * 2 ^ 59
def prefixEnd_525933 : Nat := 4983230072969 + 3 ^ 40 * 525933 * 2
def baseEnd_525933 : Nat := 180037614040797345612523

theorem tailTrace_525933 : CollatzResearch.WordTrace tailWord_525933 prefixEnd_525933 180037614040797345612523 := by
  unfold tailWord_525933
  simp only [CollatzResearch.WordTrace]
  refine ⟨19182352403642038050398453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12788234935761358700265635 19182352403642038050398453)
  ·
    refine ⟨1798345537841441067224855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19182352403642038050398453 1798345537841441067224855)
    ·
      refine ⟨2697518306762161600837283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1798345537841441067224855 2697518306762161600837283)
      ·
        refine ⟨4046277460143242401255925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2697518306762161600837283 4046277460143242401255925)
        ·
          refine ⟨379338511888428975117743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4046277460143242401255925 379338511888428975117743)
          ·
            refine ⟨569007767832643462676615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 379338511888428975117743 569007767832643462676615)
            ·
              refine ⟨853511651748965194014923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 569007767832643462676615 853511651748965194014923)
              ·
                refine ⟨1280267477623447791022385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 853511651748965194014923 1280267477623447791022385)
                ·
                  refine ⟨960200608217585843266789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1280267477623447791022385 960200608217585843266789)
                  ·
                    refine ⟨180037614040797345612523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 960200608217585843266789 180037614040797345612523)
                    ·
                      rfl

theorem cell22_525933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 1, 2, 4].length) (baseStart_525933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_525933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_525933 prefixEnd_525933 := by exact prefixLift 525933
  have htrace : WordTrace (prefixWord ++ tailWord_525933) baseStart_525933 baseEnd_525933 := by
    simpa [prefixWord, tailWord_525933, baseEnd_525933] using wordTrace_append hprefix tailTrace_525933
  have hstable : (prefixWord ++ tailWord_525933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525933).length < 2 ^ (prefixWord ++ tailWord_525933).sum := by decide
  have hdescent : baseEnd_525933 < baseStart_525933 := by decide
  rcases family_descends (prefixWord ++ tailWord_525933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525957 : List Nat := [1, 3, 1, 1, 4, 1, 1, 1, 4, 5]
def baseStart_525957 : Nat := 118140960795 + 525957 * 2 ^ 59
def prefixEnd_525957 : Nat := 4983230072969 + 3 ^ 40 * 525957 * 2
def baseEnd_525957 : Nat := 180045829731269283012449

theorem tailTrace_525957 : CollatzResearch.WordTrace tailWord_525957 prefixEnd_525957 180045829731269283012449 := by
  unfold tailWord_525957
  simp only [CollatzResearch.WordTrace]
  refine ⟨19183227755555090149272125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12788818503703393432848083 19183227755555090149272125)
  ·
    refine ⟨7193710408333158805977047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19183227755555090149272125 7193710408333158805977047)
    ·
      refine ⟨10790565612499738208965571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7193710408333158805977047 10790565612499738208965571)
      ·
        refine ⟨16185848418749607313448357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10790565612499738208965571 16185848418749607313448357)
        ·
          refine ⟨3034846578515551371271567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16185848418749607313448357 3034846578515551371271567)
          ·
            refine ⟨4552269867773327056907351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3034846578515551371271567 4552269867773327056907351)
            ·
              refine ⟨6828404801659990585361027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4552269867773327056907351 6828404801659990585361027)
              ·
                refine ⟨10242607202489985878041541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6828404801659990585361027 10242607202489985878041541)
                ·
                  refine ⟨1920488850466872352132789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10242607202489985878041541 1920488850466872352132789)
                  ·
                    refine ⟨180045829731269283012449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1920488850466872352132789 180045829731269283012449)
                    ·
                      rfl

theorem cell22_525957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 4, 5].length) (baseStart_525957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_525957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_525957 prefixEnd_525957 := by exact prefixLift 525957
  have htrace : WordTrace (prefixWord ++ tailWord_525957) baseStart_525957 baseEnd_525957 := by
    simpa [prefixWord, tailWord_525957, baseEnd_525957] using wordTrace_append hprefix tailTrace_525957
  have hstable : (prefixWord ++ tailWord_525957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525957).length < 2 ^ (prefixWord ++ tailWord_525957).sum := by decide
  have hdescent : baseEnd_525957 < baseStart_525957 := by decide
  rcases family_descends (prefixWord ++ tailWord_525957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525959 : List Nat := [1, 1, 4, 2, 1, 3, 3, 2, 5]
def baseStart_525959 : Nat := 118140960795 + 525959 * 2 ^ 59
def prefixEnd_525959 : Nat := 4983230072969 + 3 ^ 40 * 525959 * 2
def baseEnd_525959 : Nat := 60015504790713981487481

theorem tailTrace_525959 : CollatzResearch.WordTrace tailWord_525959 prefixEnd_525959 60015504790713981487481 := by
  unfold tailWord_525959
  simp only [CollatzResearch.WordTrace]
  refine ⟨19183300701547844490844931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12788867134365229660563287 19183300701547844490844931)
  ·
    refine ⟨28774951052321766736267397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19183300701547844490844931 28774951052321766736267397)
    ·
      refine ⟨5395303322310331263050137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28774951052321766736267397 5395303322310331263050137)
      ·
        refine ⟨4046477491732748447287603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5395303322310331263050137 4046477491732748447287603)
        ·
          refine ⟨6069716237599122670931405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4046477491732748447287603 6069716237599122670931405)
          ·
            refine ⟨2276143589099671001599277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6069716237599122670931405 2276143589099671001599277)
            ·
              refine ⟨853553845912376625599729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2276143589099671001599277 853553845912376625599729)
              ·
                refine ⟨640165384434282469199797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 853553845912376625599729 640165384434282469199797)
                ·
                  refine ⟨60015504790713981487481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 640165384434282469199797 60015504790713981487481)
                  ·
                    rfl

theorem cell22_525959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 2, 5].length) (baseStart_525959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_525959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_525959 prefixEnd_525959 := by exact prefixLift 525959
  have htrace : WordTrace (prefixWord ++ tailWord_525959) baseStart_525959 baseEnd_525959 := by
    simpa [prefixWord, tailWord_525959, baseEnd_525959] using wordTrace_append hprefix tailTrace_525959
  have hstable : (prefixWord ++ tailWord_525959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525959).length < 2 ^ (prefixWord ++ tailWord_525959).sum := by decide
  have hdescent : baseEnd_525959 < baseStart_525959 := by decide
  rcases family_descends (prefixWord ++ tailWord_525959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525976 : List Nat := [2, 1, 2, 4, 1, 3, 3, 1, 5]
def baseStart_525976 : Nat := 118140960795 + 525976 * 2 ^ 59
def prefixEnd_525976 : Nat := 4983230072969 + 3 ^ 40 * 525976 * 2
def baseEnd_525976 : Nat := 60017444606519855595797

theorem tailTrace_525976 : CollatzResearch.WordTrace tailWord_525976 prefixEnd_525976 60017444606519855595797 := by
  unfold tailWord_525976
  simp only [CollatzResearch.WordTrace]
  refine ⟨9591960371243128197106891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12789280494990837596142521 9591960371243128197106891)
  ·
    refine ⟨14387940556864692295660337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9591960371243128197106891 14387940556864692295660337)
    ·
      refine ⟨10790955417648519221745253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14387940556864692295660337 10790955417648519221745253)
      ·
        refine ⟨2023304140809097354077235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10790955417648519221745253 2023304140809097354077235)
        ·
          refine ⟨3034956211213646031115853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2023304140809097354077235 3034956211213646031115853)
          ·
            refine ⟨1138108579205117261668445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3034956211213646031115853 1138108579205117261668445)
            ·
              refine ⟨426790717201918973125667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1138108579205117261668445 426790717201918973125667)
              ·
                refine ⟨640186075802878459688501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 426790717201918973125667 640186075802878459688501)
                ·
                  refine ⟨60017444606519855595797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 640186075802878459688501 60017444606519855595797)
                  ·
                    rfl

theorem cell22_525976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 3, 1, 5].length) (baseStart_525976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_525976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_525976 prefixEnd_525976 := by exact prefixLift 525976
  have htrace : WordTrace (prefixWord ++ tailWord_525976) baseStart_525976 baseEnd_525976 := by
    simpa [prefixWord, tailWord_525976, baseEnd_525976] using wordTrace_append hprefix tailTrace_525976
  have hstable : (prefixWord ++ tailWord_525976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525976).length < 2 ^ (prefixWord ++ tailWord_525976).sum := by decide
  have hdescent : baseEnd_525976 < baseStart_525976 := by decide
  rcases family_descends (prefixWord ++ tailWord_525976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525987 : List Nat := [1, 1, 1, 4, 1, 1, 3, 4, 6]
def baseStart_525987 : Nat := 118140960795 + 525987 * 2 ^ 59
def prefixEnd_525987 : Nat := 4983230072969 + 3 ^ 40 * 525987 * 2
def baseEnd_525987 : Nat := 60018699781453068254119

theorem tailTrace_525987 : CollatzResearch.WordTrace tailWord_525987 prefixEnd_525987 60018699781453068254119 := by
  unfold tailWord_525987
  simp only [CollatzResearch.WordTrace]
  refine ⟨19184321945446405272864215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12789547963630936848576143 19184321945446405272864215)
  ·
    refine ⟨28776482918169607909296323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19184321945446405272864215 28776482918169607909296323)
    ·
      refine ⟨43164724377254411863944485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28776482918169607909296323 43164724377254411863944485)
      ·
        refine ⟨8093385820735202224489591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43164724377254411863944485 8093385820735202224489591)
        ·
          refine ⟨12140078731102803336734387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8093385820735202224489591 12140078731102803336734387)
          ·
            refine ⟨18210118096654205005101581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12140078731102803336734387 18210118096654205005101581)
            ·
              refine ⟨6828794286245326876913093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18210118096654205005101581 6828794286245326876913093)
              ·
                refine ⟨1280398928670998789421205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6828794286245326876913093 1280398928670998789421205)
                ·
                  refine ⟨60018699781453068254119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1280398928670998789421205 60018699781453068254119)
                  ·
                    rfl

theorem cell22_525987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 4, 6].length) (baseStart_525987 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_525987 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_525987 prefixEnd_525987 := by exact prefixLift 525987
  have htrace : WordTrace (prefixWord ++ tailWord_525987) baseStart_525987 baseEnd_525987 := by
    simpa [prefixWord, tailWord_525987, baseEnd_525987] using wordTrace_append hprefix tailTrace_525987
  have hstable : (prefixWord ++ tailWord_525987).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525987).length < 2 ^ (prefixWord ++ tailWord_525987).sum := by decide
  have hdescent : baseEnd_525987 < baseStart_525987 := by decide
  rcases family_descends (prefixWord ++ tailWord_525987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525989 : List Nat := [1, 3, 1, 2, 1, 2, 3, 4, 1, 4]
def baseStart_525989 : Nat := 118140960795 + 525989 * 2 ^ 59
def prefixEnd_525989 : Nat := 4983230072969 + 3 ^ 40 * 525989 * 2
def baseEnd_525989 : Nat := 180056783985231866212351

theorem tailTrace_525989 : CollatzResearch.WordTrace tailWord_525989 prefixEnd_525989 180056783985231866212351 := by
  unfold tailWord_525989
  simp only [CollatzResearch.WordTrace]
  refine ⟨19184394891439159614437021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12789596594292773076291347 19184394891439159614437021)
  ·
    refine ⟨7194148084289684855413883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19184394891439159614437021 7194148084289684855413883)
    ·
      refine ⟨10791222126434527283120825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7194148084289684855413883 10791222126434527283120825)
      ·
        refine ⟨8093416594825895462340619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10791222126434527283120825 8093416594825895462340619)
        ·
          refine ⟨12140124892238843193510929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8093416594825895462340619 12140124892238843193510929)
          ·
            refine ⟨9105093669179132395133197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12140124892238843193510929 9105093669179132395133197)
            ·
              refine ⟨3414410125942174648174949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9105093669179132395133197 3414410125942174648174949)
              ·
                refine ⟨640201898614157746532803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3414410125942174648174949 640201898614157746532803)
                ·
                  refine ⟨960302847921236619799205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 640201898614157746532803 960302847921236619799205)
                  ·
                    refine ⟨180056783985231866212351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 960302847921236619799205 180056783985231866212351)
                    ·
                      rfl

theorem cell22_525989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 4, 1, 4].length) (baseStart_525989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_525989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_525989 prefixEnd_525989 := by exact prefixLift 525989
  have htrace : WordTrace (prefixWord ++ tailWord_525989) baseStart_525989 baseEnd_525989 := by
    simpa [prefixWord, tailWord_525989, baseEnd_525989] using wordTrace_append hprefix tailTrace_525989
  have hstable : (prefixWord ++ tailWord_525989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525989).length < 2 ^ (prefixWord ++ tailWord_525989).sum := by decide
  have hdescent : baseEnd_525989 < baseStart_525989 := by decide
  rcases family_descends (prefixWord ++ tailWord_525989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526064 : List Nat := [2, 1, 1, 1, 3, 1, 2, 1, 7, 3]
def baseStart_526064 : Nat := 118140960795 + 526064 * 2 ^ 59
def prefixEnd_526064 : Nat := 4983230072969 + 3 ^ 40 * 526064 * 2
def baseEnd_526064 : Nat := 180082458017956670587121

theorem tailTrace_526064 : CollatzResearch.WordTrace tailWord_526064 prefixEnd_526064 180082458017956670587121 := by
  unfold tailWord_526064
  simp only [CollatzResearch.WordTrace]
  refine ⟨9593565183083723711708623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12791420244111631615611497 9593565183083723711708623)
  ·
    refine ⟨14390347774625585567562935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9593565183083723711708623 14390347774625585567562935)
    ·
      refine ⟨21585521661938378351344403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14390347774625585567562935 21585521661938378351344403)
      ·
        refine ⟨32378282492907567527016605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21585521661938378351344403 32378282492907567527016605)
        ·
          refine ⟨12141855934840337822631227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32378282492907567527016605 12141855934840337822631227)
          ·
            refine ⟨18212783902260506733946841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12141855934840337822631227 18212783902260506733946841)
            ·
              refine ⟨13659587926695380050460131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18212783902260506733946841 13659587926695380050460131)
              ·
                refine ⟨20489381890043070075690197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13659587926695380050460131 20489381890043070075690197)
                ·
                  refine ⟨480219888047884454898989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20489381890043070075690197 480219888047884454898989)
                  ·
                    refine ⟨180082458017956670587121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 480219888047884454898989 180082458017956670587121)
                    ·
                      rfl

theorem cell22_526064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 7, 3].length) (baseStart_526064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_526064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_526064 prefixEnd_526064 := by exact prefixLift 526064
  have htrace : WordTrace (prefixWord ++ tailWord_526064) baseStart_526064 baseEnd_526064 := by
    simpa [prefixWord, tailWord_526064, baseEnd_526064] using wordTrace_append hprefix tailTrace_526064
  have hstable : (prefixWord ++ tailWord_526064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526064).length < 2 ^ (prefixWord ++ tailWord_526064).sum := by decide
  have hdescent : baseEnd_526064 < baseStart_526064 := by decide
  rcases family_descends (prefixWord ++ tailWord_526064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526098 : List Nat := [3, 2, 4, 1, 1, 1, 1, 1, 5, 3]
def baseStart_526098 : Nat := 118140960795 + 526098 * 2 ^ 59
def prefixEnd_526098 : Nat := 4983230072969 + 3 ^ 40 * 526098 * 2
def baseEnd_526098 : Nat := 180094096912791915237017

theorem tailTrace_526098 : CollatzResearch.WordTrace tailWord_526098 prefixEnd_526098 180094096912791915237017 := by
  unfold tailWord_526098
  simp only [CollatzResearch.WordTrace]
  refine ⟨4797092612011067807538737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12792246965362847486769965 4797092612011067807538737)
  ·
    refine ⟨3597819459008300855654053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4797092612011067807538737 3597819459008300855654053)
    ·
      refine ⟨674591148564056410435135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3597819459008300855654053 674591148564056410435135)
      ·
        refine ⟨1011886722846084615652703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 674591148564056410435135 1011886722846084615652703)
        ·
          refine ⟨1517830084269126923479055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1011886722846084615652703 1517830084269126923479055)
          ·
            refine ⟨2276745126403690385218583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1517830084269126923479055 2276745126403690385218583)
            ·
              refine ⟨3415117689605535577827875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2276745126403690385218583 3415117689605535577827875)
              ·
                refine ⟨5122676534408303366741813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3415117689605535577827875 5122676534408303366741813)
                ·
                  refine ⟨480250925100778440632045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5122676534408303366741813 480250925100778440632045)
                  ·
                    refine ⟨180094096912791915237017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 480250925100778440632045 180094096912791915237017)
                    ·
                      rfl

theorem cell22_526098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_526098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_526098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_526098 prefixEnd_526098 := by exact prefixLift 526098
  have htrace : WordTrace (prefixWord ++ tailWord_526098) baseStart_526098 baseEnd_526098 := by
    simpa [prefixWord, tailWord_526098, baseEnd_526098] using wordTrace_append hprefix tailTrace_526098
  have hstable : (prefixWord ++ tailWord_526098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526098).length < 2 ^ (prefixWord ++ tailWord_526098).sum := by decide
  have hdescent : baseEnd_526098 < baseStart_526098 := by decide
  rcases family_descends (prefixWord ++ tailWord_526098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526169 : List Nat := [1, 2, 1, 2, 2, 3, 1, 3, 1, 6]
def baseStart_526169 : Nat := 118140960795 + 526169 * 2 ^ 59
def prefixEnd_526169 : Nat := 4983230072969 + 3 ^ 40 * 526169 * 2
def baseEnd_526169 : Nat := 180118401663771396711799

theorem tailTrace_526169 : CollatzResearch.WordTrace tailWord_526169 prefixEnd_526169 180118401663771396711799 := by
  unfold tailWord_526169
  simp only [CollatzResearch.WordTrace]
  refine ⟨19190960030787050355989561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12793973353858033570659707 19190960030787050355989561)
  ·
    refine ⟨14393220023090287766992171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19190960030787050355989561 14393220023090287766992171)
    ·
      refine ⟨21589830034635431650488257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14393220023090287766992171 21589830034635431650488257)
      ·
        refine ⟨16192372525976573737866193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21589830034635431650488257 16192372525976573737866193)
        ·
          refine ⟨12144279394482430303399645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16192372525976573737866193 12144279394482430303399645)
          ·
            refine ⟨4554104772930911363774867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12144279394482430303399645 4554104772930911363774867)
            ·
              refine ⟨6831157159396367045662301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4554104772930911363774867 6831157159396367045662301)
              ·
                refine ⟨2561683934773637642123363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6831157159396367045662301 2561683934773637642123363)
                ·
                  refine ⟨3842525902160456463185045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2561683934773637642123363 3842525902160456463185045)
                  ·
                    refine ⟨180118401663771396711799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3842525902160456463185045 180118401663771396711799)
                    ·
                      rfl

theorem cell22_526169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 3, 1, 6].length) (baseStart_526169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_526169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_526169 prefixEnd_526169 := by exact prefixLift 526169
  have htrace : WordTrace (prefixWord ++ tailWord_526169) baseStart_526169 baseEnd_526169 := by
    simpa [prefixWord, tailWord_526169, baseEnd_526169] using wordTrace_append hprefix tailTrace_526169
  have hstable : (prefixWord ++ tailWord_526169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526169).length < 2 ^ (prefixWord ++ tailWord_526169).sum := by decide
  have hdescent : baseEnd_526169 < baseStart_526169 := by decide
  rcases family_descends (prefixWord ++ tailWord_526169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526261 : List Nat := [1, 3, 3, 2, 1, 2, 1, 1, 1, 7]
def baseStart_526261 : Nat := 118140960795 + 526261 * 2 ^ 59
def prefixEnd_526261 : Nat := 4983230072969 + 3 ^ 40 * 526261 * 2
def baseEnd_526261 : Nat := 180149895143913823411517

theorem tailTrace_526261 : CollatzResearch.WordTrace tailWord_526261 prefixEnd_526261 180149895143913823411517 := by
  unfold tailWord_526261
  simp only [CollatzResearch.WordTrace]
  refine ⟨19194315546453750068338637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12796210364302500045559091 19194315546453750068338637)
  ·
    refine ⟨7197868329920156275626989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19194315546453750068338637 7197868329920156275626989)
    ·
      refine ⟨2699200623720058603360121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7197868329920156275626989 2699200623720058603360121)
      ·
        refine ⟨2024400467790043952520091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2699200623720058603360121 2024400467790043952520091)
        ·
          refine ⟨3036600701685065928780137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2024400467790043952520091 3036600701685065928780137)
          ·
            refine ⟨2277450526263799446585103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3036600701685065928780137 2277450526263799446585103)
            ·
              refine ⟨3416175789395699169877655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2277450526263799446585103 3416175789395699169877655)
              ·
                refine ⟨5124263684093548754816483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3416175789395699169877655 5124263684093548754816483)
                ·
                  refine ⟨7686395526140323132224725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5124263684093548754816483 7686395526140323132224725)
                  ·
                    refine ⟨180149895143913823411517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7686395526140323132224725 180149895143913823411517)
                    ·
                      rfl

theorem cell22_526261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_526261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_526261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_526261 prefixEnd_526261 := by exact prefixLift 526261
  have htrace : WordTrace (prefixWord ++ tailWord_526261) baseStart_526261 baseEnd_526261 := by
    simpa [prefixWord, tailWord_526261, baseEnd_526261] using wordTrace_append hprefix tailTrace_526261
  have hstable : (prefixWord ++ tailWord_526261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526261).length < 2 ^ (prefixWord ++ tailWord_526261).sum := by decide
  have hdescent : baseEnd_526261 < baseStart_526261 := by decide
  rcases family_descends (prefixWord ++ tailWord_526261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526308 : List Nat := [2, 3, 1, 1, 1, 1, 3, 6, 4]
def baseStart_526308 : Nat := 118140960795 + 526308 * 2 ^ 59
def prefixEnd_526308 : Nat := 4983230072969 + 3 ^ 40 * 526308 * 2
def baseEnd_526308 : Nat := 60055328068140455828791

theorem tailTrace_526308 : CollatzResearch.WordTrace tailWord_526308 prefixEnd_526308 60055328068140455828791 := by
  unfold tailWord_526308
  simp only [CollatzResearch.WordTrace]
  refine ⟨9598014888641738547649789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12797353184855651396866385 9598014888641738547649789)
  ·
    refine ⟨3599255583240651955368671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9598014888641738547649789 3599255583240651955368671)
    ·
      refine ⟨5398883374860977933053007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3599255583240651955368671 5398883374860977933053007)
      ·
        refine ⟨8098325062291466899579511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5398883374860977933053007 8098325062291466899579511)
        ·
          refine ⟨12147487593437200349369267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8098325062291466899579511 12147487593437200349369267)
          ·
            refine ⟨18221231390155800524053901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12147487593437200349369267 18221231390155800524053901)
            ·
              refine ⟨6832961771308425196520213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18221231390155800524053901 6832961771308425196520213)
              ·
                refine ⟨320295083030082431086885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6832961771308425196520213 320295083030082431086885)
                ·
                  refine ⟨60055328068140455828791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 320295083030082431086885 60055328068140455828791)
                  ·
                    rfl

theorem cell22_526308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 6, 4].length) (baseStart_526308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_526308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_526308 prefixEnd_526308 := by exact prefixLift 526308
  have htrace : WordTrace (prefixWord ++ tailWord_526308) baseStart_526308 baseEnd_526308 := by
    simpa [prefixWord, tailWord_526308, baseEnd_526308] using wordTrace_append hprefix tailTrace_526308
  have hstable : (prefixWord ++ tailWord_526308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526308).length < 2 ^ (prefixWord ++ tailWord_526308).sum := by decide
  have hdescent : baseEnd_526308 < baseStart_526308 := by decide
  rcases family_descends (prefixWord ++ tailWord_526308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526323 : List Nat := [1, 1, 1, 2, 2, 2, 1, 7, 2, 3]
def baseStart_526323 : Nat := 118140960795 + 526323 * 2 ^ 59
def prefixEnd_526323 : Nat := 4983230072969 + 3 ^ 40 * 526323 * 2
def baseEnd_526323 : Nat := 180171119010966328361327

theorem tailTrace_526323 : CollatzResearch.WordTrace tailWord_526323 prefixEnd_526323 180171119010966328361327 := by
  unfold tailWord_526323
  simp only [CollatzResearch.WordTrace]
  refine ⟨19196576872229134657095623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12797717914819423104730415 19196576872229134657095623)
  ·
    refine ⟨28794865308343701985643435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19196576872229134657095623 28794865308343701985643435)
    ·
      refine ⟨43192297962515552978465153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28794865308343701985643435 43192297962515552978465153)
      ·
        refine ⟨32394223471886664733848865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43192297962515552978465153 32394223471886664733848865)
        ·
          refine ⟨24295667603914998550386649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32394223471886664733848865 24295667603914998550386649)
          ·
            refine ⟨18221750702936248912789987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24295667603914998550386649 18221750702936248912789987)
            ·
              refine ⟨27332626054404373369184981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18221750702936248912789987 27332626054404373369184981)
              ·
                refine ⟨640608423150102500840273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 27332626054404373369184981 640608423150102500840273)
                ·
                  refine ⟨480456317362576875630205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 640608423150102500840273 480456317362576875630205)
                  ·
                    refine ⟨180171119010966328361327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 480456317362576875630205 180171119010966328361327)
                    ·
                      rfl

theorem cell22_526323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 7, 2, 3].length) (baseStart_526323 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_526323 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_526323 prefixEnd_526323 := by exact prefixLift 526323
  have htrace : WordTrace (prefixWord ++ tailWord_526323) baseStart_526323 baseEnd_526323 := by
    simpa [prefixWord, tailWord_526323, baseEnd_526323] using wordTrace_append hprefix tailTrace_526323
  have hstable : (prefixWord ++ tailWord_526323).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526323).length < 2 ^ (prefixWord ++ tailWord_526323).sum := by decide
  have hdescent : baseEnd_526323 < baseStart_526323 := by decide
  rcases family_descends (prefixWord ++ tailWord_526323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526445 : List Nat := [1, 5, 1, 1, 2, 1, 2, 4, 1, 4]
def baseStart_526445 : Nat := 118140960795 + 526445 * 2 ^ 59
def prefixEnd_526445 : Nat := 4983230072969 + 3 ^ 40 * 526445 * 2
def baseEnd_526445 : Nat := 180212882104198676810953

theorem tailTrace_526445 : CollatzResearch.WordTrace tailWord_526445 prefixEnd_526445 180212882104198676810953 := by
  unfold tailWord_526445
  simp only [CollatzResearch.WordTrace]
  refine ⟨19201026577787149493036789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12800684385191432995357859 19201026577787149493036789)
  ·
    refine ⟨1800096241667545264972199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19201026577787149493036789 1800096241667545264972199)
    ·
      refine ⟨2700144362501317897458299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1800096241667545264972199 2700144362501317897458299)
      ·
        refine ⟨4050216543751976846187449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2700144362501317897458299 4050216543751976846187449)
        ·
          refine ⟨3037662407813982634640587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4050216543751976846187449 3037662407813982634640587)
          ·
            refine ⟨4556493611720973951960881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3037662407813982634640587 4556493611720973951960881)
            ·
              refine ⟨3417370208790730463970661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4556493611720973951960881 3417370208790730463970661)
              ·
                refine ⟨640756914148261961994499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3417370208790730463970661 640756914148261961994499)
                ·
                  refine ⟨961135371222392942991749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 640756914148261961994499 961135371222392942991749)
                  ·
                    refine ⟨180212882104198676810953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 961135371222392942991749 180212882104198676810953)
                    ·
                      rfl

theorem cell22_526445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_526445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_526445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_526445 prefixEnd_526445 := by exact prefixLift 526445
  have htrace : WordTrace (prefixWord ++ tailWord_526445) baseStart_526445 baseEnd_526445 := by
    simpa [prefixWord, tailWord_526445, baseEnd_526445] using wordTrace_append hprefix tailTrace_526445
  have hstable : (prefixWord ++ tailWord_526445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526445).length < 2 ^ (prefixWord ++ tailWord_526445).sum := by decide
  have hdescent : baseEnd_526445 < baseStart_526445 := by decide
  rcases family_descends (prefixWord ++ tailWord_526445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526460 : List Nat := [2, 2, 2, 1, 1, 4, 1, 5, 4]
def baseStart_526460 : Nat := 118140960795 + 526460 * 2 ^ 59
def prefixEnd_526460 : Nat := 4983230072969 + 3 ^ 40 * 526460 * 2
def baseEnd_526460 : Nat := 60072672303581212561969

theorem tailTrace_526460 : CollatzResearch.WordTrace tailWord_526460 prefixEnd_526460 60072672303581212561969 := by
  unfold tailWord_526460
  simp only [CollatzResearch.WordTrace]
  refine ⟨9600786836366403527416417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12801049115155204703221889 9600786836366403527416417)
  ·
    refine ⟨7200590127274802645562313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9600786836366403527416417 7200590127274802645562313)
    ·
      refine ⟨5400442595456101984171735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7200590127274802645562313 5400442595456101984171735)
      ·
        refine ⟨8100663893184152976257603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5400442595456101984171735 8100663893184152976257603)
        ·
          refine ⟨12150995839776229464386405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8100663893184152976257603 12150995839776229464386405)
          ·
            refine ⟨2278311719958043024572451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12150995839776229464386405 2278311719958043024572451)
            ·
              refine ⟨3417467579937064536858677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2278311719958043024572451 3417467579937064536858677)
              ·
                refine ⟨320387585619099800330501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3417467579937064536858677 320387585619099800330501)
                ·
                  refine ⟨60072672303581212561969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 320387585619099800330501 60072672303581212561969)
                  ·
                    rfl

theorem cell22_526460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 5, 4].length) (baseStart_526460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_526460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_526460 prefixEnd_526460 := by exact prefixLift 526460
  have htrace : WordTrace (prefixWord ++ tailWord_526460) baseStart_526460 baseEnd_526460 := by
    simpa [prefixWord, tailWord_526460, baseEnd_526460] using wordTrace_append hprefix tailTrace_526460
  have hstable : (prefixWord ++ tailWord_526460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526460).length < 2 ^ (prefixWord ++ tailWord_526460).sum := by decide
  have hdescent : baseEnd_526460 < baseStart_526460 := by decide
  rcases family_descends (prefixWord ++ tailWord_526460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526473 : List Nat := [1, 2, 1, 1, 4, 2, 2, 1, 4, 4]
def baseStart_526473 : Nat := 118140960795 + 526473 * 2 ^ 59
def prefixEnd_526473 : Nat := 4983230072969 + 3 ^ 40 * 526473 * 2
def baseEnd_526473 : Nat := 180222467076415937110867

theorem tailTrace_526473 : CollatzResearch.WordTrace tailWord_526473 prefixEnd_526473 180222467076415937110867 := by
  unfold tailWord_526473
  simp only [CollatzResearch.WordTrace]
  refine ⟨19202047821685710275056073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12801365214457140183370715 19202047821685710275056073)
  ·
    refine ⟨14401535866264282706292055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19202047821685710275056073 14401535866264282706292055)
    ·
      refine ⟨21602303799396424059438083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14401535866264282706292055 21602303799396424059438083)
      ·
        refine ⟨32403455699094636089157125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21602303799396424059438083 32403455699094636089157125)
        ·
          refine ⟨6075647943580244266716961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32403455699094636089157125 6075647943580244266716961)
          ·
            refine ⟨4556735957685183200037721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6075647943580244266716961 4556735957685183200037721)
            ·
              refine ⟨3417551968263887400028291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4556735957685183200037721 3417551968263887400028291)
              ·
                refine ⟨5126327952395831100042437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3417551968263887400028291 5126327952395831100042437)
                ·
                  refine ⟨961186491074218331257957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5126327952395831100042437 961186491074218331257957)
                  ·
                    refine ⟨180222467076415937110867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 961186491074218331257957 180222467076415937110867)
                    ·
                      rfl

theorem cell22_526473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 4, 4].length) (baseStart_526473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_526473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_526473 prefixEnd_526473 := by exact prefixLift 526473
  have htrace : WordTrace (prefixWord ++ tailWord_526473) baseStart_526473 baseEnd_526473 := by
    simpa [prefixWord, tailWord_526473, baseEnd_526473] using wordTrace_append hprefix tailTrace_526473
  have hstable : (prefixWord ++ tailWord_526473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526473).length < 2 ^ (prefixWord ++ tailWord_526473).sum := by decide
  have hdescent : baseEnd_526473 < baseStart_526473 := by decide
  rcases family_descends (prefixWord ++ tailWord_526473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526533 : List Nat := [1, 3, 1, 1, 1, 1, 6, 1, 7]
def baseStart_526533 : Nat := 118140960795 + 526533 * 2 ^ 59
def prefixEnd_526533 : Nat := 4983230072969 + 3 ^ 40 * 526533 * 2
def baseEnd_526533 : Nat := 60081002100865260203561

theorem tailTrace_526533 : CollatzResearch.WordTrace tailWord_526533 prefixEnd_526533 60081002100865260203561 := by
  unfold tailWord_526533
  simp only [CollatzResearch.WordTrace]
  refine ⟨19204236201468340522240253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12802824134312227014826835 19204236201468340522240253)
  ·
    refine ⟨7201588575550627695840095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19204236201468340522240253 7201588575550627695840095)
    ·
      refine ⟨10802382863325941543760143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7201588575550627695840095 10802382863325941543760143)
      ·
        refine ⟨16203574294988912315640215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10802382863325941543760143 16203574294988912315640215)
        ·
          refine ⟨24305361442483368473460323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16203574294988912315640215 24305361442483368473460323)
          ·
            refine ⟨36458042163725052710190485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24305361442483368473460323 36458042163725052710190485)
            ·
              refine ⟨1708970726424611845790179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 36458042163725052710190485 1708970726424611845790179)
              ·
                refine ⟨2563456089636917768685269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1708970726424611845790179 2563456089636917768685269)
                ·
                  refine ⟨60081002100865260203561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2563456089636917768685269 60081002100865260203561)
                  ·
                    rfl

theorem cell22_526533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 1, 7].length) (baseStart_526533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_526533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_526533 prefixEnd_526533 := by exact prefixLift 526533
  have htrace : WordTrace (prefixWord ++ tailWord_526533) baseStart_526533 baseEnd_526533 := by
    simpa [prefixWord, tailWord_526533, baseEnd_526533] using wordTrace_append hprefix tailTrace_526533
  have hstable : (prefixWord ++ tailWord_526533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526533).length < 2 ^ (prefixWord ++ tailWord_526533).sum := by decide
  have hdescent : baseEnd_526533 < baseStart_526533 := by decide
  rcases family_descends (prefixWord ++ tailWord_526533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526629 : List Nat := [1, 3, 1, 2, 5, 1, 2, 3, 4]
def baseStart_526629 : Nat := 118140960795 + 526629 * 2 ^ 59
def prefixEnd_526629 : Nat := 4983230072969 + 3 ^ 40 * 526629 * 2
def baseEnd_526629 : Nat := 60091956354827843403463

theorem tailTrace_526629 : CollatzResearch.WordTrace tailWord_526629 prefixEnd_526629 60091956354827843403463 := by
  unfold tailWord_526629
  simp only [CollatzResearch.WordTrace]
  refine ⟨19207737609120548917734941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12805158406080365945156627 19207737609120548917734941)
  ·
    refine ⟨7202901603420205844150603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19207737609120548917734941 7202901603420205844150603)
    ·
      refine ⟨10804352405130308766225905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7202901603420205844150603 10804352405130308766225905)
      ·
        refine ⟨8103264303847731574669429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10804352405130308766225905 8103264303847731574669429)
        ·
          refine ⟨759681028485724835125259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8103264303847731574669429 759681028485724835125259)
          ·
            refine ⟨1139521542728587252687889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 759681028485724835125259 1139521542728587252687889)
            ·
              refine ⟨854641157046440439515917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1139521542728587252687889 854641157046440439515917)
              ·
                refine ⟨320490433892415164818469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 854641157046440439515917 320490433892415164818469)
                ·
                  refine ⟨60091956354827843403463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 320490433892415164818469 60091956354827843403463)
                  ·
                    rfl

theorem cell22_526629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 3, 4].length) (baseStart_526629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_526629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_526629 prefixEnd_526629 := by exact prefixLift 526629
  have htrace : WordTrace (prefixWord ++ tailWord_526629) baseStart_526629 baseEnd_526629 := by
    simpa [prefixWord, tailWord_526629, baseEnd_526629] using wordTrace_append hprefix tailTrace_526629
  have hstable : (prefixWord ++ tailWord_526629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526629).length < 2 ^ (prefixWord ++ tailWord_526629).sum := by decide
  have hdescent : baseEnd_526629 < baseStart_526629 := by decide
  rcases family_descends (prefixWord ++ tailWord_526629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526644 : List Nat := [2, 5, 1, 1, 1, 3, 1, 1, 4, 3]
def baseStart_526644 : Nat := 118140960795 + 526644 * 2 ^ 59
def prefixEnd_526644 : Nat := 4983230072969 + 3 ^ 40 * 526644 * 2
def baseEnd_526644 : Nat := 180281003871028491085343

theorem tailTrace_526644 : CollatzResearch.WordTrace tailWord_526644 prefixEnd_526644 180281003871028491085343 := by
  unfold tailWord_526644
  simp only [CollatzResearch.WordTrace]
  refine ⟨9604142352033103239765493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12805523136044137653020657 9604142352033103239765493)
  ·
    refine ⟨900388345503103428728015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9604142352033103239765493 900388345503103428728015)
    ·
      refine ⟨1350582518254655143092023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 900388345503103428728015 1350582518254655143092023)
      ·
        refine ⟨2025873777381982714638035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1350582518254655143092023 2025873777381982714638035)
        ·
          refine ⟨3038810666072974071957053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2025873777381982714638035 3038810666072974071957053)
          ·
            refine ⟨1139553999777365276983895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3038810666072974071957053 1139553999777365276983895)
            ·
              refine ⟨1709330999666047915475843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1139553999777365276983895 1709330999666047915475843)
              ·
                refine ⟨2563996499499071873213765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1709330999666047915475843 2563996499499071873213765)
                ·
                  refine ⟨480749343656075976227581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2563996499499071873213765 480749343656075976227581)
                  ·
                    refine ⟨180281003871028491085343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 480749343656075976227581 180281003871028491085343)
                    ·
                      rfl

theorem cell22_526644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_526644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_526644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_526644 prefixEnd_526644 := by exact prefixLift 526644
  have htrace : WordTrace (prefixWord ++ tailWord_526644) baseStart_526644 baseEnd_526644 := by
    simpa [prefixWord, tailWord_526644, baseEnd_526644] using wordTrace_append hprefix tailTrace_526644
  have hstable : (prefixWord ++ tailWord_526644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526644).length < 2 ^ (prefixWord ++ tailWord_526644).sum := by decide
  have hdescent : baseEnd_526644 < baseStart_526644 := by decide
  rcases family_descends (prefixWord ++ tailWord_526644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526672 : List Nat := [2, 1, 1, 1, 1, 6, 2, 2, 3, 3]
def baseStart_526672 : Nat := 118140960795 + 526672 * 2 ^ 59
def prefixEnd_526672 : Nat := 4983230072969 + 3 ^ 40 * 526672 * 2
def baseEnd_526672 : Nat := 180290588843245751385257

theorem tailTrace_526672 : CollatzResearch.WordTrace tailWord_526672 prefixEnd_526672 180290588843245751385257 := by
  unfold tailWord_526672
  simp only [CollatzResearch.WordTrace]
  refine ⟨9604652973982383630775135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12806203965309844841033513 9604652973982383630775135)
  ·
    refine ⟨14406979460973575446162703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9604652973982383630775135 14406979460973575446162703)
    ·
      refine ⟨21610469191460363169244055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14406979460973575446162703 21610469191460363169244055)
      ·
        refine ⟨32415703787190544753866083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21610469191460363169244055 32415703787190544753866083)
        ·
          refine ⟨48623555680785817130799125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32415703787190544753866083 48623555680785817130799125)
          ·
            refine ⟨2279229172536835178006209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 48623555680785817130799125 2279229172536835178006209)
            ·
              refine ⟨1709421879402626383504657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2279229172536835178006209 1709421879402626383504657)
              ·
                refine ⟨1282066409551969787628493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1709421879402626383504657 1282066409551969787628493)
                ·
                  refine ⟨480774903581988670360685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1282066409551969787628493 480774903581988670360685)
                  ·
                    refine ⟨180290588843245751385257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 480774903581988670360685 180290588843245751385257)
                    ·
                      rfl

theorem cell22_526672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 2, 3, 3].length) (baseStart_526672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_526672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_526672 prefixEnd_526672 := by exact prefixLift 526672
  have htrace : WordTrace (prefixWord ++ tailWord_526672) baseStart_526672 baseEnd_526672 := by
    simpa [prefixWord, tailWord_526672, baseEnd_526672] using wordTrace_append hprefix tailTrace_526672
  have hstable : (prefixWord ++ tailWord_526672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526672).length < 2 ^ (prefixWord ++ tailWord_526672).sum := by decide
  have hdescent : baseEnd_526672 < baseStart_526672 := by decide
  rcases family_descends (prefixWord ++ tailWord_526672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526732 : List Nat := [2, 2, 1, 2, 1, 5, 1, 1, 3, 4]
def baseStart_526732 : Nat := 118140960795 + 526732 * 2 ^ 59
def prefixEnd_526732 : Nat := 4983230072969 + 3 ^ 40 * 526732 * 2
def baseEnd_526732 : Nat := 180311128069425594885073

theorem tailTrace_526732 : CollatzResearch.WordTrace tailWord_526732 prefixEnd_526732 180311128069425594885073 := by
  unfold tailWord_526732
  simp only [CollatzResearch.WordTrace]
  refine ⟨9605747163873698754367225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12807662885164931672489633 9605747163873698754367225)
  ·
    refine ⟨7204310372905274065775419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9605747163873698754367225 7204310372905274065775419)
    ·
      refine ⟨10806465559357911098663129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7204310372905274065775419 10806465559357911098663129)
      ·
        refine ⟨8104849169518433323997347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10806465559357911098663129 8104849169518433323997347)
        ·
          refine ⟨12157273754277649985996021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8104849169518433323997347 12157273754277649985996021)
          ·
            refine ⟨1139744414463529686187127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12157273754277649985996021 1139744414463529686187127)
            ·
              refine ⟨1709616621695294529280691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1139744414463529686187127 1709616621695294529280691)
              ·
                refine ⟨2564424932542941793921037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1709616621695294529280691 2564424932542941793921037)
                ·
                  refine ⟨961659349703603172720389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2564424932542941793921037 961659349703603172720389)
                  ·
                    refine ⟨180311128069425594885073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 961659349703603172720389 180311128069425594885073)
                    ·
                      rfl

theorem cell22_526732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 1, 3, 4].length) (baseStart_526732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_526732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_526732 prefixEnd_526732 := by exact prefixLift 526732
  have htrace : WordTrace (prefixWord ++ tailWord_526732) baseStart_526732 baseEnd_526732 := by
    simpa [prefixWord, tailWord_526732, baseEnd_526732] using wordTrace_append hprefix tailTrace_526732
  have hstable : (prefixWord ++ tailWord_526732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526732).length < 2 ^ (prefixWord ++ tailWord_526732).sum := by decide
  have hdescent : baseEnd_526732 < baseStart_526732 := by decide
  rcases family_descends (prefixWord ++ tailWord_526732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526824 : List Nat := [2, 1, 4, 1, 1, 3, 1, 3, 3, 3]
def baseStart_526824 : Nat := 118140960795 + 526824 * 2 ^ 59
def prefixEnd_526824 : Nat := 4983230072969 + 3 ^ 40 * 526824 * 2
def baseEnd_526824 : Nat := 180342621549568021584791

theorem tailTrace_526824 : CollatzResearch.WordTrace tailWord_526824 prefixEnd_526824 180342621549568021584791 := by
  unfold tailWord_526824
  simp only [CollatzResearch.WordTrace]
  refine ⟨9607424921707048610541763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12809899895609398147389017 9607424921707048610541763)
  ·
    refine ⟨14411137382560572915812645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9607424921707048610541763 14411137382560572915812645)
    ·
      refine ⟨2702088259230107421714871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14411137382560572915812645 2702088259230107421714871)
      ·
        refine ⟨4053132388845161132572307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2702088259230107421714871 4053132388845161132572307)
        ·
          refine ⟨6079698583267741698858461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4053132388845161132572307 6079698583267741698858461)
          ·
            refine ⟨2279886968725403137071923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6079698583267741698858461 2279886968725403137071923)
            ·
              refine ⟨3419830453088104705607885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2279886968725403137071923 3419830453088104705607885)
              ·
                refine ⟨1282436419908039264602957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3419830453088104705607885 1282436419908039264602957)
                ·
                  refine ⟨480913657465514724226109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1282436419908039264602957 480913657465514724226109)
                  ·
                    refine ⟨180342621549568021584791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 480913657465514724226109 180342621549568021584791)
                    ·
                      rfl

theorem cell22_526824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 3, 3, 3].length) (baseStart_526824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_526824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_526824 prefixEnd_526824 := by exact prefixLift 526824
  have htrace : WordTrace (prefixWord ++ tailWord_526824) baseStart_526824 baseEnd_526824 := by
    simpa [prefixWord, tailWord_526824, baseEnd_526824] using wordTrace_append hprefix tailTrace_526824
  have hstable : (prefixWord ++ tailWord_526824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526824).length < 2 ^ (prefixWord ++ tailWord_526824).sum := by decide
  have hdescent : baseEnd_526824 < baseStart_526824 := by decide
  rcases family_descends (prefixWord ++ tailWord_526824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526888 : List Nat := [2, 1, 5, 2, 1, 3, 2, 1, 5]
def baseStart_526888 : Nat := 118140960795 + 526888 * 2 ^ 59
def prefixEnd_526888 : Nat := 4983230072969 + 3 ^ 40 * 526888 * 2
def baseEnd_526888 : Nat := 60121510019164395994865

theorem tailTrace_526888 : CollatzResearch.WordTrace tailWord_526888 prefixEnd_526888 60121510019164395994865 := by
  unfold tailWord_526888
  simp only [CollatzResearch.WordTrace]
  refine ⟨9608592057591118075706659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12811456076788157434275545 9608592057591118075706659)
  ·
    refine ⟨14412888086386677113559989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9608592057591118075706659 14412888086386677113559989)
    ·
      refine ⟨1351208258098750979396249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14412888086386677113559989 1351208258098750979396249)
      ·
        refine ⟨1013406193574063234547187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1351208258098750979396249 1013406193574063234547187)
        ·
          refine ⟨1520109290361094851820781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1013406193574063234547187 1520109290361094851820781)
          ·
            refine ⟨570040983885410569432793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1520109290361094851820781 570040983885410569432793)
            ·
              refine ⟨427530737914057927074595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 570040983885410569432793 427530737914057927074595)
              ·
                refine ⟨641296106871086890611893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 427530737914057927074595 641296106871086890611893)
                ·
                  refine ⟨60121510019164395994865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 641296106871086890611893 60121510019164395994865)
                  ·
                    rfl

theorem cell22_526888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 2, 1, 5].length) (baseStart_526888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_526888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_526888 prefixEnd_526888 := by exact prefixLift 526888
  have htrace : WordTrace (prefixWord ++ tailWord_526888) baseStart_526888 baseEnd_526888 := by
    simpa [prefixWord, tailWord_526888, baseEnd_526888] using wordTrace_append hprefix tailTrace_526888
  have hstable : (prefixWord ++ tailWord_526888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526888).length < 2 ^ (prefixWord ++ tailWord_526888).sum := by decide
  have hdescent : baseEnd_526888 < baseStart_526888 := by decide
  rcases family_descends (prefixWord ++ tailWord_526888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526912 : List Nat := [2, 1, 1, 2, 2, 2, 2, 3, 1, 6]
def baseStart_526912 : Nat := 118140960795 + 526912 * 2 ^ 59
def prefixEnd_526912 : Nat := 4983230072969 + 3 ^ 40 * 526912 * 2
def baseEnd_526912 : Nat := 180372745747965125384521

theorem tailTrace_526912 : CollatzResearch.WordTrace tailWord_526912 prefixEnd_526912 180372745747965125384521 := by
  unfold tailWord_526912
  simp only [CollatzResearch.WordTrace]
  refine ⟨9609029733547644125143495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12812039644730192166857993 9609029733547644125143495)
  ·
    refine ⟨14413544600321466187715243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9609029733547644125143495 14413544600321466187715243)
    ·
      refine ⟨21620316900482199281572865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14413544600321466187715243 21620316900482199281572865)
      ·
        refine ⟨16215237675361649461179649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21620316900482199281572865 16215237675361649461179649)
        ·
          refine ⟨12161428256521237095884737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16215237675361649461179649 12161428256521237095884737)
          ·
            refine ⟨9121071192390927821913553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12161428256521237095884737 9121071192390927821913553)
            ·
              refine ⟨6840803394293195866435165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9121071192390927821913553 6840803394293195866435165)
              ·
                refine ⟨2565301272859948449913187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6840803394293195866435165 2565301272859948449913187)
                ·
                  refine ⟨3847951909289922674869781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2565301272859948449913187 3847951909289922674869781)
                  ·
                    refine ⟨180372745747965125384521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3847951909289922674869781 180372745747965125384521)
                    ·
                      rfl

theorem cell22_526912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 3, 1, 6].length) (baseStart_526912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_526912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_526912 prefixEnd_526912 := by exact prefixLift 526912
  have htrace : WordTrace (prefixWord ++ tailWord_526912) baseStart_526912 baseEnd_526912 := by
    simpa [prefixWord, tailWord_526912, baseEnd_526912] using wordTrace_append hprefix tailTrace_526912
  have hstable : (prefixWord ++ tailWord_526912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526912).length < 2 ^ (prefixWord ++ tailWord_526912).sum := by decide
  have hdescent : baseEnd_526912 < baseStart_526912 := by decide
  rcases family_descends (prefixWord ++ tailWord_526912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526929 : List Nat := [1, 2, 2, 1, 3, 3, 2, 2, 2, 4]
def baseStart_526929 : Nat := 118140960795 + 526929 * 2 ^ 59
def prefixEnd_526929 : Nat := 4983230072969 + 3 ^ 40 * 526929 * 2
def baseEnd_526929 : Nat := 180378565195382747709469

theorem tailTrace_526929 : CollatzResearch.WordTrace tailWord_526929 prefixEnd_526929 180378565195382747709469 := by
  unfold tailWord_526929
  simp only [CollatzResearch.WordTrace]
  refine ⟨19218679508033700153655841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12812453005355800102437227 19218679508033700153655841)
  ·
    refine ⟨14414009631025275115241881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19218679508033700153655841 14414009631025275115241881)
    ·
      refine ⟨10810507223268956336431411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14414009631025275115241881 10810507223268956336431411)
      ·
        refine ⟨16215760834903434504647117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10810507223268956336431411 16215760834903434504647117)
        ·
          refine ⟨6080910313088787939242669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16215760834903434504647117 6080910313088787939242669)
          ·
            refine ⟨2280341367408295477216001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6080910313088787939242669 2280341367408295477216001)
            ·
              refine ⟨1710256025556221607912001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2280341367408295477216001 1710256025556221607912001)
              ·
                refine ⟨1282692019167166205934001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1710256025556221607912001 1282692019167166205934001)
                ·
                  refine ⟨962019014375374654450501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1282692019167166205934001 962019014375374654450501)
                  ·
                    refine ⟨180378565195382747709469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 962019014375374654450501 180378565195382747709469)
                    ·
                      rfl

theorem cell22_526929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 2, 2, 4].length) (baseStart_526929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_526929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_526929 prefixEnd_526929 := by exact prefixLift 526929
  have htrace : WordTrace (prefixWord ++ tailWord_526929) baseStart_526929 baseEnd_526929 := by
    simpa [prefixWord, tailWord_526929, baseEnd_526929] using wordTrace_append hprefix tailTrace_526929
  have hstable : (prefixWord ++ tailWord_526929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526929).length < 2 ^ (prefixWord ++ tailWord_526929).sum := by decide
  have hdescent : baseEnd_526929 < baseStart_526929 := by decide
  rcases family_descends (prefixWord ++ tailWord_526929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526959 : List Nat := [1, 1, 2, 1, 3, 2, 3, 1, 5, 3]
def baseStart_526959 : Nat := 118140960795 + 526959 * 2 ^ 59
def prefixEnd_526959 : Nat := 4983230072969 + 3 ^ 40 * 526959 * 2
def baseEnd_526959 : Nat := 180388834808472669459377

theorem tailTrace_526959 : CollatzResearch.WordTrace tailWord_526959 prefixEnd_526959 180388834808472669459377 := by
  unfold tailWord_526959
  simp only [CollatzResearch.WordTrace]
  refine ⟨19219773697925015277247931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12813182465283343518165287 19219773697925015277247931)
  ·
    refine ⟨28829660546887522915871897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19219773697925015277247931 28829660546887522915871897)
    ·
      refine ⟨21622245410165642186903923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28829660546887522915871897 21622245410165642186903923)
      ·
        refine ⟨32433368115248463280355885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21622245410165642186903923 32433368115248463280355885)
        ·
          refine ⟨12162513043218173730133457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32433368115248463280355885 12162513043218173730133457)
          ·
            refine ⟨9121884782413630297600093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12162513043218173730133457 9121884782413630297600093)
            ·
              refine ⟨3420706793405111361600035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9121884782413630297600093 3420706793405111361600035)
              ·
                refine ⟨5131060190107667042400053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3420706793405111361600035 5131060190107667042400053)
                ·
                  refine ⟨481036892822593785225005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5131060190107667042400053 481036892822593785225005)
                  ·
                    refine ⟨180388834808472669459377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 481036892822593785225005 180388834808472669459377)
                    ·
                      rfl

theorem cell22_526959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 5, 3].length) (baseStart_526959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_526959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_526959 prefixEnd_526959 := by exact prefixLift 526959
  have htrace : WordTrace (prefixWord ++ tailWord_526959) baseStart_526959 baseEnd_526959 := by
    simpa [prefixWord, tailWord_526959, baseEnd_526959] using wordTrace_append hprefix tailTrace_526959
  have hstable : (prefixWord ++ tailWord_526959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526959).length < 2 ^ (prefixWord ++ tailWord_526959).sum := by decide
  have hdescent : baseEnd_526959 < baseStart_526959 := by decide
  rcases family_descends (prefixWord ++ tailWord_526959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527036 : List Nat := [2, 2, 2, 3, 1, 1, 1, 5, 1, 4]
def baseStart_527036 : Nat := 118140960795 + 527036 * 2 ^ 59
def prefixEnd_527036 : Nat := 4983230072969 + 3 ^ 40 * 527036 * 2
def baseEnd_527036 : Nat := 180415193482070135284141

theorem tailTrace_527036 : CollatzResearch.WordTrace tailWord_527036 prefixEnd_527036 180415193482070135284141 := by
  unfold tailWord_527036
  simp only [CollatzResearch.WordTrace]
  refine ⟨9611291059323028713900481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12815054745764038285200641 9611291059323028713900481)
  ·
    refine ⟨7208468294492271535425361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9611291059323028713900481 7208468294492271535425361)
    ·
      refine ⟨5406351220869203651569021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7208468294492271535425361 5406351220869203651569021)
      ·
        refine ⟨2027381707825951369338383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5406351220869203651569021 2027381707825951369338383)
        ·
          refine ⟨3041072561738927054007575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2027381707825951369338383 3041072561738927054007575)
          ·
            refine ⟨4561608842608390581011363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3041072561738927054007575 4561608842608390581011363)
            ·
              refine ⟨6842413263912585871517045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4561608842608390581011363 6842413263912585871517045)
              ·
                refine ⟨641476243491804925454723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6842413263912585871517045 641476243491804925454723)
                ·
                  refine ⟨962214365237707388182085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 641476243491804925454723 962214365237707388182085)
                  ·
                    refine ⟨180415193482070135284141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 962214365237707388182085 180415193482070135284141)
                    ·
                      rfl

theorem cell22_527036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 5, 1, 4].length) (baseStart_527036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_527036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_527036 prefixEnd_527036 := by exact prefixLift 527036
  have htrace : WordTrace (prefixWord ++ tailWord_527036) baseStart_527036 baseEnd_527036 := by
    simpa [prefixWord, tailWord_527036, baseEnd_527036] using wordTrace_append hprefix tailTrace_527036
  have hstable : (prefixWord ++ tailWord_527036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527036).length < 2 ^ (prefixWord ++ tailWord_527036).sum := by decide
  have hdescent : baseEnd_527036 < baseStart_527036 := by decide
  rcases family_descends (prefixWord ++ tailWord_527036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527102 : List Nat := [4, 2, 2, 1, 2, 3, 2, 2, 4]
def baseStart_527102 : Nat := 118140960795 + 527102 * 2 ^ 59
def prefixEnd_527102 : Nat := 4983230072969 + 3 ^ 40 * 527102 * 2
def baseEnd_527102 : Nat := 60145928876955987711313

theorem tailTrace_527102 : CollatzResearch.WordTrace tailWord_527102 prefixEnd_527102 60145928876955987711313 := by
  unfold tailWord_527102
  simp only [CollatzResearch.WordTrace]
  refine ⟨2403123667050868837462945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12816659557604633799802373 2403123667050868837462945)
  ·
    refine ⟨1802342750288151628097209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2403123667050868837462945 1802342750288151628097209)
    ·
      refine ⟨1351757062716113721072907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1802342750288151628097209 1351757062716113721072907)
      ·
        refine ⟨2027635594074170581609361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1351757062716113721072907 2027635594074170581609361)
        ·
          refine ⟨1520726695555627936207021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2027635594074170581609361 1520726695555627936207021)
          ·
            refine ⟨570272510833360476077633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1520726695555627936207021 570272510833360476077633)
            ·
              refine ⟨427704383125020357058225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 570272510833360476077633 427704383125020357058225)
              ·
                refine ⟨320778287343765267793669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 427704383125020357058225 320778287343765267793669)
                ·
                  refine ⟨60145928876955987711313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 320778287343765267793669 60145928876955987711313)
                  ·
                    rfl

theorem cell22_527102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 2, 2, 4].length) (baseStart_527102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_527102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_527102 prefixEnd_527102 := by exact prefixLift 527102
  have htrace : WordTrace (prefixWord ++ tailWord_527102) baseStart_527102 baseEnd_527102 := by
    simpa [prefixWord, tailWord_527102, baseEnd_527102] using wordTrace_append hprefix tailTrace_527102
  have hstable : (prefixWord ++ tailWord_527102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527102).length < 2 ^ (prefixWord ++ tailWord_527102).sum := by decide
  have hdescent : baseEnd_527102 < baseStart_527102 := by decide
  rcases family_descends (prefixWord ++ tailWord_527102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527139 : List Nat := [1, 1, 1, 4, 2, 1, 1, 1, 3, 7]
def baseStart_527139 : Nat := 118140960795 + 527139 * 2 ^ 59
def prefixEnd_527139 : Nat := 4983230072969 + 3 ^ 40 * 527139 * 2
def baseEnd_527139 : Nat := 180450452487012199958825

theorem tailTrace_527139 : CollatzResearch.WordTrace tailWord_527139 prefixEnd_527139 180450452487012199958825 := by
  unfold tailWord_527139
  simp only [CollatzResearch.WordTrace]
  refine ⟨19226338837272906018800471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12817559224848604012533647 19226338837272906018800471)
  ·
    refine ⟨28839508255909359028200707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19226338837272906018800471 28839508255909359028200707)
    ·
      refine ⟨43259262383864038542301061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28839508255909359028200707 43259262383864038542301061)
      ·
        refine ⟨8111111696974507226681449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43259262383864038542301061 8111111696974507226681449)
        ·
          refine ⟨6083333772730880420011087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8111111696974507226681449 6083333772730880420011087)
          ·
            refine ⟨9125000659096320630016631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6083333772730880420011087 9125000659096320630016631)
            ·
              refine ⟨13687500988644480945024947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9125000659096320630016631 13687500988644480945024947)
              ·
                refine ⟨20531251482966721417537421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13687500988644480945024947 20531251482966721417537421)
                ·
                  refine ⟨7699219306112520531576533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20531251482966721417537421 7699219306112520531576533)
                  ·
                    refine ⟨180450452487012199958825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7699219306112520531576533 180450452487012199958825)
                    ·
                      rfl

theorem cell22_527139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 7].length) (baseStart_527139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_527139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_527139 prefixEnd_527139 := by exact prefixLift 527139
  have htrace : WordTrace (prefixWord ++ tailWord_527139) baseStart_527139 baseEnd_527139 := by
    simpa [prefixWord, tailWord_527139, baseEnd_527139] using wordTrace_append hprefix tailTrace_527139
  have hstable : (prefixWord ++ tailWord_527139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527139).length < 2 ^ (prefixWord ++ tailWord_527139).sum := by decide
  have hdescent : baseEnd_527139 < baseStart_527139 := by decide
  rcases family_descends (prefixWord ++ tailWord_527139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527186 : List Nat := [3, 2, 2, 1, 1, 2, 1, 4, 6]
def baseStart_527186 : Nat := 118140960795 + 527186 * 2 ^ 59
def prefixEnd_527186 : Nat := 4983230072969 + 3 ^ 40 * 527186 * 2
def baseEnd_527186 : Nat := 60155513849173248011227

theorem tailTrace_527186 : CollatzResearch.WordTrace tailWord_527186 prefixEnd_527186 60155513849173248011227 := by
  unfold tailWord_527186
  simp only [CollatzResearch.WordTrace]
  refine ⟨4807013267025658261440353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12818702045401755363840941 4807013267025658261440353)
  ·
    refine ⟨3605259950269243696080265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4807013267025658261440353 3605259950269243696080265)
    ·
      refine ⟨2703944962701932772060199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3605259950269243696080265 2703944962701932772060199)
      ·
        refine ⟨4055917444052899158090299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2703944962701932772060199 4055917444052899158090299)
        ·
          refine ⟨6083876166079348737135449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4055917444052899158090299 6083876166079348737135449)
          ·
            refine ⟨4562907124559511552851587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6083876166079348737135449 4562907124559511552851587)
            ·
              refine ⟨6844360686839267329277381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4562907124559511552851587 6844360686839267329277381)
              ·
                refine ⟨1283317628782362624239509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6844360686839267329277381 1283317628782362624239509)
                ·
                  refine ⟨60155513849173248011227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1283317628782362624239509 60155513849173248011227)
                  ·
                    rfl

theorem cell22_527186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 4, 6].length) (baseStart_527186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_527186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_527186 prefixEnd_527186 := by exact prefixLift 527186
  have htrace : WordTrace (prefixWord ++ tailWord_527186) baseStart_527186 baseEnd_527186 := by
    simpa [prefixWord, tailWord_527186, baseEnd_527186] using wordTrace_append hprefix tailTrace_527186
  have hstable : (prefixWord ++ tailWord_527186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527186).length < 2 ^ (prefixWord ++ tailWord_527186).sum := by decide
  have hdescent : baseEnd_527186 < baseStart_527186 := by decide
  rcases family_descends (prefixWord ++ tailWord_527186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527216 : List Nat := [2, 1, 1, 1, 4, 1, 3, 1, 4, 4]
def baseStart_527216 : Nat := 118140960795 + 527216 * 2 ^ 59
def prefixEnd_527216 : Nat := 4983230072969 + 3 ^ 40 * 527216 * 2
def baseEnd_527216 : Nat := 180476811160609665783589

theorem tailTrace_527216 : CollatzResearch.WordTrace tailWord_527216 prefixEnd_527216 180476811160609665783589 := by
  unfold tailWord_527216
  simp only [CollatzResearch.WordTrace]
  refine ⟨9614573628996974084676751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12819431505329298779569001 9614573628996974084676751)
  ·
    refine ⟨14421860443495461127015127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9614573628996974084676751 14421860443495461127015127)
    ·
      refine ⟨21632790665243191690522691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14421860443495461127015127 21632790665243191690522691)
      ·
        refine ⟨32449185997864787535784037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21632790665243191690522691 32449185997864787535784037)
        ·
          refine ⟨6084222374599647662959507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32449185997864787535784037 6084222374599647662959507)
          ·
            refine ⟨9126333561899471494439261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6084222374599647662959507 9126333561899471494439261)
            ·
              refine ⟨3422375085712301810414723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9126333561899471494439261 3422375085712301810414723)
              ·
                refine ⟨5133562628568452715622085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3422375085712301810414723 5133562628568452715622085)
                ·
                  refine ⟨962542992856584884179141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5133562628568452715622085 962542992856584884179141)
                  ·
                    refine ⟨180476811160609665783589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 962542992856584884179141 180476811160609665783589)
                    ·
                      rfl

theorem cell22_527216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 4, 4].length) (baseStart_527216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_527216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_527216 prefixEnd_527216 := by exact prefixLift 527216
  have htrace : WordTrace (prefixWord ++ tailWord_527216) baseStart_527216 baseEnd_527216 := by
    simpa [prefixWord, tailWord_527216, baseEnd_527216] using wordTrace_append hprefix tailTrace_527216
  have hstable : (prefixWord ++ tailWord_527216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527216).length < 2 ^ (prefixWord ++ tailWord_527216).sum := by decide
  have hdescent : baseEnd_527216 < baseStart_527216 := by decide
  rcases family_descends (prefixWord ++ tailWord_527216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527218 : List Nat := [3, 2, 1, 2, 1, 1, 4, 1, 4, 3]
def baseStart_527218 : Nat := 118140960795 + 527218 * 2 ^ 59
def prefixEnd_527218 : Nat := 4983230072969 + 3 ^ 40 * 527218 * 2
def baseEnd_527218 : Nat := 180477495801482327233583

theorem tailTrace_527218 : CollatzResearch.WordTrace tailWord_527218 prefixEnd_527218 180477495801482327233583 := by
  unfold tailWord_527218
  simp only [CollatzResearch.WordTrace]
  refine ⟨4807305050996675627731577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12819480135991135007284205 4807305050996675627731577)
  ·
    refine ⟨3605478788247506720798683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4807305050996675627731577 3605478788247506720798683)
    ·
      refine ⟨5408218182371260081198025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3605478788247506720798683 5408218182371260081198025)
      ·
        refine ⟨4056163636778445060898519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5408218182371260081198025 4056163636778445060898519)
        ·
          refine ⟨6084245455167667591347779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4056163636778445060898519 6084245455167667591347779)
          ·
            refine ⟨9126368182751501387021669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6084245455167667591347779 9126368182751501387021669)
            ·
              refine ⟨1711194034265906510066563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9126368182751501387021669 1711194034265906510066563)
              ·
                refine ⟨2566791051398859765099845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1711194034265906510066563 2566791051398859765099845)
                ·
                  refine ⟨481273322137286205956221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2566791051398859765099845 481273322137286205956221)
                  ·
                    refine ⟨180477495801482327233583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 481273322137286205956221 180477495801482327233583)
                    ·
                      rfl

theorem cell22_527218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 1, 4, 3].length) (baseStart_527218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_527218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_527218 prefixEnd_527218 := by exact prefixLift 527218
  have htrace : WordTrace (prefixWord ++ tailWord_527218) baseStart_527218 baseEnd_527218 := by
    simpa [prefixWord, tailWord_527218, baseEnd_527218] using wordTrace_append hprefix tailTrace_527218
  have hstable : (prefixWord ++ tailWord_527218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527218).length < 2 ^ (prefixWord ++ tailWord_527218).sum := by decide
  have hdescent : baseEnd_527218 < baseStart_527218 := by decide
  rcases family_descends (prefixWord ++ tailWord_527218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527314 : List Nat := [3, 2, 2, 3, 1, 2, 2, 3, 1, 3]
def baseStart_527314 : Nat := 118140960795 + 527314 * 2 ^ 59
def prefixEnd_527314 : Nat := 4983230072969 + 3 ^ 40 * 527314 * 2
def baseEnd_527314 : Nat := 180510358563370076833289

theorem tailTrace_527314 : CollatzResearch.WordTrace tailWord_527314 prefixEnd_527314 180510358563370076833289 := by
  unfold tailWord_527314
  simp only [CollatzResearch.WordTrace]
  refine ⟨4808180402909727726605249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12821814407759273937613997 4808180402909727726605249)
  ·
    refine ⟨3606135302182295794953937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4808180402909727726605249 3606135302182295794953937)
    ·
      refine ⟨2704601476636721846215453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3606135302182295794953937 2704601476636721846215453)
      ·
        refine ⟨1014225553738770692330795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2704601476636721846215453 1014225553738770692330795)
        ·
          refine ⟨1521338330608156038496193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1014225553738770692330795 1521338330608156038496193)
          ·
            refine ⟨1141003747956117028872145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1521338330608156038496193 1141003747956117028872145)
            ·
              refine ⟨855752810967087771654109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1141003747956117028872145 855752810967087771654109)
              ·
                refine ⟨320907304112657914370291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 855752810967087771654109 320907304112657914370291)
                ·
                  refine ⟨481360956168986871555437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 320907304112657914370291 481360956168986871555437)
                  ·
                    refine ⟨180510358563370076833289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 481360956168986871555437 180510358563370076833289)
                    ·
                      rfl

theorem cell22_527314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 3, 1, 3].length) (baseStart_527314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_527314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_527314 prefixEnd_527314 := by exact prefixLift 527314
  have htrace : WordTrace (prefixWord ++ tailWord_527314) baseStart_527314 baseEnd_527314 := by
    simpa [prefixWord, tailWord_527314, baseEnd_527314] using wordTrace_append hprefix tailTrace_527314
  have hstable : (prefixWord ++ tailWord_527314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527314).length < 2 ^ (prefixWord ++ tailWord_527314).sum := by decide
  have hdescent : baseEnd_527314 < baseStart_527314 := by decide
  rcases family_descends (prefixWord ++ tailWord_527314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527327 : List Nat := [1, 1, 2, 3, 6, 1, 1, 2, 5]
def baseStart_527327 : Nat := 118140960795 + 527327 * 2 ^ 59
def prefixEnd_527327 : Nat := 4983230072969 + 3 ^ 40 * 527327 * 2
def baseEnd_527327 : Nat := 60171602909680792086083

theorem tailTrace_527327 : CollatzResearch.WordTrace tailWord_527327 prefixEnd_527327 60171602909680792086083 := by
  unfold tailWord_527327
  simp only [CollatzResearch.WordTrace]
  refine ⟨19233195760591814126644235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12822130507061209417762823 19233195760591814126644235)
  ·
    refine ⟨28849793640887721189966353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19233195760591814126644235 28849793640887721189966353)
    ·
      refine ⟨21637345230665790892474765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28849793640887721189966353 21637345230665790892474765)
      ·
        refine ⟨8114004461499671584678037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21637345230665790892474765 8114004461499671584678037)
        ·
          refine ⟨380343959132797105531783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 8114004461499671584678037 380343959132797105531783)
          ·
            refine ⟨570515938699195658297675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380343959132797105531783 570515938699195658297675)
            ·
              refine ⟨855773908048793487446513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 570515938699195658297675 855773908048793487446513)
              ·
                refine ⟨641830431036595115584885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 855773908048793487446513 641830431036595115584885)
                ·
                  refine ⟨60171602909680792086083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 641830431036595115584885 60171602909680792086083)
                  ·
                    rfl

theorem cell22_527327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 2, 5].length) (baseStart_527327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_527327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_527327 prefixEnd_527327 := by exact prefixLift 527327
  have htrace : WordTrace (prefixWord ++ tailWord_527327) baseStart_527327 baseEnd_527327 := by
    simpa [prefixWord, tailWord_527327, baseEnd_527327] using wordTrace_append hprefix tailTrace_527327
  have hstable : (prefixWord ++ tailWord_527327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527327).length < 2 ^ (prefixWord ++ tailWord_527327).sum := by decide
  have hdescent : baseEnd_527327 < baseStart_527327 := by decide
  rcases family_descends (prefixWord ++ tailWord_527327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527338 : List Nat := [3, 1, 3, 1, 2, 2, 1, 3, 6]
def baseStart_527338 : Nat := 118140960795 + 527338 * 2 ^ 59
def prefixEnd_527338 : Nat := 4983230072969 + 3 ^ 40 * 527338 * 2
def baseEnd_527338 : Nat := 60172858084614004744405

theorem tailTrace_527338 : CollatzResearch.WordTrace tailWord_527338 prefixEnd_527338 60172858084614004744405 := by
  unfold tailWord_527338
  simp only [CollatzResearch.WordTrace]
  refine ⟨4808399240887990751323667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12822397975701308670196445 4808399240887990751323667)
  ·
    refine ⟨7212598861331986126985501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4808399240887990751323667 7212598861331986126985501)
    ·
      refine ⟨2704724572999494797619563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7212598861331986126985501 2704724572999494797619563)
      ·
        refine ⟨4057086859499242196429345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2704724572999494797619563 4057086859499242196429345)
        ·
          refine ⟨3042815144624431647322009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4057086859499242196429345 3042815144624431647322009)
          ·
            refine ⟨2282111358468323735491507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3042815144624431647322009 2282111358468323735491507)
            ·
              refine ⟨3423167037702485603237261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2282111358468323735491507 3423167037702485603237261)
              ·
                refine ⟨1283687639138432101213973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3423167037702485603237261 1283687639138432101213973)
                ·
                  refine ⟨60172858084614004744405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1283687639138432101213973 60172858084614004744405)
                  ·
                    rfl

theorem cell22_527338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 3, 6].length) (baseStart_527338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_527338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_527338 prefixEnd_527338 := by exact prefixLift 527338
  have htrace : WordTrace (prefixWord ++ tailWord_527338) baseStart_527338 baseEnd_527338 := by
    simpa [prefixWord, tailWord_527338, baseEnd_527338] using wordTrace_append hprefix tailTrace_527338
  have hstable : (prefixWord ++ tailWord_527338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527338).length < 2 ^ (prefixWord ++ tailWord_527338).sum := by decide
  have hdescent : baseEnd_527338 < baseStart_527338 := by decide
  rcases family_descends (prefixWord ++ tailWord_527338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527368 : List Nat := [2, 1, 3, 2, 1, 3, 2, 1, 1, 6]
def baseStart_527368 : Nat := 118140960795 + 527368 * 2 ^ 59
def prefixEnd_527368 : Nat := 4983230072969 + 3 ^ 40 * 527368 * 2
def baseEnd_527368 : Nat := 180528843866931935983123

theorem tailTrace_527368 : CollatzResearch.WordTrace tailWord_527368 prefixEnd_527368 180528843866931935983123 := by
  unfold tailWord_527368
  simp only [CollatzResearch.WordTrace]
  refine ⟨9617345576721639064443379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12823127435628852085924505 9617345576721639064443379)
  ·
    refine ⟨14426018365082458596665069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9617345576721639064443379 14426018365082458596665069)
    ·
      refine ⟨5409756886905921973749401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14426018365082458596665069 5409756886905921973749401)
      ·
        refine ⟨4057317665179441480312051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5409756886905921973749401 4057317665179441480312051)
        ·
          refine ⟨6085976497769162220468077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4057317665179441480312051 6085976497769162220468077)
          ·
            refine ⟨2282241186663435832675529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6085976497769162220468077 2282241186663435832675529)
            ·
              refine ⟨1711680889997576874506647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2282241186663435832675529 1711680889997576874506647)
              ·
                refine ⟨2567521334996365311759971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1711680889997576874506647 2567521334996365311759971)
                ·
                  refine ⟨3851282002494547967639957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2567521334996365311759971 3851282002494547967639957)
                  ·
                    refine ⟨180528843866931935983123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3851282002494547967639957 180528843866931935983123)
                    ·
                      rfl

theorem cell22_527368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 1, 1, 6].length) (baseStart_527368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_527368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_527368 prefixEnd_527368 := by exact prefixLift 527368
  have htrace : WordTrace (prefixWord ++ tailWord_527368) baseStart_527368 baseEnd_527368 := by
    simpa [prefixWord, tailWord_527368, baseEnd_527368] using wordTrace_append hprefix tailTrace_527368
  have hstable : (prefixWord ++ tailWord_527368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527368).length < 2 ^ (prefixWord ++ tailWord_527368).sum := by decide
  have hdescent : baseEnd_527368 < baseStart_527368 := by decide
  rcases family_descends (prefixWord ++ tailWord_527368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527370 : List Nat := [3, 1, 2, 2, 3, 1, 1, 2, 4, 3]
def baseStart_527370 : Nat := 118140960795 + 527370 * 2 ^ 59
def prefixEnd_527370 : Nat := 4983230072969 + 3 ^ 40 * 527370 * 2
def baseEnd_527370 : Nat := 180529528507804597433117

theorem tailTrace_527370 : CollatzResearch.WordTrace tailWord_527370 prefixEnd_527370 180529528507804597433117 := by
  unfold tailWord_527370
  simp only [CollatzResearch.WordTrace]
  refine ⟨4808691024859008117614891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12823176066290688313639709 4808691024859008117614891)
  ·
    refine ⟨7213036537288512176422337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4808691024859008117614891 7213036537288512176422337)
    ·
      refine ⟨5409777402966384132316753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7213036537288512176422337 5409777402966384132316753)
      ·
        refine ⟨4057333052224788099237565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5409777402966384132316753 4057333052224788099237565)
        ·
          refine ⟨1521499894584295537214087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4057333052224788099237565 1521499894584295537214087)
          ·
            refine ⟨2282249841876443305821131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1521499894584295537214087 2282249841876443305821131)
            ·
              refine ⟨3423374762814664958731697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2282249841876443305821131 3423374762814664958731697)
              ·
                refine ⟨2567531072110998719048773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3423374762814664958731697 2567531072110998719048773)
                ·
                  refine ⟨481412076020812259821645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2567531072110998719048773 481412076020812259821645)
                  ·
                    refine ⟨180529528507804597433117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 481412076020812259821645 180529528507804597433117)
                    ·
                      rfl

theorem cell22_527370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 2, 4, 3].length) (baseStart_527370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_527370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_527370 prefixEnd_527370 := by exact prefixLift 527370
  have htrace : WordTrace (prefixWord ++ tailWord_527370) baseStart_527370 baseEnd_527370 := by
    simpa [prefixWord, tailWord_527370, baseEnd_527370] using wordTrace_append hprefix tailTrace_527370
  have hstable : (prefixWord ++ tailWord_527370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527370).length < 2 ^ (prefixWord ++ tailWord_527370).sum := by decide
  have hdescent : baseEnd_527370 < baseStart_527370 := by decide
  rcases family_descends (prefixWord ++ tailWord_527370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527372 : List Nat := [2, 2, 1, 2, 3, 4, 1, 3, 4]
def baseStart_527372 : Nat := 118140960795 + 527372 * 2 ^ 59
def prefixEnd_527372 : Nat := 4983230072969 + 3 ^ 40 * 527372 * 2
def baseEnd_527372 : Nat := 60176737716225752961037

theorem tailTrace_527372 : CollatzResearch.WordTrace tailWord_527372 prefixEnd_527372 60176737716225752961037 := by
  unfold tailWord_527372
  simp only [CollatzResearch.WordTrace]
  refine ⟨9617418522714393406016185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12823224696952524541354913 9617418522714393406016185)
  ·
    refine ⟨7213063892035795054512139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9617418522714393406016185 7213063892035795054512139)
    ·
      refine ⟨10819595838053692581768209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7213063892035795054512139 10819595838053692581768209)
      ·
        refine ⟨8114696878540269436326157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10819595838053692581768209 8114696878540269436326157)
        ·
          refine ⟨3043011329452601038622309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8114696878540269436326157 3043011329452601038622309)
          ·
            refine ⟨570564624272362694741683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3043011329452601038622309 570564624272362694741683)
            ·
              refine ⟨855846936408544042112525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 570564624272362694741683 855846936408544042112525)
              ·
                refine ⟨320942601153204015792197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 855846936408544042112525 320942601153204015792197)
                ·
                  refine ⟨60176737716225752961037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 320942601153204015792197 60176737716225752961037)
                  ·
                    rfl

theorem cell22_527372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 3, 4].length) (baseStart_527372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_527372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_527372 prefixEnd_527372 := by exact prefixLift 527372
  have htrace : WordTrace (prefixWord ++ tailWord_527372) baseStart_527372 baseEnd_527372 := by
    simpa [prefixWord, tailWord_527372, baseEnd_527372] using wordTrace_append hprefix tailTrace_527372
  have hstable : (prefixWord ++ tailWord_527372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527372).length < 2 ^ (prefixWord ++ tailWord_527372).sum := by decide
  have hdescent : baseEnd_527372 < baseStart_527372 := by decide
  rcases family_descends (prefixWord ++ tailWord_527372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527383 : List Nat := [1, 1, 3, 5, 1, 1, 10]
def baseStart_527383 : Nat := 118140960795 + 527383 * 2 ^ 59
def prefixEnd_527383 : Nat := 4983230072969 + 3 ^ 40 * 527383 * 2
def baseEnd_527383 : Nat := 6686443654573218402151

theorem tailTrace_527383 : CollatzResearch.WordTrace tailWord_527383 prefixEnd_527383 6686443654573218402151 := by
  unfold tailWord_527383
  simp only [CollatzResearch.WordTrace]
  refine ⟨19235238248388935690682803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12823492165592623793788535 19235238248388935690682803)
  ·
    refine ⟨28852857372583403536024205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19235238248388935690682803 28852857372583403536024205)
    ·
      refine ⟨10819821514718776326009077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28852857372583403536024205 10819821514718776326009077)
      ·
        refine ⟨1014358267004885280563351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10819821514718776326009077 1014358267004885280563351)
        ·
          refine ⟨1521537400507327920845027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1014358267004885280563351 1521537400507327920845027)
          ·
            refine ⟨2282306100760991881267541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1521537400507327920845027 2282306100760991881267541)
            ·
              refine ⟨6686443654573218402151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2282306100760991881267541 6686443654573218402151)
              ·
                rfl

theorem cell22_527383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 10].length) (baseStart_527383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_527383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_527383 prefixEnd_527383 := by exact prefixLift 527383
  have htrace : WordTrace (prefixWord ++ tailWord_527383) baseStart_527383 baseEnd_527383 := by
    simpa [prefixWord, tailWord_527383, baseEnd_527383] using wordTrace_append hprefix tailTrace_527383
  have hstable : (prefixWord ++ tailWord_527383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527383).length < 2 ^ (prefixWord ++ tailWord_527383).sum := by decide
  have hdescent : baseEnd_527383 < baseStart_527383 := by decide
  rcases family_descends (prefixWord ++ tailWord_527383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527389 : List Nat := [1, 4, 2, 2, 3, 1, 3, 2, 4]
def baseStart_527389 : Nat := 118140960795 + 527389 * 2 ^ 59
def prefixEnd_527389 : Nat := 4983230072969 + 3 ^ 40 * 527389 * 2
def baseEnd_527389 : Nat := 60178677532031627069353

theorem tailTrace_527389 : CollatzResearch.WordTrace tailWord_527389 prefixEnd_527389 60178677532031627069353 := by
  unfold tailWord_527389
  simp only [CollatzResearch.WordTrace]
  refine ⟨19235457086367198715401221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12823638057578132476934147 19235457086367198715401221)
  ·
    refine ⟨3606648203693849759137729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19235457086367198715401221 3606648203693849759137729)
    ·
      refine ⟨2704986152770387319353297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3606648203693849759137729 2704986152770387319353297)
      ·
        refine ⟨2028739614577790489514973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2704986152770387319353297 2028739614577790489514973)
        ·
          refine ⟨760777355466671433568115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2028739614577790489514973 760777355466671433568115)
          ·
            refine ⟨1141166033200007150352173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 760777355466671433568115 1141166033200007150352173)
            ·
              refine ⟨427937262450002681382065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1141166033200007150352173 427937262450002681382065)
              ·
                refine ⟨320952946837502011036549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 427937262450002681382065 320952946837502011036549)
                ·
                  refine ⟨60178677532031627069353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 320952946837502011036549 60178677532031627069353)
                  ·
                    rfl

theorem cell22_527389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 3, 2, 4].length) (baseStart_527389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_527389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_527389 prefixEnd_527389 := by exact prefixLift 527389
  have htrace : WordTrace (prefixWord ++ tailWord_527389) baseStart_527389 baseEnd_527389 := by
    simpa [prefixWord, tailWord_527389, baseEnd_527389] using wordTrace_append hprefix tailTrace_527389
  have hstable : (prefixWord ++ tailWord_527389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527389).length < 2 ^ (prefixWord ++ tailWord_527389).sum := by decide
  have hdescent : baseEnd_527389 < baseStart_527389 := by decide
  rcases family_descends (prefixWord ++ tailWord_527389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527432 : List Nat := [2, 1, 3, 1, 1, 1, 4, 5, 1, 3]
def baseStart_527432 : Nat := 118140960795 + 527432 * 2 ^ 59
def prefixEnd_527432 : Nat := 4983230072969 + 3 ^ 40 * 527432 * 2
def baseEnd_527432 : Nat := 180550752374857102382927

theorem tailTrace_527432 : CollatzResearch.WordTrace tailWord_527432 prefixEnd_527432 180550752374857102382927 := by
  unfold tailWord_527432
  simp only [CollatzResearch.WordTrace]
  refine ⟨9618512712605708529608275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12824683616807611372811033 9618512712605708529608275)
  ·
    refine ⟨14427769068908562794412413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9618512712605708529608275 14427769068908562794412413)
    ·
      refine ⟨5410413400840711047904655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14427769068908562794412413 5410413400840711047904655)
      ·
        refine ⟨8115620101261066571856983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5410413400840711047904655 8115620101261066571856983)
        ·
          refine ⟨12173430151891599857785475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8115620101261066571856983 12173430151891599857785475)
          ·
            refine ⟨18260145227837399786678213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12173430151891599857785475 18260145227837399786678213)
            ·
              refine ⟨3423777230219512460002165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18260145227837399786678213 3423777230219512460002165)
              ·
                refine ⟨320979115333079293125203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3423777230219512460002165 320979115333079293125203)
                ·
                  refine ⟨481468672999618939687805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 320979115333079293125203 481468672999618939687805)
                  ·
                    refine ⟨180550752374857102382927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 481468672999618939687805 180550752374857102382927)
                    ·
                      rfl

theorem cell22_527432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 5, 1, 3].length) (baseStart_527432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_527432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_527432 prefixEnd_527432 := by exact prefixLift 527432
  have htrace : WordTrace (prefixWord ++ tailWord_527432) baseStart_527432 baseEnd_527432 := by
    simpa [prefixWord, tailWord_527432, baseEnd_527432] using wordTrace_append hprefix tailTrace_527432
  have hstable : (prefixWord ++ tailWord_527432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527432).length < 2 ^ (prefixWord ++ tailWord_527432).sum := by decide
  have hdescent : baseEnd_527432 < baseStart_527432 := by decide
  rcases family_descends (prefixWord ++ tailWord_527432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527445 : List Nat := [1, 3, 2, 2, 1, 2, 4, 2, 5]
def baseStart_527445 : Nat := 118140960795 + 527445 * 2 ^ 59
def prefixEnd_527445 : Nat := 4983230072969 + 3 ^ 40 * 527445 * 2
def baseEnd_527445 : Nat := 60185067513509800602629

theorem tailTrace_527445 : CollatzResearch.WordTrace tailWord_527445 prefixEnd_527445 60185067513509800602629 := by
  unfold tailWord_527445
  simp only [CollatzResearch.WordTrace]
  refine ⟨19237499574164320279439789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12824999716109546852959859 19237499574164320279439789)
  ·
    refine ⟨7214062340311620104789921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19237499574164320279439789 7214062340311620104789921)
    ·
      refine ⟨5410546755233715078592441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7214062340311620104789921 5410546755233715078592441)
      ·
        refine ⟨4057910066425286308944331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5410546755233715078592441 4057910066425286308944331)
        ·
          refine ⟨6086865099637929463416497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4057910066425286308944331 6086865099637929463416497)
          ·
            refine ⟨4565148824728447097562373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6086865099637929463416497 4565148824728447097562373)
            ·
              refine ⟨855965404636583830792945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4565148824728447097562373 855965404636583830792945)
              ·
                refine ⟨641974053477437873094709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 855965404636583830792945 641974053477437873094709)
                ·
                  refine ⟨60185067513509800602629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 641974053477437873094709 60185067513509800602629)
                  ·
                    rfl

theorem cell22_527445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 2, 5].length) (baseStart_527445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_527445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_527445 prefixEnd_527445 := by exact prefixLift 527445
  have htrace : WordTrace (prefixWord ++ tailWord_527445) baseStart_527445 baseEnd_527445 := by
    simpa [prefixWord, tailWord_527445, baseEnd_527445] using wordTrace_append hprefix tailTrace_527445
  have hstable : (prefixWord ++ tailWord_527445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527445).length < 2 ^ (prefixWord ++ tailWord_527445).sum := by decide
  have hdescent : baseEnd_527445 < baseStart_527445 := by decide
  rcases family_descends (prefixWord ++ tailWord_527445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527492 : List Nat := [2, 3, 2, 1, 2, 3, 1, 3, 1, 4]
def baseStart_527492 : Nat := 118140960795 + 527492 * 2 ^ 59
def prefixEnd_527492 : Nat := 4983230072969 + 3 ^ 40 * 527492 * 2
def baseEnd_527492 : Nat := 180571291601036945882743

theorem tailTrace_527492 : CollatzResearch.WordTrace tailWord_527492 prefixEnd_527492 180571291601036945882743 := by
  unfold tailWord_527492
  simp only [CollatzResearch.WordTrace]
  refine ⟨9619606902497023653200365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12826142536662698204267153 9619606902497023653200365)
  ·
    refine ⟨3607352588436383869950137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9619606902497023653200365 3607352588436383869950137)
    ·
      refine ⟨2705514441327287902462603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3607352588436383869950137 2705514441327287902462603)
      ·
        refine ⟨4058271661990931853693905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2705514441327287902462603 4058271661990931853693905)
        ·
          refine ⟨3043703746493198890270429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4058271661990931853693905 3043703746493198890270429)
          ·
            refine ⟨1141388904934949583851411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3043703746493198890270429 1141388904934949583851411)
            ·
              refine ⟨1712083357402424375777117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1141388904934949583851411 1712083357402424375777117)
              ·
                refine ⟨642031259025909140916419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1712083357402424375777117 642031259025909140916419)
                ·
                  refine ⟨963046888538863711374629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 642031259025909140916419 963046888538863711374629)
                  ·
                    refine ⟨180571291601036945882743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 963046888538863711374629 180571291601036945882743)
                    ·
                      rfl

theorem cell22_527492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_527492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_527492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_527492 prefixEnd_527492 := by exact prefixLift 527492
  have htrace : WordTrace (prefixWord ++ tailWord_527492) baseStart_527492 baseEnd_527492 := by
    simpa [prefixWord, tailWord_527492, baseEnd_527492] using wordTrace_append hprefix tailTrace_527492
  have hstable : (prefixWord ++ tailWord_527492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527492).length < 2 ^ (prefixWord ++ tailWord_527492).sum := by decide
  have hdescent : baseEnd_527492 < baseStart_527492 := by decide
  rcases family_descends (prefixWord ++ tailWord_527492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527535 : List Nat := [1, 1, 2, 1, 2, 3, 6, 6]
def baseStart_527535 : Nat := 118140960795 + 527535 * 2 ^ 59
def prefixEnd_527535 : Nat := 4983230072969 + 3 ^ 40 * 527535 * 2
def baseEnd_527535 : Nat := 20065112375533240784179

theorem tailTrace_527535 : CollatzResearch.WordTrace tailWord_527535 prefixEnd_527535 20065112375533240784179 := by
  unfold tailWord_527535
  simp only [CollatzResearch.WordTrace]
  refine ⟨19240782143838265650216059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12827188095892177100144039 19240782143838265650216059)
  ·
    refine ⟨28861173215757398475324089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19240782143838265650216059 28861173215757398475324089)
    ·
      refine ⟨21645879911818048856493067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28861173215757398475324089 21645879911818048856493067)
      ·
        refine ⟨32468819867727073284739601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21645879911818048856493067 32468819867727073284739601)
        ·
          refine ⟨24351614900795304963554701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32468819867727073284739601 24351614900795304963554701)
          ·
            refine ⟨9131855587798239361333013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24351614900795304963554701 9131855587798239361333013)
            ·
              refine ⟨428055730678042470062485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 9131855587798239361333013 428055730678042470062485)
              ·
                refine ⟨20065112375533240784179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 428055730678042470062485 20065112375533240784179)
                ·
                  rfl

theorem cell22_527535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 6, 6].length) (baseStart_527535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_527535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_527535 prefixEnd_527535 := by exact prefixLift 527535
  have htrace : WordTrace (prefixWord ++ tailWord_527535) baseStart_527535 baseEnd_527535 := by
    simpa [prefixWord, tailWord_527535, baseEnd_527535] using wordTrace_append hprefix tailTrace_527535
  have hstable : (prefixWord ++ tailWord_527535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527535).length < 2 ^ (prefixWord ++ tailWord_527535).sum := by decide
  have hdescent : baseEnd_527535 < baseStart_527535 := by decide
  rcases family_descends (prefixWord ++ tailWord_527535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527552 : List Nat := [2, 1, 1, 2, 7, 1, 8]
def baseStart_527552 : Nat := 118140960795 + 527552 * 2 ^ 59
def prefixEnd_527552 : Nat := 4983230072969 + 3 ^ 40 * 527552 * 2
def baseEnd_527552 : Nat := 6688586326933955162317

theorem tailTrace_527552 : CollatzResearch.WordTrace tailWord_527552 prefixEnd_527552 6688586326933955162317 := by
  unfold tailWord_527552
  simp only [CollatzResearch.WordTrace]
  refine ⟨9620701092388338776792455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12827601456517785035723273 9620701092388338776792455)
  ·
    refine ⟨14431051638582508165188683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9620701092388338776792455 14431051638582508165188683)
    ·
      refine ⟨21646577457873762247783025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14431051638582508165188683 21646577457873762247783025)
      ·
        refine ⟨16234933093405321685837269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21646577457873762247783025 16234933093405321685837269)
        ·
          refine ⟨380506244376687227011811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 16234933093405321685837269 380506244376687227011811)
          ·
            refine ⟨570759366565030840517717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380506244376687227011811 570759366565030840517717)
            ·
              refine ⟨6688586326933955162317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 570759366565030840517717 6688586326933955162317)
              ·
                rfl

theorem cell22_527552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 8].length) (baseStart_527552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_527552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_527552 prefixEnd_527552 := by exact prefixLift 527552
  have htrace : WordTrace (prefixWord ++ tailWord_527552) baseStart_527552 baseEnd_527552 := by
    simpa [prefixWord, tailWord_527552, baseEnd_527552] using wordTrace_append hprefix tailTrace_527552
  have hstable : (prefixWord ++ tailWord_527552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527552).length < 2 ^ (prefixWord ++ tailWord_527552).sum := by decide
  have hdescent : baseEnd_527552 < baseStart_527552 := by decide
  rcases family_descends (prefixWord ++ tailWord_527552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527558 : List Nat := [6, 1, 2, 2, 1, 2, 1, 1, 6]
def baseStart_527558 : Nat := 118140960795 + 527558 * 2 ^ 59
def prefixEnd_527558 : Nat := 4983230072969 + 3 ^ 40 * 527558 * 2
def baseEnd_527558 : Nat := 60197961583278257910847

theorem tailTrace_527558 : CollatzResearch.WordTrace tailWord_527558 prefixEnd_527558 60197961583278257910847 := by
  unfold tailWord_527558
  simp only [CollatzResearch.WordTrace]
  refine ⟨601300656961091893071979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 12827747348503293718868885 601300656961091893071979)
  ·
    refine ⟨901950985441637839607969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 601300656961091893071979 901950985441637839607969)
    ·
      refine ⟨676463239081228379705977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 901950985441637839607969 676463239081228379705977)
      ·
        refine ⟨507347429310921284779483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 676463239081228379705977 507347429310921284779483)
        ·
          refine ⟨761021143966381927169225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 507347429310921284779483 761021143966381927169225)
          ·
            refine ⟨570765857974786445376919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 761021143966381927169225 570765857974786445376919)
            ·
              refine ⟨856148786962179668065379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 570765857974786445376919 856148786962179668065379)
              ·
                refine ⟨1284223180443269502098069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 856148786962179668065379 1284223180443269502098069)
                ·
                  refine ⟨60197961583278257910847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1284223180443269502098069 60197961583278257910847)
                  ·
                    rfl

theorem cell22_527558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_527558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_527558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_527558 prefixEnd_527558 := by exact prefixLift 527558
  have htrace : WordTrace (prefixWord ++ tailWord_527558) baseStart_527558 baseEnd_527558 := by
    simpa [prefixWord, tailWord_527558, baseEnd_527558] using wordTrace_append hprefix tailTrace_527558
  have hstable : (prefixWord ++ tailWord_527558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527558).length < 2 ^ (prefixWord ++ tailWord_527558).sum := by decide
  have hdescent : baseEnd_527558 < baseStart_527558 := by decide
  rcases family_descends (prefixWord ++ tailWord_527558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527614 : List Nat := [4, 2, 2, 1, 1, 3, 2, 2, 5]
def baseStart_527614 : Nat := 118140960795 + 527614 * 2 ^ 59
def prefixEnd_527614 : Nat := 4983230072969 + 3 ^ 40 * 527614 * 2
def baseEnd_527614 : Nat := 60204351564756431444123

theorem tailTrace_527614 : CollatzResearch.WordTrace tailWord_527614 prefixEnd_527614 60204351564756431444123 := by
  unfold tailWord_527614
  simp only [CollatzResearch.WordTrace]
  refine ⟨2405457938819007767792737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12829109007034708094894597 2405457938819007767792737)
  ·
    refine ⟨1804093454114255825844553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2405457938819007767792737 1804093454114255825844553)
    ·
      refine ⟨1353070090585691869383415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1804093454114255825844553 1353070090585691869383415)
      ·
        refine ⟨2029605135878537804075123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1353070090585691869383415 2029605135878537804075123)
        ·
          refine ⟨3044407703817806706112685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2029605135878537804075123 3044407703817806706112685)
          ·
            refine ⟨1141652888931677514792257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3044407703817806706112685 1141652888931677514792257)
            ·
              refine ⟨856239666698758136094193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1141652888931677514792257 856239666698758136094193)
              ·
                refine ⟨642179750024068602070645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 856239666698758136094193 642179750024068602070645)
                ·
                  refine ⟨60204351564756431444123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 642179750024068602070645 60204351564756431444123)
                  ·
                    rfl

theorem cell22_527614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 2, 5].length) (baseStart_527614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_527614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_527614 prefixEnd_527614 := by exact prefixLift 527614
  have htrace : WordTrace (prefixWord ++ tailWord_527614) baseStart_527614 baseEnd_527614 := by
    simpa [prefixWord, tailWord_527614, baseEnd_527614] using wordTrace_append hprefix tailTrace_527614
  have hstable : (prefixWord ++ tailWord_527614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527614).length < 2 ^ (prefixWord ++ tailWord_527614).sum := by decide
  have hdescent : baseEnd_527614 < baseStart_527614 := by decide
  rcases family_descends (prefixWord ++ tailWord_527614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527618 : List Nat := [3, 4, 1, 1, 3, 1, 1, 4, 1, 3]
def baseStart_527618 : Nat := 118140960795 + 527618 * 2 ^ 59
def prefixEnd_527618 : Nat := 4983230072969 + 3 ^ 40 * 527618 * 2
def baseEnd_527618 : Nat := 180614423976014617232357

theorem tailTrace_527618 : CollatzResearch.WordTrace tailWord_527618 prefixEnd_527618 180614423976014617232357 := by
  unfold tailWord_527618
  simp only [CollatzResearch.WordTrace]
  refine ⟨4810952350634392706371877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12829206268358380550325005 4810952350634392706371877)
  ·
    refine ⟨902053565743948632444727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4810952350634392706371877 902053565743948632444727)
    ·
      refine ⟨1353080348615922948667091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 902053565743948632444727 1353080348615922948667091)
      ·
        refine ⟨2029620522923884423000637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1353080348615922948667091 2029620522923884423000637)
        ·
          refine ⟨761107696096456658625239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2029620522923884423000637 761107696096456658625239)
          ·
            refine ⟨1141661544144684987937859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 761107696096456658625239 1141661544144684987937859)
            ·
              refine ⟨1712492316217027481906789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1141661544144684987937859 1712492316217027481906789)
              ·
                refine ⟨321092309290692652857523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1712492316217027481906789 321092309290692652857523)
                ·
                  refine ⟨481638463936038979286285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 321092309290692652857523 481638463936038979286285)
                  ·
                    refine ⟨180614423976014617232357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 481638463936038979286285 180614423976014617232357)
                    ·
                      rfl

theorem cell22_527618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_527618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_527618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_527618 prefixEnd_527618 := by exact prefixLift 527618
  have htrace : WordTrace (prefixWord ++ tailWord_527618) baseStart_527618 baseEnd_527618 := by
    simpa [prefixWord, tailWord_527618, baseEnd_527618] using wordTrace_append hprefix tailTrace_527618
  have hstable : (prefixWord ++ tailWord_527618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527618).length < 2 ^ (prefixWord ++ tailWord_527618).sum := by decide
  have hdescent : baseEnd_527618 < baseStart_527618 := by decide
  rcases family_descends (prefixWord ++ tailWord_527618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527625 : List Nat := [1, 2, 1, 1, 3, 3, 2, 3, 6]
def baseStart_527625 : Nat := 118140960795 + 527625 * 2 ^ 59
def prefixEnd_527625 : Nat := 4983230072969 + 3 ^ 40 * 527625 * 2
def baseEnd_527625 : Nat := 60205606739689644102445

theorem tailTrace_527625 : CollatzResearch.WordTrace tailWord_527625 prefixEnd_527625 60205606739689644102445 := by
  unfold tailWord_527625
  simp only [CollatzResearch.WordTrace]
  refine ⟨19244064713512211020992329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12829376475674807347328219 19244064713512211020992329)
  ·
    refine ⟨14433048535134158265744247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19244064713512211020992329 14433048535134158265744247)
    ·
      refine ⟨21649572802701237398616371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14433048535134158265744247 21649572802701237398616371)
      ·
        refine ⟨32474359204051856097924557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21649572802701237398616371 32474359204051856097924557)
        ·
          refine ⟨12177884701519446036721709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32474359204051856097924557 12177884701519446036721709)
          ·
            refine ⟨4566706763069792263770641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12177884701519446036721709 4566706763069792263770641)
            ·
              refine ⟨3425030072302344197827981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4566706763069792263770641 3425030072302344197827981)
              ·
                refine ⟨1284386277113379074185493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3425030072302344197827981 1284386277113379074185493)
                ·
                  refine ⟨60205606739689644102445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1284386277113379074185493 60205606739689644102445)
                  ·
                    rfl

theorem cell22_527625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 3, 6].length) (baseStart_527625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_527625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_527625 prefixEnd_527625 := by exact prefixLift 527625
  have htrace : WordTrace (prefixWord ++ tailWord_527625) baseStart_527625 baseEnd_527625 := by
    simpa [prefixWord, tailWord_527625, baseEnd_527625] using wordTrace_append hprefix tailTrace_527625
  have hstable : (prefixWord ++ tailWord_527625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527625).length < 2 ^ (prefixWord ++ tailWord_527625).sum := by decide
  have hdescent : baseEnd_527625 < baseStart_527625 := by decide
  rcases family_descends (prefixWord ++ tailWord_527625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527642 : List Nat := [3, 1, 1, 3, 3, 2, 1, 2, 6]
def baseStart_527642 : Nat := 118140960795 + 527642 * 2 ^ 59
def prefixEnd_527642 : Nat := 4983230072969 + 3 ^ 40 * 527642 * 2
def baseEnd_527642 : Nat := 60207546555495518210761

theorem tailTrace_527642 : CollatzResearch.WordTrace tailWord_527642 prefixEnd_527642 60207546555495518210761 := by
  unfold tailWord_527642
  simp only [CollatzResearch.WordTrace]
  refine ⟨4811171188612655731090295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12829789836300415282907453 4811171188612655731090295)
  ·
    refine ⟨7216756782918983596635443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4811171188612655731090295 7216756782918983596635443)
    ·
      refine ⟨10825135174378475394953165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7216756782918983596635443 10825135174378475394953165)
      ·
        refine ⟨4059425690391928273107437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10825135174378475394953165 4059425690391928273107437)
        ·
          refine ⟨1522284633896973102415289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4059425690391928273107437 1522284633896973102415289)
          ·
            refine ⟨1141713475422729826811467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1522284633896973102415289 1141713475422729826811467)
            ·
              refine ⟨1712570213134094740217201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1141713475422729826811467 1712570213134094740217201)
              ·
                refine ⟨1284427659850571055162901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1712570213134094740217201 1284427659850571055162901)
                ·
                  refine ⟨60207546555495518210761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1284427659850571055162901 60207546555495518210761)
                  ·
                    rfl

theorem cell22_527642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 2, 6].length) (baseStart_527642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_527642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_527642 prefixEnd_527642 := by exact prefixLift 527642
  have htrace : WordTrace (prefixWord ++ tailWord_527642) baseStart_527642 baseEnd_527642 := by
    simpa [prefixWord, tailWord_527642, baseEnd_527642] using wordTrace_append hprefix tailTrace_527642
  have hstable : (prefixWord ++ tailWord_527642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527642).length < 2 ^ (prefixWord ++ tailWord_527642).sum := by decide
  have hdescent : baseEnd_527642 < baseStart_527642 := by decide
  rcases family_descends (prefixWord ++ tailWord_527642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527661 : List Nat := [1, 5, 3, 1, 1, 2, 1, 3, 1, 4]
def baseStart_527661 : Nat := 118140960795 + 527661 * 2 ^ 59
def prefixEnd_527661 : Nat := 4983230072969 + 3 ^ 40 * 527661 * 2
def baseEnd_527661 : Nat := 180629143754776838407225

theorem tailTrace_527661 : CollatzResearch.WordTrace tailWord_527661 prefixEnd_527661 180629143754776838407225 := by
  unfold tailWord_527661
  simp only [CollatzResearch.WordTrace]
  refine ⟨19245377741381789169302837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12830251827587859446201891 19245377741381789169302837)
  ·
    refine ⟨1804254163254542734622141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19245377741381789169302837 1804254163254542734622141)
    ·
      refine ⟨676595311220453525483303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1804254163254542734622141 676595311220453525483303)
      ·
        refine ⟨1014892966830680288224955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 676595311220453525483303 1014892966830680288224955)
        ·
          refine ⟨1522339450246020432337433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1014892966830680288224955 1522339450246020432337433)
          ·
            refine ⟨1141754587684515324253075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1522339450246020432337433 1141754587684515324253075)
            ·
              refine ⟨1712631881526772986379613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1141754587684515324253075 1712631881526772986379613)
              ·
                refine ⟨642236955572539869892355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1712631881526772986379613 642236955572539869892355)
                ·
                  refine ⟨963355433358809804838533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 642236955572539869892355 963355433358809804838533)
                  ·
                    refine ⟨180629143754776838407225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 963355433358809804838533 180629143754776838407225)
                    ·
                      rfl

theorem cell22_527661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_527661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_527661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_527661 prefixEnd_527661 := by exact prefixLift 527661
  have htrace : WordTrace (prefixWord ++ tailWord_527661) baseStart_527661 baseEnd_527661 := by
    simpa [prefixWord, tailWord_527661, baseEnd_527661] using wordTrace_append hprefix tailTrace_527661
  have hstable : (prefixWord ++ tailWord_527661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527661).length < 2 ^ (prefixWord ++ tailWord_527661).sum := by decide
  have hdescent : baseEnd_527661 < baseStart_527661 := by decide
  rcases family_descends (prefixWord ++ tailWord_527661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527742 : List Nat := [4, 2, 3, 2, 1, 2, 2, 1, 2, 3]
def baseStart_527742 : Nat := 118140960795 + 527742 * 2 ^ 59
def prefixEnd_527742 : Nat := 4983230072969 + 3 ^ 40 * 527742 * 2
def baseEnd_527742 : Nat := 180656871710119627131977

theorem tailTrace_527742 : CollatzResearch.WordTrace tailWord_527742 prefixEnd_527742 180656871710119627131977 := by
  unfold tailWord_527742
  simp only [CollatzResearch.WordTrace]
  refine ⟨2406041506761042500375185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12832221369392226668667653 2406041506761042500375185)
  ·
    refine ⟨1804531130070781875281389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2406041506761042500375185 1804531130070781875281389)
    ·
      refine ⟨676699173776543203230521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1804531130070781875281389 676699173776543203230521)
      ·
        refine ⟨507524380332407402422891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 676699173776543203230521 507524380332407402422891)
        ·
          refine ⟨761286570498611103634337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 507524380332407402422891 761286570498611103634337)
          ·
            refine ⟨570964927873958327725753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 761286570498611103634337 570964927873958327725753)
            ·
              refine ⟨428223695905468745794315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 570964927873958327725753 428223695905468745794315)
              ·
                refine ⟨642335543858203118691473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 428223695905468745794315 642335543858203118691473)
                ·
                  refine ⟨481751657893652339018605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 642335543858203118691473 481751657893652339018605)
                  ·
                    refine ⟨180656871710119627131977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 481751657893652339018605 180656871710119627131977)
                    ·
                      rfl

theorem cell22_527742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_527742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_527742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_527742 prefixEnd_527742 := by exact prefixLift 527742
  have htrace : WordTrace (prefixWord ++ tailWord_527742) baseStart_527742 baseEnd_527742 := by
    simpa [prefixWord, tailWord_527742, baseEnd_527742] using wordTrace_append hprefix tailTrace_527742
  have hstable : (prefixWord ++ tailWord_527742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527742).length < 2 ^ (prefixWord ++ tailWord_527742).sum := by decide
  have hdescent : baseEnd_527742 < baseStart_527742 := by decide
  rcases family_descends (prefixWord ++ tailWord_527742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527749 : List Nat := [1, 3, 1, 1, 3, 1, 6, 1, 5]
def baseStart_527749 : Nat := 118140960795 + 527749 * 2 ^ 59
def prefixEnd_527749 : Nat := 4983230072969 + 3 ^ 40 * 527749 * 2
def baseEnd_527749 : Nat := 60219755984391314068985

theorem tailTrace_527749 : CollatzResearch.WordTrace tailWord_527749 prefixEnd_527749 60219755984391314068985 := by
  unfold tailWord_527749
  simp only [CollatzResearch.WordTrace]
  refine ⟨19248587365062980198506301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12832391576708653465670867 19248587365062980198506301)
  ·
    refine ⟨7218220261898617574439863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19248587365062980198506301 7218220261898617574439863)
    ·
      refine ⟨10827330392847926361659795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7218220261898617574439863 10827330392847926361659795)
      ·
        refine ⟨16240995589271889542489693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10827330392847926361659795 16240995589271889542489693)
        ·
          refine ⟨6090373345976958578433635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16240995589271889542489693 6090373345976958578433635)
          ·
            refine ⟨9135560018965437867650453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6090373345976958578433635 9135560018965437867650453)
            ·
              refine ⟨428229375889004900046115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 9135560018965437867650453 428229375889004900046115)
              ·
                refine ⟨642344063833507350069173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 428229375889004900046115 642344063833507350069173)
                ·
                  refine ⟨60219755984391314068985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 642344063833507350069173 60219755984391314068985)
                  ·
                    rfl

theorem cell22_527749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 6, 1, 5].length) (baseStart_527749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_527749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_527749 prefixEnd_527749 := by exact prefixLift 527749
  have htrace : WordTrace (prefixWord ++ tailWord_527749) baseStart_527749 baseEnd_527749 := by
    simpa [prefixWord, tailWord_527749, baseEnd_527749] using wordTrace_append hprefix tailTrace_527749
  have hstable : (prefixWord ++ tailWord_527749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527749).length < 2 ^ (prefixWord ++ tailWord_527749).sum := by decide
  have hdescent : baseEnd_527749 < baseStart_527749 := by decide
  rcases family_descends (prefixWord ++ tailWord_527749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527807 : List Nat := [1, 1, 2, 2, 2, 1, 1, 4, 4, 4]
def baseStart_527807 : Nat := 118140960795 + 527807 * 2 ^ 59
def prefixEnd_527807 : Nat := 4983230072969 + 3 ^ 40 * 527807 * 2
def baseEnd_527807 : Nat := 180679122538481124256777

theorem tailTrace_527807 : CollatzResearch.WordTrace tailWord_527807 prefixEnd_527807 180679122538481124256777 := by
  unfold tailWord_527807
  simp only [CollatzResearch.WordTrace]
  refine ⟨19250702798852856104117675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12833801865901904069411783 19250702798852856104117675)
  ·
    refine ⟨28876054198279284156176513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19250702798852856104117675 28876054198279284156176513)
    ·
      refine ⟨21657040648709463117132385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28876054198279284156176513 21657040648709463117132385)
      ·
        refine ⟨16242780486532097337849289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21657040648709463117132385 16242780486532097337849289)
        ·
          refine ⟨12182085364899073003386967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16242780486532097337849289 12182085364899073003386967)
          ·
            refine ⟨18273128047348609505080451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12182085364899073003386967 18273128047348609505080451)
            ·
              refine ⟨27409692071022914257620677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18273128047348609505080451 27409692071022914257620677)
              ·
                refine ⟨5139317263316796423303877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27409692071022914257620677 5139317263316796423303877)
                ·
                  refine ⟨963621986871899329369477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5139317263316796423303877 963621986871899329369477)
                  ·
                    refine ⟨180679122538481124256777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 963621986871899329369477 180679122538481124256777)
                    ·
                      rfl

theorem cell22_527807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 4, 4].length) (baseStart_527807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_527807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_527807 prefixEnd_527807 := by exact prefixLift 527807
  have htrace : WordTrace (prefixWord ++ tailWord_527807) baseStart_527807 baseEnd_527807 := by
    simpa [prefixWord, tailWord_527807, baseEnd_527807] using wordTrace_append hprefix tailTrace_527807
  have hstable : (prefixWord ++ tailWord_527807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527807).length < 2 ^ (prefixWord ++ tailWord_527807).sum := by decide
  have hdescent : baseEnd_527807 < baseStart_527807 := by decide
  rcases family_descends (prefixWord ++ tailWord_527807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527822 : List Nat := [4, 1, 1, 1, 2, 1, 2, 10]
def baseStart_527822 : Nat := 118140960795 + 527822 * 2 ^ 59
def prefixEnd_527822 : Nat := 4983230072969 + 3 ^ 40 * 527822 * 2
def baseEnd_527822 : Nat := 20076028593891787236859

theorem tailTrace_527822 : CollatzResearch.WordTrace tailWord_527822 prefixEnd_527822 20076028593891787236859 := by
  unfold tailWord_527822
  simp only [CollatzResearch.WordTrace]
  refine ⟨2406406236724814208239215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12834166595865675777275813 2406406236724814208239215)
  ·
    refine ⟨3609609355087221312358823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2406406236724814208239215 3609609355087221312358823)
    ·
      refine ⟨5414414032630831968538235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3609609355087221312358823 5414414032630831968538235)
      ·
        refine ⟨8121621048946247952807353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5414414032630831968538235 8121621048946247952807353)
        ·
          refine ⟨6091215786709685964605515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8121621048946247952807353 6091215786709685964605515)
          ·
            refine ⟨9136823680064528946908273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6091215786709685964605515 9136823680064528946908273)
            ·
              refine ⟨6852617760048396710181205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9136823680064528946908273 6852617760048396710181205)
              ·
                refine ⟨20076028593891787236859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 6852617760048396710181205 20076028593891787236859)
                ·
                  rfl

theorem cell22_527822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 10].length) (baseStart_527822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_527822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_527822 prefixEnd_527822 := by exact prefixLift 527822
  have htrace : WordTrace (prefixWord ++ tailWord_527822) baseStart_527822 baseEnd_527822 := by
    simpa [prefixWord, tailWord_527822, baseEnd_527822] using wordTrace_append hprefix tailTrace_527822
  have hstable : (prefixWord ++ tailWord_527822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527822).length < 2 ^ (prefixWord ++ tailWord_527822).sum := by decide
  have hdescent : baseEnd_527822 < baseStart_527822 := by decide
  rcases family_descends (prefixWord ++ tailWord_527822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527828 : List Nat := [2, 4, 1, 2, 3, 1, 2, 3, 4]
def baseStart_527828 : Nat := 118140960795 + 527828 * 2 ^ 59
def prefixEnd_527828 : Nat := 4983230072969 + 3 ^ 40 * 527828 * 2
def baseEnd_527828 : Nat := 60228770422548023160571

theorem tailTrace_527828 : CollatzResearch.WordTrace tailWord_527828 prefixEnd_527828 60228770422548023160571 := by
  unfold tailWord_527828
  simp only [CollatzResearch.WordTrace]
  refine ⟨9625734365888388345316069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12834312487851184460421425 9625734365888388345316069)
  ·
    refine ⟨1804825193604072814746763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9625734365888388345316069 1804825193604072814746763)
    ·
      refine ⟨2707237790406109222120145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1804825193604072814746763 2707237790406109222120145)
      ·
        refine ⟨2030428342804581916590109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2707237790406109222120145 2030428342804581916590109)
        ·
          refine ⟨761410628551718218721291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2030428342804581916590109 761410628551718218721291)
          ·
            refine ⟨1142115942827577328081937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 761410628551718218721291 1142115942827577328081937)
            ·
              refine ⟨856586957120682996061453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1142115942827577328081937 856586957120682996061453)
              ·
                refine ⟨321220108920256123523045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 856586957120682996061453 321220108920256123523045)
                ·
                  refine ⟨60228770422548023160571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 321220108920256123523045 60228770422548023160571)
                  ·
                    rfl

theorem cell22_527828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 3, 4].length) (baseStart_527828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_527828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_527828 prefixEnd_527828 := by exact prefixLift 527828
  have htrace : WordTrace (prefixWord ++ tailWord_527828) baseStart_527828 baseEnd_527828 := by
    simpa [prefixWord, tailWord_527828, baseEnd_527828] using wordTrace_append hprefix tailTrace_527828
  have hstable : (prefixWord ++ tailWord_527828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527828).length < 2 ^ (prefixWord ++ tailWord_527828).sum := by decide
  have hdescent : baseEnd_527828 < baseStart_527828 := by decide
  rcases family_descends (prefixWord ++ tailWord_527828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527830 : List Nat := [5, 2, 1, 1, 1, 4, 2, 1, 1, 4]
def baseStart_527830 : Nat := 118140960795 + 527830 * 2 ^ 59
def prefixEnd_527830 : Nat := 4983230072969 + 3 ^ 40 * 527830 * 2
def baseEnd_527830 : Nat := 180686995908516730931707

theorem tailTrace_527830 : CollatzResearch.WordTrace tailWord_527830 prefixEnd_527830 180686995908516730931707 := by
  unfold tailWord_527830
  simp only [CollatzResearch.WordTrace]
  refine ⟨1203221354860595689512809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12834361118513020688136629 1203221354860595689512809)
  ·
    refine ⟨902416016145446767134607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1203221354860595689512809 902416016145446767134607)
    ·
      refine ⟨1353624024218170150701911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 902416016145446767134607 1353624024218170150701911)
      ·
        refine ⟨2030436036327255226052867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1353624024218170150701911 2030436036327255226052867)
        ·
          refine ⟨3045654054490882839079301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2030436036327255226052867 3045654054490882839079301)
          ·
            refine ⟨571060135217040532327369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3045654054490882839079301 571060135217040532327369)
            ·
              refine ⟨428295101412780399245527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 571060135217040532327369 428295101412780399245527)
              ·
                refine ⟨642442652119170598868291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 428295101412780399245527 642442652119170598868291)
                ·
                  refine ⟨963663978178755898302437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 642442652119170598868291 963663978178755898302437)
                  ·
                    refine ⟨180686995908516730931707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 963663978178755898302437 180686995908516730931707)
                    ·
                      rfl

theorem cell22_527830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_527830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_527830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_527830 prefixEnd_527830 := by exact prefixLift 527830
  have htrace : WordTrace (prefixWord ++ tailWord_527830) baseStart_527830 baseEnd_527830 := by
    simpa [prefixWord, tailWord_527830, baseEnd_527830] using wordTrace_append hprefix tailTrace_527830
  have hstable : (prefixWord ++ tailWord_527830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527830).length < 2 ^ (prefixWord ++ tailWord_527830).sum := by decide
  have hdescent : baseEnd_527830 < baseStart_527830 := by decide
  rcases family_descends (prefixWord ++ tailWord_527830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527843 : List Nat := [1, 1, 1, 6, 2, 3, 1, 2, 2, 3]
def baseStart_527843 : Nat := 118140960795 + 527843 * 2 ^ 59
def prefixEnd_527843 : Nat := 4983230072969 + 3 ^ 40 * 527843 * 2
def baseEnd_527843 : Nat := 180691446074189030356667

theorem tailTrace_527843 : CollatzResearch.WordTrace tailWord_527843 prefixEnd_527843 180691446074189030356667 := by
  unfold tailWord_527843
  simp only [CollatzResearch.WordTrace]
  refine ⟨19252015826722434252428183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12834677217814956168285455 19252015826722434252428183)
  ·
    refine ⟨28878023740083651378642275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19252015826722434252428183 28878023740083651378642275)
    ·
      refine ⟨43317035610125477067963413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28878023740083651378642275 43317035610125477067963413)
      ·
        refine ⟨2030486044224631737560785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 43317035610125477067963413 2030486044224631737560785)
        ·
          refine ⟨1522864533168473803170589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2030486044224631737560785 1522864533168473803170589)
          ·
            refine ⟨571074199938177676188971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1522864533168473803170589 571074199938177676188971)
            ·
              refine ⟨856611299907266514283457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 571074199938177676188971 856611299907266514283457)
              ·
                refine ⟨642458474930449885712593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 856611299907266514283457 642458474930449885712593)
                ·
                  refine ⟨481843856197837414284445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 642458474930449885712593 481843856197837414284445)
                  ·
                    refine ⟨180691446074189030356667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 481843856197837414284445 180691446074189030356667)
                    ·
                      rfl

theorem cell22_527843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 2, 2, 3].length) (baseStart_527843 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_527843 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_527843 prefixEnd_527843 := by exact prefixLift 527843
  have htrace : WordTrace (prefixWord ++ tailWord_527843) baseStart_527843 baseEnd_527843 := by
    simpa [prefixWord, tailWord_527843, baseEnd_527843] using wordTrace_append hprefix tailTrace_527843
  have hstable : (prefixWord ++ tailWord_527843).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527843).length < 2 ^ (prefixWord ++ tailWord_527843).sum := by decide
  have hdescent : baseEnd_527843 < baseStart_527843 := by decide
  rcases family_descends (prefixWord ++ tailWord_527843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527852 : List Nat := [2, 2, 1, 1, 2, 1, 2, 3, 2, 6]
def baseStart_527852 : Nat := 118140960795 + 527852 * 2 ^ 59
def prefixEnd_527852 : Nat := 4983230072969 + 3 ^ 40 * 527852 * 2
def baseEnd_527852 : Nat := 180694526958116006881639

theorem tailTrace_527852 : CollatzResearch.WordTrace tailWord_527852 prefixEnd_527852 180694526958116006881639 := by
  unfold tailWord_527852
  simp only [CollatzResearch.WordTrace]
  refine ⟨9626172041844914394752905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12834896055793219193003873 9626172041844914394752905)
  ·
    refine ⟨7219629031383685796064679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9626172041844914394752905 7219629031383685796064679)
    ·
      refine ⟨10829443547075528694097019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7219629031383685796064679 10829443547075528694097019)
      ·
        refine ⟨16244165320613293041145529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10829443547075528694097019 16244165320613293041145529)
        ·
          refine ⟨12183123990459969780859147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16244165320613293041145529 12183123990459969780859147)
          ·
            refine ⟨18274685985689954671288721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12183123990459969780859147 18274685985689954671288721)
            ·
              refine ⟨13706014489267466003466541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18274685985689954671288721 13706014489267466003466541)
              ·
                refine ⟨5139755433475299751299953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13706014489267466003466541 5139755433475299751299953)
                ·
                  refine ⟨3854816575106474813474965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5139755433475299751299953 3854816575106474813474965)
                  ·
                    refine ⟨180694526958116006881639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3854816575106474813474965 180694526958116006881639)
                    ·
                      rfl

theorem cell22_527852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 6].length) (baseStart_527852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_527852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_527852 prefixEnd_527852 := by exact prefixLift 527852
  have htrace : WordTrace (prefixWord ++ tailWord_527852) baseStart_527852 baseEnd_527852 := by
    simpa [prefixWord, tailWord_527852, baseEnd_527852] using wordTrace_append hprefix tailTrace_527852
  have hstable : (prefixWord ++ tailWord_527852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527852).length < 2 ^ (prefixWord ++ tailWord_527852).sum := by decide
  have hdescent : baseEnd_527852 < baseStart_527852 := by decide
  rcases family_descends (prefixWord ++ tailWord_527852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527873 : List Nat := [1, 2, 4, 1, 5, 1, 2, 6]
def baseStart_527873 : Nat := 118140960795 + 527873 * 2 ^ 59
def prefixEnd_527873 : Nat := 4983230072969 + 3 ^ 40 * 527873 * 2
def baseEnd_527873 : Nat := 20077968409697661345175

theorem tailTrace_527873 : CollatzResearch.WordTrace tailWord_527873 prefixEnd_527873 20077968409697661345175 := by
  unfold tailWord_527873
  simp only [CollatzResearch.WordTrace]
  refine ⟨19253110016613749376020273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12835406677742499584013515 19253110016613749376020273)
  ·
    refine ⟨14439832512460312032015205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19253110016613749376020273 14439832512460312032015205)
    ·
      refine ⟨2707468596086308506002851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14439832512460312032015205 2707468596086308506002851)
      ·
        refine ⟨4061202894129462759004277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2707468596086308506002851 4061202894129462759004277)
        ·
          refine ⟨380737771324637133656651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4061202894129462759004277 380737771324637133656651)
          ·
            refine ⟨571106656986955700484977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380737771324637133656651 571106656986955700484977)
            ·
              refine ⟨428329992740216775363733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 571106656986955700484977 428329992740216775363733)
              ·
                refine ⟨20077968409697661345175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 428329992740216775363733 20077968409697661345175)
                ·
                  rfl

theorem cell22_527873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 2, 6].length) (baseStart_527873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_527873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_527873 prefixEnd_527873 := by exact prefixLift 527873
  have htrace : WordTrace (prefixWord ++ tailWord_527873) baseStart_527873 baseEnd_527873 := by
    simpa [prefixWord, tailWord_527873, baseEnd_527873] using wordTrace_append hprefix tailTrace_527873
  have hstable : (prefixWord ++ tailWord_527873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527873).length < 2 ^ (prefixWord ++ tailWord_527873).sum := by decide
  have hdescent : baseEnd_527873 < baseStart_527873 := by decide
  rcases family_descends (prefixWord ++ tailWord_527873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527905 : List Nat := [1, 2, 3, 2, 2, 3, 3, 2, 1, 3]
def baseStart_527905 : Nat := 118140960795 + 527905 * 2 ^ 59
def prefixEnd_527905 : Nat := 4983230072969 + 3 ^ 40 * 527905 * 2
def baseEnd_527905 : Nat := 180712669941241535306477

theorem tailTrace_527905 : CollatzResearch.WordTrace tailWord_527905 prefixEnd_527905 180712669941241535306477 := by
  unfold tailWord_527905
  simp only [CollatzResearch.WordTrace]
  refine ⟨19254277152497818841185169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12836184768331879227456779 19254277152497818841185169)
  ·
    refine ⟨14440707864373364130888877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19254277152497818841185169 14440707864373364130888877)
    ·
      refine ⟨5415265449140011549083329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14440707864373364130888877 5415265449140011549083329)
      ·
        refine ⟨4061449086855008661812497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5415265449140011549083329 4061449086855008661812497)
        ·
          refine ⟨3046086815141256496359373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4061449086855008661812497 3046086815141256496359373)
          ·
            refine ⟨1142282555677971186134765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3046086815141256496359373 1142282555677971186134765)
            ·
              refine ⟨428355958379239194800537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1142282555677971186134765 428355958379239194800537)
              ·
                refine ⟨321266968784429396100403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 428355958379239194800537 321266968784429396100403)
                ·
                  refine ⟨481900453176644094150605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 321266968784429396100403 481900453176644094150605)
                  ·
                    refine ⟨180712669941241535306477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 481900453176644094150605 180712669941241535306477)
                    ·
                      rfl

theorem cell22_527905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 3, 2, 1, 3].length) (baseStart_527905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_527905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_527905 prefixEnd_527905 := by exact prefixLift 527905
  have htrace : WordTrace (prefixWord ++ tailWord_527905) baseStart_527905 baseEnd_527905 := by
    simpa [prefixWord, tailWord_527905, baseEnd_527905] using wordTrace_append hprefix tailTrace_527905
  have hstable : (prefixWord ++ tailWord_527905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527905).length < 2 ^ (prefixWord ++ tailWord_527905).sum := by decide
  have hdescent : baseEnd_527905 < baseStart_527905 := by decide
  rcases family_descends (prefixWord ++ tailWord_527905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527918 : List Nat := [4, 1, 3, 1, 2, 1, 4, 1, 5]
def baseStart_527918 : Nat := 118140960795 + 527918 * 2 ^ 59
def prefixEnd_527918 : Nat := 4983230072969 + 3 ^ 40 * 527918 * 2
def baseEnd_527918 : Nat := 60239040035637944910479

theorem tailTrace_527918 : CollatzResearch.WordTrace tailWord_527918 prefixEnd_527918 60239040035637944910479 := by
  unfold tailWord_527918
  simp only [CollatzResearch.WordTrace]
  refine ⟨2406843912681340257676051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12836500867633814707605605 2406843912681340257676051)
  ·
    refine ⟨3610265869022010386514077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2406843912681340257676051 3610265869022010386514077)
    ·
      refine ⟨1353849700883253894942779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3610265869022010386514077 1353849700883253894942779)
      ·
        refine ⟨2030774551324880842414169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1353849700883253894942779 2030774551324880842414169)
        ·
          refine ⟨1523080913493660631810627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2030774551324880842414169 1523080913493660631810627)
          ·
            refine ⟨2284621370240490947715941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1523080913493660631810627 2284621370240490947715941)
            ·
              refine ⟨428366506920092052696739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2284621370240490947715941 428366506920092052696739)
              ·
                refine ⟨642549760380138079045109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 428366506920092052696739 642549760380138079045109)
                ·
                  refine ⟨60239040035637944910479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 642549760380138079045109 60239040035637944910479)
                  ·
                    rfl

theorem cell22_527918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 4, 1, 5].length) (baseStart_527918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_527918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_527918 prefixEnd_527918 := by exact prefixLift 527918
  have htrace : WordTrace (prefixWord ++ tailWord_527918) baseStart_527918 baseEnd_527918 := by
    simpa [prefixWord, tailWord_527918, baseEnd_527918] using wordTrace_append hprefix tailTrace_527918
  have hstable : (prefixWord ++ tailWord_527918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527918).length < 2 ^ (prefixWord ++ tailWord_527918).sum := by decide
  have hdescent : baseEnd_527918 < baseStart_527918 := by decide
  rcases family_descends (prefixWord ++ tailWord_527918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527946 : List Nat := [3, 1, 2, 1, 1, 3, 2, 5, 4]
def baseStart_527946 : Nat := 118140960795 + 527946 * 2 ^ 59
def prefixEnd_527946 : Nat := 4983230072969 + 3 ^ 40 * 527946 * 2
def baseEnd_527946 : Nat := 60242235026377031677117

theorem tailTrace_527946 : CollatzResearch.WordTrace tailWord_527946 prefixEnd_527946 60242235026377031677117 := by
  unfold tailWord_527946
  simp only [CollatzResearch.WordTrace]
  refine ⟨4813943136337320710856923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12837181696899521895618461 4813943136337320710856923)
  ·
    refine ⟨7220914704505981066285385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4813943136337320710856923 7220914704505981066285385)
    ·
      refine ⟨5415686028379485799714039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7220914704505981066285385 5415686028379485799714039)
      ·
        refine ⟨8123529042569228699571059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5415686028379485799714039 8123529042569228699571059)
        ·
          refine ⟨12185293563853843049356589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8123529042569228699571059 12185293563853843049356589)
          ·
            refine ⟨4569485086445191143508721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12185293563853843049356589 4569485086445191143508721)
            ·
              refine ⟨3427113814833893357631541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4569485086445191143508721 3427113814833893357631541)
              ·
                refine ⟨321291920140677502277957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3427113814833893357631541 321291920140677502277957)
                ·
                  refine ⟨60242235026377031677117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 321291920140677502277957 60242235026377031677117)
                  ·
                    rfl

theorem cell22_527946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 5, 4].length) (baseStart_527946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_527946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_527946 prefixEnd_527946 := by exact prefixLift 527946
  have htrace : WordTrace (prefixWord ++ tailWord_527946) baseStart_527946 baseEnd_527946 := by
    simpa [prefixWord, tailWord_527946, baseEnd_527946] using wordTrace_append hprefix tailTrace_527946
  have hstable : (prefixWord ++ tailWord_527946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527946).length < 2 ^ (prefixWord ++ tailWord_527946).sum := by decide
  have hdescent : baseEnd_527946 < baseStart_527946 := by decide
  rcases family_descends (prefixWord ++ tailWord_527946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527948 : List Nat := [2, 2, 1, 3, 1, 4, 3, 1, 1, 4]
def baseStart_527948 : Nat := 118140960795 + 527948 * 2 ^ 59
def prefixEnd_527948 : Nat := 4983230072969 + 3 ^ 40 * 527948 * 2
def baseEnd_527948 : Nat := 180727389720003756481345

theorem tailTrace_527948 : CollatzResearch.WordTrace tailWord_527948 prefixEnd_527948 180727389720003756481345 := by
  unfold tailWord_527948
  simp only [CollatzResearch.WordTrace]
  refine ⟨9627922745671018592500249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12837230327561358123333665 9627922745671018592500249)
  ·
    refine ⟨7220942059253263944375187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9627922745671018592500249 7220942059253263944375187)
    ·
      refine ⟨10831413088879895916562781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7220942059253263944375187 10831413088879895916562781)
      ·
        refine ⟨4061779908329960968711043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10831413088879895916562781 4061779908329960968711043)
        ·
          refine ⟨6092669862494941453066565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4061779908329960968711043 6092669862494941453066565)
          ·
            refine ⟨1142375599217801522449981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6092669862494941453066565 1142375599217801522449981)
            ·
              refine ⟨428390849706675570918743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1142375599217801522449981 428390849706675570918743)
              ·
                refine ⟨642586274560013356378115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 428390849706675570918743 642586274560013356378115)
                ·
                  refine ⟨963879411840020034567173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 642586274560013356378115 963879411840020034567173)
                  ·
                    refine ⟨180727389720003756481345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 963879411840020034567173 180727389720003756481345)
                    ·
                      rfl

theorem cell22_527948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 3, 1, 1, 4].length) (baseStart_527948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_527948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_527948 prefixEnd_527948 := by exact prefixLift 527948
  have htrace : WordTrace (prefixWord ++ tailWord_527948) baseStart_527948 baseEnd_527948 := by
    simpa [prefixWord, tailWord_527948, baseEnd_527948] using wordTrace_append hprefix tailTrace_527948
  have hstable : (prefixWord ++ tailWord_527948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527948).length < 2 ^ (prefixWord ++ tailWord_527948).sum := by decide
  have hdescent : baseEnd_527948 < baseStart_527948 := by decide
  rcases family_descends (prefixWord ++ tailWord_527948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527978 : List Nat := [3, 1, 3, 2, 1, 2, 2, 3, 2, 3]
def baseStart_527978 : Nat := 118140960795 + 527978 * 2 ^ 59
def prefixEnd_527978 : Nat := 4983230072969 + 3 ^ 40 * 527978 * 2
def baseEnd_527978 : Nat := 180737659333093678231253

theorem tailTrace_527978 : CollatzResearch.WordTrace tailWord_527978 prefixEnd_527978 180737659333093678231253 := by
  unfold tailWord_527978
  simp only [CollatzResearch.WordTrace]
  refine ⟨4814234920308338077148147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12837959787488901539061725 4814234920308338077148147)
  ·
    refine ⟨7221352380462507115722221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4814234920308338077148147 7221352380462507115722221)
    ·
      refine ⟨2708007142673440168395833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7221352380462507115722221 2708007142673440168395833)
      ·
        refine ⟨2031005357005080126296875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2708007142673440168395833 2031005357005080126296875)
        ·
          refine ⟨3046508035507620189445313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2031005357005080126296875 3046508035507620189445313)
          ·
            refine ⟨2284881026630715142083985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3046508035507620189445313 2284881026630715142083985)
            ·
              refine ⟨1713660769973036356562989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2284881026630715142083985 1713660769973036356562989)
              ·
                refine ⟨642622788739888633711121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1713660769973036356562989 642622788739888633711121)
                ·
                  refine ⟨481967091554916475283341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 642622788739888633711121 481967091554916475283341)
                  ·
                    refine ⟨180737659333093678231253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 481967091554916475283341 180737659333093678231253)
                    ·
                      rfl

theorem cell22_527978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 3, 2, 3].length) (baseStart_527978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_527978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_527978 prefixEnd_527978 := by exact prefixLift 527978
  have htrace : WordTrace (prefixWord ++ tailWord_527978) baseStart_527978 baseEnd_527978 := by
    simpa [prefixWord, tailWord_527978, baseEnd_527978] using wordTrace_append hprefix tailTrace_527978
  have hstable : (prefixWord ++ tailWord_527978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527978).length < 2 ^ (prefixWord ++ tailWord_527978).sum := by decide
  have hdescent : baseEnd_527978 < baseStart_527978 := by decide
  rcases family_descends (prefixWord ++ tailWord_527978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528023 : List Nat := [1, 1, 3, 3, 2, 3, 2, 1, 3, 3]
def baseStart_528023 : Nat := 118140960795 + 528023 * 2 ^ 59
def prefixEnd_528023 : Nat := 4983230072969 + 3 ^ 40 * 528023 * 2
def baseEnd_528023 : Nat := 180753063752728560856115

theorem tailTrace_528023 : CollatzResearch.WordTrace tailWord_528023 prefixEnd_528023 180753063752728560856115 := by
  unfold tailWord_528023
  simp only [CollatzResearch.WordTrace]
  refine ⟨19258580966070324993980723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12839053977380216662653815 19258580966070324993980723)
  ·
    refine ⟨28887871449105487490971085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19258580966070324993980723 28887871449105487490971085)
    ·
      refine ⟨10832951793414557809114157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28887871449105487490971085 10832951793414557809114157)
      ·
        refine ⟨4062356922530459178417809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10832951793414557809114157 4062356922530459178417809)
        ·
          refine ⟨3046767691897844383813357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4062356922530459178417809 3046767691897844383813357)
          ·
            refine ⟨1142537884461691643930009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3046767691897844383813357 1142537884461691643930009)
            ·
              refine ⟨856903413346268732947507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1142537884461691643930009 856903413346268732947507)
              ·
                refine ⟨1285355120019403099421261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 856903413346268732947507 1285355120019403099421261)
                ·
                  refine ⟨482008170007276162282973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1285355120019403099421261 482008170007276162282973)
                  ·
                    refine ⟨180753063752728560856115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 482008170007276162282973 180753063752728560856115)
                    ·
                      rfl

theorem cell22_528023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 1, 3, 3].length) (baseStart_528023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_528023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_528023 prefixEnd_528023 := by exact prefixLift 528023
  have htrace : WordTrace (prefixWord ++ tailWord_528023) baseStart_528023 baseEnd_528023 := by
    simpa [prefixWord, tailWord_528023, baseEnd_528023] using wordTrace_append hprefix tailTrace_528023
  have hstable : (prefixWord ++ tailWord_528023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528023).length < 2 ^ (prefixWord ++ tailWord_528023).sum := by decide
  have hdescent : baseEnd_528023 < baseStart_528023 := by decide
  rcases family_descends (prefixWord ++ tailWord_528023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528070 : List Nat := [6, 1, 2, 1, 1, 1, 2, 1, 7]
def baseStart_528070 : Nat := 118140960795 + 528070 * 2 ^ 59
def prefixEnd_528070 : Nat := 4983230072969 + 3 ^ 40 * 528070 * 2
def baseEnd_528070 : Nat := 60256384271078701643657

theorem tailTrace_528070 : CollatzResearch.WordTrace tailWord_528070 prefixEnd_528070 60256384271078701643657 := by
  unfold tailWord_528070
  simp only [CollatzResearch.WordTrace]
  refine ⟨601884224903126625654427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 12840196797933368013961109 601884224903126625654427)
  ·
    refine ⟨902826337354689938481641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 601884224903126625654427 902826337354689938481641)
    ·
      refine ⟨677119753016017453861231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 902826337354689938481641 677119753016017453861231)
      ·
        refine ⟨1015679629524026180791847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 677119753016017453861231 1015679629524026180791847)
        ·
          refine ⟨1523519444286039271187771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1015679629524026180791847 1523519444286039271187771)
          ·
            refine ⟨2285279166429058906781657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1523519444286039271187771 2285279166429058906781657)
            ·
              refine ⟨1713959374821794180086243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2285279166429058906781657 1713959374821794180086243)
              ·
                refine ⟨2570939062232691270129365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1713959374821794180086243 2570939062232691270129365)
                ·
                  refine ⟨60256384271078701643657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2570939062232691270129365 60256384271078701643657)
                  ·
                    rfl

theorem cell22_528070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_528070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_528070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_528070 prefixEnd_528070 := by exact prefixLift 528070
  have htrace : WordTrace (prefixWord ++ tailWord_528070) baseStart_528070 baseEnd_528070 := by
    simpa [prefixWord, tailWord_528070, baseEnd_528070] using wordTrace_append hprefix tailTrace_528070
  have hstable : (prefixWord ++ tailWord_528070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528070).length < 2 ^ (prefixWord ++ tailWord_528070).sum := by decide
  have hdescent : baseEnd_528070 < baseStart_528070 := by decide
  rcases family_descends (prefixWord ++ tailWord_528070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528081 : List Nat := [1, 2, 2, 1, 2, 4, 3, 1, 6]
def baseStart_528081 : Nat := 118140960795 + 528081 * 2 ^ 59
def prefixEnd_528081 : Nat := 4983230072969 + 3 ^ 40 * 528081 * 2
def baseEnd_528081 : Nat := 60257639446011914301979

theorem tailTrace_528081 : CollatzResearch.WordTrace tailWord_528081 prefixEnd_528081 60257639446011914301979 := by
  unfold tailWord_528081
  simp only [CollatzResearch.WordTrace]
  refine ⟨19260696399860200899592097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12840464266573467266394731 19260696399860200899592097)
  ·
    refine ⟨14445522299895150674694073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19260696399860200899592097 14445522299895150674694073)
    ·
      refine ⟨10834141724921363006020555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14445522299895150674694073 10834141724921363006020555)
      ·
        refine ⟨16251212587382044509030833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10834141724921363006020555 16251212587382044509030833)
        ·
          refine ⟨12188409440536533381773125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16251212587382044509030833 12188409440536533381773125)
          ·
            refine ⟨2285326770100600009082461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12188409440536533381773125 2285326770100600009082461)
            ·
              refine ⟨856997538787725003405923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2285326770100600009082461 856997538787725003405923)
              ·
                refine ⟨1285496308181587505108885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 856997538787725003405923 1285496308181587505108885)
                ·
                  refine ⟨60257639446011914301979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1285496308181587505108885 60257639446011914301979)
                  ·
                    rfl

theorem cell22_528081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 1, 6].length) (baseStart_528081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_528081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_528081 prefixEnd_528081 := by exact prefixLift 528081
  have htrace : WordTrace (prefixWord ++ tailWord_528081) baseStart_528081 baseEnd_528081 := by
    simpa [prefixWord, tailWord_528081, baseEnd_528081] using wordTrace_append hprefix tailTrace_528081
  have hstable : (prefixWord ++ tailWord_528081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528081).length < 2 ^ (prefixWord ++ tailWord_528081).sum := by decide
  have hdescent : baseEnd_528081 < baseStart_528081 := by decide
  rcases family_descends (prefixWord ++ tailWord_528081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528126 : List Nat := [4, 2, 2, 1, 13]
def baseStart_528126 : Nat := 118140960795 + 528126 * 2 ^ 59
def prefixEnd_528126 : Nat := 4983230072969 + 3 ^ 40 * 528126 * 2
def baseEnd_528126 : Nat := 743984867315516977493

theorem tailTrace_528126 : CollatzResearch.WordTrace tailWord_528126 prefixEnd_528126 743984867315516977493 := by
  unfold tailWord_528126
  simp only [CollatzResearch.WordTrace]
  refine ⟨2407792210587146698122529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12841558456464782389986821 2407792210587146698122529)
  ·
    refine ⟨1805844157940360023591897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2407792210587146698122529 1805844157940360023591897)
    ·
      refine ⟨1354383118455270017693923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1805844157940360023591897 1354383118455270017693923)
      ·
        refine ⟨2031574677682905026540885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1354383118455270017693923 2031574677682905026540885)
        ·
          refine ⟨743984867315516977493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 2031574677682905026540885 743984867315516977493)
          ·
            rfl

theorem cell22_528126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 13].length) (baseStart_528126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_528126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_528126 prefixEnd_528126 := by exact prefixLift 528126
  have htrace : WordTrace (prefixWord ++ tailWord_528126) baseStart_528126 baseEnd_528126 := by
    simpa [prefixWord, tailWord_528126, baseEnd_528126] using wordTrace_append hprefix tailTrace_528126
  have hstable : (prefixWord ++ tailWord_528126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528126).length < 2 ^ (prefixWord ++ tailWord_528126).sum := by decide
  have hdescent : baseEnd_528126 < baseStart_528126 := by decide
  rcases family_descends (prefixWord ++ tailWord_528126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528132 : List Nat := [2, 3, 2, 2, 1, 4, 2, 2, 4]
def baseStart_528132 : Nat := 118140960795 + 528132 * 2 ^ 59
def prefixEnd_528132 : Nat := 4983230072969 + 3 ^ 40 * 528132 * 2
def baseEnd_528132 : Nat := 60263458893429536626927

theorem tailTrace_528132 : CollatzResearch.WordTrace tailWord_528132 prefixEnd_528132 60263458893429536626927 := by
  unfold tailWord_528132
  simp only [CollatzResearch.WordTrace]
  refine ⟨9631278261337718304849325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12841704348450291073132433 9631278261337718304849325)
  ·
    refine ⟨3611729348001644364318497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9631278261337718304849325 3611729348001644364318497)
    ·
      refine ⟨2708797011001233273238873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3611729348001644364318497 2708797011001233273238873)
      ·
        refine ⟨2031597758250924954929155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2708797011001233273238873 2031597758250924954929155)
        ·
          refine ⟨3047396637376387432393733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2031597758250924954929155 3047396637376387432393733)
          ·
            refine ⟨571386869508072643573825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3047396637376387432393733 571386869508072643573825)
            ·
              refine ⟨428540152131054482680369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 571386869508072643573825 428540152131054482680369)
              ·
                refine ⟨321405114098290862010277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 428540152131054482680369 321405114098290862010277)
                ·
                  refine ⟨60263458893429536626927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 321405114098290862010277 60263458893429536626927)
                  ·
                    rfl

theorem cell22_528132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 2, 2, 4].length) (baseStart_528132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_528132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_528132 prefixEnd_528132 := by exact prefixLift 528132
  have htrace : WordTrace (prefixWord ++ tailWord_528132) baseStart_528132 baseEnd_528132 := by
    simpa [prefixWord, tailWord_528132, baseEnd_528132] using wordTrace_append hprefix tailTrace_528132
  have hstable : (prefixWord ++ tailWord_528132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528132).length < 2 ^ (prefixWord ++ tailWord_528132).sum := by decide
  have hdescent : baseEnd_528132 < baseStart_528132 := by decide
  rcases family_descends (prefixWord ++ tailWord_528132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528156 : List Nat := [2, 2, 3, 1, 1, 2, 1, 2, 2, 6]
def baseStart_528156 : Nat := 118140960795 + 528156 * 2 ^ 59
def prefixEnd_528156 : Nat := 4983230072969 + 3 ^ 40 * 528156 * 2
def baseEnd_528156 : Nat := 180798592370760547280707

theorem tailTrace_528156 : CollatzResearch.WordTrace tailWord_528156 prefixEnd_528156 180798592370760547280707 := by
  unfold tailWord_528156
  simp only [CollatzResearch.WordTrace]
  refine ⟨9631715937294244354286161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12842287916392325805714881 9631715937294244354286161)
  ·
    refine ⟨7223786952970683265714621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9631715937294244354286161 7223786952970683265714621)
    ·
      refine ⟨2708920107364006224642983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7223786952970683265714621 2708920107364006224642983)
      ·
        refine ⟨4063380161046009336964475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2708920107364006224642983 4063380161046009336964475)
        ·
          refine ⟨6095070241569014005446713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4063380161046009336964475 6095070241569014005446713)
          ·
            refine ⟨4571302681176760504085035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6095070241569014005446713 4571302681176760504085035)
            ·
              refine ⟨6856954021765140756127553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4571302681176760504085035 6856954021765140756127553)
              ·
                refine ⟨5142715516323855567095665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6856954021765140756127553 5142715516323855567095665)
                ·
                  refine ⟨3857036637242891675321749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5142715516323855567095665 3857036637242891675321749)
                  ·
                    refine ⟨180798592370760547280707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3857036637242891675321749 180798592370760547280707)
                    ·
                      rfl

theorem cell22_528156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_528156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_528156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_528156 prefixEnd_528156 := by exact prefixLift 528156
  have htrace : WordTrace (prefixWord ++ tailWord_528156) baseStart_528156 baseEnd_528156 := by
    simpa [prefixWord, tailWord_528156, baseEnd_528156] using wordTrace_append hprefix tailTrace_528156
  have hstable : (prefixWord ++ tailWord_528156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528156).length < 2 ^ (prefixWord ++ tailWord_528156).sum := by decide
  have hdescent : baseEnd_528156 < baseStart_528156 := by decide
  rcases family_descends (prefixWord ++ tailWord_528156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528188 : List Nat := [2, 2, 2, 2, 1, 1, 5, 2, 5]
def baseStart_528188 : Nat := 118140960795 + 528188 * 2 ^ 59
def prefixEnd_528188 : Nat := 4983230072969 + 3 ^ 40 * 528188 * 2
def baseEnd_528188 : Nat := 60269848874907710160203

theorem tailTrace_528188 : CollatzResearch.WordTrace tailWord_528188 prefixEnd_528188 60269848874907710160203 := by
  unfold tailWord_528188
  simp only [CollatzResearch.WordTrace]
  refine ⟨9632299505236279086868609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12843066006981705449158145 9632299505236279086868609)
  ·
    refine ⟨7224224628927209315151457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9632299505236279086868609 7224224628927209315151457)
    ·
      refine ⟨5418168471695406986363593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7224224628927209315151457 5418168471695406986363593)
      ·
        refine ⟨4063626353771555239772695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5418168471695406986363593 4063626353771555239772695)
        ·
          refine ⟨6095439530657332859659043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4063626353771555239772695 6095439530657332859659043)
          ·
            refine ⟨9143159295985999289488565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6095439530657332859659043 9143159295985999289488565)
            ·
              refine ⟨857171183998687433389553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9143159295985999289488565 857171183998687433389553)
              ·
                refine ⟨642878387999015575042165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 857171183998687433389553 642878387999015575042165)
                ·
                  refine ⟨60269848874907710160203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 642878387999015575042165 60269848874907710160203)
                  ·
                    rfl

theorem cell22_528188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 2, 5].length) (baseStart_528188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_528188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_528188 prefixEnd_528188 := by exact prefixLift 528188
  have htrace : WordTrace (prefixWord ++ tailWord_528188) baseStart_528188 baseEnd_528188 := by
    simpa [prefixWord, tailWord_528188, baseEnd_528188] using wordTrace_append hprefix tailTrace_528188
  have hstable : (prefixWord ++ tailWord_528188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528188).length < 2 ^ (prefixWord ++ tailWord_528188).sum := by decide
  have hdescent : baseEnd_528188 < baseStart_528188 := by decide
  rcases family_descends (prefixWord ++ tailWord_528188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528265 : List Nat := [1, 2, 1, 1, 5, 1, 3, 3, 2, 3]
def baseStart_528265 : Nat := 118140960795 + 528265 * 2 ^ 59
def prefixEnd_528265 : Nat := 4983230072969 + 3 ^ 40 * 528265 * 2
def baseEnd_528265 : Nat := 180835905298320596305373

theorem tailTrace_528265 : CollatzResearch.WordTrace tailWord_528265 prefixEnd_528265 180835905298320596305373 := by
  unfold tailWord_528265
  simp only [CollatzResearch.WordTrace]
  refine ⟨19267407431193600324290249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12844938287462400216193499 19267407431193600324290249)
  ·
    refine ⟨14450555573395200243217687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19267407431193600324290249 14450555573395200243217687)
    ·
      refine ⟨21675833360092800364826531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14450555573395200243217687 21675833360092800364826531)
      ·
        refine ⟨32513750040139200547239797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21675833360092800364826531 32513750040139200547239797)
        ·
          refine ⟨3048164066263050051303731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32513750040139200547239797 3048164066263050051303731)
          ·
            refine ⟨4572246099394575076955597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3048164066263050051303731 4572246099394575076955597)
            ·
              refine ⟨1714592287272965653858349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4572246099394575076955597 1714592287272965653858349)
              ·
                refine ⟨642972107727362120196881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1714592287272965653858349 642972107727362120196881)
                ·
                  refine ⟨482229080795521590147661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 642972107727362120196881 482229080795521590147661)
                  ·
                    refine ⟨180835905298320596305373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 482229080795521590147661 180835905298320596305373)
                    ·
                      rfl

theorem cell22_528265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 3, 2, 3].length) (baseStart_528265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_528265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_528265 prefixEnd_528265 := by exact prefixLift 528265
  have htrace : WordTrace (prefixWord ++ tailWord_528265) baseStart_528265 baseEnd_528265 := by
    simpa [prefixWord, tailWord_528265, baseEnd_528265] using wordTrace_append hprefix tailTrace_528265
  have hstable : (prefixWord ++ tailWord_528265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528265).length < 2 ^ (prefixWord ++ tailWord_528265).sum := by decide
  have hdescent : baseEnd_528265 < baseStart_528265 := by decide
  rcases family_descends (prefixWord ++ tailWord_528265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528286 : List Nat := [4, 3, 1, 3, 1, 1, 3, 1, 1, 4]
def baseStart_528286 : Nat := 118140960795 + 528286 * 2 ^ 59
def prefixEnd_528286 : Nat := 4983230072969 + 3 ^ 40 * 528286 * 2
def baseEnd_528286 : Nat := 180843094027483541530309

theorem tailTrace_528286 : CollatzResearch.WordTrace tailWord_528286 prefixEnd_528286 180843094027483541530309 := by
  unfold tailWord_528286
  simp only [CollatzResearch.WordTrace]
  refine ⟨2408521670514690113850589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12845448909411680607203141 2408521670514690113850589)
  ·
    refine ⟨903195626443008792693971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2408521670514690113850589 903195626443008792693971)
    ·
      refine ⟨1354793439664513189040957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 903195626443008792693971 1354793439664513189040957)
      ·
        refine ⟨508047539874192445890359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1354793439664513189040957 508047539874192445890359)
        ·
          refine ⟨762071309811288668835539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 508047539874192445890359 762071309811288668835539)
          ·
            refine ⟨1143106964716933003253309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 762071309811288668835539 1143106964716933003253309)
            ·
              refine ⟨428665111768849876219991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1143106964716933003253309 428665111768849876219991)
              ·
                refine ⟨642997667653274814329987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 428665111768849876219991 642997667653274814329987)
                ·
                  refine ⟨964496501479912221494981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 642997667653274814329987 964496501479912221494981)
                  ·
                    refine ⟨180843094027483541530309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 964496501479912221494981 180843094027483541530309)
                    ·
                      rfl

theorem cell22_528286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_528286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_528286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_528286 prefixEnd_528286 := by exact prefixLift 528286
  have htrace : WordTrace (prefixWord ++ tailWord_528286) baseStart_528286 baseEnd_528286 := by
    simpa [prefixWord, tailWord_528286, baseEnd_528286] using wordTrace_append hprefix tailTrace_528286
  have hstable : (prefixWord ++ tailWord_528286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528286).length < 2 ^ (prefixWord ++ tailWord_528286).sum := by decide
  have hdescent : baseEnd_528286 < baseStart_528286 := by decide
  rcases family_descends (prefixWord ++ tailWord_528286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528368 : List Nat := [2, 1, 1, 1, 3, 2, 3, 3, 6]
def baseStart_528368 : Nat := 118140960795 + 528368 * 2 ^ 59
def prefixEnd_528368 : Nat := 4983230072969 + 3 ^ 40 * 528368 * 2
def baseEnd_528368 : Nat := 60290388101087553660019

theorem tailTrace_528368 : CollatzResearch.WordTrace tailWord_528368 prefixEnd_528368 60290388101087553660019 := by
  unfold tailWord_528368
  simp only [CollatzResearch.WordTrace]
  refine ⟨9635582074910224457644879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12847442766546965943526505 9635582074910224457644879)
  ·
    refine ⟨14453373112365336686467319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9635582074910224457644879 14453373112365336686467319)
    ·
      refine ⟨21680059668548005029700979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14453373112365336686467319 21680059668548005029700979)
      ·
        refine ⟨32520089502822007544551469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21680059668548005029700979 32520089502822007544551469)
        ·
          refine ⟨12195033563558252829206801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32520089502822007544551469 12195033563558252829206801)
          ·
            refine ⟨9146275172668689621905101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12195033563558252829206801 9146275172668689621905101)
            ·
              refine ⟨3429853189750758608214413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9146275172668689621905101 3429853189750758608214413)
              ·
                refine ⟨1286194946156534478080405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3429853189750758608214413 1286194946156534478080405)
                ·
                  refine ⟨60290388101087553660019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1286194946156534478080405 60290388101087553660019)
                  ·
                    rfl

theorem cell22_528368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 3, 6].length) (baseStart_528368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_528368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_528368 prefixEnd_528368 := by exact prefixLift 528368
  have htrace : WordTrace (prefixWord ++ tailWord_528368) baseStart_528368 baseEnd_528368 := by
    simpa [prefixWord, tailWord_528368, baseEnd_528368] using wordTrace_append hprefix tailTrace_528368
  have hstable : (prefixWord ++ tailWord_528368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528368).length < 2 ^ (prefixWord ++ tailWord_528368).sum := by decide
  have hdescent : baseEnd_528368 < baseStart_528368 := by decide
  rcases family_descends (prefixWord ++ tailWord_528368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528374 : List Nat := [5, 1, 1, 1, 4, 1, 3, 1, 5]
def baseStart_528374 : Nat := 118140960795 + 528374 * 2 ^ 59
def prefixEnd_528374 : Nat := 4983230072969 + 3 ^ 40 * 528374 * 2
def baseEnd_528374 : Nat := 60291072741960215110013

theorem tailTrace_528374 : CollatzResearch.WordTrace tailWord_528374 prefixEnd_528374 60291072741960215110013 := by
  unfold tailWord_528374
  simp only [CollatzResearch.WordTrace]
  refine ⟨1204461436737419496250511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12847588658532474626672117 1204461436737419496250511)
  ·
    refine ⟨1806692155106129244375767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1204461436737419496250511 1806692155106129244375767)
    ·
      refine ⟨2710038232659193866563651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1806692155106129244375767 2710038232659193866563651)
      ·
        refine ⟨4065057348988790799845477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2710038232659193866563651 4065057348988790799845477)
        ·
          refine ⟨762198252935398274971027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4065057348988790799845477 762198252935398274971027)
          ·
            refine ⟨1143297379403097412456541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 762198252935398274971027 1143297379403097412456541)
            ·
              refine ⟨428736517276161529671203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1143297379403097412456541 428736517276161529671203)
              ·
                refine ⟨643104775914242294506805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 428736517276161529671203 643104775914242294506805)
                ·
                  refine ⟨60291072741960215110013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 643104775914242294506805 60291072741960215110013)
                  ·
                    rfl

theorem cell22_528374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 3, 1, 5].length) (baseStart_528374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_528374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_528374 prefixEnd_528374 := by exact prefixLift 528374
  have htrace : WordTrace (prefixWord ++ tailWord_528374) baseStart_528374 baseEnd_528374 := by
    simpa [prefixWord, tailWord_528374, baseEnd_528374] using wordTrace_append hprefix tailTrace_528374
  have hstable : (prefixWord ++ tailWord_528374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528374).length < 2 ^ (prefixWord ++ tailWord_528374).sum := by decide
  have hdescent : baseEnd_528374 < baseStart_528374 := by decide
  rcases family_descends (prefixWord ++ tailWord_528374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528415 : List Nat := [1, 1, 2, 4, 1, 2, 3, 2, 2, 4]
def baseStart_528415 : Nat := 118140960795 + 528415 * 2 ^ 59
def prefixEnd_528415 : Nat := 4983230072969 + 3 ^ 40 * 528415 * 2
def baseEnd_528415 : Nat := 180887253363770205054913

theorem tailTrace_528415 : CollatzResearch.WordTrace tailWord_528415 prefixEnd_528415 180887253363770205054913 := by
  unfold tailWord_528415
  simp only [CollatzResearch.WordTrace]
  refine ⟨19272878380650175942250699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12848585587100117294833799 19272878380650175942250699)
  ·
    refine ⟨28909317570975263913376049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19272878380650175942250699 28909317570975263913376049)
    ·
      refine ⟨21681988178231447935032037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28909317570975263913376049 21681988178231447935032037)
      ·
        refine ⟨4065372783418396487818507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21681988178231447935032037 4065372783418396487818507)
        ·
          refine ⟨6098059175127594731727761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4065372783418396487818507 6098059175127594731727761)
          ·
            refine ⟨4573544381345696048795821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6098059175127594731727761 4573544381345696048795821)
            ·
              refine ⟨1715079143004636018298433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4573544381345696048795821 1715079143004636018298433)
              ·
                refine ⟨1286309357253477013723825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1715079143004636018298433 1286309357253477013723825)
                ·
                  refine ⟨964732017940107760292869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1286309357253477013723825 964732017940107760292869)
                  ·
                    refine ⟨180887253363770205054913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 964732017940107760292869 180887253363770205054913)
                    ·
                      rfl

theorem cell22_528415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 2, 2, 4].length) (baseStart_528415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_528415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_528415 prefixEnd_528415 := by exact prefixLift 528415
  have htrace : WordTrace (prefixWord ++ tailWord_528415) baseStart_528415 baseEnd_528415 := by
    simpa [prefixWord, tailWord_528415, baseEnd_528415] using wordTrace_append hprefix tailTrace_528415
  have hstable : (prefixWord ++ tailWord_528415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528415).length < 2 ^ (prefixWord ++ tailWord_528415).sum := by decide
  have hdescent : baseEnd_528415 < baseStart_528415 := by decide
  rcases family_descends (prefixWord ++ tailWord_528415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528428 : List Nat := [2, 2, 1, 1, 1, 2, 2, 2, 2, 7]
def baseStart_528428 : Nat := 118140960795 + 528428 * 2 ^ 59
def prefixEnd_528428 : Nat := 4983230072969 + 3 ^ 40 * 528428 * 2
def baseEnd_528428 : Nat := 180891703529442504479873

theorem tailTrace_528428 : CollatzResearch.WordTrace tailWord_528428 prefixEnd_528428 180891703529442504479873 := by
  unfold tailWord_528428
  simp only [CollatzResearch.WordTrace]
  refine ⟨9636676264801539581236969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12848901686402052774982625 9636676264801539581236969)
  ·
    refine ⟨7227507198601154685927727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9636676264801539581236969 7227507198601154685927727)
    ·
      refine ⟨10841260797901732028891591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7227507198601154685927727 10841260797901732028891591)
      ·
        refine ⟨16261891196852598043337387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10841260797901732028891591 16261891196852598043337387)
        ·
          refine ⟨24392836795278897065006081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16261891196852598043337387 24392836795278897065006081)
          ·
            refine ⟨18294627596459172798754561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24392836795278897065006081 18294627596459172798754561)
            ·
              refine ⟨13720970697344379599065921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18294627596459172798754561 13720970697344379599065921)
              ·
                refine ⟨10290728023008284699299441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13720970697344379599065921 10290728023008284699299441)
                ·
                  refine ⟨7718046017256213524474581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10290728023008284699299441 7718046017256213524474581)
                  ·
                    refine ⟨180891703529442504479873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7718046017256213524474581 180891703529442504479873)
                    ·
                      rfl

theorem cell22_528428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 7].length) (baseStart_528428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_528428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_528428 prefixEnd_528428 := by exact prefixLift 528428
  have htrace : WordTrace (prefixWord ++ tailWord_528428) baseStart_528428 baseEnd_528428 := by
    simpa [prefixWord, tailWord_528428, baseEnd_528428] using wordTrace_append hprefix tailTrace_528428
  have hstable : (prefixWord ++ tailWord_528428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528428).length < 2 ^ (prefixWord ++ tailWord_528428).sum := by decide
  have hdescent : baseEnd_528428 < baseStart_528428 := by decide
  rcases family_descends (prefixWord ++ tailWord_528428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528430 : List Nat := [4, 1, 3, 1, 1, 2, 1, 9]
def baseStart_528430 : Nat := 118140960795 + 528430 * 2 ^ 59
def prefixEnd_528430 : Nat := 4983230072969 + 3 ^ 40 * 528430 * 2
def baseEnd_528430 : Nat := 20099154241146129547763

theorem tailTrace_528430 : CollatzResearch.WordTrace tailWord_528430 prefixEnd_528430 20099154241146129547763 := by
  unfold tailWord_528430
  simp only [CollatzResearch.WordTrace]
  refine ⟨2409178184449479188005843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12848950317063889002697829 2409178184449479188005843)
  ·
    refine ⟨3613767276674218782008765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2409178184449479188005843 3613767276674218782008765)
    ·
      refine ⟨1355162728752832043253287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3613767276674218782008765 1355162728752832043253287)
      ·
        refine ⟨2032744093129248064879931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1355162728752832043253287 2032744093129248064879931)
        ·
          refine ⟨3049116139693872097319897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2032744093129248064879931 3049116139693872097319897)
          ·
            refine ⟨2286837104770404072989923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3049116139693872097319897 2286837104770404072989923)
            ·
              refine ⟨3430255657155606109484885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2286837104770404072989923 3430255657155606109484885)
              ·
                refine ⟨20099154241146129547763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3430255657155606109484885 20099154241146129547763)
                ·
                  rfl

theorem cell22_528430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 9].length) (baseStart_528430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_528430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_528430 prefixEnd_528430 := by exact prefixLift 528430
  have htrace : WordTrace (prefixWord ++ tailWord_528430) baseStart_528430 baseEnd_528430 := by
    simpa [prefixWord, tailWord_528430, baseEnd_528430] using wordTrace_append hprefix tailTrace_528430
  have hstable : (prefixWord ++ tailWord_528430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528430).length < 2 ^ (prefixWord ++ tailWord_528430).sum := by decide
  have hdescent : baseEnd_528430 < baseStart_528430 := by decide
  rcases family_descends (prefixWord ++ tailWord_528430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528434 : List Nat := [3, 2, 1, 1, 2, 3, 4, 1, 2, 3]
def baseStart_528434 : Nat := 118140960795 + 528434 * 2 ^ 59
def prefixEnd_528434 : Nat := 4983230072969 + 3 ^ 40 * 528434 * 2
def baseEnd_528434 : Nat := 180893757452060488829855

theorem tailTrace_528434 : CollatzResearch.WordTrace tailWord_528434 prefixEnd_528434 180893757452060488829855 := by
  unfold tailWord_528434
  simp only [CollatzResearch.WordTrace]
  refine ⟨4818392841895335546798089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12849047578387561458128237 4818392841895335546798089)
  ·
    refine ⟨3613794631421501660098567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4818392841895335546798089 3613794631421501660098567)
    ·
      refine ⟨5420691947132252490147851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3613794631421501660098567 5420691947132252490147851)
      ·
        refine ⟨8131037920698378735221777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5420691947132252490147851 8131037920698378735221777)
        ·
          refine ⟨6098278440523784051416333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8131037920698378735221777 6098278440523784051416333)
          ·
            refine ⟨2286854415196419019281125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6098278440523784051416333 2286854415196419019281125)
            ·
              refine ⟨428785202849328566115211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2286854415196419019281125 428785202849328566115211)
              ·
                refine ⟨643177804273992849172817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 428785202849328566115211 643177804273992849172817)
                ·
                  refine ⟨482383353205494636879613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 643177804273992849172817 482383353205494636879613)
                  ·
                    refine ⟨180893757452060488829855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 482383353205494636879613 180893757452060488829855)
                    ·
                      rfl

theorem cell22_528434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 4, 1, 2, 3].length) (baseStart_528434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_528434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_528434 prefixEnd_528434 := by exact prefixLift 528434
  have htrace : WordTrace (prefixWord ++ tailWord_528434) baseStart_528434 baseEnd_528434 := by
    simpa [prefixWord, tailWord_528434, baseEnd_528434] using wordTrace_append hprefix tailTrace_528434
  have hstable : (prefixWord ++ tailWord_528434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528434).length < 2 ^ (prefixWord ++ tailWord_528434).sum := by decide
  have hdescent : baseEnd_528434 < baseStart_528434 := by decide
  rcases family_descends (prefixWord ++ tailWord_528434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528443 : List Nat := [1, 1, 1, 1, 1, 2, 1, 6, 2, 6]
def baseStart_528443 : Nat := 118140960795 + 528443 * 2 ^ 59
def prefixEnd_528443 : Nat := 4983230072969 + 3 ^ 40 * 528443 * 2
def baseEnd_528443 : Nat := 180896838335987465354827

theorem tailTrace_528443 : CollatzResearch.WordTrace tailWord_528443 prefixEnd_528443 180896838335987465354827 := by
  unfold tailWord_528443
  simp only [CollatzResearch.WordTrace]
  refine ⟨19273899624548736724269983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12849266416365824482846655 19273899624548736724269983)
  ·
    refine ⟨28910849436823105086404975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19273899624548736724269983 28910849436823105086404975)
    ·
      refine ⟨43366274155234657629607463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28910849436823105086404975 43366274155234657629607463)
      ·
        refine ⟨65049411232851986444411195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43366274155234657629607463 65049411232851986444411195)
        ·
          refine ⟨97574116849277979666616793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65049411232851986444411195 97574116849277979666616793)
          ·
            refine ⟨73180587636958484749962595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97574116849277979666616793 73180587636958484749962595)
            ·
              refine ⟨109770881455437727124943893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73180587636958484749962595 109770881455437727124943893)
              ·
                refine ⟨5145510068223643458981745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 109770881455437727124943893 5145510068223643458981745)
                ·
                  refine ⟨3859132551167732594236309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5145510068223643458981745 3859132551167732594236309)
                  ·
                    refine ⟨180896838335987465354827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3859132551167732594236309 180896838335987465354827)
                    ·
                      rfl

theorem cell22_528443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 2, 6].length) (baseStart_528443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_528443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_528443 prefixEnd_528443 := by exact prefixLift 528443
  have htrace : WordTrace (prefixWord ++ tailWord_528443) baseStart_528443 baseEnd_528443 := by
    simpa [prefixWord, tailWord_528443, baseEnd_528443] using wordTrace_append hprefix tailTrace_528443
  have hstable : (prefixWord ++ tailWord_528443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528443).length < 2 ^ (prefixWord ++ tailWord_528443).sum := by decide
  have hdescent : baseEnd_528443 < baseStart_528443 := by decide
  rcases family_descends (prefixWord ++ tailWord_528443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528477 : List Nat := [1, 4, 4, 1, 1, 1, 1, 1, 2, 6]
def baseStart_528477 : Nat := 118140960795 + 528477 * 2 ^ 59
def prefixEnd_528477 : Nat := 4983230072969 + 3 ^ 40 * 528477 * 2
def baseEnd_528477 : Nat := 180908477230822710004723

theorem tailTrace_528477 : CollatzResearch.WordTrace tailWord_528477 prefixEnd_528477 180908477230822710004723 := by
  unfold tailWord_528477
  simp only [CollatzResearch.WordTrace]
  refine ⟨19275139706425560531007685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12850093137617040354005123 19275139706425560531007685)
  ·
    refine ⟨3614088694954792599563941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19275139706425560531007685 3614088694954792599563941)
    ·
      refine ⟨677641630304023612418239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3614088694954792599563941 677641630304023612418239)
      ·
        refine ⟨1016462445456035418627359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 677641630304023612418239 1016462445456035418627359)
        ·
          refine ⟨1524693668184053127941039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1016462445456035418627359 1524693668184053127941039)
          ·
            refine ⟨2287040502276079691911559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1524693668184053127941039 2287040502276079691911559)
            ·
              refine ⟨3430560753414119537867339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2287040502276079691911559 3430560753414119537867339)
              ·
                refine ⟨5145841130121179306801009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3430560753414119537867339 5145841130121179306801009)
                ·
                  refine ⟨3859380847590884480100757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5145841130121179306801009 3859380847590884480100757)
                  ·
                    refine ⟨180908477230822710004723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3859380847590884480100757 180908477230822710004723)
                    ·
                      rfl

theorem cell22_528477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_528477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_528477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_528477 prefixEnd_528477 := by exact prefixLift 528477
  have htrace : WordTrace (prefixWord ++ tailWord_528477) baseStart_528477 baseEnd_528477 := by
    simpa [prefixWord, tailWord_528477, baseEnd_528477] using wordTrace_append hprefix tailTrace_528477
  have hstable : (prefixWord ++ tailWord_528477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528477).length < 2 ^ (prefixWord ++ tailWord_528477).sum := by decide
  have hdescent : baseEnd_528477 < baseStart_528477 := by decide
  rcases family_descends (prefixWord ++ tailWord_528477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528526 : List Nat := [4, 1, 1, 3, 4, 1, 1, 2, 5]
def baseStart_528526 : Nat := 118140960795 + 528526 * 2 ^ 59
def prefixEnd_528526 : Nat := 4983230072969 + 3 ^ 40 * 528526 * 2
def baseEnd_528526 : Nat := 60308416977400971843191

theorem tailTrace_528526 : CollatzResearch.WordTrace tailWord_528526 prefixEnd_528526 60308416977400971843191 := by
  unfold tailWord_528526
  simp only [CollatzResearch.WordTrace]
  refine ⟨2409615860406005237442679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12851284588832027933027621 2409615860406005237442679)
  ·
    refine ⟨3614423790609007856164019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2409615860406005237442679 3614423790609007856164019)
    ·
      refine ⟨5421635685913511784246029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3614423790609007856164019 5421635685913511784246029)
      ·
        refine ⟨2033113382217566919092261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5421635685913511784246029 2033113382217566919092261)
        ·
          refine ⟨381208759165793797329799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2033113382217566919092261 381208759165793797329799)
          ·
            refine ⟨571813138748690695994699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 381208759165793797329799 571813138748690695994699)
            ·
              refine ⟨857719708123036043992049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 571813138748690695994699 857719708123036043992049)
              ·
                refine ⟨643289781092277032994037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 857719708123036043992049 643289781092277032994037)
                ·
                  refine ⟨60308416977400971843191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 643289781092277032994037 60308416977400971843191)
                  ·
                    rfl

theorem cell22_528526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 2, 5].length) (baseStart_528526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_528526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_528526 prefixEnd_528526 := by exact prefixLift 528526
  have htrace : WordTrace (prefixWord ++ tailWord_528526) baseStart_528526 baseEnd_528526 := by
    simpa [prefixWord, tailWord_528526, baseEnd_528526] using wordTrace_append hprefix tailTrace_528526
  have hstable : (prefixWord ++ tailWord_528526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528526).length < 2 ^ (prefixWord ++ tailWord_528526).sum := by decide
  have hdescent : baseEnd_528526 < baseStart_528526 := by decide
  rcases family_descends (prefixWord ++ tailWord_528526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528564 : List Nat := [2, 5, 3, 1, 2, 1, 1, 3, 1, 3]
def baseStart_528564 : Nat := 118140960795 + 528564 * 2 ^ 59
def prefixEnd_528564 : Nat := 4983230072969 + 3 ^ 40 * 528564 * 2
def baseEnd_528564 : Nat := 180938259108783483079457

theorem tailTrace_528564 : CollatzResearch.WordTrace tailWord_528564 prefixEnd_528564 180938259108783483079457 := by
  unfold tailWord_528564
  simp only [CollatzResearch.WordTrace]
  refine ⟨9639156428555187194712373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12852208571406916259616497 9639156428555187194712373)
  ·
    refine ⟨903670915177048799504285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9639156428555187194712373 903670915177048799504285)
    ·
      refine ⟨338876593191393299814107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 903670915177048799504285 338876593191393299814107)
      ·
        refine ⟨508314889787089949721161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338876593191393299814107 508314889787089949721161)
        ·
          refine ⟨381236167340317462290871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 508314889787089949721161 381236167340317462290871)
          ·
            refine ⟨571854251010476193436307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 381236167340317462290871 571854251010476193436307)
            ·
              refine ⟨857781376515714290154461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 571854251010476193436307 857781376515714290154461)
              ·
                refine ⟨321668016193392858807923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 857781376515714290154461 321668016193392858807923)
                ·
                  refine ⟨482502024290089288211885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 321668016193392858807923 482502024290089288211885)
                  ·
                    refine ⟨180938259108783483079457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 482502024290089288211885 180938259108783483079457)
                    ·
                      rfl

theorem cell22_528564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_528564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_528564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_528564 prefixEnd_528564 := by exact prefixLift 528564
  have htrace : WordTrace (prefixWord ++ tailWord_528564) baseStart_528564 baseEnd_528564 := by
    simpa [prefixWord, tailWord_528564, baseEnd_528564] using wordTrace_append hprefix tailTrace_528564
  have hstable : (prefixWord ++ tailWord_528564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528564).length < 2 ^ (prefixWord ++ tailWord_528564).sum := by decide
  have hdescent : baseEnd_528564 < baseStart_528564 := by decide
  rcases family_descends (prefixWord ++ tailWord_528564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528588 : List Nat := [2, 2, 1, 6, 1, 1, 3, 2, 4]
def baseStart_528588 : Nat := 118140960795 + 528588 * 2 ^ 59
def prefixEnd_528588 : Nat := 4983230072969 + 3 ^ 40 * 528588 * 2
def baseEnd_528588 : Nat := 60315491599751806826461

theorem tailTrace_528588 : CollatzResearch.WordTrace tailWord_528588 prefixEnd_528588 60315491599751806826461 := by
  unfold tailWord_528588
  simp only [CollatzResearch.WordTrace]
  refine ⟨9639594104511713244149209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12852792139348950992198945 9639594104511713244149209)
  ·
    refine ⟨7229695578383784933111907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9639594104511713244149209 7229695578383784933111907)
    ·
      refine ⟨10844543367575677399667861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7229695578383784933111907 10844543367575677399667861)
      ·
        refine ⟨508337970355109878109431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 10844543367575677399667861 508337970355109878109431)
        ·
          refine ⟨762506955532664817164147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 508337970355109878109431 762506955532664817164147)
          ·
            refine ⟨1143760433298997225746221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 762506955532664817164147 1143760433298997225746221)
            ·
              refine ⟨428910162487123959654833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1143760433298997225746221 428910162487123959654833)
              ·
                refine ⟨321682621865342969741125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 428910162487123959654833 321682621865342969741125)
                ·
                  refine ⟨60315491599751806826461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 321682621865342969741125 60315491599751806826461)
                  ·
                    rfl

theorem cell22_528588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 3, 2, 4].length) (baseStart_528588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_528588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_528588 prefixEnd_528588 := by exact prefixLift 528588
  have htrace : WordTrace (prefixWord ++ tailWord_528588) baseStart_528588 baseEnd_528588 := by
    simpa [prefixWord, tailWord_528588, baseEnd_528588] using wordTrace_append hprefix tailTrace_528588
  have hstable : (prefixWord ++ tailWord_528588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528588).length < 2 ^ (prefixWord ++ tailWord_528588).sum := by decide
  have hdescent : baseEnd_528588 < baseStart_528588 := by decide
  rcases family_descends (prefixWord ++ tailWord_528588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528648 : List Nat := [2, 1, 3, 2, 3, 1, 4, 2, 1, 3]
def baseStart_528648 : Nat := 118140960795 + 528648 * 2 ^ 59
def prefixEnd_528648 : Nat := 4983230072969 + 3 ^ 40 * 528648 * 2
def baseEnd_528648 : Nat := 180967014025435263979199

theorem tailTrace_528648 : CollatzResearch.WordTrace tailWord_528648 prefixEnd_528648 180967014025435263979199 := by
  unfold tailWord_528648
  simp only [CollatzResearch.WordTrace]
  refine ⟨9640688294403028367741299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12854251059204037823655065 9640688294403028367741299)
  ·
    refine ⟨14461032441604542551611949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9640688294403028367741299 14461032441604542551611949)
    ·
      refine ⟨5422887165601703456854481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14461032441604542551611949 5422887165601703456854481)
      ·
        refine ⟨4067165374201277592640861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5422887165601703456854481 4067165374201277592640861)
        ·
          refine ⟨1525187015325479097240323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4067165374201277592640861 1525187015325479097240323)
          ·
            refine ⟨2287780522988218645860485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1525187015325479097240323 2287780522988218645860485)
            ·
              refine ⟨428958848060290996098841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2287780522988218645860485 428958848060290996098841)
              ·
                refine ⟨321719136045218247074131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 428958848060290996098841 321719136045218247074131)
                ·
                  refine ⟨482578704067827370611197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 321719136045218247074131 482578704067827370611197)
                  ·
                    refine ⟨180967014025435263979199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 482578704067827370611197 180967014025435263979199)
                    ·
                      rfl

theorem cell22_528648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 4, 2, 1, 3].length) (baseStart_528648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_528648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_528648 prefixEnd_528648 := by exact prefixLift 528648
  have htrace : WordTrace (prefixWord ++ tailWord_528648) baseStart_528648 baseEnd_528648 := by
    simpa [prefixWord, tailWord_528648, baseEnd_528648] using wordTrace_append hprefix tailTrace_528648
  have hstable : (prefixWord ++ tailWord_528648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528648).length < 2 ^ (prefixWord ++ tailWord_528648).sum := by decide
  have hdescent : baseEnd_528648 < baseStart_528648 := by decide
  rcases family_descends (prefixWord ++ tailWord_528648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528655 : List Nat := [1, 1, 2, 1, 1, 1, 3, 2, 10]
def baseStart_528655 : Nat := 118140960795 + 528655 * 2 ^ 59
def prefixEnd_528655 : Nat := 4983230072969 + 3 ^ 40 * 528655 * 2
def baseEnd_528655 : Nat := 60323136756163193018059

theorem tailTrace_528655 : CollatzResearch.WordTrace tailWord_528655 prefixEnd_528655 60323136756163193018059 := by
  unfold tailWord_528655
  simp only [CollatzResearch.WordTrace]
  refine ⟨19281631899780696930987419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12854421266520464620658279 19281631899780696930987419)
  ·
    refine ⟨28922447849671045396481129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19281631899780696930987419 28922447849671045396481129)
    ·
      refine ⟨21691835887253284047360847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28922447849671045396481129 21691835887253284047360847)
      ·
        refine ⟨32537753830879926071041271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21691835887253284047360847 32537753830879926071041271)
        ·
          refine ⟨48806630746319889106561907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32537753830879926071041271 48806630746319889106561907)
          ·
            refine ⟨73209946119479833659842861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48806630746319889106561907 73209946119479833659842861)
            ·
              refine ⟨27453729794804937622441073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73209946119479833659842861 27453729794804937622441073)
              ·
                refine ⟨20590297346103703216830805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27453729794804937622441073 20590297346103703216830805)
                ·
                  refine ⟨60323136756163193018059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 20590297346103703216830805 60323136756163193018059)
                  ·
                    rfl

theorem cell22_528655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 10].length) (baseStart_528655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_528655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_528655 prefixEnd_528655 := by exact prefixLift 528655
  have htrace : WordTrace (prefixWord ++ tailWord_528655) baseStart_528655 baseEnd_528655 := by
    simpa [prefixWord, tailWord_528655, baseEnd_528655] using wordTrace_append hprefix tailTrace_528655
  have hstable : (prefixWord ++ tailWord_528655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528655).length < 2 ^ (prefixWord ++ tailWord_528655).sum := by decide
  have hdescent : baseEnd_528655 < baseStart_528655 := by decide
  rcases family_descends (prefixWord ++ tailWord_528655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528657 : List Nat := [1, 2, 2, 1, 1, 5, 1, 2, 3, 4]
def baseStart_528657 : Nat := 118140960795 + 528657 * 2 ^ 59
def prefixEnd_528657 : Nat := 4983230072969 + 3 ^ 40 * 528657 * 2
def baseEnd_528657 : Nat := 180970094909362240504171

theorem tailTrace_528657 : CollatzResearch.WordTrace tailWord_528657 prefixEnd_528657 180970094909362240504171 := by
  unfold tailWord_528657
  simp only [CollatzResearch.WordTrace]
  refine ⟨19281704845773451272560225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12854469897182300848373483 19281704845773451272560225)
  ·
    refine ⟨14461278634330088454420169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19281704845773451272560225 14461278634330088454420169)
    ·
      refine ⟨10845958975747566340815127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14461278634330088454420169 10845958975747566340815127)
      ·
        refine ⟨16268938463621349511222691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10845958975747566340815127 16268938463621349511222691)
        ·
          refine ⟨24403407695432024266834037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16268938463621349511222691 24403407695432024266834037)
          ·
            refine ⟨2287819471446752275015691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24403407695432024266834037 2287819471446752275015691)
            ·
              refine ⟨3431729207170128412523537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2287819471446752275015691 3431729207170128412523537)
              ·
                refine ⟨2573796905377596309392653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3431729207170128412523537 2573796905377596309392653)
                ·
                  refine ⟨965173839516598616022245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2573796905377596309392653 965173839516598616022245)
                  ·
                    refine ⟨180970094909362240504171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 965173839516598616022245 180970094909362240504171)
                    ·
                      rfl

theorem cell22_528657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 4].length) (baseStart_528657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_528657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_528657 prefixEnd_528657 := by exact prefixLift 528657
  have htrace : WordTrace (prefixWord ++ tailWord_528657) baseStart_528657 baseEnd_528657 := by
    simpa [prefixWord, tailWord_528657, baseEnd_528657] using wordTrace_append hprefix tailTrace_528657
  have hstable : (prefixWord ++ tailWord_528657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528657).length < 2 ^ (prefixWord ++ tailWord_528657).sum := by decide
  have hdescent : baseEnd_528657 < baseStart_528657 := by decide
  rcases family_descends (prefixWord ++ tailWord_528657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528672 : List Nat := [2, 1, 1, 5, 2, 1, 1, 1, 8]
def baseStart_528672 : Nat := 118140960795 + 528672 * 2 ^ 59
def prefixEnd_528672 : Nat := 4983230072969 + 3 ^ 40 * 528672 * 2
def baseEnd_528672 : Nat := 60325076571969067126375

theorem tailTrace_528672 : CollatzResearch.WordTrace tailWord_528672 prefixEnd_528672 60325076571969067126375 := by
  unfold tailWord_528672
  simp only [CollatzResearch.WordTrace]
  refine ⟨9641125970359554417178135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12854834627146072556237513 9641125970359554417178135)
  ·
    refine ⟨14461688955539331625767203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9641125970359554417178135 14461688955539331625767203)
    ·
      refine ⟨21692533433308997438650805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14461688955539331625767203 21692533433308997438650805)
      ·
        refine ⟨2033675009372718509873513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21692533433308997438650805 2033675009372718509873513)
        ·
          refine ⟨1525256257029538882405135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2033675009372718509873513 1525256257029538882405135)
          ·
            refine ⟨2287884385544308323607703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1525256257029538882405135 2287884385544308323607703)
            ·
              refine ⟨3431826578316462485411555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2287884385544308323607703 3431826578316462485411555)
              ·
                refine ⟨5147739867474693728117333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3431826578316462485411555 5147739867474693728117333)
                ·
                  refine ⟨60325076571969067126375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5147739867474693728117333 60325076571969067126375)
                  ·
                    rfl

theorem cell22_528672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 8].length) (baseStart_528672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_528672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_528672 prefixEnd_528672 := by exact prefixLift 528672
  have htrace : WordTrace (prefixWord ++ tailWord_528672) baseStart_528672 baseEnd_528672 := by
    simpa [prefixWord, tailWord_528672, baseEnd_528672] using wordTrace_append hprefix tailTrace_528672
  have hstable : (prefixWord ++ tailWord_528672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528672).length < 2 ^ (prefixWord ++ tailWord_528672).sum := by decide
  have hdescent : baseEnd_528672 < baseStart_528672 := by decide
  rcases family_descends (prefixWord ++ tailWord_528672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528674 : List Nat := [3, 3, 1, 1, 3, 1, 2, 1, 3, 4]
def baseStart_528674 : Nat := 118140960795 + 528674 * 2 ^ 59
def prefixEnd_528674 : Nat := 4983230072969 + 3 ^ 40 * 528674 * 2
def baseEnd_528674 : Nat := 180975914356779862829119

theorem tailTrace_528674 : CollatzResearch.WordTrace tailWord_528674 prefixEnd_528674 180975914356779862829119 := by
  unfold tailWord_528674
  simp only [CollatzResearch.WordTrace]
  refine ⟨4820581221677965793982269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12854883257807908783952717 4820581221677965793982269)
  ·
    refine ⟨1807717958129237172743351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4820581221677965793982269 1807717958129237172743351)
    ·
      refine ⟨2711576937193855759115027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1807717958129237172743351 2711576937193855759115027)
      ·
        refine ⟨4067365405790783638672541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2711576937193855759115027 4067365405790783638672541)
        ·
          refine ⟨1525262027171543864502203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4067365405790783638672541 1525262027171543864502203)
          ·
            refine ⟨2287893040757315796753305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1525262027171543864502203 2287893040757315796753305)
            ·
              refine ⟨1715919780567986847564979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2287893040757315796753305 1715919780567986847564979)
              ·
                refine ⟨2573879670851980271347469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1715919780567986847564979 2573879670851980271347469)
                ·
                  refine ⟨965204876569492601755301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2573879670851980271347469 965204876569492601755301)
                  ·
                    refine ⟨180975914356779862829119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 965204876569492601755301 180975914356779862829119)
                    ·
                      rfl

theorem cell22_528674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_528674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_528674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_528674 prefixEnd_528674 := by exact prefixLift 528674
  have htrace : WordTrace (prefixWord ++ tailWord_528674) baseStart_528674 baseEnd_528674 := by
    simpa [prefixWord, tailWord_528674, baseEnd_528674] using wordTrace_append hprefix tailTrace_528674
  have hstable : (prefixWord ++ tailWord_528674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528674).length < 2 ^ (prefixWord ++ tailWord_528674).sum := by decide
  have hdescent : baseEnd_528674 < baseStart_528674 := by decide
  rcases family_descends (prefixWord ++ tailWord_528674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528687 : List Nat := [1, 1, 2, 1, 2, 1, 6, 2, 1, 5]
def baseStart_528687 : Nat := 118140960795 + 528687 * 2 ^ 59
def prefixEnd_528687 : Nat := 4983230072969 + 3 ^ 40 * 528687 * 2
def baseEnd_528687 : Nat := 180980364522452162254079

theorem tailTrace_528687 : CollatzResearch.WordTrace tailWord_528687 prefixEnd_528687 180980364522452162254079 := by
  unfold tailWord_528687
  simp only [CollatzResearch.WordTrace]
  refine ⟨19282799035664766396152315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12855199357109844264101543 19282799035664766396152315)
  ·
    refine ⟨28924198553497149594228473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19282799035664766396152315 28924198553497149594228473)
    ·
      refine ⟨21693148915122862195671355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28924198553497149594228473 21693148915122862195671355)
      ·
        refine ⟨32539723372684293293507033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21693148915122862195671355 32539723372684293293507033)
        ·
          refine ⟨24404792529513219970130275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32539723372684293293507033 24404792529513219970130275)
          ·
            refine ⟨36607188794269829955195413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24404792529513219970130275 36607188794269829955195413)
            ·
              refine ⟨1715961974731398279149785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 36607188794269829955195413 1715961974731398279149785)
              ·
                refine ⟨1286971481048548709362339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1715961974731398279149785 1286971481048548709362339)
                ·
                  refine ⟨1930457221572823064043509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1286971481048548709362339 1930457221572823064043509)
                  ·
                    refine ⟨180980364522452162254079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1930457221572823064043509 180980364522452162254079)
                    ·
                      rfl

theorem cell22_528687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 2, 1, 5].length) (baseStart_528687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_528687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_528687 prefixEnd_528687 := by exact prefixLift 528687
  have htrace : WordTrace (prefixWord ++ tailWord_528687) baseStart_528687 baseEnd_528687 := by
    simpa [prefixWord, tailWord_528687, baseEnd_528687] using wordTrace_append hprefix tailTrace_528687
  have hstable : (prefixWord ++ tailWord_528687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528687).length < 2 ^ (prefixWord ++ tailWord_528687).sum := by decide
  have hdescent : baseEnd_528687 < baseStart_528687 := by decide
  rcases family_descends (prefixWord ++ tailWord_528687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528704 : List Nat := [2, 1, 1, 2, 2, 1, 2, 6, 2, 3]
def baseStart_528704 : Nat := 118140960795 + 528704 * 2 ^ 59
def prefixEnd_528704 : Nat := 4983230072969 + 3 ^ 40 * 528704 * 2
def baseEnd_528704 : Nat := 180986183969869784579027

theorem tailTrace_528704 : CollatzResearch.WordTrace tailWord_528704 prefixEnd_528704 180986183969869784579027 := by
  unfold tailWord_528704
  simp only [CollatzResearch.WordTrace]
  refine ⟨9641709538301589149760583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12855612717735452199680777 9641709538301589149760583)
  ·
    refine ⟨14462564307452383724640875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9641709538301589149760583 14462564307452383724640875)
    ·
      refine ⟨21693846461178575586961313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14462564307452383724640875 21693846461178575586961313)
      ·
        refine ⟨16270384845883931690220985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21693846461178575586961313 16270384845883931690220985)
        ·
          refine ⟨12202788634412948767665739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16270384845883931690220985 12202788634412948767665739)
          ·
            refine ⟨18304182951619423151498609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12202788634412948767665739 18304182951619423151498609)
            ·
              refine ⟨13728137213714567363623957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18304182951619423151498609 13728137213714567363623957)
              ·
                refine ⟨643506431892870345169873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13728137213714567363623957 643506431892870345169873)
                ·
                  refine ⟨482629823919652758877405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 643506431892870345169873 482629823919652758877405)
                  ·
                    refine ⟨180986183969869784579027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 482629823919652758877405 180986183969869784579027)
                    ·
                      rfl

theorem cell22_528704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 6, 2, 3].length) (baseStart_528704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_528704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_528704 prefixEnd_528704 := by exact prefixLift 528704
  have htrace : WordTrace (prefixWord ++ tailWord_528704) baseStart_528704 baseEnd_528704 := by
    simpa [prefixWord, tailWord_528704, baseEnd_528704] using wordTrace_append hprefix tailTrace_528704
  have hstable : (prefixWord ++ tailWord_528704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528704).length < 2 ^ (prefixWord ++ tailWord_528704).sum := by decide
  have hdescent : baseEnd_528704 < baseStart_528704 := by decide
  rcases family_descends (prefixWord ++ tailWord_528704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528779 : List Nat := [1, 1, 1, 1, 4, 5, 1, 3, 5]
def baseStart_528779 : Nat := 118140960795 + 528779 * 2 ^ 59
def prefixEnd_528779 : Nat := 4983230072969 + 3 ^ 40 * 528779 * 2
def baseEnd_528779 : Nat := 60337286000864862984599

theorem tailTrace_528779 : CollatzResearch.WordTrace tailWord_528779 prefixEnd_528779 60337286000864862984599 := by
  unfold tailWord_528779
  simp only [CollatzResearch.WordTrace]
  refine ⟨19286154551331466108501391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12857436367554310739000927 19286154551331466108501391)
  ·
    refine ⟨28929231826997199162752087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19286154551331466108501391 28929231826997199162752087)
    ·
      refine ⟨43393847740495798744128131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28929231826997199162752087 43393847740495798744128131)
      ·
        refine ⟨65090771610743698116192197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43393847740495798744128131 65090771610743698116192197)
        ·
          refine ⟨12204519677014443396786037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65090771610743698116192197 12204519677014443396786037)
          ·
            refine ⟨1144173719720104068448691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12204519677014443396786037 1144173719720104068448691)
            ·
              refine ⟨1716260579580156102673037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1144173719720104068448691 1716260579580156102673037)
              ·
                refine ⟨643597717342558538502389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1716260579580156102673037 643597717342558538502389)
                ·
                  refine ⟨60337286000864862984599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 643597717342558538502389 60337286000864862984599)
                  ·
                    rfl

theorem cell22_528779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 3, 5].length) (baseStart_528779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_528779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_528779 prefixEnd_528779 := by exact prefixLift 528779
  have htrace : WordTrace (prefixWord ++ tailWord_528779) baseStart_528779 baseEnd_528779 := by
    simpa [prefixWord, tailWord_528779, baseEnd_528779] using wordTrace_append hprefix tailTrace_528779
  have hstable : (prefixWord ++ tailWord_528779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528779).length < 2 ^ (prefixWord ++ tailWord_528779).sum := by decide
  have hdescent : baseEnd_528779 < baseStart_528779 := by decide
  rcases family_descends (prefixWord ++ tailWord_528779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528809 : List Nat := [1, 2, 1, 1, 1, 1, 3, 7, 1, 4]
def baseStart_528809 : Nat := 118140960795 + 528809 * 2 ^ 59
def prefixEnd_528809 : Nat := 4983230072969 + 3 ^ 40 * 528809 * 2
def baseEnd_528809 : Nat := 181022127615684510703705

theorem tailTrace_528809 : CollatzResearch.WordTrace tailWord_528809 prefixEnd_528809 181022127615684510703705 := by
  unfold tailWord_528809
  simp only [CollatzResearch.WordTrace]
  refine ⟨19287248741222781232093481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12858165827481854154728987 19287248741222781232093481)
  ·
    refine ⟨14465436555917085924070111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19287248741222781232093481 14465436555917085924070111)
    ·
      refine ⟨21698154833875628886105167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14465436555917085924070111 21698154833875628886105167)
      ·
        refine ⟨32547232250813443329157751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21698154833875628886105167 32547232250813443329157751)
        ·
          refine ⟨48820848376220164993736627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32547232250813443329157751 48820848376220164993736627)
          ·
            refine ⟨73231272564330247490604941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48820848376220164993736627 73231272564330247490604941)
            ·
              refine ⟨27461727211623842808976853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73231272564330247490604941 27461727211623842808976853)
              ·
                refine ⟨643634231522433815835395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 27461727211623842808976853 643634231522433815835395)
                ·
                  refine ⟨965451347283650723753093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 643634231522433815835395 965451347283650723753093)
                  ·
                    refine ⟨181022127615684510703705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 965451347283650723753093 181022127615684510703705)
                    ·
                      rfl

theorem cell22_528809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 7, 1, 4].length) (baseStart_528809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_528809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_528809 prefixEnd_528809 := by exact prefixLift 528809
  have htrace : WordTrace (prefixWord ++ tailWord_528809) baseStart_528809 baseEnd_528809 := by
    simpa [prefixWord, tailWord_528809, baseEnd_528809] using wordTrace_append hprefix tailTrace_528809
  have hstable : (prefixWord ++ tailWord_528809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528809).length < 2 ^ (prefixWord ++ tailWord_528809).sum := by decide
  have hdescent : baseEnd_528809 < baseStart_528809 := by decide
  rcases family_descends (prefixWord ++ tailWord_528809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528813 : List Nat := [1, 5, 2, 2, 2, 1, 2, 2, 5]
def baseStart_528813 : Nat := 118140960795 + 528813 * 2 ^ 59
def prefixEnd_528813 : Nat := 4983230072969 + 3 ^ 40 * 528813 * 2
def baseEnd_528813 : Nat := 60341165632476611201231

theorem tailTrace_528813 : CollatzResearch.WordTrace tailWord_528813 prefixEnd_528813 60341165632476611201231 := by
  unfold tailWord_528813
  simp only [CollatzResearch.WordTrace]
  refine ⟨19287394633208289915239093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12858263088805526610159395 19287394633208289915239093)
  ·
    refine ⟨1808193246863277179553665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19287394633208289915239093 1808193246863277179553665)
    ·
      refine ⟨1356144935147457884665249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1808193246863277179553665 1356144935147457884665249)
      ·
        refine ⟨1017108701360593413498937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1356144935147457884665249 1017108701360593413498937)
        ·
          refine ⟨762831526020445060124203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1017108701360593413498937 762831526020445060124203)
          ·
            refine ⟨1144247289030667590186305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 762831526020445060124203 1144247289030667590186305)
            ·
              refine ⟨858185466773000692639729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1144247289030667590186305 858185466773000692639729)
              ·
                refine ⟨643639100079750519479797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 858185466773000692639729 643639100079750519479797)
                ·
                  refine ⟨60341165632476611201231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 643639100079750519479797 60341165632476611201231)
                  ·
                    rfl

theorem cell22_528813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 2, 5].length) (baseStart_528813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_528813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_528813 prefixEnd_528813 := by exact prefixLift 528813
  have htrace : WordTrace (prefixWord ++ tailWord_528813) baseStart_528813 baseEnd_528813 := by
    simpa [prefixWord, tailWord_528813, baseEnd_528813] using wordTrace_append hprefix tailTrace_528813
  have hstable : (prefixWord ++ tailWord_528813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528813).length < 2 ^ (prefixWord ++ tailWord_528813).sum := by decide
  have hdescent : baseEnd_528813 < baseStart_528813 := by decide
  rcases family_descends (prefixWord ++ tailWord_528813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528839 : List Nat := [1, 1, 4, 1, 1, 4, 1, 3, 1, 5]
def baseStart_528839 : Nat := 118140960795 + 528839 * 2 ^ 59
def prefixEnd_528839 : Nat := 4983230072969 + 3 ^ 40 * 528839 * 2
def baseEnd_528839 : Nat := 181032397228774432453613

theorem tailTrace_528839 : CollatzResearch.WordTrace tailWord_528839 prefixEnd_528839 181032397228774432453613 := by
  unfold tailWord_528839
  simp only [CollatzResearch.WordTrace]
  refine ⟨19288342931114096355685571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12858895287409397570457047 19288342931114096355685571)
  ·
    refine ⟨28932514396671144533528357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19288342931114096355685571 28932514396671144533528357)
    ·
      refine ⟨5424846449375839600036567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28932514396671144533528357 5424846449375839600036567)
      ·
        refine ⟨8137269674063759400054851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5424846449375839600036567 8137269674063759400054851)
        ·
          refine ⟨12205904511095639100082277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8137269674063759400054851 12205904511095639100082277)
          ·
            refine ⟨2288607095830432331265427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12205904511095639100082277 2288607095830432331265427)
            ·
              refine ⟨3432910643745648496898141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2288607095830432331265427 3432910643745648496898141)
              ·
                refine ⟨1287341491404618186336803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3432910643745648496898141 1287341491404618186336803)
                ·
                  refine ⟨1931012237106927279505205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1287341491404618186336803 1931012237106927279505205)
                  ·
                    refine ⟨181032397228774432453613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1931012237106927279505205 181032397228774432453613)
                    ·
                      rfl

theorem cell22_528839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 3, 1, 5].length) (baseStart_528839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_528839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_528839 prefixEnd_528839 := by exact prefixLift 528839
  have htrace : WordTrace (prefixWord ++ tailWord_528839) baseStart_528839 baseEnd_528839 := by
    simpa [prefixWord, tailWord_528839, baseEnd_528839] using wordTrace_append hprefix tailTrace_528839
  have hstable : (prefixWord ++ tailWord_528839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528839).length < 2 ^ (prefixWord ++ tailWord_528839).sum := by decide
  have hdescent : baseEnd_528839 < baseStart_528839 := by decide
  rcases family_descends (prefixWord ++ tailWord_528839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528901 : List Nat := [1, 3, 1, 1, 2, 2, 4, 2, 3, 3]
def baseStart_528901 : Nat := 118140960795 + 528901 * 2 ^ 59
def prefixEnd_528901 : Nat := 4983230072969 + 3 ^ 40 * 528901 * 2
def baseEnd_528901 : Nat := 181053621095826937403423

theorem tailTrace_528901 : CollatzResearch.WordTrace tailWord_528901 prefixEnd_528901 181053621095826937403423 := by
  unfold tailWord_528901
  simp only [CollatzResearch.WordTrace]
  refine ⟨19290604256889480944442557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12860402837926320629628371 19290604256889480944442557)
  ·
    refine ⟨7233976596333555354165959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19290604256889480944442557 7233976596333555354165959)
    ·
      refine ⟨10850964894500333031248939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7233976596333555354165959 10850964894500333031248939)
      ·
        refine ⟨16276447341750499546873409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10850964894500333031248939 16276447341750499546873409)
        ·
          refine ⟨12207335506312874660155057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16276447341750499546873409 12207335506312874660155057)
          ·
            refine ⟨9155501629734655995116293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12207335506312874660155057 9155501629734655995116293)
            ·
              refine ⟨1716656555575247999084305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9155501629734655995116293 1716656555575247999084305)
              ·
                refine ⟨1287492416681435999313229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1716656555575247999084305 1287492416681435999313229)
                ·
                  refine ⟨482809656255538499742461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1287492416681435999313229 482809656255538499742461)
                  ·
                    refine ⟨181053621095826937403423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 482809656255538499742461 181053621095826937403423)
                    ·
                      rfl

theorem cell22_528901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 2, 3, 3].length) (baseStart_528901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_528901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_528901 prefixEnd_528901 := by exact prefixLift 528901
  have htrace : WordTrace (prefixWord ++ tailWord_528901) baseStart_528901 baseEnd_528901 := by
    simpa [prefixWord, tailWord_528901, baseEnd_528901] using wordTrace_append hprefix tailTrace_528901
  have hstable : (prefixWord ++ tailWord_528901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528901).length < 2 ^ (prefixWord ++ tailWord_528901).sum := by decide
  have hdescent : baseEnd_528901 < baseStart_528901 := by decide
  rcases family_descends (prefixWord ++ tailWord_528901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528903 : List Nat := [1, 1, 4, 3, 3, 2, 2, 6]
def baseStart_528903 : Nat := 118140960795 + 528903 * 2 ^ 59
def prefixEnd_528903 : Nat := 4983230072969 + 3 ^ 40 * 528903 * 2
def baseEnd_528903 : Nat := 20117145081855510983713

theorem tailTrace_528903 : CollatzResearch.WordTrace tailWord_528903 prefixEnd_528903 20117145081855510983713 := by
  unfold tailWord_528903
  simp only [CollatzResearch.WordTrace]
  refine ⟨19290677202882235286015363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12860451468588156857343575 19290677202882235286015363)
  ·
    refine ⟨28936015804323352929023045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19290677202882235286015363 28936015804323352929023045)
    ·
      refine ⟨5425502963310628674191821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28936015804323352929023045 5425502963310628674191821)
      ·
        refine ⟨2034563611241485752821933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5425502963310628674191821 2034563611241485752821933)
        ·
          refine ⟨762961354215557157308225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2034563611241485752821933 762961354215557157308225)
          ·
            refine ⟨572221015661667867981169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 762961354215557157308225 572221015661667867981169)
            ·
              refine ⟨429165761746250900985877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 572221015661667867981169 429165761746250900985877)
              ·
                refine ⟨20117145081855510983713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 429165761746250900985877 20117145081855510983713)
                ·
                  rfl

theorem cell22_528903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 2, 6].length) (baseStart_528903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_528903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_528903 prefixEnd_528903 := by exact prefixLift 528903
  have htrace : WordTrace (prefixWord ++ tailWord_528903) baseStart_528903 baseEnd_528903 := by
    simpa [prefixWord, tailWord_528903, baseEnd_528903] using wordTrace_append hprefix tailTrace_528903
  have hstable : (prefixWord ++ tailWord_528903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528903).length < 2 ^ (prefixWord ++ tailWord_528903).sum := by decide
  have hdescent : baseEnd_528903 < baseStart_528903 := by decide
  rcases family_descends (prefixWord ++ tailWord_528903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528941 : List Nat := [1, 5, 4, 1, 1, 2, 2, 1, 2, 3]
def baseStart_528941 : Nat := 118140960795 + 528941 * 2 ^ 59
def prefixEnd_528941 : Nat := 4983230072969 + 3 ^ 40 * 528941 * 2
def baseEnd_528941 : Nat := 181067313913280166403301

theorem tailTrace_528941 : CollatzResearch.WordTrace tailWord_528941 prefixEnd_528941 181067313913280166403301 := by
  unfold tailWord_528941
  simp only [CollatzResearch.WordTrace]
  refine ⟨19292063176744567775898677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12861375451163045183932451 19292063176744567775898677)
  ·
    refine ⟨1808630922819803228990501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19292063176744567775898677 1808630922819803228990501)
    ·
      refine ⟨339118298028713105435719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1808630922819803228990501 339118298028713105435719)
      ·
        refine ⟨508677447043069658153579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339118298028713105435719 508677447043069658153579)
        ·
          refine ⟨763016170564604487230369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 508677447043069658153579 763016170564604487230369)
          ·
            refine ⟨572262127923453365422777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 763016170564604487230369 572262127923453365422777)
            ·
              refine ⟨429196595942590024067083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 572262127923453365422777 429196595942590024067083)
              ·
                refine ⟨643794893913885036100625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 429196595942590024067083 643794893913885036100625)
                ·
                  refine ⟨482846170435413777075469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 643794893913885036100625 482846170435413777075469)
                  ·
                    refine ⟨181067313913280166403301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 482846170435413777075469 181067313913280166403301)
                    ·
                      rfl

theorem cell22_528941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_528941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_528941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_528941 prefixEnd_528941 := by exact prefixLift 528941
  have htrace : WordTrace (prefixWord ++ tailWord_528941) baseStart_528941 baseEnd_528941 := by
    simpa [prefixWord, tailWord_528941, baseEnd_528941] using wordTrace_append hprefix tailTrace_528941
  have hstable : (prefixWord ++ tailWord_528941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528941).length < 2 ^ (prefixWord ++ tailWord_528941).sum := by decide
  have hdescent : baseEnd_528941 < baseStart_528941 := by decide
  rcases family_descends (prefixWord ++ tailWord_528941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528959 : List Nat := [1, 1, 2, 2, 3, 2, 2, 1, 8]
def baseStart_528959 : Nat := 118140960795 + 528959 * 2 ^ 59
def prefixEnd_528959 : Nat := 4983230072969 + 3 ^ 40 * 528959 * 2
def baseEnd_528959 : Nat := 60357825227044706484415

theorem tailTrace_528959 : CollatzResearch.WordTrace tailWord_528959 prefixEnd_528959 60357825227044706484415 := by
  unfold tailWord_528959
  simp only [CollatzResearch.WordTrace]
  refine ⟨19292719690679356850053931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12861813127119571233369287 19292719690679356850053931)
  ·
    refine ⟨28939079536019035275080897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19292719690679356850053931 28939079536019035275080897)
    ·
      refine ⟨21704309652014276456310673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28939079536019035275080897 21704309652014276456310673)
      ·
        refine ⟨16278232239010707342233005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21704309652014276456310673 16278232239010707342233005)
        ·
          refine ⟨6104337089629015253337377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16278232239010707342233005 6104337089629015253337377)
          ·
            refine ⟨4578252817221761440003033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6104337089629015253337377 4578252817221761440003033)
            ·
              refine ⟨3433689612916321080002275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4578252817221761440003033 3433689612916321080002275)
              ·
                refine ⟨5150534419374481620003413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3433689612916321080002275 5150534419374481620003413)
                ·
                  refine ⟨60357825227044706484415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5150534419374481620003413 60357825227044706484415)
                  ·
                    rfl

theorem cell22_528959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 8].length) (baseStart_528959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_528959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_528959 prefixEnd_528959 := by exact prefixLift 528959
  have htrace : WordTrace (prefixWord ++ tailWord_528959) baseStart_528959 baseEnd_528959 := by
    simpa [prefixWord, tailWord_528959, baseEnd_528959] using wordTrace_append hprefix tailTrace_528959
  have hstable : (prefixWord ++ tailWord_528959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528959).length < 2 ^ (prefixWord ++ tailWord_528959).sum := by decide
  have hdescent : baseEnd_528959 < baseStart_528959 := by decide
  rcases family_descends (prefixWord ++ tailWord_528959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528991 : List Nat := [1, 1, 2, 3, 1, 1, 1, 5, 4, 3]
def baseStart_528991 : Nat := 118140960795 + 528991 * 2 ^ 59
def prefixEnd_528991 : Nat := 4983230072969 + 3 ^ 40 * 528991 * 2
def baseEnd_528991 : Nat := 181084429935096702653147

theorem tailTrace_528991 : CollatzResearch.WordTrace tailWord_528991 prefixEnd_528991 181084429935096702653147 := by
  unfold tailWord_528991
  simp only [CollatzResearch.WordTrace]
  refine ⟨19293886826563426315218827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12862591217708950876812551 19293886826563426315218827)
  ·
    refine ⟨28940830239845139472828241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19293886826563426315218827 28940830239845139472828241)
    ·
      refine ⟨21705622679883854604621181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28940830239845139472828241 21705622679883854604621181)
      ·
        refine ⟨8139608504956445476732943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21705622679883854604621181 8139608504956445476732943)
        ·
          refine ⟨12209412757434668215099415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8139608504956445476732943 12209412757434668215099415)
          ·
            refine ⟨18314119136152002322649123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12209412757434668215099415 18314119136152002322649123)
            ·
              refine ⟨27471178704228003483973685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18314119136152002322649123 27471178704228003483973685)
              ·
                refine ⟨2575423003521375326622533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27471178704228003483973685 2575423003521375326622533)
                ·
                  refine ⟨482891813160257873741725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2575423003521375326622533 482891813160257873741725)
                  ·
                    refine ⟨181084429935096702653147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 482891813160257873741725 181084429935096702653147)
                    ·
                      rfl

theorem cell22_528991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 5, 4, 3].length) (baseStart_528991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_528991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_528991 prefixEnd_528991 := by exact prefixLift 528991
  have htrace : WordTrace (prefixWord ++ tailWord_528991) baseStart_528991 baseEnd_528991 := by
    simpa [prefixWord, tailWord_528991, baseEnd_528991] using wordTrace_append hprefix tailTrace_528991
  have hstable : (prefixWord ++ tailWord_528991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528991).length < 2 ^ (prefixWord ++ tailWord_528991).sum := by decide
  have hdescent : baseEnd_528991 < baseStart_528991 := by decide
  rcases family_descends (prefixWord ++ tailWord_528991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528993 : List Nat := [1, 2, 3, 1, 1, 5, 1, 4, 4]
def baseStart_528993 : Nat := 118140960795 + 528993 * 2 ^ 59
def prefixEnd_528993 : Nat := 4983230072969 + 3 ^ 40 * 528993 * 2
def baseEnd_528993 : Nat := 60361704858656454701047

theorem tailTrace_528993 : CollatzResearch.WordTrace tailWord_528993 prefixEnd_528993 60361704858656454701047 := by
  unfold tailWord_528993
  simp only [CollatzResearch.WordTrace]
  refine ⟨19293959772556180656791633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12862639848370787104527755 19293959772556180656791633)
  ·
    refine ⟨14470469829417135492593725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19293959772556180656791633 14470469829417135492593725)
    ·
      refine ⟨5426426186031425809722647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14470469829417135492593725 5426426186031425809722647)
      ·
        refine ⟨8139639279047138714583971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5426426186031425809722647 8139639279047138714583971)
        ·
          refine ⟨12209458918570708071875957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8139639279047138714583971 12209458918570708071875957)
          ·
            refine ⟨1144636773616003881738371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12209458918570708071875957 1144636773616003881738371)
            ·
              refine ⟨1716955160424005822607557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1144636773616003881738371 1716955160424005822607557)
              ·
                refine ⟨321929092579501091738917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1716955160424005822607557 321929092579501091738917)
                ·
                  refine ⟨60361704858656454701047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 321929092579501091738917 60361704858656454701047)
                  ·
                    rfl

theorem cell22_528993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 4, 4].length) (baseStart_528993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_528993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_528993 prefixEnd_528993 := by exact prefixLift 528993
  have htrace : WordTrace (prefixWord ++ tailWord_528993) baseStart_528993 baseEnd_528993 := by
    simpa [prefixWord, tailWord_528993, baseEnd_528993] using wordTrace_append hprefix tailTrace_528993
  have hstable : (prefixWord ++ tailWord_528993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528993).length < 2 ^ (prefixWord ++ tailWord_528993).sum := by decide
  have hdescent : baseEnd_528993 < baseStart_528993 := by decide
  rcases family_descends (prefixWord ++ tailWord_528993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529008 : List Nat := [2, 1, 1, 1, 7, 1, 2, 1, 1, 5]
def baseStart_529008 : Nat := 118140960795 + 529008 * 2 ^ 59
def prefixEnd_529008 : Nat := 4983230072969 + 3 ^ 40 * 529008 * 2
def baseEnd_529008 : Nat := 181090249382514324978095

theorem tailTrace_529008 : CollatzResearch.WordTrace tailWord_529008 prefixEnd_529008 181090249382514324978095 := by
  unfold tailWord_529008
  simp only [CollatzResearch.WordTrace]
  refine ⟨9647253433750919109293839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12863004578334558812391785 9647253433750919109293839)
  ·
    refine ⟨14470880150626378663940759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9647253433750919109293839 14470880150626378663940759)
    ·
      refine ⟨21706320225939567995911139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14470880150626378663940759 21706320225939567995911139)
      ·
        refine ⟨32559480338909351993866709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21706320225939567995911139 32559480338909351993866709)
        ·
          refine ⟨763112820443187937356251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 32559480338909351993866709 763112820443187937356251)
          ·
            refine ⟨1144669230664781906034377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 763112820443187937356251 1144669230664781906034377)
            ·
              refine ⟨858501922998586429525783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1144669230664781906034377 858501922998586429525783)
              ·
                refine ⟨1287752884497879644288675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 858501922998586429525783 1287752884497879644288675)
                ·
                  refine ⟨1931629326746819466433013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1287752884497879644288675 1931629326746819466433013)
                  ·
                    refine ⟨181090249382514324978095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1931629326746819466433013 181090249382514324978095)
                    ·
                      rfl

theorem cell22_529008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 1, 1, 5].length) (baseStart_529008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_529008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_529008 prefixEnd_529008 := by exact prefixLift 529008
  have htrace : WordTrace (prefixWord ++ tailWord_529008) baseStart_529008 baseEnd_529008 := by
    simpa [prefixWord, tailWord_529008, baseEnd_529008] using wordTrace_append hprefix tailTrace_529008
  have hstable : (prefixWord ++ tailWord_529008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529008).length < 2 ^ (prefixWord ++ tailWord_529008).sum := by decide
  have hdescent : baseEnd_529008 < baseStart_529008 := by decide
  rcases family_descends (prefixWord ++ tailWord_529008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529019 : List Nat := [1, 1, 1, 1, 1, 4, 2, 1, 1, 9]
def baseStart_529019 : Nat := 118140960795 + 529019 * 2 ^ 59
def prefixEnd_529019 : Nat := 4983230072969 + 3 ^ 40 * 529019 * 2
def baseEnd_529019 : Nat := 181094014907313962953061

theorem tailTrace_529019 : CollatzResearch.WordTrace tailWord_529019 prefixEnd_529019 181094014907313962953061 := by
  unfold tailWord_529019
  simp only [CollatzResearch.WordTrace]
  refine ⟨19294908070461987097238111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12863272046974658064825407 19294908070461987097238111)
  ·
    refine ⟨28942362105692980645857167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19294908070461987097238111 28942362105692980645857167)
    ·
      refine ⟨43413543158539470968785751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28942362105692980645857167 43413543158539470968785751)
      ·
        refine ⟨65120314737809206453178627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43413543158539470968785751 65120314737809206453178627)
        ·
          refine ⟨97680472106713809679767941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65120314737809206453178627 97680472106713809679767941)
          ·
            refine ⟨18315088520008839314956489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 97680472106713809679767941 18315088520008839314956489)
            ·
              refine ⟨13736316390006629486217367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18315088520008839314956489 13736316390006629486217367)
              ·
                refine ⟨20604474585009944229326051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13736316390006629486217367 20604474585009944229326051)
                ·
                  refine ⟨30906711877514916343989077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20604474585009944229326051 30906711877514916343989077)
                  ·
                    refine ⟨181094014907313962953061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 30906711877514916343989077 181094014907313962953061)
                    ·
                      rfl

theorem cell22_529019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 9].length) (baseStart_529019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_529019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_529019 prefixEnd_529019 := by exact prefixLift 529019
  have htrace : WordTrace (prefixWord ++ tailWord_529019) baseStart_529019 baseEnd_529019 := by
    simpa [prefixWord, tailWord_529019, baseEnd_529019] using wordTrace_append hprefix tailTrace_529019
  have hstable : (prefixWord ++ tailWord_529019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529019).length < 2 ^ (prefixWord ++ tailWord_529019).sum := by decide
  have hdescent : baseEnd_529019 < baseStart_529019 := by decide
  rcases family_descends (prefixWord ++ tailWord_529019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529042 : List Nat := [3, 2, 3, 1, 2, 3, 1, 2, 2, 3]
def baseStart_529042 : Nat := 118140960795 + 529042 * 2 ^ 59
def prefixEnd_529042 : Nat := 4983230072969 + 3 ^ 40 * 529042 * 2
def baseEnd_529042 : Nat := 181101888277349569627991

theorem tailTrace_529042 : CollatzResearch.WordTrace tailWord_529042 prefixEnd_529042 181101888277349569627991 := by
  unfold tailWord_529042
  simp only [CollatzResearch.WordTrace]
  refine ⟨4823936737344665506331345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12863831299585774683550253 4823936737344665506331345)
  ·
    refine ⟨3617952553008499129748509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4823936737344665506331345 3617952553008499129748509)
    ·
      refine ⟨1356732207378187173655691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3617952553008499129748509 1356732207378187173655691)
      ·
        refine ⟨2035098311067280760483537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1356732207378187173655691 2035098311067280760483537)
        ·
          refine ⟨1526323733300460570362653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2035098311067280760483537 1526323733300460570362653)
          ·
            refine ⟨572371399987672713885995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1526323733300460570362653 572371399987672713885995)
            ·
              refine ⟨858557099981509070828993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 572371399987672713885995 858557099981509070828993)
              ·
                refine ⟨643917824986131803121745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 858557099981509070828993 643917824986131803121745)
                ·
                  refine ⟨482938368739598852341309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 643917824986131803121745 482938368739598852341309)
                  ·
                    refine ⟨181101888277349569627991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 482938368739598852341309 181101888277349569627991)
                    ·
                      rfl

theorem cell22_529042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_529042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_529042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_529042 prefixEnd_529042 := by exact prefixLift 529042
  have htrace : WordTrace (prefixWord ++ tailWord_529042) baseStart_529042 baseEnd_529042 := by
    simpa [prefixWord, tailWord_529042, baseEnd_529042] using wordTrace_append hprefix tailTrace_529042
  have hstable : (prefixWord ++ tailWord_529042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529042).length < 2 ^ (prefixWord ++ tailWord_529042).sum := by decide
  have hdescent : baseEnd_529042 < baseStart_529042 := by decide
  rcases family_descends (prefixWord ++ tailWord_529042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529053 : List Nat := [1, 4, 2, 1, 1, 1, 3, 3, 3, 3]
def baseStart_529053 : Nat := 118140960795 + 529053 * 2 ^ 59
def prefixEnd_529053 : Nat := 4983230072969 + 3 ^ 40 * 529053 * 2
def baseEnd_529053 : Nat := 181105653802149207602957

theorem tailTrace_529053 : CollatzResearch.WordTrace tailWord_529053 prefixEnd_529053 181105653802149207602957 := by
  unfold tailWord_529053
  simp only [CollatzResearch.WordTrace]
  refine ⟨19296148152338810903975813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12864098768225873935983875 19296148152338810903975813)
  ·
    refine ⟨3618027778563527044495465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19296148152338810903975813 3618027778563527044495465)
    ·
      refine ⟨2713520833922645283371599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3618027778563527044495465 2713520833922645283371599)
      ·
        refine ⟨4070281250883967925057399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2713520833922645283371599 4070281250883967925057399)
        ·
          refine ⟨6105421876325951887586099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4070281250883967925057399 6105421876325951887586099)
          ·
            refine ⟨9158132814488927831379149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6105421876325951887586099 9158132814488927831379149)
            ·
              refine ⟨3434299805433347936767181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9158132814488927831379149 3434299805433347936767181)
              ·
                refine ⟨1287862427037505476287693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3434299805433347936767181 1287862427037505476287693)
                ·
                  refine ⟨482948410139064553607885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1287862427037505476287693 482948410139064553607885)
                  ·
                    refine ⟨181105653802149207602957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 482948410139064553607885 181105653802149207602957)
                    ·
                      rfl

theorem cell22_529053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 3, 3, 3].length) (baseStart_529053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_529053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_529053 prefixEnd_529053 := by exact prefixLift 529053
  have htrace : WordTrace (prefixWord ++ tailWord_529053) baseStart_529053 baseEnd_529053 := by
    simpa [prefixWord, tailWord_529053, baseEnd_529053] using wordTrace_append hprefix tailTrace_529053
  have hstable : (prefixWord ++ tailWord_529053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529053).length < 2 ^ (prefixWord ++ tailWord_529053).sum := by decide
  have hdescent : baseEnd_529053 < baseStart_529053 := by decide
  rcases family_descends (prefixWord ++ tailWord_529053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529087 : List Nat := [1, 1, 2, 2, 2, 6, 1, 3, 1, 3]
def baseStart_529087 : Nat := 118140960795 + 529087 * 2 ^ 59
def prefixEnd_529087 : Nat := 4983230072969 + 3 ^ 40 * 529087 * 2
def baseEnd_529087 : Nat := 181117292696984452252853

theorem tailTrace_529087 : CollatzResearch.WordTrace tailWord_529087 prefixEnd_529087 181117292696984452252853 := by
  unfold tailWord_529087
  simp only [CollatzResearch.WordTrace]
  refine ⟨19297388234215634710713515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12864925489477089807142343 19297388234215634710713515)
  ·
    refine ⟨28946082351323452066070273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19297388234215634710713515 28946082351323452066070273)
    ·
      refine ⟨21709561763492589049552705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28946082351323452066070273 21709561763492589049552705)
      ·
        refine ⟨16282171322619441787164529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21709561763492589049552705 16282171322619441787164529)
        ·
          refine ⟨12211628491964581340373397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16282171322619441787164529 12211628491964581340373397)
          ·
            refine ⟨572420085560839750330003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 12211628491964581340373397 572420085560839750330003)
            ·
              refine ⟨858630128341259625495005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 572420085560839750330003 858630128341259625495005)
              ·
                refine ⟨321986298127972359560627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 858630128341259625495005 321986298127972359560627)
                ·
                  refine ⟨482979447191958539340941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 321986298127972359560627 482979447191958539340941)
                  ·
                    refine ⟨181117292696984452252853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 482979447191958539340941 181117292696984452252853)
                    ·
                      rfl

theorem cell22_529087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 3, 1, 3].length) (baseStart_529087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_529087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_529087 prefixEnd_529087 := by exact prefixLift 529087
  have htrace : WordTrace (prefixWord ++ tailWord_529087) baseStart_529087 baseEnd_529087 := by
    simpa [prefixWord, tailWord_529087, baseEnd_529087] using wordTrace_append hprefix tailTrace_529087
  have hstable : (prefixWord ++ tailWord_529087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529087).length < 2 ^ (prefixWord ++ tailWord_529087).sum := by decide
  have hdescent : baseEnd_529087 < baseStart_529087 := by decide
  rcases family_descends (prefixWord ++ tailWord_529087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529160 : List Nat := [2, 1, 3, 2, 2, 2, 1, 4, 2, 3]
def baseStart_529160 : Nat := 118140960795 + 529160 * 2 ^ 59
def prefixEnd_529160 : Nat := 4983230072969 + 3 ^ 40 * 529160 * 2
def baseEnd_529160 : Nat := 181142282088836595177629

theorem tailTrace_529160 : CollatzResearch.WordTrace tailWord_529160 prefixEnd_529160 181142282088836595177629 := by
  unfold tailWord_529160
  simp only [CollatzResearch.WordTrace]
  refine ⟨9650025381475584089060467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12866700508634112118747289 9650025381475584089060467)
  ·
    refine ⟨14475038072213376133590701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9650025381475584089060467 14475038072213376133590701)
    ·
      refine ⟨5428139277080016050096513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14475038072213376133590701 5428139277080016050096513)
      ·
        refine ⟨4071104457810012037572385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5428139277080016050096513 4071104457810012037572385)
        ·
          refine ⟨3053328343357509028179289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4071104457810012037572385 3053328343357509028179289)
          ·
            refine ⟨2289996257518131771134467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3053328343357509028179289 2289996257518131771134467)
            ·
              refine ⟨3434994386277197656701701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2289996257518131771134467 3434994386277197656701701)
              ·
                refine ⟨644061447426974560631569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3434994386277197656701701 644061447426974560631569)
                ·
                  refine ⟨483046085570230920473677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 644061447426974560631569 483046085570230920473677)
                  ·
                    refine ⟨181142282088836595177629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 483046085570230920473677 181142282088836595177629)
                    ·
                      rfl

theorem cell22_529160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 4, 2, 3].length) (baseStart_529160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_529160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_529160 prefixEnd_529160 := by exact prefixLift 529160
  have htrace : WordTrace (prefixWord ++ tailWord_529160) baseStart_529160 baseEnd_529160 := by
    simpa [prefixWord, tailWord_529160, baseEnd_529160] using wordTrace_append hprefix tailTrace_529160
  have hstable : (prefixWord ++ tailWord_529160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529160).length < 2 ^ (prefixWord ++ tailWord_529160).sum := by decide
  have hdescent : baseEnd_529160 < baseStart_529160 := by decide
  rcases family_descends (prefixWord ++ tailWord_529160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529265 : List Nat := [1, 2, 2, 2, 1, 4, 2, 3, 1, 4]
def baseStart_529265 : Nat := 118140960795 + 529265 * 2 ^ 59
def prefixEnd_529265 : Nat := 4983230072969 + 3 ^ 40 * 529265 * 2
def baseEnd_529265 : Nat := 181178225734651321302307

theorem tailTrace_529265 : CollatzResearch.WordTrace tailWord_529265 prefixEnd_529265 181178225734651321302307 := by
  unfold tailWord_529265
  simp only [CollatzResearch.WordTrace]
  refine ⟨19303880427570771110693249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12869253618380514073795499 19303880427570771110693249)
  ·
    refine ⟨14477910320678078333019937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19303880427570771110693249 14477910320678078333019937)
    ·
      refine ⟨10858432740508558749764953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14477910320678078333019937 10858432740508558749764953)
      ·
        refine ⟨8143824555381419062323715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10858432740508558749764953 8143824555381419062323715)
        ·
          refine ⟨12215736833072128593485573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8143824555381419062323715 12215736833072128593485573)
          ·
            refine ⟨2290450656201024111278545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12215736833072128593485573 2290450656201024111278545)
            ·
              refine ⟨1717837992150768083458909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2290450656201024111278545 1717837992150768083458909)
              ·
                refine ⟨644189247056538031297091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1717837992150768083458909 644189247056538031297091)
                ·
                  refine ⟨966283870584807046945637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 644189247056538031297091 966283870584807046945637)
                  ·
                    refine ⟨181178225734651321302307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 966283870584807046945637 181178225734651321302307)
                    ·
                      rfl

theorem cell22_529265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 3, 1, 4].length) (baseStart_529265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_529265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_529265 prefixEnd_529265 := by exact prefixLift 529265
  have htrace : WordTrace (prefixWord ++ tailWord_529265) baseStart_529265 baseEnd_529265 := by
    simpa [prefixWord, tailWord_529265, baseEnd_529265] using wordTrace_append hprefix tailTrace_529265
  have hstable : (prefixWord ++ tailWord_529265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529265).length < 2 ^ (prefixWord ++ tailWord_529265).sum := by decide
  have hdescent : baseEnd_529265 < baseStart_529265 := by decide
  rcases family_descends (prefixWord ++ tailWord_529265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529325 : List Nat := [1, 5, 2, 3, 11]
def baseStart_529325 : Nat := 118140960795 + 529325 * 2 ^ 59
def prefixEnd_529325 : Nat := 4983230072969 + 3 ^ 40 * 529325 * 2
def baseEnd_529325 : Nat := 745673929879963641161

theorem tailTrace_529325 : CollatzResearch.WordTrace tailWord_529325 prefixEnd_529325 745673929879963641161 := by
  unfold tailWord_529325
  simp only [CollatzResearch.WordTrace]
  refine ⟨19306068807353401357877429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12870712538235600905251619 19306068807353401357877429)
  ·
    refine ⟨1809943950689381377301009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19306068807353401357877429 1809943950689381377301009)
    ·
      refine ⟨1357457963017036032975757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1809943950689381377301009 1357457963017036032975757)
      ·
        refine ⟨509046736131388512365909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1357457963017036032975757 509046736131388512365909)
        ·
          refine ⟨745673929879963641161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 509046736131388512365909 745673929879963641161)
          ·
            rfl

theorem cell22_529325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 11].length) (baseStart_529325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_529325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_529325 prefixEnd_529325 := by exact prefixLift 529325
  have htrace : WordTrace (prefixWord ++ tailWord_529325) baseStart_529325 baseEnd_529325 := by
    simpa [prefixWord, tailWord_529325, baseEnd_529325] using wordTrace_append hprefix tailTrace_529325
  have hstable : (prefixWord ++ tailWord_529325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529325).length < 2 ^ (prefixWord ++ tailWord_529325).sum := by decide
  have hdescent : baseEnd_529325 < baseStart_529325 := by decide
  rcases family_descends (prefixWord ++ tailWord_529325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
