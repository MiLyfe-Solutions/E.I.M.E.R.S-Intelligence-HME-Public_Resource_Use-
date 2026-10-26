import V185TrunkScan20Chunk146

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_894519 : List Nat := [1, 1, 3, 1, 2, 4, 4, 2, 2]
def baseStart_894519 : Nat := 118140960795 + 894519 * 2 ^ 59
def prefixEnd_894519 : Nat := 4983230072969 + 3 ^ 40 * 894519 * 2
def baseEnd_894519 : Nat := 408282845848258599109945

theorem tailTrace_894519 : CollatzResearch.WordTrace tailWord_894519 prefixEnd_894519 408282845848258599109945 := by
  unfold tailWord_894519
  simp only [CollatzResearch.WordTrace]
  refine ⟨32625788246317909527534611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21750525497545273018356407 32625788246317909527534611)
  ·
    refine ⟨48938682369476864291301917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32625788246317909527534611 48938682369476864291301917)
    ·
      refine ⟨18352005888553824109238219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48938682369476864291301917 18352005888553824109238219)
      ·
        refine ⟨27528008832830736163857329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18352005888553824109238219 27528008832830736163857329)
        ·
          refine ⟨20646006624623052122892997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27528008832830736163857329 20646006624623052122892997)
          ·
            refine ⟨3871126242116822273042437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20646006624623052122892997 3871126242116822273042437)
            ·
              refine ⟨725836170396904176195457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3871126242116822273042437 725836170396904176195457)
              ·
                refine ⟨544377127797678132146593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 725836170396904176195457 544377127797678132146593)
                ·
                  refine ⟨408282845848258599109945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 544377127797678132146593 408282845848258599109945)
                  ·
                    rfl

theorem cell20_894519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 4, 2, 2].length) (baseStart_894519 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_894519 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_894519 prefixEnd_894519 := by exact prefixLift 894519
  have htrace : WordTrace (prefixWord ++ tailWord_894519) baseStart_894519 baseEnd_894519 := by
    simpa [prefixWord, tailWord_894519, baseEnd_894519] using wordTrace_append hprefix tailTrace_894519
  have hstable : (prefixWord ++ tailWord_894519).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894519).length < 2 ^ (prefixWord ++ tailWord_894519).sum := by decide
  have hdescent : baseEnd_894519 < baseStart_894519 := by decide
  rcases family_descends (prefixWord ++ tailWord_894519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894578 : List Nat := [3, 2, 1, 2, 3, 2, 2, 1, 4]
def baseStart_894578 : Nat := 118140960795 + 894578 * 2 ^ 59
def prefixEnd_894578 : Nat := 4983230072969 + 3 ^ 40 * 894578 * 2
def baseEnd_894578 : Nat := 408309775055916616143037

theorem tailTrace_894578 : CollatzResearch.WordTrace tailWord_894578 prefixEnd_894578 408309775055916616143037 := by
  unfold tailWord_894578
  simp only [CollatzResearch.WordTrace]
  refine ⟨8156985038276040650983097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21751960102069441735954925 8156985038276040650983097)
  ·
    refine ⟨6117738778707030488237323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8156985038276040650983097 6117738778707030488237323)
    ·
      refine ⟨9176608168060545732355985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6117738778707030488237323 9176608168060545732355985)
      ·
        refine ⟨6882456126045409299266989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9176608168060545732355985 6882456126045409299266989)
        ·
          refine ⟨2580921047267028487225121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6882456126045409299266989 2580921047267028487225121)
          ·
            refine ⟨1935690785450271365418841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2580921047267028487225121 1935690785450271365418841)
            ·
              refine ⟨1451768089087703524064131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1935690785450271365418841 1451768089087703524064131)
              ·
                refine ⟨2177652133631555286096197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1451768089087703524064131 2177652133631555286096197)
                ·
                  refine ⟨408309775055916616143037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2177652133631555286096197 408309775055916616143037)
                  ·
                    rfl

theorem cell20_894578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_894578 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_894578 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_894578 prefixEnd_894578 := by exact prefixLift 894578
  have htrace : WordTrace (prefixWord ++ tailWord_894578) baseStart_894578 baseEnd_894578 := by
    simpa [prefixWord, tailWord_894578, baseEnd_894578] using wordTrace_append hprefix tailTrace_894578
  have hstable : (prefixWord ++ tailWord_894578).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894578).length < 2 ^ (prefixWord ++ tailWord_894578).sum := by decide
  have hdescent : baseEnd_894578 < baseStart_894578 := by decide
  rcases family_descends (prefixWord ++ tailWord_894578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894599 : List Nat := [1, 1, 4, 2, 1, 3, 2, 2, 4]
def baseStart_894599 : Nat := 118140960795 + 894599 * 2 ^ 59
def prefixEnd_894599 : Nat := 4983230072969 + 3 ^ 40 * 894599 * 2
def baseEnd_894599 : Nat := 408319360028133876442951

theorem tailTrace_894599 : CollatzResearch.WordTrace tailWord_894599 prefixEnd_894599 408319360028133876442951 := by
  unfold tailWord_894599
  simp only [CollatzResearch.WordTrace]
  refine ⟨32628706086028083190446851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21752470724018722126964567 32628706086028083190446851)
  ·
    refine ⟨48943059129042124785670277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32628706086028083190446851 48943059129042124785670277)
    ·
      refine ⟨9176823586695398397313177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48943059129042124785670277 9176823586695398397313177)
      ·
        refine ⟨6882617690021548797984883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9176823586695398397313177 6882617690021548797984883)
        ·
          refine ⟨10323926535032323196977325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6882617690021548797984883 10323926535032323196977325)
          ·
            refine ⟨3871472450637121198866497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10323926535032323196977325 3871472450637121198866497)
            ·
              refine ⟨2903604337977840899149873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3871472450637121198866497 2903604337977840899149873)
              ·
                refine ⟨2177703253483380674362405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2903604337977840899149873 2177703253483380674362405)
                ·
                  refine ⟨408319360028133876442951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2177703253483380674362405 408319360028133876442951)
                  ·
                    rfl

theorem cell20_894599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 2, 4].length) (baseStart_894599 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_894599 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_894599 prefixEnd_894599 := by exact prefixLift 894599
  have htrace : WordTrace (prefixWord ++ tailWord_894599) baseStart_894599 baseEnd_894599 := by
    simpa [prefixWord, tailWord_894599, baseEnd_894599] using wordTrace_append hprefix tailTrace_894599
  have hstable : (prefixWord ++ tailWord_894599).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894599).length < 2 ^ (prefixWord ++ tailWord_894599).sum := by decide
  have hdescent : baseEnd_894599 < baseStart_894599 := by decide
  rcases family_descends (prefixWord ++ tailWord_894599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894602 : List Nat := [3, 1, 2, 3, 2, 3, 2, 4]
def baseStart_894602 : Nat := 118140960795 + 894602 * 2 ^ 59
def prefixEnd_894602 : Nat := 4983230072969 + 3 ^ 40 * 894602 * 2
def baseEnd_894602 : Nat := 136106909769959733114313

theorem tailTrace_894602 : CollatzResearch.WordTrace tailWord_894602 prefixEnd_894602 136106909769959733114313 := by
  unfold tailWord_894602
  simp only [CollatzResearch.WordTrace]
  refine ⟨8157203876254303675701515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21752543670011476468537373 8157203876254303675701515)
  ·
    refine ⟨12235805814381455513552273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8157203876254303675701515 12235805814381455513552273)
    ·
      refine ⟨9176854360786091635164205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12235805814381455513552273 9176854360786091635164205)
      ·
        refine ⟨3441320385294784363186577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9176854360786091635164205 3441320385294784363186577)
        ·
          refine ⟨2580990288971088272389933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3441320385294784363186577 2580990288971088272389933)
          ·
            refine ⟨967871358364158102146225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2580990288971088272389933 967871358364158102146225)
            ·
              refine ⟨725903518773118576609669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 967871358364158102146225 725903518773118576609669)
              ·
                refine ⟨136106909769959733114313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 725903518773118576609669 136106909769959733114313)
                ·
                  rfl

theorem cell20_894602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 2, 4].length) (baseStart_894602 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_894602 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_894602 prefixEnd_894602 := by exact prefixLift 894602
  have htrace : WordTrace (prefixWord ++ tailWord_894602) baseStart_894602 baseEnd_894602 := by
    simpa [prefixWord, tailWord_894602, baseEnd_894602] using wordTrace_append hprefix tailTrace_894602
  have hstable : (prefixWord ++ tailWord_894602).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894602).length < 2 ^ (prefixWord ++ tailWord_894602).sum := by decide
  have hdescent : baseEnd_894602 < baseStart_894602 := by decide
  rcases family_descends (prefixWord ++ tailWord_894602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894647 : List Nat := [1, 1, 3, 1, 5, 1, 4, 1, 3]
def baseStart_894647 : Nat := 118140960795 + 894647 * 2 ^ 59
def prefixEnd_894647 : Nat := 4983230072969 + 3 ^ 40 * 894647 * 2
def baseEnd_894647 : Nat := 408341268536059042842755

theorem tailTrace_894647 : CollatzResearch.WordTrace tailWord_894647 prefixEnd_894647 408341268536059042842755 := by
  unfold tailWord_894647
  simp only [CollatzResearch.WordTrace]
  refine ⟨32630456789854187388194195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21753637859902791592129463 32630456789854187388194195)
  ·
    refine ⟨48945685184781281082291293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32630456789854187388194195 48945685184781281082291293)
    ·
      refine ⟨18354631944292980405859235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48945685184781281082291293 18354631944292980405859235)
      ·
        refine ⟨27531947916439470608788853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18354631944292980405859235 27531947916439470608788853)
        ·
          refine ⟨2581120117166200369573955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27531947916439470608788853 2581120117166200369573955)
          ·
            refine ⟨3871680175749300554360933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2581120117166200369573955 3871680175749300554360933)
            ·
              refine ⟨725940032952993853942675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3871680175749300554360933 725940032952993853942675)
              ·
                refine ⟨1088910049429490780914013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 725940032952993853942675 1088910049429490780914013)
                ·
                  refine ⟨408341268536059042842755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1088910049429490780914013 408341268536059042842755)
                  ·
                    rfl

theorem cell20_894647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 4, 1, 3].length) (baseStart_894647 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_894647 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_894647 prefixEnd_894647 := by exact prefixLift 894647
  have htrace : WordTrace (prefixWord ++ tailWord_894647) baseStart_894647 baseEnd_894647 := by
    simpa [prefixWord, tailWord_894647, baseEnd_894647] using wordTrace_append hprefix tailTrace_894647
  have hstable : (prefixWord ++ tailWord_894647).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894647).length < 2 ^ (prefixWord ++ tailWord_894647).sum := by decide
  have hdescent : baseEnd_894647 < baseStart_894647 := by decide
  rcases family_descends (prefixWord ++ tailWord_894647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894678 : List Nat := [5, 2, 1, 3, 1, 8]
def baseStart_894678 : Nat := 118140960795 + 894678 * 2 ^ 59
def prefixEnd_894678 : Nat := 4983230072969 + 3 ^ 40 * 894678 * 2
def baseEnd_894678 : Nat := 15124274732620767141085

theorem tailTrace_894678 : CollatzResearch.WordTrace tailWord_894678 prefixEnd_894678 15124274732620767141085 := by
  unfold tailWord_894678
  simp only [CollatzResearch.WordTrace]
  refine ⟨2039474215796367480160793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21754391635161253121715125 2039474215796367480160793)
  ·
    refine ⟨1529605661847275610120595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2039474215796367480160793 1529605661847275610120595)
    ·
      refine ⟨2294408492770913415180893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1529605661847275610120595 2294408492770913415180893)
      ·
        refine ⟨860403184789092530692835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2294408492770913415180893 860403184789092530692835)
        ·
          refine ⟨1290604777183638796039253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 860403184789092530692835 1290604777183638796039253)
          ·
            refine ⟨15124274732620767141085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1290604777183638796039253 15124274732620767141085)
            ·
              rfl

theorem cell20_894678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 8].length) (baseStart_894678 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_894678 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_894678 prefixEnd_894678 := by exact prefixLift 894678
  have htrace : WordTrace (prefixWord ++ tailWord_894678) baseStart_894678 baseEnd_894678 := by
    simpa [prefixWord, tailWord_894678, baseEnd_894678] using wordTrace_append hprefix tailTrace_894678
  have hstable : (prefixWord ++ tailWord_894678).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894678).length < 2 ^ (prefixWord ++ tailWord_894678).sum := by decide
  have hdescent : baseEnd_894678 < baseStart_894678 := by decide
  rcases family_descends (prefixWord ++ tailWord_894678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894684 : List Nat := [2, 2, 5, 1, 3, 1, 2, 2, 2]
def baseStart_894684 : Nat := 118140960795 + 894684 * 2 ^ 59
def prefixEnd_894684 : Nat := 4983230072969 + 3 ^ 40 * 894684 * 2
def baseEnd_894684 : Nat := 408358156344251358609271

theorem tailTrace_894684 : CollatzResearch.WordTrace tailWord_894684 prefixEnd_894684 408358156344251358609271 := by
  unfold tailWord_894684
  simp only [CollatzResearch.WordTrace]
  refine ⟨16315903145360071353645553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21754537527146761804860737 16315903145360071353645553)
  ·
    refine ⟨12236927359020053515234165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16315903145360071353645553 12236927359020053515234165)
    ·
      refine ⟨1147211939908130017053203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12236927359020053515234165 1147211939908130017053203)
      ·
        refine ⟨1720817909862195025579805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1147211939908130017053203 1720817909862195025579805)
        ·
          refine ⟨645306716198323134592427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1720817909862195025579805 645306716198323134592427)
          ·
            refine ⟨967960074297484701888641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 645306716198323134592427 967960074297484701888641)
            ·
              refine ⟨725970055723113526416481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 967960074297484701888641 725970055723113526416481)
              ·
                refine ⟨544477541792335144812361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 725970055723113526416481 544477541792335144812361)
                ·
                  refine ⟨408358156344251358609271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 544477541792335144812361 408358156344251358609271)
                  ·
                    rfl

theorem cell20_894684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 2, 2, 2].length) (baseStart_894684 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_894684 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_894684 prefixEnd_894684 := by exact prefixLift 894684
  have htrace : WordTrace (prefixWord ++ tailWord_894684) baseStart_894684 baseEnd_894684 := by
    simpa [prefixWord, tailWord_894684, baseEnd_894684] using wordTrace_append hprefix tailTrace_894684
  have hstable : (prefixWord ++ tailWord_894684).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894684).length < 2 ^ (prefixWord ++ tailWord_894684).sum := by decide
  have hdescent : baseEnd_894684 < baseStart_894684 := by decide
  rcases family_descends (prefixWord ++ tailWord_894684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894692 : List Nat := [2, 3, 1, 1, 1, 3, 3, 4, 2]
def baseStart_894692 : Nat := 118140960795 + 894692 * 2 ^ 59
def prefixEnd_894692 : Nat := 4983230072969 + 3 ^ 40 * 894692 * 2
def baseEnd_894692 : Nat := 408361807762238886342571

theorem tailTrace_894692 : CollatzResearch.WordTrace tailWord_894692 prefixEnd_894692 408361807762238886342571 := by
  unfold tailWord_894692
  simp only [CollatzResearch.WordTrace]
  refine ⟨16316049037345580036791165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21754732049794106715721553 16316049037345580036791165)
  ·
    refine ⟨6118518389004592513796687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16316049037345580036791165 6118518389004592513796687)
    ·
      refine ⟨9177777583506888770695031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6118518389004592513796687 9177777583506888770695031)
      ·
        refine ⟨13766666375260333156042547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9177777583506888770695031 13766666375260333156042547)
        ·
          refine ⟨20649999562890499734063821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13766666375260333156042547 20649999562890499734063821)
          ·
            refine ⟨7743749836083937400273933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20649999562890499734063821 7743749836083937400273933)
            ·
              refine ⟨2903906188531476525102725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7743749836083937400273933 2903906188531476525102725)
              ·
                refine ⟨544482410349651848456761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2903906188531476525102725 544482410349651848456761)
                ·
                  refine ⟨408361807762238886342571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 544482410349651848456761 408361807762238886342571)
                  ·
                    rfl

theorem cell20_894692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 4, 2].length) (baseStart_894692 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_894692 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_894692 prefixEnd_894692 := by exact prefixLift 894692
  have htrace : WordTrace (prefixWord ++ tailWord_894692) baseStart_894692 baseEnd_894692 := by
    simpa [prefixWord, tailWord_894692, baseEnd_894692] using wordTrace_append hprefix tailTrace_894692
  have hstable : (prefixWord ++ tailWord_894692).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894692).length < 2 ^ (prefixWord ++ tailWord_894692).sum := by decide
  have hdescent : baseEnd_894692 < baseStart_894692 := by decide
  rcases family_descends (prefixWord ++ tailWord_894692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894695 : List Nat := [1, 1, 5, 4, 2, 1, 1, 5]
def baseStart_894695 : Nat := 118140960795 + 894695 * 2 ^ 59
def prefixEnd_894695 : Nat := 4983230072969 + 3 ^ 40 * 894695 * 2
def baseEnd_894695 : Nat := 136121059014661403080853

theorem tailTrace_894695 : CollatzResearch.WordTrace tailWord_894695 prefixEnd_894695 136121059014661403080853 := by
  unfold tailWord_894695
  simp only [CollatzResearch.WordTrace]
  refine ⟨32632207493680291585941539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21754804995786861057294359 32632207493680291585941539)
  ·
    refine ⟨48948311240520437378912309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32632207493680291585941539 48948311240520437378912309)
    ·
      refine ⟨4588904178798791004273029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48948311240520437378912309 4588904178798791004273029)
      ·
        refine ⟨860419533524773313301193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4588904178798791004273029 860419533524773313301193)
        ·
          refine ⟨645314650143579984975895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 860419533524773313301193 645314650143579984975895)
          ·
            refine ⟨967971975215369977463843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 645314650143579984975895 967971975215369977463843)
            ·
              refine ⟨1451957962823054966195765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 967971975215369977463843 1451957962823054966195765)
              ·
                refine ⟨136121059014661403080853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1451957962823054966195765 136121059014661403080853)
                ·
                  rfl

theorem cell20_894695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 5].length) (baseStart_894695 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_894695 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_894695 prefixEnd_894695 := by exact prefixLift 894695
  have htrace : WordTrace (prefixWord ++ tailWord_894695) baseStart_894695 baseEnd_894695 := by
    simpa [prefixWord, tailWord_894695, baseEnd_894695] using wordTrace_append hprefix tailTrace_894695
  have hstable : (prefixWord ++ tailWord_894695).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894695).length < 2 ^ (prefixWord ++ tailWord_894695).sum := by decide
  have hdescent : baseEnd_894695 < baseStart_894695 := by decide
  rcases family_descends (prefixWord ++ tailWord_894695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894706 : List Nat := [3, 2, 1, 3, 1, 1, 1, 5, 3]
def baseStart_894706 : Nat := 118140960795 + 894706 * 2 ^ 59
def prefixEnd_894706 : Nat := 4983230072969 + 3 ^ 40 * 894706 * 2
def baseEnd_894706 : Nat := 408368197743717059875847

theorem tailTrace_894706 : CollatzResearch.WordTrace tailWord_894706 prefixEnd_894706 408368197743717059875847 := by
  unfold tailWord_894706
  simp only [CollatzResearch.WordTrace]
  refine ⟨8158152174160110116147993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21755072464426960309727981 8158152174160110116147993)
  ·
    refine ⟨6118614130620082587110995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8158152174160110116147993 6118614130620082587110995)
    ·
      refine ⟨9177921195930123880666493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6118614130620082587110995 9177921195930123880666493)
      ·
        refine ⟨3441720448473796455249935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9177921195930123880666493 3441720448473796455249935)
        ·
          refine ⟨5162580672710694682874903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3441720448473796455249935 5162580672710694682874903)
          ·
            refine ⟨7743871009066042024312355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5162580672710694682874903 7743871009066042024312355)
            ·
              refine ⟨11615806513599063036468533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7743871009066042024312355 11615806513599063036468533)
              ·
                refine ⟨1088981860649912159668925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11615806513599063036468533 1088981860649912159668925)
                ·
                  refine ⟨408368197743717059875847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1088981860649912159668925 408368197743717059875847)
                  ·
                    rfl

theorem cell20_894706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 5, 3].length) (baseStart_894706 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_894706 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_894706 prefixEnd_894706 := by exact prefixLift 894706
  have htrace : WordTrace (prefixWord ++ tailWord_894706) baseStart_894706 baseEnd_894706 := by
    simpa [prefixWord, tailWord_894706, baseEnd_894706] using wordTrace_append hprefix tailTrace_894706
  have hstable : (prefixWord ++ tailWord_894706).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894706).length < 2 ^ (prefixWord ++ tailWord_894706).sum := by decide
  have hdescent : baseEnd_894706 < baseStart_894706 := by decide
  rcases family_descends (prefixWord ++ tailWord_894706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894730 : List Nat := [3, 1, 2, 2, 1, 3, 1, 5, 2]
def baseStart_894730 : Nat := 118140960795 + 894730 * 2 ^ 59
def prefixEnd_894730 : Nat := 4983230072969 + 3 ^ 40 * 894730 * 2
def baseEnd_894730 : Nat := 408379151997679643075749

theorem tailTrace_894730 : CollatzResearch.WordTrace tailWord_894730 prefixEnd_894730 408379151997679643075749 := by
  unfold tailWord_894730
  simp only [CollatzResearch.WordTrace]
  refine ⟨8158371012138373140866411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21755656032368995042310429 8158371012138373140866411)
  ·
    refine ⟨12237556518207559711299617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8158371012138373140866411 12237556518207559711299617)
    ·
      refine ⟨9178167388655669783474713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12237556518207559711299617 9178167388655669783474713)
      ·
        refine ⟨6883625541491752337606035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9178167388655669783474713 6883625541491752337606035)
        ·
          refine ⟨10325438312237628506409053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6883625541491752337606035 10325438312237628506409053)
          ·
            refine ⟨3872039367089110689903395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10325438312237628506409053 3872039367089110689903395)
            ·
              refine ⟨5808059050633666034855093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3872039367089110689903395 5808059050633666034855093)
              ·
                refine ⟨544505535996906190767665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5808059050633666034855093 544505535996906190767665)
                ·
                  refine ⟨408379151997679643075749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 544505535996906190767665 408379151997679643075749)
                  ·
                    rfl

theorem cell20_894730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 5, 2].length) (baseStart_894730 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_894730 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_894730 prefixEnd_894730 := by exact prefixLift 894730
  have htrace : WordTrace (prefixWord ++ tailWord_894730) baseStart_894730 baseEnd_894730 := by
    simpa [prefixWord, tailWord_894730, baseEnd_894730] using wordTrace_append hprefix tailTrace_894730
  have hstable : (prefixWord ++ tailWord_894730).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894730).length < 2 ^ (prefixWord ++ tailWord_894730).sum := by decide
  have hdescent : baseEnd_894730 < baseStart_894730 := by decide
  rcases family_descends (prefixWord ++ tailWord_894730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894744 : List Nat := [2, 1, 2, 3, 1, 1, 5, 2, 3]
def baseStart_894744 : Nat := 118140960795 + 894744 * 2 ^ 59
def prefixEnd_894744 : Nat := 4983230072969 + 3 ^ 40 * 894744 * 2
def baseEnd_894744 : Nat := 408385541979157816609025

theorem tailTrace_894744 : CollatzResearch.WordTrace tailWord_894744 prefixEnd_894744 408385541979157816609025 := by
  unfold tailWord_894744
  simp only [CollatzResearch.WordTrace]
  refine ⟨16316997335251386477237643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21755996447001848636316857 16316997335251386477237643)
  ·
    refine ⟨24475496002877079715856465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16316997335251386477237643 24475496002877079715856465)
    ·
      refine ⟨18356622002157809786892349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24475496002877079715856465 18356622002157809786892349)
      ·
        refine ⟨6883733250809178670084631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18356622002157809786892349 6883733250809178670084631)
        ·
          refine ⟨10325599876213768005126947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6883733250809178670084631 10325599876213768005126947)
          ·
            refine ⟨15488399814320652007690421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10325599876213768005126947 15488399814320652007690421)
            ·
              refine ⟨1452037482592561125720977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15488399814320652007690421 1452037482592561125720977)
              ·
                refine ⟨1089028111944420844290733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1452037482592561125720977 1089028111944420844290733)
                ·
                  refine ⟨408385541979157816609025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1089028111944420844290733 408385541979157816609025)
                  ·
                    rfl

theorem cell20_894744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 2, 3].length) (baseStart_894744 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_894744 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_894744 prefixEnd_894744 := by exact prefixLift 894744
  have htrace : WordTrace (prefixWord ++ tailWord_894744) baseStart_894744 baseEnd_894744 := by
    simpa [prefixWord, tailWord_894744, baseEnd_894744] using wordTrace_append hprefix tailTrace_894744
  have hstable : (prefixWord ++ tailWord_894744).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894744).length < 2 ^ (prefixWord ++ tailWord_894744).sum := by decide
  have hdescent : baseEnd_894744 < baseStart_894744 := by decide
  rcases family_descends (prefixWord ++ tailWord_894744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894751 : List Nat := [1, 1, 2, 4, 2, 1, 4, 1, 4]
def baseStart_894751 : Nat := 118140960795 + 894751 * 2 ^ 59
def prefixEnd_894751 : Nat := 4983230072969 + 3 ^ 40 * 894751 * 2
def baseEnd_894751 : Nat := 408388736969896903375663

theorem tailTrace_894751 : CollatzResearch.WordTrace tailWord_894751 prefixEnd_894751 408388736969896903375663 := by
  unfold tailWord_894751
  simp only [CollatzResearch.WordTrace]
  refine ⟨32634249981477413149980107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21756166654318275433320071 32634249981477413149980107)
  ·
    refine ⟨48951374972216119724970161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32634249981477413149980107 48951374972216119724970161)
    ·
      refine ⟨36713531229162089793727621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48951374972216119724970161 36713531229162089793727621)
      ·
        refine ⟨6883787105467891836323929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36713531229162089793727621 6883787105467891836323929)
        ·
          refine ⟨5162840329100918877242947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6883787105467891836323929 5162840329100918877242947)
          ·
            refine ⟨7744260493651378315864421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5162840329100918877242947 7744260493651378315864421)
            ·
              refine ⟨1452048842559633434224579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7744260493651378315864421 1452048842559633434224579)
              ·
                refine ⟨2178073263839450151336869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1452048842559633434224579 2178073263839450151336869)
                ·
                  refine ⟨408388736969896903375663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2178073263839450151336869 408388736969896903375663)
                  ·
                    rfl

theorem cell20_894751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 1, 4].length) (baseStart_894751 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_894751 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_894751 prefixEnd_894751 := by exact prefixLift 894751
  have htrace : WordTrace (prefixWord ++ tailWord_894751) baseStart_894751 baseEnd_894751 := by
    simpa [prefixWord, tailWord_894751, baseEnd_894751] using wordTrace_append hprefix tailTrace_894751
  have hstable : (prefixWord ++ tailWord_894751).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894751).length < 2 ^ (prefixWord ++ tailWord_894751).sum := by decide
  have hdescent : baseEnd_894751 < baseStart_894751 := by decide
  rcases family_descends (prefixWord ++ tailWord_894751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894782 : List Nat := [4, 2, 1, 2, 2, 1, 1, 2, 5]
def baseStart_894782 : Nat := 118140960795 + 894782 * 2 ^ 59
def prefixEnd_894782 : Nat := 4983230072969 + 3 ^ 40 * 894782 * 2
def baseEnd_894782 : Nat := 408402886214598573342203

theorem tailTrace_894782 : CollatzResearch.WordTrace tailWord_894782 prefixEnd_894782 408402886214598573342203 := by
  unfold tailWord_894782
  simp only [CollatzResearch.WordTrace]
  refine ⟨4079422580545638180544825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21756920429576736962905733 4079422580545638180544825)
  ·
    refine ⟨3059566935409228635408619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4079422580545638180544825 3059566935409228635408619)
    ·
      refine ⟨4589350403113842953112929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3059566935409228635408619 4589350403113842953112929)
      ·
        refine ⟨3442012802335382214834697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4589350403113842953112929 3442012802335382214834697)
        ·
          refine ⟨2581509601751536661126023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3442012802335382214834697 2581509601751536661126023)
          ·
            refine ⟨3872264402627304991689035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2581509601751536661126023 3872264402627304991689035)
            ·
              refine ⟨5808396603940957487533553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3872264402627304991689035 5808396603940957487533553)
              ·
                refine ⟨4356297452955718115650165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5808396603940957487533553 4356297452955718115650165)
                ·
                  refine ⟨408402886214598573342203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4356297452955718115650165 408402886214598573342203)
                  ·
                    rfl

theorem cell20_894782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_894782 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_894782 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_894782 prefixEnd_894782 := by exact prefixLift 894782
  have htrace : WordTrace (prefixWord ++ tailWord_894782) baseStart_894782 baseEnd_894782 := by
    simpa [prefixWord, tailWord_894782, baseEnd_894782] using wordTrace_append hprefix tailTrace_894782
  have hstable : (prefixWord ++ tailWord_894782).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894782).length < 2 ^ (prefixWord ++ tailWord_894782).sum := by decide
  have hdescent : baseEnd_894782 < baseStart_894782 := by decide
  rcases family_descends (prefixWord ++ tailWord_894782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894855 : List Nat := [1, 1, 4, 2, 12]
def baseStart_894855 : Nat := 118140960795 + 894855 * 2 ^ 59
def prefixEnd_894855 : Nat := 4983230072969 + 3 ^ 40 * 894855 * 2
def baseEnd_894855 : Nat := 5042422288934997085291

theorem tailTrace_894855 : CollatzResearch.WordTrace tailWord_894855 prefixEnd_894855 5042422288934997085291 := by
  unfold tailWord_894855
  simp only [CollatzResearch.WordTrace]
  refine ⟨32638043173100638911766019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21758695448733759274510679 32638043173100638911766019)
  ·
    refine ⟨48957064759650958367649029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32638043173100638911766019 48957064759650958367649029)
    ·
      refine ⟨9179449642434554693934193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48957064759650958367649029 9179449642434554693934193)
      ·
        refine ⟨6884587231825916020450645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9179449642434554693934193 6884587231825916020450645)
        ·
          refine ⟨5042422288934997085291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 6884587231825916020450645 5042422288934997085291)
          ·
            rfl

theorem cell20_894855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 12].length) (baseStart_894855 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_894855 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_894855 prefixEnd_894855 := by exact prefixLift 894855
  have htrace : WordTrace (prefixWord ++ tailWord_894855) baseStart_894855 baseEnd_894855 := by
    simpa [prefixWord, tailWord_894855, baseEnd_894855] using wordTrace_append hprefix tailTrace_894855
  have hstable : (prefixWord ++ tailWord_894855).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894855).length < 2 ^ (prefixWord ++ tailWord_894855).sum := by decide
  have hdescent : baseEnd_894855 < baseStart_894855 := by decide
  rcases family_descends (prefixWord ++ tailWord_894855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894882 : List Nat := [3, 3, 1, 2, 3, 1, 1, 2, 4]
def baseStart_894882 : Nat := 118140960795 + 894882 * 2 ^ 59
def prefixEnd_894882 : Nat := 4983230072969 + 3 ^ 40 * 894882 * 2
def baseEnd_894882 : Nat := 408448528939442670008461

theorem tailTrace_894882 : CollatzResearch.WordTrace tailWord_894882 prefixEnd_894882 408448528939442670008461 := by
  unfold tailWord_894882
  simp only [CollatzResearch.WordTrace]
  refine ⟨8159756986000705630749725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21759351962668548348665933 8159756986000705630749725)
  ·
    refine ⟨3059908869750264611531147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8159756986000705630749725 3059908869750264611531147)
    ·
      refine ⟨4589863304625396917296721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3059908869750264611531147 4589863304625396917296721)
      ·
        refine ⟨3442397478469047687972541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4589863304625396917296721 3442397478469047687972541)
        ·
          refine ⟨1290899054425892882989703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3442397478469047687972541 1290899054425892882989703)
          ·
            refine ⟨1936348581638839324484555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1290899054425892882989703 1936348581638839324484555)
            ·
              refine ⟨2904522872458258986726833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1936348581638839324484555 2904522872458258986726833)
              ·
                refine ⟨2178392154343694240045125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2904522872458258986726833 2178392154343694240045125)
                ·
                  refine ⟨408448528939442670008461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2178392154343694240045125 408448528939442670008461)
                  ·
                    rfl

theorem cell20_894882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_894882 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_894882 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_894882 prefixEnd_894882 := by exact prefixLift 894882
  have htrace : WordTrace (prefixWord ++ tailWord_894882) baseStart_894882 baseEnd_894882 := by
    simpa [prefixWord, tailWord_894882, baseEnd_894882] using wordTrace_append hprefix tailTrace_894882
  have hstable : (prefixWord ++ tailWord_894882).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894882).length < 2 ^ (prefixWord ++ tailWord_894882).sum := by decide
  have hdescent : baseEnd_894882 < baseStart_894882 := by decide
  rcases family_descends (prefixWord ++ tailWord_894882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894910 : List Nat := [4, 2, 1, 1, 1, 4, 7]
def baseStart_894910 : Nat := 118140960795 + 894910 * 2 ^ 59
def prefixEnd_894910 : Nat := 4983230072969 + 3 ^ 40 * 894910 * 2
def baseEnd_894910 : Nat := 45384589878044335230557

theorem tailTrace_894910 : CollatzResearch.WordTrace tailWord_894910 prefixEnd_894910 45384589878044335230557 := by
  unfold tailWord_894910
  simp only [CollatzResearch.WordTrace]
  refine ⟨4080006148487672913127273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21760032791934255536678789 4080006148487672913127273)
  ·
    refine ⟨3060004611365754684845455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4080006148487672913127273 3060004611365754684845455)
    ·
      refine ⟨4590006917048632027268183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3060004611365754684845455 4590006917048632027268183)
      ·
        refine ⟨6885010375572948040902275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4590006917048632027268183 6885010375572948040902275)
        ·
          refine ⟨10327515563359422061353413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6885010375572948040902275 10327515563359422061353413)
          ·
            refine ⟨1936409168129891636503765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10327515563359422061353413 1936409168129891636503765)
            ·
              refine ⟨45384589878044335230557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1936409168129891636503765 45384589878044335230557)
              ·
                rfl

theorem cell20_894910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 7].length) (baseStart_894910 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_894910 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_894910 prefixEnd_894910 := by exact prefixLift 894910
  have htrace : WordTrace (prefixWord ++ tailWord_894910) baseStart_894910 baseEnd_894910 := by
    simpa [prefixWord, tailWord_894910, baseEnd_894910] using wordTrace_append hprefix tailTrace_894910
  have hstable : (prefixWord ++ tailWord_894910).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894910).length < 2 ^ (prefixWord ++ tailWord_894910).sum := by decide
  have hdescent : baseEnd_894910 < baseStart_894910 := by decide
  rcases family_descends (prefixWord ++ tailWord_894910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894917 : List Nat := [1, 3, 1, 1, 1, 1, 1, 8, 3]
def baseStart_894917 : Nat := 118140960795 + 894917 * 2 ^ 59
def prefixEnd_894917 : Nat := 4983230072969 + 3 ^ 40 * 894917 * 2
def baseEnd_894917 : Nat := 408464503893138103841651

theorem tailTrace_894917 : CollatzResearch.WordTrace tailWord_894917 prefixEnd_894917 408464503893138103841651 := by
  unfold tailWord_894917
  simp only [CollatzResearch.WordTrace]
  refine ⟨32640304498876023500523005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21760202999250682333682003 32640304498876023500523005)
  ·
    refine ⟨12240114187078508812696127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32640304498876023500523005 12240114187078508812696127)
    ·
      refine ⟨18360171280617763219044191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12240114187078508812696127 18360171280617763219044191)
      ·
        refine ⟨27540256920926644828566287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18360171280617763219044191 27540256920926644828566287)
        ·
          refine ⟨41310385381389967242849431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27540256920926644828566287 41310385381389967242849431)
          ·
            refine ⟨61965578072084950864274147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41310385381389967242849431 61965578072084950864274147)
            ·
              refine ⟨92948367108127426296411221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61965578072084950864274147 92948367108127426296411221)
              ·
                refine ⟨1089238677048368276911069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 92948367108127426296411221 1089238677048368276911069)
                ·
                  refine ⟨408464503893138103841651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1089238677048368276911069 408464503893138103841651)
                  ·
                    rfl

theorem cell20_894917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 8, 3].length) (baseStart_894917 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_894917 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_894917 prefixEnd_894917 := by exact prefixLift 894917
  have htrace : WordTrace (prefixWord ++ tailWord_894917) baseStart_894917 baseEnd_894917 := by
    simpa [prefixWord, tailWord_894917, baseEnd_894917] using wordTrace_append hprefix tailTrace_894917
  have hstable : (prefixWord ++ tailWord_894917).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894917).length < 2 ^ (prefixWord ++ tailWord_894917).sum := by decide
  have hdescent : baseEnd_894917 < baseStart_894917 := by decide
  rcases family_descends (prefixWord ++ tailWord_894917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894920 : List Nat := [2, 1, 3, 1, 4, 1, 2, 4, 2]
def baseStart_894920 : Nat := 118140960795 + 894920 * 2 ^ 59
def prefixEnd_894920 : Nat := 4983230072969 + 3 ^ 40 * 894920 * 2
def baseEnd_894920 : Nat := 408465873174883426741639

theorem tailTrace_894920 : CollatzResearch.WordTrace tailWord_894920 prefixEnd_894920 408465873174883426741639 := by
  unfold tailWord_894920
  simp only [CollatzResearch.WordTrace]
  refine ⟨16320206958932577506441107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21760275945243436675254809 16320206958932577506441107)
  ·
    refine ⟨24480310438398866259661661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16320206958932577506441107 24480310438398866259661661)
    ·
      refine ⟨9180116414399574847373123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24480310438398866259661661 9180116414399574847373123)
      ·
        refine ⟨13770174621599362271059685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9180116414399574847373123 13770174621599362271059685)
        ·
          refine ⟨2581907741549880425823691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13770174621599362271059685 2581907741549880425823691)
          ·
            refine ⟨3872861612324820638735537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2581907741549880425823691 3872861612324820638735537)
            ·
              refine ⟨2904646209243615479051653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3872861612324820638735537 2904646209243615479051653)
              ·
                refine ⟨544621164233177902322185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2904646209243615479051653 544621164233177902322185)
                ·
                  refine ⟨408465873174883426741639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 544621164233177902322185 408465873174883426741639)
                  ·
                    rfl

theorem cell20_894920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 4, 2].length) (baseStart_894920 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_894920 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_894920 prefixEnd_894920 := by exact prefixLift 894920
  have htrace : WordTrace (prefixWord ++ tailWord_894920) baseStart_894920 baseEnd_894920 := by
    simpa [prefixWord, tailWord_894920, baseEnd_894920] using wordTrace_append hprefix tailTrace_894920
  have hstable : (prefixWord ++ tailWord_894920).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894920).length < 2 ^ (prefixWord ++ tailWord_894920).sum := by decide
  have hdescent : baseEnd_894920 < baseStart_894920 := by decide
  rcases family_descends (prefixWord ++ tailWord_894920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894930 : List Nat := [3, 2, 2, 3, 2, 1, 3, 1, 3]
def baseStart_894930 : Nat := 118140960795 + 894930 * 2 ^ 59
def prefixEnd_894930 : Nat := 4983230072969 + 3 ^ 40 * 894930 * 2
def baseEnd_894930 : Nat := 408470437447367836408265

theorem tailTrace_894930 : CollatzResearch.WordTrace tailWord_894930 prefixEnd_894930 408470437447367836408265 := by
  unfold tailWord_894930
  simp only [CollatzResearch.WordTrace]
  refine ⟨8160194661957231680186561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21760519098552617813830829 8160194661957231680186561)
  ·
    refine ⟨6120145996467923760139921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8160194661957231680186561 6120145996467923760139921)
    ·
      refine ⟨4590109497350942820104941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6120145996467923760139921 4590109497350942820104941)
      ·
        refine ⟨1721291061506603557539353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4590109497350942820104941 1721291061506603557539353)
        ·
          refine ⟨1290968296129952668154515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1721291061506603557539353 1290968296129952668154515)
          ·
            refine ⟨1936452444194929002231773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1290968296129952668154515 1936452444194929002231773)
            ·
              refine ⟨726169666573098375836915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1936452444194929002231773 726169666573098375836915)
              ·
                refine ⟨1089254499859647563755373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 726169666573098375836915 1089254499859647563755373)
                ·
                  refine ⟨408470437447367836408265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1089254499859647563755373 408470437447367836408265)
                  ·
                    rfl

theorem cell20_894930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 3, 1, 3].length) (baseStart_894930 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_894930 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_894930 prefixEnd_894930 := by exact prefixLift 894930
  have htrace : WordTrace (prefixWord ++ tailWord_894930) baseStart_894930 baseEnd_894930 := by
    simpa [prefixWord, tailWord_894930, baseEnd_894930] using wordTrace_append hprefix tailTrace_894930
  have hstable : (prefixWord ++ tailWord_894930).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894930).length < 2 ^ (prefixWord ++ tailWord_894930).sum := by decide
  have hdescent : baseEnd_894930 < baseStart_894930 := by decide
  rcases family_descends (prefixWord ++ tailWord_894930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894940 : List Nat := [2, 2, 6, 1, 1, 2, 2, 4]
def baseStart_894940 : Nat := 118140960795 + 894940 * 2 ^ 59
def prefixEnd_894940 : Nat := 4983230072969 + 3 ^ 40 * 894940 * 2
def baseEnd_894940 : Nat := 136158333906617415358297

theorem tailTrace_894940 : CollatzResearch.WordTrace tailWord_894940 prefixEnd_894940 136158333906617415358297 := by
  unfold tailWord_894940
  simp only [CollatzResearch.WordTrace]
  refine ⟨16320571688896349214305137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21760762251861798952406849 16320571688896349214305137)
  ·
    refine ⟨12240428766672261910728853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16320571688896349214305137 12240428766672261910728853)
    ·
      refine ⟨573770098437762277065415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 12240428766672261910728853 573770098437762277065415)
      ·
        refine ⟨860655147656643415598123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 573770098437762277065415 860655147656643415598123)
        ·
          refine ⟨1290982721484965123397185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 860655147656643415598123 1290982721484965123397185)
          ·
            refine ⟨968237041113723842547889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1290982721484965123397185 968237041113723842547889)
            ·
              refine ⟨726177780835292881910917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 968237041113723842547889 726177780835292881910917)
              ·
                refine ⟨136158333906617415358297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 726177780835292881910917 136158333906617415358297)
                ·
                  rfl

theorem cell20_894940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 2, 4].length) (baseStart_894940 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_894940 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_894940 prefixEnd_894940 := by exact prefixLift 894940
  have htrace : WordTrace (prefixWord ++ tailWord_894940) baseStart_894940 baseEnd_894940 := by
    simpa [prefixWord, tailWord_894940, baseEnd_894940] using wordTrace_append hprefix tailTrace_894940
  have hstable : (prefixWord ++ tailWord_894940).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894940).length < 2 ^ (prefixWord ++ tailWord_894940).sum := by decide
  have hdescent : baseEnd_894940 < baseStart_894940 := by decide
  rcases family_descends (prefixWord ++ tailWord_894940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894969 : List Nat := [1, 2, 1, 3, 1, 4, 8]
def baseStart_894969 : Nat := 118140960795 + 894969 * 2 ^ 59
def prefixEnd_894969 : Nat := 4983230072969 + 3 ^ 40 * 894969 * 2
def baseEnd_894969 : Nat := 45387582012228559345345

theorem tailTrace_894969 : CollatzResearch.WordTrace tailWord_894969 prefixEnd_894969 45387582012228559345345 := by
  unfold tailWord_894969
  simp only [CollatzResearch.WordTrace]
  refine ⟨32642201094687636381415961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21761467396458424254277307 32642201094687636381415961)
  ·
    refine ⟨24481650821015727286061971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32642201094687636381415961 24481650821015727286061971)
    ·
      refine ⟨36722476231523590929092957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24481650821015727286061971 36722476231523590929092957)
      ·
        refine ⟨13770928586821346598409859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36722476231523590929092957 13770928586821346598409859)
        ·
          refine ⟨20656392880232019897614789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13770928586821346598409859 20656392880232019897614789)
          ·
            refine ⟨3873073665043503730802773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20656392880232019897614789 3873073665043503730802773)
            ·
              refine ⟨45387582012228559345345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3873073665043503730802773 45387582012228559345345)
              ·
                rfl

theorem cell20_894969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 8].length) (baseStart_894969 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_894969 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_894969 prefixEnd_894969 := by exact prefixLift 894969
  have htrace : WordTrace (prefixWord ++ tailWord_894969) baseStart_894969 baseEnd_894969 := by
    simpa [prefixWord, tailWord_894969, baseEnd_894969] using wordTrace_append hprefix tailTrace_894969
  have hstable : (prefixWord ++ tailWord_894969).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894969).length < 2 ^ (prefixWord ++ tailWord_894969).sum := by decide
  have hdescent : baseEnd_894969 < baseStart_894969 := by decide
  rcases family_descends (prefixWord ++ tailWord_894969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894979 : List Nat := [1, 1, 1, 3, 2, 1, 1, 8, 2]
def baseStart_894979 : Nat := 118140960795 + 894979 * 2 ^ 59
def prefixEnd_894979 : Nat := 4983230072969 + 3 ^ 40 * 894979 * 2
def baseEnd_894979 : Nat := 408492802382541443774731

theorem tailTrace_894979 : CollatzResearch.WordTrace tailWord_894979 prefixEnd_894979 408492802382541443774731 := by
  unfold tailWord_894979
  simp only [CollatzResearch.WordTrace]
  refine ⟨32642565824651408089279991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21761710549767605392853327 32642565824651408089279991)
  ·
    refine ⟨48963848736977112133919987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32642565824651408089279991 48963848736977112133919987)
    ·
      refine ⟨73445773105465668200879981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48963848736977112133919987 73445773105465668200879981)
      ·
        refine ⟨27542164914549625575329993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73445773105465668200879981 27542164914549625575329993)
        ·
          refine ⟨20656623685912219181497495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27542164914549625575329993 20656623685912219181497495)
          ·
            refine ⟨30984935528868328772246243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20656623685912219181497495 30984935528868328772246243)
            ·
              refine ⟨46477403293302493158369365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30984935528868328772246243 46477403293302493158369365)
              ·
                refine ⟨544657069843388591699641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 46477403293302493158369365 544657069843388591699641)
                ·
                  refine ⟨408492802382541443774731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 544657069843388591699641 408492802382541443774731)
                  ·
                    rfl

theorem cell20_894979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 8, 2].length) (baseStart_894979 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_894979 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_894979 prefixEnd_894979 := by exact prefixLift 894979
  have htrace : WordTrace (prefixWord ++ tailWord_894979) baseStart_894979 baseEnd_894979 := by
    simpa [prefixWord, tailWord_894979, baseEnd_894979] using wordTrace_append hprefix tailTrace_894979
  have hstable : (prefixWord ++ tailWord_894979).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894979).length < 2 ^ (prefixWord ++ tailWord_894979).sum := by decide
  have hdescent : baseEnd_894979 < baseStart_894979 := by decide
  rcases family_descends (prefixWord ++ tailWord_894979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895000 : List Nat := [2, 1, 2, 3, 2, 1, 2, 1, 6]
def baseStart_895000 : Nat := 118140960795 + 895000 * 2 ^ 59
def prefixEnd_895000 : Nat := 4983230072969 + 3 ^ 40 * 895000 * 2
def baseEnd_895000 : Nat := 408502387354758704074645

theorem tailTrace_895000 : CollatzResearch.WordTrace tailWord_895000 prefixEnd_895000 408502387354758704074645 := by
  unfold tailWord_895000
  simp only [CollatzResearch.WordTrace]
  refine ⟨16321665878787664337897227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21762221171716885783862969 16321665878787664337897227)
  ·
    refine ⟨24482498818181496506845841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16321665878787664337897227 24482498818181496506845841)
    ·
      refine ⟨18361874113636122380134381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24482498818181496506845841 18361874113636122380134381)
      ·
        refine ⟨6885702792613545892550393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18361874113636122380134381 6885702792613545892550393)
        ·
          refine ⟨5164277094460159419412795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6885702792613545892550393 5164277094460159419412795)
          ·
            refine ⟨7746415641690239129119193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5164277094460159419412795 7746415641690239129119193)
            ·
              refine ⟨5809811731267679346839395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7746415641690239129119193 5809811731267679346839395)
              ·
                refine ⟨8714717596901519020259093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5809811731267679346839395 8714717596901519020259093)
                ·
                  refine ⟨408502387354758704074645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8714717596901519020259093 408502387354758704074645)
                  ·
                    rfl

theorem cell20_895000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 6].length) (baseStart_895000 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_895000 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_895000 prefixEnd_895000 := by exact prefixLift 895000
  have htrace : WordTrace (prefixWord ++ tailWord_895000) baseStart_895000 baseEnd_895000 := by
    simpa [prefixWord, tailWord_895000, baseEnd_895000] using wordTrace_append hprefix tailTrace_895000
  have hstable : (prefixWord ++ tailWord_895000).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895000).length < 2 ^ (prefixWord ++ tailWord_895000).sum := by decide
  have hdescent : baseEnd_895000 < baseStart_895000 := by decide
  rcases family_descends (prefixWord ++ tailWord_895000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895007 : List Nat := [1, 1, 2, 4, 1, 2, 1, 8]
def baseStart_895007 : Nat := 118140960795 + 895007 * 2 ^ 59
def prefixEnd_895007 : Nat := 4983230072969 + 3 ^ 40 * 895007 * 2
def baseEnd_895007 : Nat := 136168527448499263613761

theorem tailTrace_895007 : CollatzResearch.WordTrace tailWord_895007 prefixEnd_895007 136168527448499263613761 := by
  unfold tailWord_895007
  simp only [CollatzResearch.WordTrace]
  refine ⟨32643587068549968871299275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21762391379033312580866183 32643587068549968871299275)
  ·
    refine ⟨48965380602824953306948913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32643587068549968871299275 48965380602824953306948913)
    ·
      refine ⟨36724035452118714980211685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48965380602824953306948913 36724035452118714980211685)
      ·
        refine ⟨6885756647272259058789691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36724035452118714980211685 6885756647272259058789691)
        ·
          refine ⟨10328634970908388588184537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6885756647272259058789691 10328634970908388588184537)
          ·
            refine ⟨7746476228181291441138403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10328634970908388588184537 7746476228181291441138403)
            ·
              refine ⟨11619714342271937161707605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7746476228181291441138403 11619714342271937161707605)
              ·
                refine ⟨136168527448499263613761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11619714342271937161707605 136168527448499263613761)
                ·
                  rfl

theorem cell20_895007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 8].length) (baseStart_895007 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_895007 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_895007 prefixEnd_895007 := by exact prefixLift 895007
  have htrace : WordTrace (prefixWord ++ tailWord_895007) baseStart_895007 baseEnd_895007 := by
    simpa [prefixWord, tailWord_895007, baseEnd_895007] using wordTrace_append hprefix tailTrace_895007
  have hstable : (prefixWord ++ tailWord_895007).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895007).length < 2 ^ (prefixWord ++ tailWord_895007).sum := by decide
  have hdescent : baseEnd_895007 < baseStart_895007 := by decide
  rcases family_descends (prefixWord ++ tailWord_895007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895031 : List Nat := [1, 1, 3, 1, 2, 2, 3, 4, 3]
def baseStart_895031 : Nat := 118140960795 + 895031 * 2 ^ 59
def prefixEnd_895031 : Nat := 4983230072969 + 3 ^ 40 * 895031 * 2
def baseEnd_895031 : Nat := 408516536599460374041185

theorem tailTrace_895031 : CollatzResearch.WordTrace tailWord_895031 prefixEnd_895031 408516536599460374041185 := by
  unfold tailWord_895031
  simp only [CollatzResearch.WordTrace]
  refine ⟨32644462420463020970172947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21762974946975347313448631 32644462420463020970172947)
  ·
    refine ⟨48966693630694531455259421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32644462420463020970172947 48966693630694531455259421)
    ·
      refine ⟨18362510111510449295722283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48966693630694531455259421 18362510111510449295722283)
      ·
        refine ⟨27543765167265673943583425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18362510111510449295722283 27543765167265673943583425)
        ·
          refine ⟨20657823875449255457687569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27543765167265673943583425 20657823875449255457687569)
          ·
            refine ⟨15493367906586941593265677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20657823875449255457687569 15493367906586941593265677)
            ·
              refine ⟨5810012964970103097474629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15493367906586941593265677 5810012964970103097474629)
              ·
                refine ⟨1089377430931894330776493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5810012964970103097474629 1089377430931894330776493)
                ·
                  refine ⟨408516536599460374041185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1089377430931894330776493 408516536599460374041185)
                  ·
                    rfl

theorem cell20_895031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 4, 3].length) (baseStart_895031 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_895031 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_895031 prefixEnd_895031 := by exact prefixLift 895031
  have htrace : WordTrace (prefixWord ++ tailWord_895031) baseStart_895031 baseEnd_895031 := by
    simpa [prefixWord, tailWord_895031, baseEnd_895031] using wordTrace_append hprefix tailTrace_895031
  have hstable : (prefixWord ++ tailWord_895031).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895031).length < 2 ^ (prefixWord ++ tailWord_895031).sum := by decide
  have hdescent : baseEnd_895031 < baseStart_895031 := by decide
  rcases family_descends (prefixWord ++ tailWord_895031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895041 : List Nat := [1, 2, 5, 1, 2, 3, 1, 5]
def baseStart_895041 : Nat := 118140960795 + 895041 * 2 ^ 59
def prefixEnd_895041 : Nat := 4983230072969 + 3 ^ 40 * 895041 * 2
def baseEnd_895041 : Nat := 136173700290648261235937

theorem tailTrace_895041 : CollatzResearch.WordTrace tailWord_895041 prefixEnd_895041 136173700290648261235937 := by
  unfold tailWord_895041
  simp only [CollatzResearch.WordTrace]
  refine ⟨32644827150426792678036977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21763218100284528452024651 32644827150426792678036977)
  ·
    refine ⟨24483620362820094508527733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32644827150426792678036977 24483620362820094508527733)
    ·
      refine ⟨2295339409014383860174475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24483620362820094508527733 2295339409014383860174475)
      ·
        refine ⟨3443009113521575790261713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2295339409014383860174475 3443009113521575790261713)
        ·
          refine ⟨2582256835141181842696285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3443009113521575790261713 2582256835141181842696285)
          ·
            refine ⟨968346313177943191011107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2582256835141181842696285 968346313177943191011107)
            ·
              refine ⟨1452519469766914786516661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 968346313177943191011107 1452519469766914786516661)
              ·
                refine ⟨136173700290648261235937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1452519469766914786516661 136173700290648261235937)
                ·
                  rfl

theorem cell20_895041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 5].length) (baseStart_895041 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_895041 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_895041 prefixEnd_895041 := by exact prefixLift 895041
  have htrace : WordTrace (prefixWord ++ tailWord_895041) baseStart_895041 baseEnd_895041 := by
    simpa [prefixWord, tailWord_895041, baseEnd_895041] using wordTrace_append hprefix tailTrace_895041
  have hstable : (prefixWord ++ tailWord_895041).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895041).length < 2 ^ (prefixWord ++ tailWord_895041).sum := by decide
  have hdescent : baseEnd_895041 < baseStart_895041 := by decide
  rcases family_descends (prefixWord ++ tailWord_895041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895072 : List Nat := [2, 1, 1, 3, 2, 4, 2, 3, 2]
def baseStart_895072 : Nat := 118140960795 + 895072 * 2 ^ 59
def prefixEnd_895072 : Nat := 4983230072969 + 3 ^ 40 * 895072 * 2
def baseEnd_895072 : Nat := 408535250116646453674351

theorem tailTrace_895072 : CollatzResearch.WordTrace tailWord_895072 prefixEnd_895072 408535250116646453674351 := by
  unfold tailWord_895072
  simp only [CollatzResearch.WordTrace]
  refine ⟨16322978906657242486207735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21763971875542989981610313 16322978906657242486207735)
  ·
    refine ⟨24484468359985863729311603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16322978906657242486207735 24484468359985863729311603)
    ·
      refine ⟨36726702539978795593967405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24484468359985863729311603 36726702539978795593967405)
      ·
        refine ⟨13772513452492048347737777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36726702539978795593967405 13772513452492048347737777)
        ·
          refine ⟨10329385089369036260803333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13772513452492048347737777 10329385089369036260803333)
          ·
            refine ⟨1936759704256694298900625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10329385089369036260803333 1936759704256694298900625)
            ·
              refine ⟨1452569778192520724175469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1936759704256694298900625 1452569778192520724175469)
              ·
                refine ⟨544713666822195271565801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1452569778192520724175469 544713666822195271565801)
                ·
                  refine ⟨408535250116646453674351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 544713666822195271565801 408535250116646453674351)
                  ·
                    rfl

theorem cell20_895072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 3, 2].length) (baseStart_895072 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_895072 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_895072 prefixEnd_895072 := by exact prefixLift 895072
  have htrace : WordTrace (prefixWord ++ tailWord_895072) baseStart_895072 baseEnd_895072 := by
    simpa [prefixWord, tailWord_895072, baseEnd_895072] using wordTrace_append hprefix tailTrace_895072
  have hstable : (prefixWord ++ tailWord_895072).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895072).length < 2 ^ (prefixWord ++ tailWord_895072).sum := by decide
  have hdescent : baseEnd_895072 < baseStart_895072 := by decide
  rcases family_descends (prefixWord ++ tailWord_895072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895082 : List Nat := [3, 1, 3, 2, 4, 1, 1, 2, 3]
def baseStart_895082 : Nat := 118140960795 + 895082 * 2 ^ 59
def prefixEnd_895082 : Nat := 4983230072969 + 3 ^ 40 * 895082 * 2
def baseEnd_895082 : Nat := 408539814389130863340977

theorem tailTrace_895082 : CollatzResearch.WordTrace tailWord_895082 prefixEnd_895082 408539814389130863340977 := by
  unfold tailWord_895082
  simp only [CollatzResearch.WordTrace]
  refine ⟨8161580635819564170069875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21764215028852171120186333 8161580635819564170069875)
  ·
    refine ⟨12242370953729346255104813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8161580635819564170069875 12242370953729346255104813)
    ·
      refine ⟨4590889107648504845664305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12242370953729346255104813 4590889107648504845664305)
      ·
        refine ⟨3443166830736378634248229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4590889107648504845664305 3443166830736378634248229)
        ·
          refine ⟨645593780763070993921543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3443166830736378634248229 645593780763070993921543)
          ·
            refine ⟨968390671144606490882315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 645593780763070993921543 968390671144606490882315)
            ·
              refine ⟨1452586006716909736323473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 968390671144606490882315 1452586006716909736323473)
              ·
                refine ⟨1089439505037682302242605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1452586006716909736323473 1089439505037682302242605)
                ·
                  refine ⟨408539814389130863340977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1089439505037682302242605 408539814389130863340977)
                  ·
                    rfl

theorem cell20_895082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 2, 3].length) (baseStart_895082 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_895082 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_895082 prefixEnd_895082 := by exact prefixLift 895082
  have htrace : WordTrace (prefixWord ++ tailWord_895082) baseStart_895082 baseEnd_895082 := by
    simpa [prefixWord, tailWord_895082, baseEnd_895082] using wordTrace_append hprefix tailTrace_895082
  have hstable : (prefixWord ++ tailWord_895082).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895082).length < 2 ^ (prefixWord ++ tailWord_895082).sum := by decide
  have hdescent : baseEnd_895082 < baseStart_895082 := by decide
  rcases family_descends (prefixWord ++ tailWord_895082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895127 : List Nat := [1, 1, 3, 3, 4, 2, 1, 3, 2]
def baseStart_895127 : Nat := 118140960795 + 895127 * 2 ^ 59
def prefixEnd_895127 : Nat := 4983230072969 + 3 ^ 40 * 895127 * 2
def baseEnd_895127 : Nat := 408560353615310706840793

theorem tailTrace_895127 : CollatzResearch.WordTrace tailWord_895127 prefixEnd_895127 408560353615310706840793 := by
  unfold tailWord_895127
  simp only [CollatzResearch.WordTrace]
  refine ⟨32647963828115229365667635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21765309218743486243778423 32647963828115229365667635)
  ·
    refine ⟨48971945742172844048501453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32647963828115229365667635 48971945742172844048501453)
    ·
      refine ⟨18364479653314816518188045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48971945742172844048501453 18364479653314816518188045)
      ·
        refine ⟨6886679869993056194320517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18364479653314816518188045 6886679869993056194320517)
        ·
          refine ⟨1291252475623698036435097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6886679869993056194320517 1291252475623698036435097)
          ·
            refine ⟨968439356717773527326323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1291252475623698036435097 968439356717773527326323)
            ·
              refine ⟨1452659035076660290989485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 968439356717773527326323 1452659035076660290989485)
              ·
                refine ⟨544747138153747609121057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1452659035076660290989485 544747138153747609121057)
                ·
                  refine ⟨408560353615310706840793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 544747138153747609121057 408560353615310706840793)
                  ·
                    rfl

theorem cell20_895127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 3, 2].length) (baseStart_895127 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_895127 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_895127 prefixEnd_895127 := by exact prefixLift 895127
  have htrace : WordTrace (prefixWord ++ tailWord_895127) baseStart_895127 baseEnd_895127 := by
    simpa [prefixWord, tailWord_895127, baseEnd_895127] using wordTrace_append hprefix tailTrace_895127
  have hstable : (prefixWord ++ tailWord_895127).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895127).length < 2 ^ (prefixWord ++ tailWord_895127).sum := by decide
  have hdescent : baseEnd_895127 < baseStart_895127 := by decide
  rcases family_descends (prefixWord ++ tailWord_895127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895134 : List Nat := [4, 3, 1, 1, 4, 1, 6]
def baseStart_895134 : Nat := 118140960795 + 895134 * 2 ^ 59
def prefixEnd_895134 : Nat := 4983230072969 + 3 ^ 40 * 895134 * 2
def baseEnd_895134 : Nat := 45395949845116643734159

theorem tailTrace_895134 : CollatzResearch.WordTrace tailWord_895134 prefixEnd_895134 45395949845116643734159 := by
  unfold tailWord_895134
  simp only [CollatzResearch.WordTrace]
  refine ⟨4081027392386233695146557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21765479426059913040781637 4081027392386233695146557)
  ·
    refine ⟨1530385272144837635679959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4081027392386233695146557 1530385272144837635679959)
    ·
      refine ⟨2295577908217256453519939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1530385272144837635679959 2295577908217256453519939)
      ·
        refine ⟨3443366862325884680279909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2295577908217256453519939 3443366862325884680279909)
        ·
          refine ⟨645631286686103377552483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3443366862325884680279909 645631286686103377552483)
          ·
            refine ⟨968446930029155066328725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 645631286686103377552483 968446930029155066328725)
            ·
              refine ⟨45395949845116643734159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 968446930029155066328725 45395949845116643734159)
              ·
                rfl

theorem cell20_895134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 6].length) (baseStart_895134 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_895134 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_895134 prefixEnd_895134 := by exact prefixLift 895134
  have htrace : WordTrace (prefixWord ++ tailWord_895134) baseStart_895134 baseEnd_895134 := by
    simpa [prefixWord, tailWord_895134, baseEnd_895134] using wordTrace_append hprefix tailTrace_895134
  have hstable : (prefixWord ++ tailWord_895134).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895134).length < 2 ^ (prefixWord ++ tailWord_895134).sum := by decide
  have hdescent : baseEnd_895134 < baseStart_895134 := by decide
  rcases family_descends (prefixWord ++ tailWord_895134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895138 : List Nat := [3, 3, 1, 3, 1, 1, 8]
def baseStart_895138 : Nat := 118140960795 + 895138 * 2 ^ 59
def prefixEnd_895138 : Nat := 4983230072969 + 3 ^ 40 * 895138 * 2
def baseEnd_895138 : Nat := 45396152701671506386009

theorem tailTrace_895138 : CollatzResearch.WordTrace tailWord_895138 prefixEnd_895138 45396152701671506386009 := by
  unfold tailWord_895138
  simp only [CollatzResearch.WordTrace]
  refine ⟨8162091257768844561079517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21765576687383585496212045 8162091257768844561079517)
  ·
    refine ⟨3060784221663316710404819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8162091257768844561079517 3060784221663316710404819)
    ·
      refine ⟨4591176332494975065607229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3060784221663316710404819 4591176332494975065607229)
      ·
        refine ⟨1721691124685615649602711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4591176332494975065607229 1721691124685615649602711)
        ·
          refine ⟨2582536687028423474404067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1721691124685615649602711 2582536687028423474404067)
          ·
            refine ⟨3873805030542635211606101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2582536687028423474404067 3873805030542635211606101)
            ·
              refine ⟨45396152701671506386009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3873805030542635211606101 45396152701671506386009)
              ·
                rfl

theorem cell20_895138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 8].length) (baseStart_895138 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_895138 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_895138 prefixEnd_895138 := by exact prefixLift 895138
  have htrace : WordTrace (prefixWord ++ tailWord_895138) baseStart_895138 baseEnd_895138 := by
    simpa [prefixWord, tailWord_895138, baseEnd_895138] using wordTrace_append hprefix tailTrace_895138
  have hstable : (prefixWord ++ tailWord_895138).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895138).length < 2 ^ (prefixWord ++ tailWord_895138).sum := by decide
  have hdescent : baseEnd_895138 < baseStart_895138 := by decide
  rcases family_descends (prefixWord ++ tailWord_895138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895159 : List Nat := [1, 1, 3, 1, 4, 2, 1, 7]
def baseStart_895159 : Nat := 118140960795 + 895159 * 2 ^ 59
def prefixEnd_895159 : Nat := 4983230072969 + 3 ^ 40 * 895159 * 2
def baseEnd_895159 : Nat := 136191653095753605924665

theorem tailTrace_895159 : CollatzResearch.WordTrace tailWord_895159 prefixEnd_895159 136191653095753605924665 := by
  unfold tailWord_895159
  simp only [CollatzResearch.WordTrace]
  refine ⟨32649130963999298830832531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21766087309332865887221687 32649130963999298830832531)
  ·
    refine ⟨48973696445998948246248797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32649130963999298830832531 48973696445998948246248797)
    ·
      refine ⟨18365136167249605592343299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48973696445998948246248797 18365136167249605592343299)
      ·
        refine ⟨27547704250874408388514949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18365136167249605592343299 27547704250874408388514949)
        ·
          refine ⟨5165194547038951572846553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27547704250874408388514949 5165194547038951572846553)
          ·
            refine ⟨3873895910279213679634915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5165194547038951572846553 3873895910279213679634915)
            ·
              refine ⟨5810843865418820519452373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3873895910279213679634915 5810843865418820519452373)
              ·
                refine ⟨136191653095753605924665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5810843865418820519452373 136191653095753605924665)
                ·
                  rfl

theorem cell20_895159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 7].length) (baseStart_895159 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_895159 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_895159 prefixEnd_895159 := by exact prefixLift 895159
  have htrace : WordTrace (prefixWord ++ tailWord_895159) baseStart_895159 baseEnd_895159 := by
    simpa [prefixWord, tailWord_895159, baseEnd_895159] using wordTrace_append hprefix tailTrace_895159
  have hstable : (prefixWord ++ tailWord_895159).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895159).length < 2 ^ (prefixWord ++ tailWord_895159).sum := by decide
  have hdescent : baseEnd_895159 < baseStart_895159 := by decide
  rcases family_descends (prefixWord ++ tailWord_895159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895162 : List Nat := [3, 1, 1, 1, 2, 2, 6, 1, 3]
def baseStart_895162 : Nat := 118140960795 + 895162 * 2 ^ 59
def prefixEnd_895162 : Nat := 4983230072969 + 3 ^ 40 * 895162 * 2
def baseEnd_895162 : Nat := 408576328569006140673983

theorem tailTrace_895162 : CollatzResearch.WordTrace tailWord_895162 prefixEnd_895162 408576328569006140673983 := by
  unfold tailWord_895162
  simp only [CollatzResearch.WordTrace]
  refine ⟨8162310095747107585797935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21766160255325620228794493 8162310095747107585797935)
  ·
    refine ⟨12243465143620661378696903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8162310095747107585797935 12243465143620661378696903)
    ·
      refine ⟨18365197715430992068045355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12243465143620661378696903 18365197715430992068045355)
      ·
        refine ⟨27547796573146488102068033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18365197715430992068045355 27547796573146488102068033)
        ·
          refine ⟨20660847429859866076551025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27547796573146488102068033 20660847429859866076551025)
          ·
            refine ⟨15495635572394899557413269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20660847429859866076551025 15495635572394899557413269)
            ·
              refine ⟨726357917456010916753747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15495635572394899557413269 726357917456010916753747)
              ·
                refine ⟨1089536876184016375130621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 726357917456010916753747 1089536876184016375130621)
                ·
                  refine ⟨408576328569006140673983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1089536876184016375130621 408576328569006140673983)
                  ·
                    rfl

theorem cell20_895162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 6, 1, 3].length) (baseStart_895162 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_895162 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_895162 prefixEnd_895162 := by exact prefixLift 895162
  have htrace : WordTrace (prefixWord ++ tailWord_895162) baseStart_895162 baseEnd_895162 := by
    simpa [prefixWord, tailWord_895162, baseEnd_895162] using wordTrace_append hprefix tailTrace_895162
  have hstable : (prefixWord ++ tailWord_895162).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895162).length < 2 ^ (prefixWord ++ tailWord_895162).sum := by decide
  have hdescent : baseEnd_895162 < baseStart_895162 := by decide
  rcases family_descends (prefixWord ++ tailWord_895162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895196 : List Nat := [2, 2, 5, 2, 1, 1, 2, 2, 3]
def baseStart_895196 : Nat := 118140960795 + 895196 * 2 ^ 59
def prefixEnd_895196 : Nat := 4983230072969 + 3 ^ 40 * 895196 * 2
def baseEnd_895196 : Nat := 408591847095453133540511

theorem tailTrace_895196 : CollatzResearch.WordTrace tailWord_895196 prefixEnd_895196 408591847095453133540511 := by
  unfold tailWord_895196
  simp only [CollatzResearch.WordTrace]
  refine ⟨16325240232432627074964721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21766986976576836099952961 16325240232432627074964721)
  ·
    refine ⟨12243930174324470306223541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16325240232432627074964721 12243930174324470306223541)
    ·
      refine ⟨1147868453842919091208457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12243930174324470306223541 1147868453842919091208457)
      ·
        refine ⟨860901340382189318406343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1147868453842919091208457 860901340382189318406343)
        ·
          refine ⟨1291352010573283977609515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 860901340382189318406343 1291352010573283977609515)
          ·
            refine ⟨1937028015859925966414273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1291352010573283977609515 1937028015859925966414273)
            ·
              refine ⟨1452771011894944474810705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1937028015859925966414273 1452771011894944474810705)
              ·
                refine ⟨1089578258921208356108029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1452771011894944474810705 1089578258921208356108029)
                ·
                  refine ⟨408591847095453133540511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1089578258921208356108029 408591847095453133540511)
                  ·
                    rfl

theorem cell20_895196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 2, 3].length) (baseStart_895196 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_895196 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_895196 prefixEnd_895196 := by exact prefixLift 895196
  have htrace : WordTrace (prefixWord ++ tailWord_895196) baseStart_895196 baseEnd_895196 := by
    simpa [prefixWord, tailWord_895196, baseEnd_895196] using wordTrace_append hprefix tailTrace_895196
  have hstable : (prefixWord ++ tailWord_895196).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895196).length < 2 ^ (prefixWord ++ tailWord_895196).sum := by decide
  have hdescent : baseEnd_895196 < baseStart_895196 := by decide
  rcases family_descends (prefixWord ++ tailWord_895196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895203 : List Nat := [1, 1, 1, 8, 1, 1, 1, 4, 2]
def baseStart_895203 : Nat := 118140960795 + 895203 * 2 ^ 59
def prefixEnd_895203 : Nat := 4983230072969 + 3 ^ 40 * 895203 * 2
def baseEnd_895203 : Nat := 408595042086192220307149

theorem tailTrace_895203 : CollatzResearch.WordTrace tailWord_895203 prefixEnd_895203 408595042086192220307149 := by
  unfold tailWord_895203
  simp only [CollatzResearch.WordTrace]
  refine ⟨32650735775839894345434263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21767157183893262896956175 32650735775839894345434263)
  ·
    refine ⟨48976103663759841518151395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32650735775839894345434263 48976103663759841518151395)
    ·
      refine ⟨73464155495639762277227093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48976103663759841518151395 73464155495639762277227093)
      ·
        refine ⟨860908072214528464186255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 73464155495639762277227093 860908072214528464186255)
        ·
          refine ⟨1291362108321792696279383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 860908072214528464186255 1291362108321792696279383)
          ·
            refine ⟨1937043162482689044419075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1291362108321792696279383 1937043162482689044419075)
            ·
              refine ⟨2905564743724033566628613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1937043162482689044419075 2905564743724033566628613)
              ·
                refine ⟨544793389448256293742865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2905564743724033566628613 544793389448256293742865)
                ·
                  refine ⟨408595042086192220307149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 544793389448256293742865 408595042086192220307149)
                  ·
                    rfl

theorem cell20_895203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 4, 2].length) (baseStart_895203 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_895203 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_895203 prefixEnd_895203 := by exact prefixLift 895203
  have htrace : WordTrace (prefixWord ++ tailWord_895203) baseStart_895203 baseEnd_895203 := by
    simpa [prefixWord, tailWord_895203, baseEnd_895203] using wordTrace_append hprefix tailTrace_895203
  have hstable : (prefixWord ++ tailWord_895203).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895203).length < 2 ^ (prefixWord ++ tailWord_895203).sum := by decide
  have hdescent : baseEnd_895203 < baseStart_895203 := by decide
  rcases family_descends (prefixWord ++ tailWord_895203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895228 : List Nat := [2, 2, 2, 1, 4, 1, 1, 1, 6]
def baseStart_895228 : Nat := 118140960795 + 895228 * 2 ^ 59
def prefixEnd_895228 : Nat := 4983230072969 + 3 ^ 40 * 895228 * 2
def baseEnd_895228 : Nat := 408606452767403244473713

theorem tailTrace_895228 : CollatzResearch.WordTrace tailWord_895228 prefixEnd_895228 408606452767403244473713 := by
  unfold tailWord_895228
  simp only [CollatzResearch.WordTrace]
  refine ⟨16325823800374661807547169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21767765067166215743396225 16325823800374661807547169)
  ·
    refine ⟨12244367850280996355660377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16325823800374661807547169 12244367850280996355660377)
    ·
      refine ⟨9183275887710747266745283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12244367850280996355660377 9183275887710747266745283)
      ·
        refine ⟨13774913831566120900117925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9183275887710747266745283 13774913831566120900117925)
        ·
          refine ⟨2582796343418647668772111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13774913831566120900117925 2582796343418647668772111)
          ·
            refine ⟨3874194515127971503158167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2582796343418647668772111 3874194515127971503158167)
            ·
              refine ⟨5811291772691957254737251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3874194515127971503158167 5811291772691957254737251)
              ·
                refine ⟨8716937659037935882105877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5811291772691957254737251 8716937659037935882105877)
                ·
                  refine ⟨408606452767403244473713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8716937659037935882105877 408606452767403244473713)
                  ·
                    rfl

theorem cell20_895228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 6].length) (baseStart_895228 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_895228 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_895228 prefixEnd_895228 := by exact prefixLift 895228
  have htrace : WordTrace (prefixWord ++ tailWord_895228) baseStart_895228 baseEnd_895228 := by
    simpa [prefixWord, tailWord_895228, baseEnd_895228] using wordTrace_append hprefix tailTrace_895228
  have hstable : (prefixWord ++ tailWord_895228).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895228).length < 2 ^ (prefixWord ++ tailWord_895228).sum := by decide
  have hdescent : baseEnd_895228 < baseStart_895228 := by decide
  rcases family_descends (prefixWord ++ tailWord_895228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895259 : List Nat := [1, 1, 1, 1, 1, 1, 9, 2, 3]
def baseStart_895259 : Nat := 118140960795 + 895259 * 2 ^ 59
def prefixEnd_895259 : Nat := 4983230072969 + 3 ^ 40 * 895259 * 2
def baseEnd_895259 : Nat := 408620602012104914440253

theorem tailTrace_895259 : CollatzResearch.WordTrace tailWord_895259 prefixEnd_895259 408620602012104914440253 := by
  unfold tailWord_895259
  simp only [CollatzResearch.WordTrace]
  refine ⟨32652778263637015909472831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21768518842424677272981887 32652778263637015909472831)
  ·
    refine ⟨48979167395455523864209247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32652778263637015909472831 48979167395455523864209247)
    ·
      refine ⟨73468751093183285796313871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48979167395455523864209247 73468751093183285796313871)
      ·
        refine ⟨110203126639774928694470807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73468751093183285796313871 110203126639774928694470807)
        ·
          refine ⟨165304689959662393041706211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110203126639774928694470807 165304689959662393041706211)
          ·
            refine ⟨247957034939493589562559317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165304689959662393041706211 247957034939493589562559317)
            ·
              refine ⟨1452873251598595251343121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 247957034939493589562559317 1452873251598595251343121)
              ·
                refine ⟨1089654938698946438507341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1452873251598595251343121 1089654938698946438507341)
                ·
                  refine ⟨408620602012104914440253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1089654938698946438507341 408620602012104914440253)
                  ·
                    rfl

theorem cell20_895259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 2, 3].length) (baseStart_895259 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_895259 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_895259 prefixEnd_895259 := by exact prefixLift 895259
  have htrace : WordTrace (prefixWord ++ tailWord_895259) baseStart_895259 baseEnd_895259 := by
    simpa [prefixWord, tailWord_895259, baseEnd_895259] using wordTrace_append hprefix tailTrace_895259
  have hstable : (prefixWord ++ tailWord_895259).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895259).length < 2 ^ (prefixWord ++ tailWord_895259).sum := by decide
  have hdescent : baseEnd_895259 < baseStart_895259 := by decide
  rcases family_descends (prefixWord ++ tailWord_895259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895262 : List Nat := [4, 3, 2, 1, 1, 1, 1, 3, 4]
def baseStart_895262 : Nat := 118140960795 + 895262 * 2 ^ 59
def prefixEnd_895262 : Nat := 4983230072969 + 3 ^ 40 * 895262 * 2
def baseEnd_895262 : Nat := 408621971293850237340241

theorem tailTrace_895262 : CollatzResearch.WordTrace tailWord_895262 prefixEnd_895262 408621971293850237340241 := by
  unfold tailWord_895262
  simp only [CollatzResearch.WordTrace]
  refine ⟨4081610960328268427729005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21768591788417431614554693 4081610960328268427729005)
  ·
    refine ⟨1530604110123100660398377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4081610960328268427729005 1530604110123100660398377)
    ·
      refine ⟨1147953082592325495298783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1530604110123100660398377 1147953082592325495298783)
      ·
        refine ⟨1721929623888488242948175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1147953082592325495298783 1721929623888488242948175)
        ·
          refine ⟨2582894435832732364422263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1721929623888488242948175 2582894435832732364422263)
          ·
            refine ⟨3874341653749098546633395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2582894435832732364422263 3874341653749098546633395)
            ·
              refine ⟨5811512480623647819950093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3874341653749098546633395 5811512480623647819950093)
              ·
                refine ⟨2179317180233867932481285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5811512480623647819950093 2179317180233867932481285)
                ·
                  refine ⟨408621971293850237340241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2179317180233867932481285 408621971293850237340241)
                  ·
                    rfl

theorem cell20_895262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_895262 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_895262 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_895262 prefixEnd_895262 := by exact prefixLift 895262
  have htrace : WordTrace (prefixWord ++ tailWord_895262) baseStart_895262 baseEnd_895262 := by
    simpa [prefixWord, tailWord_895262, baseEnd_895262] using wordTrace_append hprefix tailTrace_895262
  have hstable : (prefixWord ++ tailWord_895262).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895262).length < 2 ^ (prefixWord ++ tailWord_895262).sum := by decide
  have hdescent : baseEnd_895262 < baseStart_895262 := by decide
  rcases family_descends (prefixWord ++ tailWord_895262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895290 : List Nat := [3, 1, 1, 1, 4, 2, 4, 4]
def baseStart_895290 : Nat := 118140960795 + 895290 * 2 ^ 59
def prefixEnd_895290 : Nat := 4983230072969 + 3 ^ 40 * 895290 * 2
def baseEnd_895290 : Nat := 136211583752268861468931

theorem tailTrace_895290 : CollatzResearch.WordTrace tailWord_895290 prefixEnd_895290 136211583752268861468931 := by
  unfold tailWord_895290
  simp only [CollatzResearch.WordTrace]
  refine ⟨8163477231631177050962831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21769272617683138802567549 8163477231631177050962831)
  ·
    refine ⟨12245215847446765576444247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8163477231631177050962831 12245215847446765576444247)
    ·
      refine ⟨18367823771170148364666371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12245215847446765576444247 18367823771170148364666371)
      ·
        refine ⟨27551735656755222546999557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18367823771170148364666371 27551735656755222546999557)
        ·
          refine ⟨5165950435641604227562417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27551735656755222546999557 5165950435641604227562417)
          ·
            refine ⟨3874462826731203170671813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5165950435641604227562417 3874462826731203170671813)
            ·
              refine ⟨726461780012100594500965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3874462826731203170671813 726461780012100594500965)
              ·
                refine ⟨136211583752268861468931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 726461780012100594500965 136211583752268861468931)
                ·
                  rfl

theorem cell20_895290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 4, 4].length) (baseStart_895290 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_895290 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_895290 prefixEnd_895290 := by exact prefixLift 895290
  have htrace : WordTrace (prefixWord ++ tailWord_895290) baseStart_895290 baseEnd_895290 := by
    simpa [prefixWord, tailWord_895290, baseEnd_895290] using wordTrace_append hprefix tailTrace_895290
  have hstable : (prefixWord ++ tailWord_895290).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895290).length < 2 ^ (prefixWord ++ tailWord_895290).sum := by decide
  have hdescent : baseEnd_895290 < baseStart_895290 := by decide
  rcases family_descends (prefixWord ++ tailWord_895290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895317 : List Nat := [1, 3, 2, 2, 4, 1, 3, 2, 2]
def baseStart_895317 : Nat := 118140960795 + 895317 * 2 ^ 59
def prefixEnd_895317 : Nat := 4983230072969 + 3 ^ 40 * 895317 * 2
def baseEnd_895317 : Nat := 408647074792514490506683

theorem tailTrace_895317 : CollatzResearch.WordTrace tailWord_895317 prefixEnd_895317 408647074792514490506683 := by
  unfold tailWord_895317
  simp only [CollatzResearch.WordTrace]
  refine ⟨32654893697426891815084205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21769929131617927876722803 32654893697426891815084205)
  ·
    refine ⟨12245585136535084430656577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32654893697426891815084205 12245585136535084430656577)
    ·
      refine ⟨9184188852401313322992433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12245585136535084430656577 9184188852401313322992433)
      ·
        refine ⟨6888141639300984992244325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9184188852401313322992433 6888141639300984992244325)
        ·
          refine ⟨1291526557368934686045811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6888141639300984992244325 1291526557368934686045811)
          ·
            refine ⟨1937289836053402029068717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1291526557368934686045811 1937289836053402029068717)
            ·
              refine ⟨726483688520025760900769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1937289836053402029068717 726483688520025760900769)
              ·
                refine ⟨544862766390019320675577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 726483688520025760900769 544862766390019320675577)
                ·
                  refine ⟨408647074792514490506683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 544862766390019320675577 408647074792514490506683)
                  ·
                    rfl

theorem cell20_895317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 3, 2, 2].length) (baseStart_895317 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_895317 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_895317 prefixEnd_895317 := by exact prefixLift 895317
  have htrace : WordTrace (prefixWord ++ tailWord_895317) baseStart_895317 baseEnd_895317 := by
    simpa [prefixWord, tailWord_895317, baseEnd_895317] using wordTrace_append hprefix tailTrace_895317
  have hstable : (prefixWord ++ tailWord_895317).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895317).length < 2 ^ (prefixWord ++ tailWord_895317).sum := by decide
  have hdescent : baseEnd_895317 < baseStart_895317 := by decide
  rcases family_descends (prefixWord ++ tailWord_895317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895328 : List Nat := [2, 1, 1, 3, 5, 1, 2, 5]
def baseStart_895328 : Nat := 118140960795 + 895328 * 2 ^ 59
def prefixEnd_895328 : Nat := 4983230072969 + 3 ^ 40 * 895328 * 2
def baseEnd_895328 : Nat := 136217365164082447046657

theorem tailTrace_895328 : CollatzResearch.WordTrace tailWord_895328 prefixEnd_895328 136217365164082447046657 := by
  unfold tailWord_895328
  simp only [CollatzResearch.WordTrace]
  refine ⟨16327647450193520346867319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21770196600258027129156425 16327647450193520346867319)
  ·
    refine ⟨24491471175290280520300979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16327647450193520346867319 24491471175290280520300979)
    ·
      refine ⟨36737206762935420780451469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24491471175290280520300979 36737206762935420780451469)
      ·
        refine ⟨13776452536100782792669301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36737206762935420780451469 13776452536100782792669301)
        ·
          refine ⟨1291542425259448386812747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13776452536100782792669301 1291542425259448386812747)
          ·
            refine ⟨1937313637889172580219121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1291542425259448386812747 1937313637889172580219121)
            ·
              refine ⟨1452985228416879435164341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1937313637889172580219121 1452985228416879435164341)
              ·
                refine ⟨136217365164082447046657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1452985228416879435164341 136217365164082447046657)
                ·
                  rfl

theorem cell20_895328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 5].length) (baseStart_895328 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_895328 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_895328 prefixEnd_895328 := by exact prefixLift 895328
  have htrace : WordTrace (prefixWord ++ tailWord_895328) baseStart_895328 baseEnd_895328 := by
    simpa [prefixWord, tailWord_895328, baseEnd_895328] using wordTrace_append hprefix tailTrace_895328
  have hstable : (prefixWord ++ tailWord_895328).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895328).length < 2 ^ (prefixWord ++ tailWord_895328).sum := by decide
  have hdescent : baseEnd_895328 < baseStart_895328 := by decide
  rcases family_descends (prefixWord ++ tailWord_895328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895356 : List Nat := [2, 2, 2, 1, 1, 1, 2, 4, 5]
def baseStart_895356 : Nat := 118140960795 + 895356 * 2 ^ 59
def prefixEnd_895356 : Nat := 4983230072969 + 3 ^ 40 * 895356 * 2
def baseEnd_895356 : Nat := 408664875455203688206523

theorem tailTrace_895356 : CollatzResearch.WordTrace tailWord_895356 prefixEnd_895356 408664875455203688206523 := by
  unfold tailWord_895356
  simp only [CollatzResearch.WordTrace]
  refine ⟨16328158072142800737876961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21770877429523734317169281 16328158072142800737876961)
  ·
    refine ⟨12246118554107100553407721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16328158072142800737876961 12246118554107100553407721)
    ·
      refine ⟨9184588915580325415055791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12246118554107100553407721 9184588915580325415055791)
      ·
        refine ⟨13776883373370488122583687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9184588915580325415055791 13776883373370488122583687)
        ·
          refine ⟨20665325060055732183875531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13776883373370488122583687 20665325060055732183875531)
          ·
            refine ⟨30997987590083598275813297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20665325060055732183875531 30997987590083598275813297)
            ·
              refine ⟨23248490692562698706859973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30997987590083598275813297 23248490692562698706859973)
              ·
                refine ⟨4359092004855506007536245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23248490692562698706859973 4359092004855506007536245)
                ·
                  refine ⟨408664875455203688206523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4359092004855506007536245 408664875455203688206523)
                  ·
                    rfl

theorem cell20_895356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 4, 5].length) (baseStart_895356 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_895356 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_895356 prefixEnd_895356 := by exact prefixLift 895356
  have htrace : WordTrace (prefixWord ++ tailWord_895356) baseStart_895356 baseEnd_895356 := by
    simpa [prefixWord, tailWord_895356, baseEnd_895356] using wordTrace_append hprefix tailTrace_895356
  have hstable : (prefixWord ++ tailWord_895356).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895356).length < 2 ^ (prefixWord ++ tailWord_895356).sum := by decide
  have hdescent : baseEnd_895356 < baseStart_895356 := by decide
  rcases family_descends (prefixWord ++ tailWord_895356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895428 : List Nat := [2, 3, 3, 2, 2, 1, 1, 1, 5]
def baseStart_895428 : Nat := 118140960795 + 895428 * 2 ^ 59
def prefixEnd_895428 : Nat := 4983230072969 + 3 ^ 40 * 895428 * 2
def baseEnd_895428 : Nat := 408697738217091437806229

theorem tailTrace_895428 : CollatzResearch.WordTrace tailWord_895428 prefixEnd_895428 408697738217091437806229 := by
  unfold tailWord_895428
  simp only [CollatzResearch.WordTrace]
  refine ⟨16329471100012378886187469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21772628133349838514916625 16329471100012378886187469)
  ·
    refine ⟨6123551662504642082320301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16329471100012378886187469 6123551662504642082320301)
    ·
      refine ⟨2296331873439240780870113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6123551662504642082320301 2296331873439240780870113)
      ·
        refine ⟨1722248905079430585652585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2296331873439240780870113 1722248905079430585652585)
        ·
          refine ⟨1291686678809572939239439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1722248905079430585652585 1291686678809572939239439)
          ·
            refine ⟨1937530018214359408859159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1291686678809572939239439 1937530018214359408859159)
            ·
              refine ⟨2906295027321539113288739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1937530018214359408859159 2906295027321539113288739)
              ·
                refine ⟨4359442540982308669933109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2906295027321539113288739 4359442540982308669933109)
                ·
                  refine ⟨408697738217091437806229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4359442540982308669933109 408697738217091437806229)
                  ·
                    rfl

theorem cell20_895428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 1, 5].length) (baseStart_895428 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_895428 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_895428 prefixEnd_895428 := by exact prefixLift 895428
  have htrace : WordTrace (prefixWord ++ tailWord_895428) baseStart_895428 baseEnd_895428 := by
    simpa [prefixWord, tailWord_895428, baseEnd_895428] using wordTrace_append hprefix tailTrace_895428
  have hstable : (prefixWord ++ tailWord_895428).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895428).length < 2 ^ (prefixWord ++ tailWord_895428).sum := by decide
  have hdescent : baseEnd_895428 < baseStart_895428 := by decide
  rcases family_descends (prefixWord ++ tailWord_895428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895459 : List Nat := [1, 1, 1, 6, 3, 2, 2, 4]
def baseStart_895459 : Nat := 118140960795 + 895459 * 2 ^ 59
def prefixEnd_895459 : Nat := 4983230072969 + 3 ^ 40 * 895459 * 2
def baseEnd_895459 : Nat := 136237295820597702590923

theorem tailTrace_895459 : CollatzResearch.WordTrace tailWord_895459 prefixEnd_895459 136237295820597702590923 := by
  unfold tailWord_895459
  simp only [CollatzResearch.WordTrace]
  refine ⟨32660072862912450066753431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21773381908608300044502287 32660072862912450066753431)
  ·
    refine ⟨48990109294368675100130147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32660072862912450066753431 48990109294368675100130147)
    ·
      refine ⟨73485163941553012650195221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48990109294368675100130147 73485163941553012650195221)
      ·
        refine ⟨3444617059760297467977901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 73485163941553012650195221 3444617059760297467977901)
        ·
          refine ⟨1291731397410111550491713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3444617059760297467977901 1291731397410111550491713)
          ·
            refine ⟨968798548057583662868785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1291731397410111550491713 968798548057583662868785)
            ·
              refine ⟨726598911043187747151589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 968798548057583662868785 726598911043187747151589)
              ·
                refine ⟨136237295820597702590923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 726598911043187747151589 136237295820597702590923)
                ·
                  rfl

theorem cell20_895459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 2, 4].length) (baseStart_895459 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_895459 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_895459 prefixEnd_895459 := by exact prefixLift 895459
  have htrace : WordTrace (prefixWord ++ tailWord_895459) baseStart_895459 baseEnd_895459 := by
    simpa [prefixWord, tailWord_895459, baseEnd_895459] using wordTrace_append hprefix tailTrace_895459
  have hstable : (prefixWord ++ tailWord_895459).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895459).length < 2 ^ (prefixWord ++ tailWord_895459).sum := by decide
  have hdescent : baseEnd_895459 < baseStart_895459 := by decide
  rcases family_descends (prefixWord ++ tailWord_895459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895463 : List Nat := [1, 1, 5, 2, 1, 1, 3, 6]
def baseStart_895463 : Nat := 118140960795 + 895463 * 2 ^ 59
def prefixEnd_895463 : Nat := 4983230072969 + 3 ^ 40 * 895463 * 2
def baseEnd_895463 : Nat := 136237904390262290546473

theorem tailTrace_895463 : CollatzResearch.WordTrace tailWord_895463 prefixEnd_895463 136237904390262290546473 := by
  unfold tailWord_895463
  simp only [CollatzResearch.WordTrace]
  refine ⟨32660218754897958749899043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21773479169931972499932695 32660218754897958749899043)
  ·
    refine ⟨48990328132346938124848565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32660218754897958749899043 48990328132346938124848565)
    ·
      refine ⟨4592843262407525449204553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48990328132346938124848565 4592843262407525449204553)
      ·
        refine ⟨3444632446805644086903415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4592843262407525449204553 3444632446805644086903415)
        ·
          refine ⟨5166948670208466130355123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3444632446805644086903415 5166948670208466130355123)
          ·
            refine ⟨7750423005312699195532685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5166948670208466130355123 7750423005312699195532685)
            ·
              refine ⟨2906408626992262198324757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7750423005312699195532685 2906408626992262198324757)
              ·
                refine ⟨136237904390262290546473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2906408626992262198324757 136237904390262290546473)
                ·
                  rfl

theorem cell20_895463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 6].length) (baseStart_895463 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_895463 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_895463 prefixEnd_895463 := by exact prefixLift 895463
  have htrace : WordTrace (prefixWord ++ tailWord_895463) baseStart_895463 baseEnd_895463 := by
    simpa [prefixWord, tailWord_895463, baseEnd_895463] using wordTrace_append hprefix tailTrace_895463
  have hstable : (prefixWord ++ tailWord_895463).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895463).length < 2 ^ (prefixWord ++ tailWord_895463).sum := by decide
  have hdescent : baseEnd_895463 < baseStart_895463 := by decide
  rcases family_descends (prefixWord ++ tailWord_895463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895469 : List Nat := [1, 5, 1, 3, 1, 3, 1, 3, 2]
def baseStart_895469 : Nat := 118140960795 + 895469 * 2 ^ 59
def prefixEnd_895469 : Nat := 4983230072969 + 3 ^ 40 * 895469 * 2
def baseEnd_895469 : Nat := 408716451734277517439395

theorem tailTrace_895469 : CollatzResearch.WordTrace tailWord_895469 prefixEnd_895469 408716451734277517439395 := by
  unfold tailWord_895469
  simp only [CollatzResearch.WordTrace]
  refine ⟨32660437592876221774617461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21773625061917481183078307 32660437592876221774617461)
  ·
    refine ⟨3061916024332145791370387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32660437592876221774617461 3061916024332145791370387)
    ·
      refine ⟨4592874036498218687055581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3061916024332145791370387 4592874036498218687055581)
      ·
        refine ⟨1722327763686832007645843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4592874036498218687055581 1722327763686832007645843)
        ·
          refine ⟨2583491645530248011468765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1722327763686832007645843 2583491645530248011468765)
          ·
            refine ⟨968809367073843004300787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2583491645530248011468765 968809367073843004300787)
            ·
              refine ⟨1453214050610764506451181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 968809367073843004300787 1453214050610764506451181)
              ·
                refine ⟨544955268979036689919193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1453214050610764506451181 544955268979036689919193)
                ·
                  refine ⟨408716451734277517439395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 544955268979036689919193 408716451734277517439395)
                  ·
                    rfl

theorem cell20_895469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 3, 2].length) (baseStart_895469 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_895469 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_895469 prefixEnd_895469 := by exact prefixLift 895469
  have htrace : WordTrace (prefixWord ++ tailWord_895469) baseStart_895469 baseEnd_895469 := by
    simpa [prefixWord, tailWord_895469, baseEnd_895469] using wordTrace_append hprefix tailTrace_895469
  have hstable : (prefixWord ++ tailWord_895469).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895469).length < 2 ^ (prefixWord ++ tailWord_895469).sum := by decide
  have hdescent : baseEnd_895469 < baseStart_895469 := by decide
  rcases family_descends (prefixWord ++ tailWord_895469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895542 : List Nat := [5, 1, 2, 1, 2, 1, 1, 4, 3]
def baseStart_895542 : Nat := 118140960795 + 895542 * 2 ^ 59
def prefixEnd_895542 : Nat := 4983230072969 + 3 ^ 40 * 895542 * 2
def baseEnd_895542 : Nat := 408749770923413708005763

theorem tailTrace_895542 : CollatzResearch.WordTrace tailWord_895542 prefixEnd_895542 408749770923413708005763 := by
  unfold tailWord_895542
  simp only [CollatzResearch.WordTrace]
  refine ⟨2041443757600734702626555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21775400081074503494683253 2041443757600734702626555)
  ·
    refine ⟨3062165636401102053939833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2041443757600734702626555 3062165636401102053939833)
    ·
      refine ⟨2296624227300826540454875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3062165636401102053939833 2296624227300826540454875)
      ·
        refine ⟨3444936340951239810682313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2296624227300826540454875 3444936340951239810682313)
        ·
          refine ⟨2583702255713429858011735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3444936340951239810682313 2583702255713429858011735)
          ·
            refine ⟨3875553383570144787017603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2583702255713429858011735 3875553383570144787017603)
            ·
              refine ⟨5813330075355217180526405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3875553383570144787017603 5813330075355217180526405)
              ·
                refine ⟨1089999389129103221348701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5813330075355217180526405 1089999389129103221348701)
                ·
                  refine ⟨408749770923413708005763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1089999389129103221348701 408749770923413708005763)
                  ·
                    rfl

theorem cell20_895542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_895542 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_895542 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_895542 prefixEnd_895542 := by exact prefixLift 895542
  have htrace : WordTrace (prefixWord ++ tailWord_895542) baseStart_895542 baseEnd_895542 := by
    simpa [prefixWord, tailWord_895542, baseEnd_895542] using wordTrace_append hprefix tailTrace_895542
  have hstable : (prefixWord ++ tailWord_895542).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895542).length < 2 ^ (prefixWord ++ tailWord_895542).sum := by decide
  have hdescent : baseEnd_895542 < baseStart_895542 := by decide
  rcases family_descends (prefixWord ++ tailWord_895542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895570 : List Nat := [3, 2, 2, 1, 2, 1, 3, 2, 4]
def baseStart_895570 : Nat := 118140960795 + 895570 * 2 ^ 59
def prefixEnd_895570 : Nat := 4983230072969 + 3 ^ 40 * 895570 * 2
def baseEnd_895570 : Nat := 408762550886370055072315

theorem tailTrace_895570 : CollatzResearch.WordTrace tailWord_895570 prefixEnd_895570 408762550886370055072315 := by
  unfold tailWord_895570
  simp only [CollatzResearch.WordTrace]
  refine ⟨8166030341377579006011041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21776080910340210682696109 8166030341377579006011041)
  ·
    refine ⟨6124522756033184254508281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8166030341377579006011041 6124522756033184254508281)
    ·
      refine ⟨4593392067024888190881211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6124522756033184254508281 4593392067024888190881211)
      ·
        refine ⟨6890088100537332286321817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4593392067024888190881211 6890088100537332286321817)
        ·
          refine ⟨5167566075402999214741363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6890088100537332286321817 5167566075402999214741363)
          ·
            refine ⟨7751349113104498822112045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5167566075402999214741363 7751349113104498822112045)
            ·
              refine ⟨2906755917414187058292017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7751349113104498822112045 2906755917414187058292017)
              ·
                refine ⟨2180066938060640293719013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2906755917414187058292017 2180066938060640293719013)
                ·
                  refine ⟨408762550886370055072315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2180066938060640293719013 408762550886370055072315)
                  ·
                    rfl

theorem cell20_895570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_895570 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_895570 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_895570 prefixEnd_895570 := by exact prefixLift 895570
  have htrace : WordTrace (prefixWord ++ tailWord_895570) baseStart_895570 baseEnd_895570 := by
    simpa [prefixWord, tailWord_895570, baseEnd_895570] using wordTrace_append hprefix tailTrace_895570
  have hstable : (prefixWord ++ tailWord_895570).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895570).length < 2 ^ (prefixWord ++ tailWord_895570).sum := by decide
  have hdescent : baseEnd_895570 < baseStart_895570 := by decide
  rcases family_descends (prefixWord ++ tailWord_895570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895587 : List Nat := [1, 1, 1, 5, 1, 2, 4, 3, 2]
def baseStart_895587 : Nat := 118140960795 + 895587 * 2 ^ 59
def prefixEnd_895587 : Nat := 4983230072969 + 3 ^ 40 * 895587 * 2
def baseEnd_895587 : Nat := 408770310149593551505579

theorem tailTrace_895587 : CollatzResearch.WordTrace tailWord_895587 prefixEnd_895587 408770310149593551505579 := by
  unfold tailWord_895587
  simp only [CollatzResearch.WordTrace]
  refine ⟨32664741406448727927413015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21776494270965818618275343 32664741406448727927413015)
  ·
    refine ⟨48997112109673091891119523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32664741406448727927413015 48997112109673091891119523)
    ·
      refine ⟨73495668164509637836679285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48997112109673091891119523 73495668164509637836679285)
      ·
        refine ⟨6890218890422778547188683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73495668164509637836679285 6890218890422778547188683)
        ·
          refine ⟨10335328335634167820783025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6890218890422778547188683 10335328335634167820783025)
          ·
            refine ⟨7751496251725625865587269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10335328335634167820783025 7751496251725625865587269)
            ·
              refine ⟨1453405547198554849797613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7751496251725625865587269 1453405547198554849797613)
              ·
                refine ⟨545027080199458068674105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1453405547198554849797613 545027080199458068674105)
                ·
                  refine ⟨408770310149593551505579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 545027080199458068674105 408770310149593551505579)
                  ·
                    rfl

theorem cell20_895587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 3, 2].length) (baseStart_895587 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_895587 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_895587 prefixEnd_895587 := by exact prefixLift 895587
  have htrace : WordTrace (prefixWord ++ tailWord_895587) baseStart_895587 baseEnd_895587 := by
    simpa [prefixWord, tailWord_895587, baseEnd_895587] using wordTrace_append hprefix tailTrace_895587
  have hstable : (prefixWord ++ tailWord_895587).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895587).length < 2 ^ (prefixWord ++ tailWord_895587).sum := by decide
  have hdescent : baseEnd_895587 < baseStart_895587 := by decide
  rcases family_descends (prefixWord ++ tailWord_895587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895591 : List Nat := [1, 1, 5, 1, 1, 1, 1, 1, 8]
def baseStart_895591 : Nat := 118140960795 + 895591 * 2 ^ 59
def prefixEnd_895591 : Nat := 4983230072969 + 3 ^ 40 * 895591 * 2
def baseEnd_895591 : Nat := 408772135858587315372229

theorem tailTrace_895591 : CollatzResearch.WordTrace tailWord_895591 prefixEnd_895591 408772135858587315372229 := by
  unfold tailWord_895591
  simp only [CollatzResearch.WordTrace]
  refine ⟨32664887298434236610558627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21776591532289491073705751 32664887298434236610558627)
  ·
    refine ⟨48997330947651354915837941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32664887298434236610558627 48997330947651354915837941)
    ·
      refine ⟨4593499776342314523359807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48997330947651354915837941 4593499776342314523359807)
      ·
        refine ⟨6890249664513471785039711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4593499776342314523359807 6890249664513471785039711)
        ·
          refine ⟨10335374496770207677559567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6890249664513471785039711 10335374496770207677559567)
          ·
            refine ⟨15503061745155311516339351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10335374496770207677559567 15503061745155311516339351)
            ·
              refine ⟨23254592617732967274509027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15503061745155311516339351 23254592617732967274509027)
              ·
                refine ⟨34881888926599450911763541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23254592617732967274509027 34881888926599450911763541)
                ·
                  refine ⟨408772135858587315372229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34881888926599450911763541 408772135858587315372229)
                  ·
                    rfl

theorem cell20_895591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 8].length) (baseStart_895591 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_895591 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_895591 prefixEnd_895591 := by exact prefixLift 895591
  have htrace : WordTrace (prefixWord ++ tailWord_895591) baseStart_895591 baseEnd_895591 := by
    simpa [prefixWord, tailWord_895591, baseEnd_895591] using wordTrace_append hprefix tailTrace_895591
  have hstable : (prefixWord ++ tailWord_895591).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895591).length < 2 ^ (prefixWord ++ tailWord_895591).sum := by decide
  have hdescent : baseEnd_895591 < baseStart_895591 := by decide
  rcases family_descends (prefixWord ++ tailWord_895591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895677 : List Nat := [1, 4, 1, 2, 1, 4, 1, 3, 3]
def baseStart_895677 : Nat := 118140960795 + 895677 * 2 ^ 59
def prefixEnd_895677 : Nat := 4983230072969 + 3 ^ 40 * 895677 * 2
def baseEnd_895677 : Nat := 408811388601953238505211

theorem tailTrace_895677 : CollatzResearch.WordTrace tailWord_895677 prefixEnd_895677 408811388601953238505211 := by
  unfold tailWord_895677
  simp only [CollatzResearch.WordTrace]
  refine ⟨32668023976122673298189285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21778682650748448865459523 32668023976122673298189285)
  ·
    refine ⟨6125254495523001243410491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32668023976122673298189285 6125254495523001243410491)
    ·
      refine ⟨9187881743284501865115737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6125254495523001243410491 9187881743284501865115737)
      ·
        refine ⟨6890911307463376398836803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9187881743284501865115737 6890911307463376398836803)
        ·
          refine ⟨10336366961195064598255205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6890911307463376398836803 10336366961195064598255205)
          ·
            refine ⟨1938068805224074612172851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10336366961195064598255205 1938068805224074612172851)
            ·
              refine ⟨2907103207836111918259277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1938068805224074612172851 2907103207836111918259277)
              ·
                refine ⟨1090163702938541969347229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2907103207836111918259277 1090163702938541969347229)
                ·
                  refine ⟨408811388601953238505211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1090163702938541969347229 408811388601953238505211)
                  ·
                    rfl

theorem cell20_895677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 3, 3].length) (baseStart_895677 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_895677 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_895677 prefixEnd_895677 := by exact prefixLift 895677
  have htrace : WordTrace (prefixWord ++ tailWord_895677) baseStart_895677 baseEnd_895677 := by
    simpa [prefixWord, tailWord_895677, baseEnd_895677] using wordTrace_append hprefix tailTrace_895677
  have hstable : (prefixWord ++ tailWord_895677).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895677).length < 2 ^ (prefixWord ++ tailWord_895677).sum := by decide
  have hdescent : baseEnd_895677 < baseStart_895677 := by decide
  rcases family_descends (prefixWord ++ tailWord_895677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895715 : List Nat := [1, 1, 1, 7, 1, 1, 1, 4, 3]
def baseStart_895715 : Nat := 118140960795 + 895715 * 2 ^ 59
def prefixEnd_895715 : Nat := 4983230072969 + 3 ^ 40 * 895715 * 2
def baseEnd_895715 : Nat := 408828732837393995238389

theorem tailTrace_895715 : CollatzResearch.WordTrace tailWord_895715 prefixEnd_895715 408828732837393995238389 := by
  unfold tailWord_895715
  simp only [CollatzResearch.WordTrace]
  refine ⟨32669409949985005788072599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21779606633323337192048399 32669409949985005788072599)
  ·
    refine ⟨49004114924977508682108899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32669409949985005788072599 49004114924977508682108899)
    ·
      refine ⟨73506172387466263023163349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49004114924977508682108899 73506172387466263023163349)
      ·
        refine ⟨1722800915331240539605391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 73506172387466263023163349 1722800915331240539605391)
        ·
          refine ⟨2584201372996860809408087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1722800915331240539605391 2584201372996860809408087)
          ·
            refine ⟨3876302059495291214112131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2584201372996860809408087 3876302059495291214112131)
            ·
              refine ⟨5814453089242936821168197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3876302059495291214112131 5814453089242936821168197)
              ·
                refine ⟨1090209954233050653969037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5814453089242936821168197 1090209954233050653969037)
                ·
                  refine ⟨408828732837393995238389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1090209954233050653969037 408828732837393995238389)
                  ·
                    rfl

theorem cell20_895715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 4, 3].length) (baseStart_895715 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_895715 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_895715 prefixEnd_895715 := by exact prefixLift 895715
  have htrace : WordTrace (prefixWord ++ tailWord_895715) baseStart_895715 baseEnd_895715 := by
    simpa [prefixWord, tailWord_895715, baseEnd_895715] using wordTrace_append hprefix tailTrace_895715
  have hstable : (prefixWord ++ tailWord_895715).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895715).length < 2 ^ (prefixWord ++ tailWord_895715).sum := by decide
  have hdescent : baseEnd_895715 < baseStart_895715 := by decide
  rcases family_descends (prefixWord ++ tailWord_895715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895736 : List Nat := [2, 1, 2, 1, 1, 2, 3, 5, 3]
def baseStart_895736 : Nat := 118140960795 + 895736 * 2 ^ 59
def prefixEnd_895736 : Nat := 4983230072969 + 3 ^ 40 * 895736 * 2
def baseEnd_895736 : Nat := 408838317809611255538303

theorem tailTrace_895736 : CollatzResearch.WordTrace tailWord_895736 prefixEnd_895736 408838317809611255538303 := by
  unfold tailWord_895736
  simp only [CollatzResearch.WordTrace]
  refine ⟨16335087941454463187293531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21780117255272617583058041 16335087941454463187293531)
  ·
    refine ⟨24502631912181694780940297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16335087941454463187293531 24502631912181694780940297)
    ·
      refine ⟨18376973934136271085705223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24502631912181694780940297 18376973934136271085705223)
      ·
        refine ⟨27565460901204406628557835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18376973934136271085705223 27565460901204406628557835)
        ·
          refine ⟨41348191351806609942836753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27565460901204406628557835 41348191351806609942836753)
          ·
            refine ⟨31011143513854957457127565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41348191351806609942836753 31011143513854957457127565)
            ·
              refine ⟨11629178817695609046422837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31011143513854957457127565 11629178817695609046422837)
              ·
                refine ⟨1090235514158963348102141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11629178817695609046422837 1090235514158963348102141)
                ·
                  refine ⟨408838317809611255538303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1090235514158963348102141 408838317809611255538303)
                  ·
                    rfl

theorem cell20_895736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 5, 3].length) (baseStart_895736 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_895736 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_895736 prefixEnd_895736 := by exact prefixLift 895736
  have htrace : WordTrace (prefixWord ++ tailWord_895736) baseStart_895736 baseEnd_895736 := by
    simpa [prefixWord, tailWord_895736, baseEnd_895736] using wordTrace_append hprefix tailTrace_895736
  have hstable : (prefixWord ++ tailWord_895736).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895736).length < 2 ^ (prefixWord ++ tailWord_895736).sum := by decide
  have hdescent : baseEnd_895736 < baseStart_895736 := by decide
  rcases family_descends (prefixWord ++ tailWord_895736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895767 : List Nat := [1, 1, 3, 4, 3, 1, 7]
def baseStart_895767 : Nat := 118140960795 + 895767 * 2 ^ 59
def prefixEnd_895767 : Nat := 4983230072969 + 3 ^ 40 * 895767 * 2
def baseEnd_895767 : Nat := 45428051894923658389427

theorem tailTrace_895767 : CollatzResearch.WordTrace tailWord_895767 prefixEnd_895767 45428051894923658389427 := by
  unfold tailWord_895767
  simp only [CollatzResearch.WordTrace]
  refine ⟨32671306545796618668965555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21780871030531079112643703 32671306545796618668965555)
  ·
    refine ⟨49006959818694928003448333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32671306545796618668965555 49006959818694928003448333)
    ·
      refine ⟨18377609932010598001293125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49006959818694928003448333 18377609932010598001293125)
      ·
        refine ⟨3445801862251987125242461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18377609932010598001293125 3445801862251987125242461)
        ·
          refine ⟨1292175698344495171965923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3445801862251987125242461 1292175698344495171965923)
          ·
            refine ⟨1938263547516742757948885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1292175698344495171965923 1938263547516742757948885)
            ·
              refine ⟨45428051894923658389427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1938263547516742757948885 45428051894923658389427)
              ·
                rfl

theorem cell20_895767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 7].length) (baseStart_895767 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_895767 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_895767 prefixEnd_895767 := by exact prefixLift 895767
  have htrace : WordTrace (prefixWord ++ tailWord_895767) baseStart_895767 baseEnd_895767 := by
    simpa [prefixWord, tailWord_895767, baseEnd_895767] using wordTrace_append hprefix tailTrace_895767
  have hstable : (prefixWord ++ tailWord_895767).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895767).length < 2 ^ (prefixWord ++ tailWord_895767).sum := by decide
  have hdescent : baseEnd_895767 < baseStart_895767 := by decide
  rcases family_descends (prefixWord ++ tailWord_895767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895788 : List Nat := [2, 2, 1, 1, 1, 4, 2, 7]
def baseStart_895788 : Nat := 118140960795 + 895788 * 2 ^ 59
def prefixEnd_895788 : Nat := 4983230072969 + 3 ^ 40 * 895788 * 2
def baseEnd_895788 : Nat := 136287350675510061934919

theorem tailTrace_895788 : CollatzResearch.WordTrace tailWord_895788 prefixEnd_895788 136287350675510061934919 := by
  unfold tailWord_895788
  simp only [CollatzResearch.WordTrace]
  refine ⟨16336036239360269627740009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21781381652480359503653345 16336036239360269627740009)
  ·
    refine ⟨12252027179520202220805007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16336036239360269627740009 12252027179520202220805007)
    ·
      refine ⟨18378040769280303331207511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12252027179520202220805007 18378040769280303331207511)
      ·
        refine ⟨27567061153920454996811267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18378040769280303331207511 27567061153920454996811267)
        ·
          refine ⟨41350591730880682495216901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27567061153920454996811267 41350591730880682495216901)
          ·
            refine ⟨7753235949540127967853169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41350591730880682495216901 7753235949540127967853169)
            ·
              refine ⟨5814926962155095975889877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7753235949540127967853169 5814926962155095975889877)
              ·
                refine ⟨136287350675510061934919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5814926962155095975889877 136287350675510061934919)
                ·
                  rfl

theorem cell20_895788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 7].length) (baseStart_895788 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_895788 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_895788 prefixEnd_895788 := by exact prefixLift 895788
  have htrace : WordTrace (prefixWord ++ tailWord_895788) baseStart_895788 baseEnd_895788 := by
    simpa [prefixWord, tailWord_895788, baseEnd_895788] using wordTrace_append hprefix tailTrace_895788
  have hstable : (prefixWord ++ tailWord_895788).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895788).length < 2 ^ (prefixWord ++ tailWord_895788).sum := by decide
  have hdescent : baseEnd_895788 < baseStart_895788 := by decide
  rcases family_descends (prefixWord ++ tailWord_895788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895842 : List Nat := [3, 3, 2, 1, 4, 1, 2, 1, 3]
def baseStart_895842 : Nat := 118140960795 + 895842 * 2 ^ 59
def prefixEnd_895842 : Nat := 4983230072969 + 3 ^ 40 * 895842 * 2
def baseEnd_895842 : Nat := 408886699097945998004537

theorem tailTrace_895842 : CollatzResearch.WordTrace tailWord_895842 prefixEnd_895842 408886699097945998004537 := by
  unfold tailWord_895842
  simp only [CollatzResearch.WordTrace]
  refine ⟨8168510505131226619486445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21782694680349937651963853 8168510505131226619486445)
  ·
    refine ⟨3063191439424209982307417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8168510505131226619486445 3063191439424209982307417)
    ·
      refine ⟨2297393579568157486730563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3063191439424209982307417 2297393579568157486730563)
      ·
        refine ⟨3446090369352236230095845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2297393579568157486730563 3446090369352236230095845)
        ·
          refine ⟨646141944253544293142971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3446090369352236230095845 646141944253544293142971)
          ·
            refine ⟨969212916380316439714457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 646141944253544293142971 969212916380316439714457)
            ·
              refine ⟨726909687285237329785843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 969212916380316439714457 726909687285237329785843)
              ·
                refine ⟨1090364530927855994678765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 726909687285237329785843 1090364530927855994678765)
                ·
                  refine ⟨408886699097945998004537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1090364530927855994678765 408886699097945998004537)
                  ·
                    rfl

theorem cell20_895842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 2, 1, 3].length) (baseStart_895842 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_895842 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_895842 prefixEnd_895842 := by exact prefixLift 895842
  have htrace : WordTrace (prefixWord ++ tailWord_895842) baseStart_895842 baseEnd_895842 := by
    simpa [prefixWord, tailWord_895842, baseEnd_895842] using wordTrace_append hprefix tailTrace_895842
  have hstable : (prefixWord ++ tailWord_895842).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895842).length < 2 ^ (prefixWord ++ tailWord_895842).sum := by decide
  have hdescent : baseEnd_895842 < baseStart_895842 := by decide
  rcases family_descends (prefixWord ++ tailWord_895842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895843 : List Nat := [1, 1, 1, 5, 3, 2, 2, 5]
def baseStart_895843 : Nat := 118140960795 + 895843 * 2 ^ 59
def prefixEnd_895843 : Nat := 4983230072969 + 3 ^ 40 * 895843 * 2
def baseEnd_895843 : Nat := 136295718508398146323733

theorem tailTrace_895843 : CollatzResearch.WordTrace tailWord_895843 prefixEnd_895843 136295718508398146323733 := by
  unfold tailWord_895843
  simp only [CollatzResearch.WordTrace]
  refine ⟨32674078493521283648732183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21782718995680855765821455 32674078493521283648732183)
  ·
    refine ⟨49011117740281925473098275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32674078493521283648732183 49011117740281925473098275)
    ·
      refine ⟨73516676610422888209647413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49011117740281925473098275 73516676610422888209647413)
      ·
        refine ⟨6892188432227145769654445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73516676610422888209647413 6892188432227145769654445)
        ·
          refine ⟨2584570662085179663620417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6892188432227145769654445 2584570662085179663620417)
          ·
            refine ⟨1938427996563884747715313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2584570662085179663620417 1938427996563884747715313)
            ·
              refine ⟨1453820997422913560786485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1938427996563884747715313 1453820997422913560786485)
              ·
                refine ⟨136295718508398146323733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1453820997422913560786485 136295718508398146323733)
                ·
                  rfl

theorem cell20_895843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 5].length) (baseStart_895843 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_895843 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_895843 prefixEnd_895843 := by exact prefixLift 895843
  have htrace : WordTrace (prefixWord ++ tailWord_895843) baseStart_895843 baseEnd_895843 := by
    simpa [prefixWord, tailWord_895843, baseEnd_895843] using wordTrace_append hprefix tailTrace_895843
  have hstable : (prefixWord ++ tailWord_895843).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895843).length < 2 ^ (prefixWord ++ tailWord_895843).sum := by decide
  have hdescent : baseEnd_895843 < baseStart_895843 := by decide
  rcases family_descends (prefixWord ++ tailWord_895843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895871 : List Nat := [1, 1, 2, 2, 1, 1, 4, 1, 7]
def baseStart_895871 : Nat := 118140960795 + 895871 * 2 ^ 59
def prefixEnd_895871 : Nat := 4983230072969 + 3 ^ 40 * 895871 * 2
def baseEnd_895871 : Nat := 408899935488150786037751

theorem tailTrace_895871 : CollatzResearch.WordTrace tailWord_895871 prefixEnd_895871 408899935488150786037751 := by
  unfold tailWord_895871
  simp only [CollatzResearch.WordTrace]
  refine ⟨32675099737419844430751467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21783399824946562953834311 32675099737419844430751467)
  ·
    refine ⟨49012649606129766646127201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32675099737419844430751467 49012649606129766646127201)
    ·
      refine ⟨36759487204597324984595401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49012649606129766646127201 36759487204597324984595401)
      ·
        refine ⟨27569615403447993738446551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36759487204597324984595401 27569615403447993738446551)
        ·
          refine ⟨41354423105171990607669827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27569615403447993738446551 41354423105171990607669827)
          ·
            refine ⟨62031634657757985911504741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41354423105171990607669827 62031634657757985911504741)
            ·
              refine ⟨11630931498329622358407139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62031634657757985911504741 11630931498329622358407139)
              ·
                refine ⟨17446397247494433537610709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11630931498329622358407139 17446397247494433537610709)
                ·
                  refine ⟨408899935488150786037751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17446397247494433537610709 408899935488150786037751)
                  ·
                    rfl

theorem cell20_895871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 7].length) (baseStart_895871 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_895871 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_895871 prefixEnd_895871 := by exact prefixLift 895871
  have htrace : WordTrace (prefixWord ++ tailWord_895871) baseStart_895871 baseEnd_895871 := by
    simpa [prefixWord, tailWord_895871, baseEnd_895871] using wordTrace_append hprefix tailTrace_895871
  have hstable : (prefixWord ++ tailWord_895871).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895871).length < 2 ^ (prefixWord ++ tailWord_895871).sum := by decide
  have hdescent : baseEnd_895871 < baseStart_895871 := by decide
  rcases family_descends (prefixWord ++ tailWord_895871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895894 : List Nat := [5, 3, 1, 1, 1, 3, 1, 5]
def baseStart_895894 : Nat := 118140960795 + 895894 * 2 ^ 59
def prefixEnd_895894 : Nat := 4983230072969 + 3 ^ 40 * 895894 * 2
def baseEnd_895894 : Nat := 136303477771621642756997

theorem tailTrace_895894 : CollatzResearch.WordTrace tailWord_895894 prefixEnd_895894 136303477771621642756997 := by
  unfold tailWord_895894
  simp only [CollatzResearch.WordTrace]
  refine ⟨2042246163521032459927421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21783959077557679572559157 2042246163521032459927421)
  ·
    refine ⟨765842311320387172472783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2042246163521032459927421 765842311320387172472783)
    ·
      refine ⟨1148763466980580758709175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 765842311320387172472783 1148763466980580758709175)
      ·
        refine ⟨1723145200470871138063763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1148763466980580758709175 1723145200470871138063763)
        ·
          refine ⟨2584717800706306707095645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1723145200470871138063763 2584717800706306707095645)
          ·
            refine ⟨969269175264865015160867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2584717800706306707095645 969269175264865015160867)
            ·
              refine ⟨1453903762897297522741301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 969269175264865015160867 1453903762897297522741301)
              ·
                refine ⟨136303477771621642756997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1453903762897297522741301 136303477771621642756997)
                ·
                  rfl

theorem cell20_895894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_895894 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_895894 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_895894 prefixEnd_895894 := by exact prefixLift 895894
  have htrace : WordTrace (prefixWord ++ tailWord_895894) baseStart_895894 baseEnd_895894 := by
    simpa [prefixWord, tailWord_895894, baseEnd_895894] using wordTrace_append hprefix tailTrace_895894
  have hstable : (prefixWord ++ tailWord_895894).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895894).length < 2 ^ (prefixWord ++ tailWord_895894).sum := by decide
  have hdescent : baseEnd_895894 < baseStart_895894 := by decide
  rcases family_descends (prefixWord ++ tailWord_895894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895895 : List Nat := [1, 1, 3, 3, 1, 2, 2, 3, 4]
def baseStart_895895 : Nat := 118140960795 + 895895 * 2 ^ 59
def prefixEnd_895895 : Nat := 4983230072969 + 3 ^ 40 * 895895 * 2
def baseEnd_895895 : Nat := 408910889742113369237653

theorem tailTrace_895895 : CollatzResearch.WordTrace tailWord_895895 prefixEnd_895895 408910889742113369237653 := by
  unfold tailWord_895895
  simp only [CollatzResearch.WordTrace]
  refine ⟨32675975089332896529625139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21783983392888597686416759 32675975089332896529625139)
  ·
    refine ⟨49013962633999344794437709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32675975089332896529625139 49013962633999344794437709)
    ·
      refine ⟨18380235987749754297914141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49013962633999344794437709 18380235987749754297914141)
      ·
        refine ⟨6892588495406157861717803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18380235987749754297914141 6892588495406157861717803)
        ·
          refine ⟨10338882743109236792576705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6892588495406157861717803 10338882743109236792576705)
          ·
            refine ⟨7754162057331927594432529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10338882743109236792576705 7754162057331927594432529)
            ·
              refine ⟨5815621542998945695824397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7754162057331927594432529 5815621542998945695824397)
              ·
                refine ⟨2180858078624604635934149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5815621542998945695824397 2180858078624604635934149)
                ·
                  refine ⟨408910889742113369237653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2180858078624604635934149 408910889742113369237653)
                  ·
                    rfl

theorem cell20_895895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 3, 4].length) (baseStart_895895 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_895895 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_895895 prefixEnd_895895 := by exact prefixLift 895895
  have htrace : WordTrace (prefixWord ++ tailWord_895895) baseStart_895895 baseEnd_895895 := by
    simpa [prefixWord, tailWord_895895, baseEnd_895895] using wordTrace_append hprefix tailTrace_895895
  have hstable : (prefixWord ++ tailWord_895895).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895895).length < 2 ^ (prefixWord ++ tailWord_895895).sum := by decide
  have hdescent : baseEnd_895895 < baseStart_895895 := by decide
  rcases family_descends (prefixWord ++ tailWord_895895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895898 : List Nat := [3, 1, 1, 4, 3, 2, 1, 5]
def baseStart_895898 : Nat := 118140960795 + 895898 * 2 ^ 59
def prefixEnd_895898 : Nat := 4983230072969 + 3 ^ 40 * 895898 * 2
def baseEnd_895898 : Nat := 136304086341286230712547

theorem tailTrace_895898 : CollatzResearch.WordTrace tailWord_895898 prefixEnd_895898 136304086341286230712547 := by
  unfold tailWord_895898
  simp only [CollatzResearch.WordTrace]
  refine ⟨8169021127080507010496087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21784056338881352027989565 8169021127080507010496087)
  ·
    refine ⟨12253531690620760515744131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8169021127080507010496087 12253531690620760515744131)
    ·
      refine ⟨18380297535931140773616197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12253531690620760515744131 18380297535931140773616197)
      ·
        refine ⟨3446305787987088895053037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18380297535931140773616197 3446305787987088895053037)
        ·
          refine ⟨1292364670495158335644889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3446305787987088895053037 1292364670495158335644889)
          ·
            refine ⟨969273502871368751733667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1292364670495158335644889 969273502871368751733667)
            ·
              refine ⟨1453910254307053127600501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 969273502871368751733667 1453910254307053127600501)
              ·
                refine ⟨136304086341286230712547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1453910254307053127600501 136304086341286230712547)
                ·
                  rfl

theorem cell20_895898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 5].length) (baseStart_895898 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_895898 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_895898 prefixEnd_895898 := by exact prefixLift 895898
  have htrace : WordTrace (prefixWord ++ tailWord_895898) baseStart_895898 baseEnd_895898 := by
    simpa [prefixWord, tailWord_895898, baseEnd_895898] using wordTrace_append hprefix tailTrace_895898
  have hstable : (prefixWord ++ tailWord_895898).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895898).length < 2 ^ (prefixWord ++ tailWord_895898).sum := by decide
  have hdescent : baseEnd_895898 < baseStart_895898 := by decide
  rcases family_descends (prefixWord ++ tailWord_895898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895905 : List Nat := [1, 2, 3, 4, 1, 1, 2, 3, 3]
def baseStart_895905 : Nat := 118140960795 + 895905 * 2 ^ 59
def prefixEnd_895905 : Nat := 4983230072969 + 3 ^ 40 * 895905 * 2
def baseEnd_895905 : Nat := 408915454014597778904279

theorem tailTrace_895905 : CollatzResearch.WordTrace tailWord_895905 prefixEnd_895905 408915454014597778904279 := by
  unfold tailWord_895905
  simp only [CollatzResearch.WordTrace]
  refine ⟨32676339819296668237489169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21784226546197778824992779 32676339819296668237489169)
  ·
    refine ⟨24507254864472501178116877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32676339819296668237489169 24507254864472501178116877)
    ·
      refine ⟨9190220574177187941793829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24507254864472501178116877 9190220574177187941793829)
      ·
        refine ⟨1723166357658222739086343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9190220574177187941793829 1723166357658222739086343)
        ·
          refine ⟨2584749536487334108629515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1723166357658222739086343 2584749536487334108629515)
          ·
            refine ⟨3877124304731001162944273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2584749536487334108629515 3877124304731001162944273)
            ·
              refine ⟨2907843228548250872208205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3877124304731001162944273 2907843228548250872208205)
              ·
                refine ⟨1090441210705594077078077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2907843228548250872208205 1090441210705594077078077)
                ·
                  refine ⟨408915454014597778904279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1090441210705594077078077 408915454014597778904279)
                  ·
                    rfl

theorem cell20_895905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 3, 3].length) (baseStart_895905 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_895905 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_895905 prefixEnd_895905 := by exact prefixLift 895905
  have htrace : WordTrace (prefixWord ++ tailWord_895905) baseStart_895905 baseEnd_895905 := by
    simpa [prefixWord, tailWord_895905, baseEnd_895905] using wordTrace_append hprefix tailTrace_895905
  have hstable : (prefixWord ++ tailWord_895905).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895905).length < 2 ^ (prefixWord ++ tailWord_895905).sum := by decide
  have hdescent : baseEnd_895905 < baseStart_895905 := by decide
  rcases family_descends (prefixWord ++ tailWord_895905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895909 : List Nat := [1, 3, 1, 2, 1, 1, 1, 1, 9]
def baseStart_895909 : Nat := 118140960795 + 895909 * 2 ^ 59
def prefixEnd_895909 : Nat := 4983230072969 + 3 ^ 40 * 895909 * 2
def baseEnd_895909 : Nat := 408917279723591542770929

theorem tailTrace_895909 : CollatzResearch.WordTrace tailWord_895909 prefixEnd_895909 408917279723591542770929 := by
  unfold tailWord_895909
  simp only [CollatzResearch.WordTrace]
  refine ⟨32676485711282176920634781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21784323807521451280423187 32676485711282176920634781)
  ·
    refine ⟨12253682141730816345238043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32676485711282176920634781 12253682141730816345238043)
    ·
      refine ⟨18380523212596224517857065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12253682141730816345238043 18380523212596224517857065)
      ·
        refine ⟨13785392409447168388392799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18380523212596224517857065 13785392409447168388392799)
        ·
          refine ⟨20678088614170752582589199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13785392409447168388392799 20678088614170752582589199)
          ·
            refine ⟨31017132921256128873883799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20678088614170752582589199 31017132921256128873883799)
            ·
              refine ⟨46525699381884193310825699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31017132921256128873883799 46525699381884193310825699)
              ·
                refine ⟨69788549072826289966238549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46525699381884193310825699 69788549072826289966238549)
                ·
                  refine ⟨408917279723591542770929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 69788549072826289966238549 408917279723591542770929)
                  ·
                    rfl

theorem cell20_895909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 9].length) (baseStart_895909 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_895909 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_895909 prefixEnd_895909 := by exact prefixLift 895909
  have htrace : WordTrace (prefixWord ++ tailWord_895909) baseStart_895909 baseEnd_895909 := by
    simpa [prefixWord, tailWord_895909, baseEnd_895909] using wordTrace_append hprefix tailTrace_895909
  have hstable : (prefixWord ++ tailWord_895909).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895909).length < 2 ^ (prefixWord ++ tailWord_895909).sum := by decide
  have hdescent : baseEnd_895909 < baseStart_895909 := by decide
  rcases family_descends (prefixWord ++ tailWord_895909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895929 : List Nat := [1, 2, 1, 4, 2, 3, 2, 3, 2]
def baseStart_895929 : Nat := 118140960795 + 895929 * 2 ^ 59
def prefixEnd_895929 : Nat := 4983230072969 + 3 ^ 40 * 895929 * 2
def baseEnd_895929 : Nat := 408926408268560362104181

theorem tailTrace_895929 : CollatzResearch.WordTrace tailWord_895929 prefixEnd_895929 408926408268560362104181 := by
  unfold tailWord_895929
  simp only [CollatzResearch.WordTrace]
  refine ⟨32677215171209720336362841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21784810114139813557575227 32677215171209720336362841)
  ·
    refine ⟨24507911378407290252272131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32677215171209720336362841 24507911378407290252272131)
    ·
      refine ⟨36761867067610935378408197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24507911378407290252272131 36761867067610935378408197)
      ·
        refine ⟨6892850075177050383451537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36761867067610935378408197 6892850075177050383451537)
        ·
          refine ⟨5169637556382787787588653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6892850075177050383451537 5169637556382787787588653)
          ·
            refine ⟨1938614083643545420345745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5169637556382787787588653 1938614083643545420345745)
            ·
              refine ⟨1453960562732659065259309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1938614083643545420345745 1453960562732659065259309)
              ·
                refine ⟨545235211024747149472241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1453960562732659065259309 545235211024747149472241)
                ·
                  refine ⟨408926408268560362104181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 545235211024747149472241 408926408268560362104181)
                  ·
                    rfl

theorem cell20_895929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 3, 2].length) (baseStart_895929 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_895929 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_895929 prefixEnd_895929 := by exact prefixLift 895929
  have htrace : WordTrace (prefixWord ++ tailWord_895929) baseStart_895929 baseEnd_895929 := by
    simpa [prefixWord, tailWord_895929, baseEnd_895929] using wordTrace_append hprefix tailTrace_895929
  have hstable : (prefixWord ++ tailWord_895929).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895929).length < 2 ^ (prefixWord ++ tailWord_895929).sum := by decide
  have hdescent : baseEnd_895929 < baseStart_895929 := by decide
  rcases family_descends (prefixWord ++ tailWord_895929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895942 : List Nat := [6, 1, 3, 1, 1, 1, 2, 1, 4]
def baseStart_895942 : Nat := 118140960795 + 895942 * 2 ^ 59
def prefixEnd_895942 : Nat := 4983230072969 + 3 ^ 40 * 895942 * 2
def baseEnd_895942 : Nat := 408932341822790094670795

theorem tailTrace_895942 : CollatzResearch.WordTrace tailWord_895942 prefixEnd_895942 408932341822790094670795 := by
  unfold tailWord_895942
  simp only [CollatzResearch.WordTrace]
  refine ⟨1021177791255081986143315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 21785126213441749037724053 1021177791255081986143315)
  ·
    refine ⟨1531766686882622979214973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1021177791255081986143315 1531766686882622979214973)
    ·
      refine ⟨574412507580983617205615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1531766686882622979214973 574412507580983617205615)
      ·
        refine ⟨861618761371475425808423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 574412507580983617205615 861618761371475425808423)
        ·
          refine ⟨1292428142057213138712635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 861618761371475425808423 1292428142057213138712635)
          ·
            refine ⟨1938642213085819708068953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1292428142057213138712635 1938642213085819708068953)
            ·
              refine ⟨1453981659814364781051715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1938642213085819708068953 1453981659814364781051715)
              ·
                refine ⟨2180972489721547171577573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1453981659814364781051715 2180972489721547171577573)
                ·
                  refine ⟨408932341822790094670795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2180972489721547171577573 408932341822790094670795)
                  ·
                    rfl

theorem cell20_895942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_895942 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_895942 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_895942 prefixEnd_895942 := by exact prefixLift 895942
  have htrace : WordTrace (prefixWord ++ tailWord_895942) baseStart_895942 baseEnd_895942 := by
    simpa [prefixWord, tailWord_895942, baseEnd_895942] using wordTrace_append hprefix tailTrace_895942
  have hstable : (prefixWord ++ tailWord_895942).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895942).length < 2 ^ (prefixWord ++ tailWord_895942).sum := by decide
  have hdescent : baseEnd_895942 < baseStart_895942 := by decide
  rcases family_descends (prefixWord ++ tailWord_895942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895950 : List Nat := [4, 1, 1, 1, 2, 4, 2, 1, 4]
def baseStart_895950 : Nat := 118140960795 + 895950 * 2 ^ 59
def prefixEnd_895950 : Nat := 4983230072969 + 3 ^ 40 * 895950 * 2
def baseEnd_895950 : Nat := 408935993240777622404095

theorem tailTrace_895950 : CollatzResearch.WordTrace tailWord_895950 prefixEnd_895950 408935993240777622404095 := by
  unfold tailWord_895950
  simp only [CollatzResearch.WordTrace]
  refine ⟨4084747638016705115359663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21785320736089093948584869 4084747638016705115359663)
  ·
    refine ⟨6127121457025057673039495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4084747638016705115359663 6127121457025057673039495)
    ·
      refine ⟨9190682185537586509559243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6127121457025057673039495 9190682185537586509559243)
      ·
        refine ⟨13786023278306379764338865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9190682185537586509559243 13786023278306379764338865)
        ·
          refine ⟨10339517458729784823254149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13786023278306379764338865 10339517458729784823254149)
          ·
            refine ⟨1938659523511834654360153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10339517458729784823254149 1938659523511834654360153)
            ·
              refine ⟨1453994642633875990770115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1938659523511834654360153 1453994642633875990770115)
              ·
                refine ⟨2180991963950813986155173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1453994642633875990770115 2180991963950813986155173)
                ·
                  refine ⟨408935993240777622404095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2180991963950813986155173 408935993240777622404095)
                  ·
                    rfl

theorem cell20_895950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_895950 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_895950 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_895950 prefixEnd_895950 := by exact prefixLift 895950
  have htrace : WordTrace (prefixWord ++ tailWord_895950) baseStart_895950 baseEnd_895950 := by
    simpa [prefixWord, tailWord_895950, baseEnd_895950] using wordTrace_append hprefix tailTrace_895950
  have hstable : (prefixWord ++ tailWord_895950).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895950).length < 2 ^ (prefixWord ++ tailWord_895950).sum := by decide
  have hdescent : baseEnd_895950 < baseStart_895950 := by decide
  rcases family_descends (prefixWord ++ tailWord_895950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895971 : List Nat := [1, 1, 1, 6, 1, 1, 1, 4, 4]
def baseStart_895971 : Nat := 118140960795 + 895971 * 2 ^ 59
def prefixEnd_895971 : Nat := 4983230072969 + 3 ^ 40 * 895971 * 2
def baseEnd_895971 : Nat := 408945578212994882704009

theorem tailTrace_895971 : CollatzResearch.WordTrace tailWord_895971 prefixEnd_895971 408945578212994882704009 := by
  unfold tailWord_895971
  simp only [CollatzResearch.WordTrace]
  refine ⟨32678747037057561509391767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21785831358038374339594511 32678747037057561509391767)
  ·
    refine ⟨49018120555586342264087651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32678747037057561509391767 49018120555586342264087651)
    ·
      refine ⟨73527180833379513396131477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49018120555586342264087651 73527180833379513396131477)
      ·
        refine ⟨3446586601564664690443663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 73527180833379513396131477 3446586601564664690443663)
        ·
          refine ⟨5169879902346997035665495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3446586601564664690443663 5169879902346997035665495)
          ·
            refine ⟨7754819853520495553498243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5169879902346997035665495 7754819853520495553498243)
            ·
              refine ⟨11632229780280743330247365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7754819853520495553498243 11632229780280743330247365)
              ·
                refine ⟨2181043083802639374421381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11632229780280743330247365 2181043083802639374421381)
                ·
                  refine ⟨408945578212994882704009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2181043083802639374421381 408945578212994882704009)
                  ·
                    rfl

theorem cell20_895971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 4, 4].length) (baseStart_895971 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_895971 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_895971 prefixEnd_895971 := by exact prefixLift 895971
  have htrace : WordTrace (prefixWord ++ tailWord_895971) baseStart_895971 baseEnd_895971 := by
    simpa [prefixWord, tailWord_895971, baseEnd_895971] using wordTrace_append hprefix tailTrace_895971
  have hstable : (prefixWord ++ tailWord_895971).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895971).length < 2 ^ (prefixWord ++ tailWord_895971).sum := by decide
  have hdescent : baseEnd_895971 < baseStart_895971 := by decide
  rcases family_descends (prefixWord ++ tailWord_895971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896005 : List Nat := [1, 3, 1, 1, 2, 3, 5, 2, 2]
def baseStart_896005 : Nat := 118140960795 + 896005 * 2 ^ 59
def prefixEnd_896005 : Nat := 4983230072969 + 3 ^ 40 * 896005 * 2
def baseEnd_896005 : Nat := 408961096739441875570537

theorem tailTrace_896005 : CollatzResearch.WordTrace tailWord_896005 prefixEnd_896005 408961096739441875570537 := by
  unfold tailWord_896005
  simp only [CollatzResearch.WordTrace]
  refine ⟨32679987118934385316129469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21786658079289590210752979 32679987118934385316129469)
  ·
    refine ⟨12254995169600394493548551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32679987118934385316129469 12254995169600394493548551)
    ·
      refine ⟨18382492754400591740322827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12254995169600394493548551 18382492754400591740322827)
      ·
        refine ⟨27573739131600887610484241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18382492754400591740322827 27573739131600887610484241)
        ·
          refine ⟨20680304348700665707863181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27573739131600887610484241 20680304348700665707863181)
          ·
            refine ⟨7755114130762749640448693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20680304348700665707863181 7755114130762749640448693)
            ·
              refine ⟨727041949759007778792065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7755114130762749640448693 727041949759007778792065)
              ·
                refine ⟨545281462319255834094049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 727041949759007778792065 545281462319255834094049)
                ·
                  refine ⟨408961096739441875570537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 545281462319255834094049 408961096739441875570537)
                  ·
                    rfl

theorem cell20_896005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 5, 2, 2].length) (baseStart_896005 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_896005 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_896005 prefixEnd_896005 := by exact prefixLift 896005
  have htrace : WordTrace (prefixWord ++ tailWord_896005) baseStart_896005 baseEnd_896005 := by
    simpa [prefixWord, tailWord_896005, baseEnd_896005] using wordTrace_append hprefix tailTrace_896005
  have hstable : (prefixWord ++ tailWord_896005).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896005).length < 2 ^ (prefixWord ++ tailWord_896005).sum := by decide
  have hdescent : baseEnd_896005 < baseStart_896005 := by decide
  rcases family_descends (prefixWord ++ tailWord_896005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896057 : List Nat := [1, 2, 1, 5, 2, 2, 2, 2, 3]
def baseStart_896057 : Nat := 118140960795 + 896057 * 2 ^ 59
def prefixEnd_896057 : Nat := 4983230072969 + 3 ^ 40 * 896057 * 2
def baseEnd_896057 : Nat := 408984830956360805836991

theorem tailTrace_896057 : CollatzResearch.WordTrace tailWord_896057 prefixEnd_896057 408984830956360805836991 := by
  unfold tailWord_896057
  simp only [CollatzResearch.WordTrace]
  refine ⟨32681883714745998197022425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21787922476497332131348283 32681883714745998197022425)
  ·
    refine ⟨24511412786059498647766819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32681883714745998197022425 24511412786059498647766819)
    ·
      refine ⟨36767119179089247971650229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24511412786059498647766819 36767119179089247971650229)
      ·
        refine ⟨3446917423039616997342209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36767119179089247971650229 3446917423039616997342209)
        ·
          refine ⟨2585188067279712748006657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3446917423039616997342209 2585188067279712748006657)
          ·
            refine ⟨1938891050459784561004993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2585188067279712748006657 1938891050459784561004993)
            ·
              refine ⟨1454168287844838420753745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1938891050459784561004993 1454168287844838420753745)
              ·
                refine ⟨1090626215883628815565309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1454168287844838420753745 1090626215883628815565309)
                ·
                  refine ⟨408984830956360805836991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1090626215883628815565309 408984830956360805836991)
                  ·
                    rfl

theorem cell20_896057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 2, 3].length) (baseStart_896057 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_896057 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_896057 prefixEnd_896057 := by exact prefixLift 896057
  have htrace : WordTrace (prefixWord ++ tailWord_896057) baseStart_896057 baseEnd_896057 := by
    simpa [prefixWord, tailWord_896057, baseEnd_896057] using wordTrace_append hprefix tailTrace_896057
  have hstable : (prefixWord ++ tailWord_896057).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896057).length < 2 ^ (prefixWord ++ tailWord_896057).sum := by decide
  have hdescent : baseEnd_896057 < baseStart_896057 := by decide
  rcases family_descends (prefixWord ++ tailWord_896057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896060 : List Nat := [2, 2, 2, 2, 2, 4, 2, 2, 2]
def baseStart_896060 : Nat := 118140960795 + 896060 * 2 ^ 59
def prefixEnd_896060 : Nat := 4983230072969 + 3 ^ 40 * 896060 * 2
def baseEnd_896060 : Nat := 408986200238106128736979

theorem tailTrace_896060 : CollatzResearch.WordTrace tailWord_896060 prefixEnd_896060 408986200238106128736979 := by
  unfold tailWord_896060
  simp only [CollatzResearch.WordTrace]
  refine ⟨16340996566867564854690817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21787995422490086472921089 16340996566867564854690817)
  ·
    refine ⟨12255747425150673641018113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16340996566867564854690817 12255747425150673641018113)
    ·
      refine ⟨9191810568863005230763585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12255747425150673641018113 9191810568863005230763585)
      ·
        refine ⟨6893857926647253923072689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9191810568863005230763585 6893857926647253923072689)
        ·
          refine ⟨5170393444985440442304517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6893857926647253923072689 5170393444985440442304517)
          ·
            refine ⟨969448770934770082932097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5170393444985440442304517 969448770934770082932097)
            ·
              refine ⟨727086578201077562199073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 969448770934770082932097 727086578201077562199073)
              ·
                refine ⟨545314933650808171649305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 727086578201077562199073 545314933650808171649305)
                ·
                  refine ⟨408986200238106128736979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 545314933650808171649305 408986200238106128736979)
                  ·
                    rfl

theorem cell20_896060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 2, 2, 2].length) (baseStart_896060 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_896060 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_896060 prefixEnd_896060 := by exact prefixLift 896060
  have htrace : WordTrace (prefixWord ++ tailWord_896060) baseStart_896060 baseEnd_896060 := by
    simpa [prefixWord, tailWord_896060, baseEnd_896060] using wordTrace_append hprefix tailTrace_896060
  have hstable : (prefixWord ++ tailWord_896060).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896060).length < 2 ^ (prefixWord ++ tailWord_896060).sum := by decide
  have hdescent : baseEnd_896060 < baseStart_896060 := by decide
  rcases family_descends (prefixWord ++ tailWord_896060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896064 : List Nat := [2, 1, 1, 2, 2, 3, 3, 4, 2]
def baseStart_896064 : Nat := 118140960795 + 896064 * 2 ^ 59
def prefixEnd_896064 : Nat := 4983230072969 + 3 ^ 40 * 896064 * 2
def baseEnd_896064 : Nat := 408988025947099892603629

theorem tailTrace_896064 : CollatzResearch.WordTrace tailWord_896064 prefixEnd_896064 408988025947099892603629 := by
  unfold tailWord_896064
  simp only [CollatzResearch.WordTrace]
  refine ⟨16341069512860319196263623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21788092683813758928351497 16341069512860319196263623)
  ·
    refine ⟨24511604269290478794395435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16341069512860319196263623 24511604269290478794395435)
    ·
      refine ⟨36767406403935718191593153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24511604269290478794395435 36767406403935718191593153)
      ·
        refine ⟨27575554802951788643694865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36767406403935718191593153 27575554802951788643694865)
        ·
          refine ⟨20681666102213841482771149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27575554802951788643694865 20681666102213841482771149)
          ·
            refine ⟨7755624788330190556039181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20681666102213841482771149 7755624788330190556039181)
            ·
              refine ⟨2908359295623821458514693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7755624788330190556039181 2908359295623821458514693)
              ·
                refine ⟨545317367929466523471505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2908359295623821458514693 545317367929466523471505)
                ·
                  refine ⟨408988025947099892603629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 545317367929466523471505 408988025947099892603629)
                  ·
                    rfl

theorem cell20_896064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 4, 2].length) (baseStart_896064 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_896064 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_896064 prefixEnd_896064 := by exact prefixLift 896064
  have htrace : WordTrace (prefixWord ++ tailWord_896064) baseStart_896064 baseEnd_896064 := by
    simpa [prefixWord, tailWord_896064, baseEnd_896064] using wordTrace_append hprefix tailTrace_896064
  have hstable : (prefixWord ++ tailWord_896064).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896064).length < 2 ^ (prefixWord ++ tailWord_896064).sum := by decide
  have hdescent : baseEnd_896064 < baseStart_896064 := by decide
  rcases family_descends (prefixWord ++ tailWord_896064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896071 : List Nat := [1, 1, 4, 1, 3, 4, 1, 5]
def baseStart_896071 : Nat := 118140960795 + 896071 * 2 ^ 59
def prefixEnd_896071 : Nat := 4983230072969 + 3 ^ 40 * 896071 * 2
def baseEnd_896071 : Nat := 136330406979279659790089

theorem tailTrace_896071 : CollatzResearch.WordTrace tailWord_896071 prefixEnd_896071 136330406979279659790089 := by
  unfold tailWord_896071
  simp only [CollatzResearch.WordTrace]
  refine ⟨32682394336695278588032067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21788262891130185725354711 32682394336695278588032067)
  ·
    refine ⟨49023591505042917882048101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32682394336695278588032067 49023591505042917882048101)
    ·
      refine ⟨9191923407195547102884019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49023591505042917882048101 9191923407195547102884019)
      ·
        refine ⟨13787885110793320654326029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9191923407195547102884019 13787885110793320654326029)
        ·
          refine ⟨5170456916547495245372261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13787885110793320654326029 5170456916547495245372261)
          ·
            refine ⟨969460671852655358507299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5170456916547495245372261 969460671852655358507299)
            ·
              refine ⟨1454191007778983037760949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 969460671852655358507299 1454191007778983037760949)
              ·
                refine ⟨136330406979279659790089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1454191007778983037760949 136330406979279659790089)
                ·
                  rfl

theorem cell20_896071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 5].length) (baseStart_896071 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_896071 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_896071 prefixEnd_896071 := by exact prefixLift 896071
  have htrace : WordTrace (prefixWord ++ tailWord_896071) baseStart_896071 baseEnd_896071 := by
    simpa [prefixWord, tailWord_896071, baseEnd_896071] using wordTrace_append hprefix tailTrace_896071
  have hstable : (prefixWord ++ tailWord_896071).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896071).length < 2 ^ (prefixWord ++ tailWord_896071).sum := by decide
  have hdescent : baseEnd_896071 < baseStart_896071 := by decide
  rcases family_descends (prefixWord ++ tailWord_896071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896078 : List Nat := [4, 1, 1, 1, 1, 3, 1, 5, 3]
def baseStart_896078 : Nat := 118140960795 + 896078 * 2 ^ 59
def prefixEnd_896078 : Nat := 4983230072969 + 3 ^ 40 * 896078 * 2
def baseEnd_896078 : Nat := 408994415928578066136905

theorem tailTrace_896078 : CollatzResearch.WordTrace tailWord_896078 prefixEnd_896078 408994415928578066136905 := by
  unfold tailWord_896078
  simp only [CollatzResearch.WordTrace]
  refine ⟨4085331205958739847942111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21788433098446612522357925 4085331205958739847942111)
  ·
    refine ⟨6127996808938109771913167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4085331205958739847942111 6127996808938109771913167)
    ·
      refine ⟨9191995213407164657869751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6127996808938109771913167 9191995213407164657869751)
      ·
        refine ⟨13787992820110746986804627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9191995213407164657869751 13787992820110746986804627)
        ·
          refine ⟨20681989230166120480206941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13787992820110746986804627 20681989230166120480206941)
          ·
            refine ⟨7755745961312295180077603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20681989230166120480206941 7755745961312295180077603)
            ·
              refine ⟨11633618941968442770116405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7755745961312295180077603 11633618941968442770116405)
              ·
                refine ⟨1090651775809541509698413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11633618941968442770116405 1090651775809541509698413)
                ·
                  refine ⟨408994415928578066136905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1090651775809541509698413 408994415928578066136905)
                  ·
                    rfl

theorem cell20_896078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 5, 3].length) (baseStart_896078 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_896078 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_896078 prefixEnd_896078 := by exact prefixLift 896078
  have htrace : WordTrace (prefixWord ++ tailWord_896078) baseStart_896078 baseEnd_896078 := by
    simpa [prefixWord, tailWord_896078, baseEnd_896078] using wordTrace_append hprefix tailTrace_896078
  have hstable : (prefixWord ++ tailWord_896078).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896078).length < 2 ^ (prefixWord ++ tailWord_896078).sum := by decide
  have hdescent : baseEnd_896078 < baseStart_896078 := by decide
  rcases family_descends (prefixWord ++ tailWord_896078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896085 : List Nat := [1, 3, 2, 2, 1, 2, 3, 2, 4]
def baseStart_896085 : Nat := 118140960795 + 896085 * 2 ^ 59
def prefixEnd_896085 : Nat := 4983230072969 + 3 ^ 40 * 896085 * 2
def baseEnd_896085 : Nat := 408997610919317152903543

theorem tailTrace_896085 : CollatzResearch.WordTrace tailWord_896085 prefixEnd_896085 408997610919317152903543 := by
  unfold tailWord_896085
  simp only [CollatzResearch.WordTrace]
  refine ⟨32682904958644558979041709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21788603305763039319361139 32682904958644558979041709)
  ·
    refine ⟨12256089359491709617140641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32682904958644558979041709 12256089359491709617140641)
    ·
      refine ⟨9192067019618782212855481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12256089359491709617140641 9192067019618782212855481)
      ·
        refine ⟨6894050264714086659641611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9192067019618782212855481 6894050264714086659641611)
        ·
          refine ⟨10341075397071129989462417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6894050264714086659641611 10341075397071129989462417)
          ·
            refine ⟨7755806547803347492096813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10341075397071129989462417 7755806547803347492096813)
            ·
              refine ⟨2908427455426255309536305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7755806547803347492096813 2908427455426255309536305)
              ·
                refine ⟨2181320591569691482152229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2908427455426255309536305 2181320591569691482152229)
                ·
                  refine ⟨408997610919317152903543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2181320591569691482152229 408997610919317152903543)
                  ·
                    rfl

theorem cell20_896085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 2, 4].length) (baseStart_896085 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_896085 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_896085 prefixEnd_896085 := by exact prefixLift 896085
  have htrace : WordTrace (prefixWord ++ tailWord_896085) baseStart_896085 baseEnd_896085 := by
    simpa [prefixWord, tailWord_896085, baseEnd_896085] using wordTrace_append hprefix tailTrace_896085
  have hstable : (prefixWord ++ tailWord_896085).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896085).length < 2 ^ (prefixWord ++ tailWord_896085).sum := by decide
  have hdescent : baseEnd_896085 < baseStart_896085 := by decide
  rcases family_descends (prefixWord ++ tailWord_896085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896098 : List Nat := [3, 3, 2, 2, 1, 2, 2, 3, 2]
def baseStart_896098 : Nat := 118140960795 + 896098 * 2 ^ 59
def prefixEnd_896098 : Nat := 4983230072969 + 3 ^ 40 * 896098 * 2
def baseEnd_896098 : Nat := 409003544473546885470157

theorem tailTrace_896098 : CollatzResearch.WordTrace tailWord_896098 prefixEnd_896098 409003544473546885470157 := by
  unfold tailWord_896098
  simp only [CollatzResearch.WordTrace]
  refine ⟨8170844776899365549816237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21788919405064974799509965 8170844776899365549816237)
  ·
    refine ⟨3064066791337262081181089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8170844776899365549816237 3064066791337262081181089)
    ·
      refine ⟨2298050093502946560885817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3064066791337262081181089 2298050093502946560885817)
      ·
        refine ⟨1723537570127209920664363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2298050093502946560885817 1723537570127209920664363)
        ·
          refine ⟨2585306355190814880996545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1723537570127209920664363 2585306355190814880996545)
          ·
            refine ⟨1938979766393111160747409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2585306355190814880996545 1938979766393111160747409)
            ·
              refine ⟨1454234824794833370560557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1938979766393111160747409 1454234824794833370560557)
              ·
                refine ⟨545338059298062513960209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1454234824794833370560557 545338059298062513960209)
                ·
                  refine ⟨409003544473546885470157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 545338059298062513960209 409003544473546885470157)
                  ·
                    rfl

theorem cell20_896098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 3, 2].length) (baseStart_896098 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_896098 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_896098 prefixEnd_896098 := by exact prefixLift 896098
  have htrace : WordTrace (prefixWord ++ tailWord_896098) baseStart_896098 baseEnd_896098 := by
    simpa [prefixWord, tailWord_896098, baseEnd_896098] using wordTrace_append hprefix tailTrace_896098
  have hstable : (prefixWord ++ tailWord_896098).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896098).length < 2 ^ (prefixWord ++ tailWord_896098).sum := by decide
  have hdescent : baseEnd_896098 < baseStart_896098 := by decide
  rcases family_descends (prefixWord ++ tailWord_896098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896099 : List Nat := [1, 1, 1, 5, 1, 1, 1, 4, 5]
def baseStart_896099 : Nat := 118140960795 + 896099 * 2 ^ 59
def prefixEnd_896099 : Nat := 4983230072969 + 3 ^ 40 * 896099 * 2
def baseEnd_896099 : Nat := 409004000900795326436819

theorem tailTrace_896099 : CollatzResearch.WordTrace tailWord_896099 prefixEnd_896099 409004000900795326436819 := by
  unfold tailWord_896099
  simp only [CollatzResearch.WordTrace]
  refine ⟨32683415580593839370051351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21788943720395892913367567 32683415580593839370051351)
  ·
    refine ⟨49025123370890759055077027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32683415580593839370051351 49025123370890759055077027)
    ·
      refine ⟨73537685056336138582615541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49025123370890759055077027 73537685056336138582615541)
      ·
        refine ⟨6894157974031512992120207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73537685056336138582615541 6894157974031512992120207)
        ·
          refine ⟨10341236961047269488180311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6894157974031512992120207 10341236961047269488180311)
          ·
            refine ⟨15511855441570904232270467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10341236961047269488180311 15511855441570904232270467)
            ·
              refine ⟨23267783162356356348405701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15511855441570904232270467 23267783162356356348405701)
              ·
                refine ⟨4362709342941816815326069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23267783162356356348405701 4362709342941816815326069)
                ·
                  refine ⟨409004000900795326436819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4362709342941816815326069 409004000900795326436819)
                  ·
                    rfl

theorem cell20_896099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 4, 5].length) (baseStart_896099 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_896099 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_896099 prefixEnd_896099 := by exact prefixLift 896099
  have htrace : WordTrace (prefixWord ++ tailWord_896099) baseStart_896099 baseEnd_896099 := by
    simpa [prefixWord, tailWord_896099, baseEnd_896099] using wordTrace_append hprefix tailTrace_896099
  have hstable : (prefixWord ++ tailWord_896099).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896099).length < 2 ^ (prefixWord ++ tailWord_896099).sum := by decide
  have hdescent : baseEnd_896099 < baseStart_896099 := by decide
  rcases family_descends (prefixWord ++ tailWord_896099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896144 : List Nat := [2, 1, 1, 1, 1, 1, 4, 3, 6]
def baseStart_896144 : Nat := 118140960795 + 896144 * 2 ^ 59
def prefixEnd_896144 : Nat := 4983230072969 + 3 ^ 40 * 896144 * 2
def baseEnd_896144 : Nat := 409024540126975169936635

theorem tailTrace_896144 : CollatzResearch.WordTrace tailWord_896144 prefixEnd_896144 409024540126975169936635 := by
  unfold tailWord_896144
  simp only [CollatzResearch.WordTrace]
  refine ⟨16342528432715406027719743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21790037910287208036959657 16342528432715406027719743)
  ·
    refine ⟨24513792649073109041579615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16342528432715406027719743 24513792649073109041579615)
    ·
      refine ⟨36770688973609663562369423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24513792649073109041579615 36770688973609663562369423)
      ·
        refine ⟨55156033460414495343554135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36770688973609663562369423 55156033460414495343554135)
        ·
          refine ⟨82734050190621743015331203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55156033460414495343554135 82734050190621743015331203)
          ·
            refine ⟨124101075285932614522996805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82734050190621743015331203 124101075285932614522996805)
            ·
              refine ⟨23268951616112365223061901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 124101075285932614522996805 23268951616112365223061901)
              ·
                refine ⟨8725856856042136958648213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23268951616112365223061901 8725856856042136958648213)
                ·
                  refine ⟨409024540126975169936635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8725856856042136958648213 409024540126975169936635)
                  ·
                    rfl

theorem cell20_896144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 6].length) (baseStart_896144 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_896144 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_896144 prefixEnd_896144 := by exact prefixLift 896144
  have htrace : WordTrace (prefixWord ++ tailWord_896144) baseStart_896144 baseEnd_896144 := by
    simpa [prefixWord, tailWord_896144, baseEnd_896144] using wordTrace_append hprefix tailTrace_896144
  have hstable : (prefixWord ++ tailWord_896144).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896144).length < 2 ^ (prefixWord ++ tailWord_896144).sum := by decide
  have hdescent : baseEnd_896144 < baseStart_896144 := by decide
  rcases family_descends (prefixWord ++ tailWord_896144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896154 : List Nat := [3, 1, 1, 5, 1, 1, 1, 2, 5]
def baseStart_896154 : Nat := 118140960795 + 896154 * 2 ^ 59
def prefixEnd_896154 : Nat := 4983230072969 + 3 ^ 40 * 896154 * 2
def baseEnd_896154 : Nat := 409029104399459579603261

theorem tailTrace_896154 : CollatzResearch.WordTrace tailWord_896154 prefixEnd_896154 409029104399459579603261 := by
  unfold tailWord_896154
  simp only [CollatzResearch.WordTrace]
  refine ⟨8171355398848645940825879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21790281063596389175535677 8171355398848645940825879)
  ·
    refine ⟨12257033098272968911238819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8171355398848645940825879 12257033098272968911238819)
    ·
      refine ⟨18385549647409453366858229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12257033098272968911238819 18385549647409453366858229)
      ·
        refine ⟨1723645279444636253142959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18385549647409453366858229 1723645279444636253142959)
        ·
          refine ⟨2585467919166954379714439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1723645279444636253142959 2585467919166954379714439)
          ·
            refine ⟨3878201878750431569571659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2585467919166954379714439 3878201878750431569571659)
            ·
              refine ⟨5817302818125647354357489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3878201878750431569571659 5817302818125647354357489)
              ·
                refine ⟨4362977113594235515768117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5817302818125647354357489 4362977113594235515768117)
                ·
                  refine ⟨409029104399459579603261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4362977113594235515768117 409029104399459579603261)
                  ·
                    rfl

theorem cell20_896154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 2, 5].length) (baseStart_896154 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_896154 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_896154 prefixEnd_896154 := by exact prefixLift 896154
  have htrace : WordTrace (prefixWord ++ tailWord_896154) baseStart_896154 baseEnd_896154 := by
    simpa [prefixWord, tailWord_896154, baseEnd_896154] using wordTrace_append hprefix tailTrace_896154
  have hstable : (prefixWord ++ tailWord_896154).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896154).length < 2 ^ (prefixWord ++ tailWord_896154).sum := by decide
  have hdescent : baseEnd_896154 < baseStart_896154 := by decide
  rcases family_descends (prefixWord ++ tailWord_896154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896175 : List Nat := [1, 1, 2, 1, 2, 3, 4, 1, 5]
def baseStart_896175 : Nat := 118140960795 + 896175 * 2 ^ 59
def prefixEnd_896175 : Nat := 4983230072969 + 3 ^ 40 * 896175 * 2
def baseEnd_896175 : Nat := 409038689371676839903175

theorem tailTrace_896175 : CollatzResearch.WordTrace tailWord_896175 prefixEnd_896175 409038689371676839903175 := by
  unfold tailWord_896175
  simp only [CollatzResearch.WordTrace]
  refine ⟨32686187528318504349817979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21790791685545669566545319 32686187528318504349817979)
  ·
    refine ⟨49029281292477756524726969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32686187528318504349817979 49029281292477756524726969)
    ·
      refine ⟨36771960969358317393545227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49029281292477756524726969 36771960969358317393545227)
      ·
        refine ⟨55157941454037476090317841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36771960969358317393545227 55157941454037476090317841)
        ·
          refine ⟨41368456090528107067738381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55157941454037476090317841 41368456090528107067738381)
          ·
            refine ⟨15513171033948040150401893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41368456090528107067738381 15513171033948040150401893)
            ·
              refine ⟨2908719568865257528200355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15513171033948040150401893 2908719568865257528200355)
              ·
                refine ⟨4363079353297886292300533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2908719568865257528200355 4363079353297886292300533)
                ·
                  refine ⟨409038689371676839903175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4363079353297886292300533 409038689371676839903175)
                  ·
                    rfl

theorem cell20_896175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 1, 5].length) (baseStart_896175 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_896175 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_896175 prefixEnd_896175 := by exact prefixLift 896175
  have htrace : WordTrace (prefixWord ++ tailWord_896175) baseStart_896175 baseEnd_896175 := by
    simpa [prefixWord, tailWord_896175, baseEnd_896175] using wordTrace_append hprefix tailTrace_896175
  have hstable : (prefixWord ++ tailWord_896175).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896175).length < 2 ^ (prefixWord ++ tailWord_896175).sum := by decide
  have hdescent : baseEnd_896175 < baseStart_896175 := by decide
  rcases family_descends (prefixWord ++ tailWord_896175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896178 : List Nat := [3, 2, 1, 1, 1, 6, 1, 1, 4]
def baseStart_896178 : Nat := 118140960795 + 896178 * 2 ^ 59
def prefixEnd_896178 : Nat := 4983230072969 + 3 ^ 40 * 896178 * 2
def baseEnd_896178 : Nat := 409040058653422162803163

theorem tailTrace_896178 : CollatzResearch.WordTrace tailWord_896178 prefixEnd_896178 409040058653422162803163 := by
  unfold tailWord_896178
  simp only [CollatzResearch.WordTrace]
  refine ⟨8171574236826908965544297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21790864631538423908118125 8171574236826908965544297)
  ·
    refine ⟨6128680677620181724158223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8171574236826908965544297 6128680677620181724158223)
    ·
      refine ⟨9193021016430272586237335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6128680677620181724158223 9193021016430272586237335)
      ·
        refine ⟨13789531524645408879356003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9193021016430272586237335 13789531524645408879356003)
        ·
          refine ⟨20684297286968113319034005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13789531524645408879356003 20684297286968113319034005)
          ·
            refine ⟨969576435326630311829719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 20684297286968113319034005 969576435326630311829719)
            ·
              refine ⟨1454364652989945467744579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 969576435326630311829719 1454364652989945467744579)
              ·
                refine ⟨2181546979484918201616869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1454364652989945467744579 2181546979484918201616869)
                ·
                  refine ⟨409040058653422162803163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2181546979484918201616869 409040058653422162803163)
                  ·
                    rfl

theorem cell20_896178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 1, 4].length) (baseStart_896178 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_896178 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_896178 prefixEnd_896178 := by exact prefixLift 896178
  have htrace : WordTrace (prefixWord ++ tailWord_896178) baseStart_896178 baseEnd_896178 := by
    simpa [prefixWord, tailWord_896178, baseEnd_896178] using wordTrace_append hprefix tailTrace_896178
  have hstable : (prefixWord ++ tailWord_896178).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896178).length < 2 ^ (prefixWord ++ tailWord_896178).sum := by decide
  have hdescent : baseEnd_896178 < baseStart_896178 := by decide
  rcases family_descends (prefixWord ++ tailWord_896178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896188 : List Nat := [2, 2, 2, 3, 2, 3, 2, 1, 3]
def baseStart_896188 : Nat := 118140960795 + 896188 * 2 ^ 59
def prefixEnd_896188 : Nat := 4983230072969 + 3 ^ 40 * 896188 * 2
def baseEnd_896188 : Nat := 409044622925906572469789

theorem tailTrace_896188 : CollatzResearch.WordTrace tailWord_896188 prefixEnd_896188 409044622925906572469789 := by
  unfold tailWord_896188
  simp only [CollatzResearch.WordTrace]
  refine ⟨16343330838635703785020609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21791107784847605046694145 16343330838635703785020609)
  ·
    refine ⟨12257498128976777838765457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16343330838635703785020609 12257498128976777838765457)
    ·
      refine ⟨9193123596732583379074093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12257498128976777838765457 9193123596732583379074093)
      ·
        refine ⟨3447421348774718767152785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9193123596732583379074093 3447421348774718767152785)
        ·
          refine ⟨2585566011581039075364589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3447421348774718767152785 2585566011581039075364589)
          ·
            refine ⟨969587254342889653261721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2585566011581039075364589 969587254342889653261721)
            ·
              refine ⟨727190440757167239946291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 969587254342889653261721 727190440757167239946291)
              ·
                refine ⟨1090785661135750859919437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 727190440757167239946291 1090785661135750859919437)
                ·
                  refine ⟨409044622925906572469789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1090785661135750859919437 409044622925906572469789)
                  ·
                    rfl

theorem cell20_896188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 2, 1, 3].length) (baseStart_896188 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_896188 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_896188 prefixEnd_896188 := by exact prefixLift 896188
  have htrace : WordTrace (prefixWord ++ tailWord_896188) baseStart_896188 baseEnd_896188 := by
    simpa [prefixWord, tailWord_896188, baseEnd_896188] using wordTrace_append hprefix tailTrace_896188
  have hstable : (prefixWord ++ tailWord_896188).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896188).length < 2 ^ (prefixWord ++ tailWord_896188).sum := by decide
  have hdescent : baseEnd_896188 < baseStart_896188 := by decide
  rcases family_descends (prefixWord ++ tailWord_896188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896227 : List Nat := [1, 1, 1, 17]
def baseStart_896227 : Nat := 118140960795 + 896227 * 2 ^ 59
def prefixEnd_896227 : Nat := 4983230072969 + 3 ^ 40 * 896227 * 2
def baseEnd_896227 : Nat := 1683384459212328272303

theorem tailTrace_896227 : CollatzResearch.WordTrace tailWord_896227 prefixEnd_896227 1683384459212328272303 := by
  unfold tailWord_896227
  simp only [CollatzResearch.WordTrace]
  refine ⟨32688084124130117230710935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21792056082753411487140623 32688084124130117230710935)
  ·
    refine ⟨49032126186195175846066403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32688084124130117230710935 49032126186195175846066403)
    ·
      refine ⟨73548189279292763769099605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49032126186195175846066403 73548189279292763769099605)
      ·
        refine ⟨1683384459212328272303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 17 73548189279292763769099605 1683384459212328272303)
        ·
          rfl

theorem cell20_896227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 17].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 17].length) (baseStart_896227 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_896227 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_896227 prefixEnd_896227 := by exact prefixLift 896227
  have htrace : WordTrace (prefixWord ++ tailWord_896227) baseStart_896227 baseEnd_896227 := by
    simpa [prefixWord, tailWord_896227, baseEnd_896227] using wordTrace_append hprefix tailTrace_896227
  have hstable : (prefixWord ++ tailWord_896227).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896227).length < 2 ^ (prefixWord ++ tailWord_896227).sum := by decide
  have hdescent : baseEnd_896227 < baseStart_896227 := by decide
  rcases family_descends (prefixWord ++ tailWord_896227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896229 : List Nat := [1, 3, 1, 4, 4, 1, 2, 2, 2]
def baseStart_896229 : Nat := 118140960795 + 896229 * 2 ^ 59
def prefixEnd_896229 : Nat := 4983230072969 + 3 ^ 40 * 896229 * 2
def baseEnd_896229 : Nat := 409063336443092652102955

theorem tailTrace_896229 : CollatzResearch.WordTrace tailWord_896229 prefixEnd_896229 409063336443092652102955 := by
  unfold tailWord_896229
  simp only [CollatzResearch.WordTrace]
  refine ⟨32688157070122871572283741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21792104713415247714855827 32688157070122871572283741)
  ·
    refine ⟨12258058901296076839606403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32688157070122871572283741 12258058901296076839606403)
    ·
      refine ⟨18387088351944115259409605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12258058901296076839606403 18387088351944115259409605)
      ·
        refine ⟨3447579065989521611139301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18387088351944115259409605 3447579065989521611139301)
        ·
          refine ⟨646421074873035302088619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3447579065989521611139301 646421074873035302088619)
          ·
            refine ⟨969631612309552953132929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 646421074873035302088619 969631612309552953132929)
            ·
              refine ⟨727223709232164714849697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 969631612309552953132929 727223709232164714849697)
              ·
                refine ⟨545417781924123536137273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 727223709232164714849697 545417781924123536137273)
                ·
                  refine ⟨409063336443092652102955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 545417781924123536137273 409063336443092652102955)
                  ·
                    rfl

theorem cell20_896229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 2, 2, 2].length) (baseStart_896229 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_896229 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_896229 prefixEnd_896229 := by exact prefixLift 896229
  have htrace : WordTrace (prefixWord ++ tailWord_896229) baseStart_896229 baseEnd_896229 := by
    simpa [prefixWord, tailWord_896229, baseEnd_896229] using wordTrace_append hprefix tailTrace_896229
  have hstable : (prefixWord ++ tailWord_896229).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896229).length < 2 ^ (prefixWord ++ tailWord_896229).sum := by decide
  have hdescent : baseEnd_896229 < baseStart_896229 := by decide
  rcases family_descends (prefixWord ++ tailWord_896229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896254 : List Nat := [4, 2, 2, 1, 1, 3, 1, 2, 4]
def baseStart_896254 : Nat := 118140960795 + 896254 * 2 ^ 59
def prefixEnd_896254 : Nat := 4983230072969 + 3 ^ 40 * 896254 * 2
def baseEnd_896254 : Nat := 409074747124303676269519

theorem tailTrace_896254 : CollatzResearch.WordTrace tailWord_896254 prefixEnd_896254 409074747124303676269519 := by
  unfold tailWord_896254
  simp only [CollatzResearch.WordTrace]
  refine ⟨4086133611879037605242977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21792712596688200561295877 4086133611879037605242977)
  ·
    refine ⟨3064600208909278203932233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4086133611879037605242977 3064600208909278203932233)
    ·
      refine ⟨2298450156681958652949175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3064600208909278203932233 2298450156681958652949175)
      ·
        refine ⟨3447675235022937979423763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2298450156681958652949175 3447675235022937979423763)
        ·
          refine ⟨5171512852534406969135645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3447675235022937979423763 5171512852534406969135645)
          ·
            refine ⟨1939317319700402613425867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5171512852534406969135645 1939317319700402613425867)
            ·
              refine ⟨2908975979550603920138801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1939317319700402613425867 2908975979550603920138801)
              ·
                refine ⟨2181731984662952940104101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2908975979550603920138801 2181731984662952940104101)
                ·
                  refine ⟨409074747124303676269519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2181731984662952940104101 409074747124303676269519)
                  ·
                    rfl

theorem cell20_896254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_896254 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_896254 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_896254 prefixEnd_896254 := by exact prefixLift 896254
  have htrace : WordTrace (prefixWord ++ tailWord_896254) baseStart_896254 baseEnd_896254 := by
    simpa [prefixWord, tailWord_896254, baseEnd_896254] using wordTrace_append hprefix tailTrace_896254
  have hstable : (prefixWord ++ tailWord_896254).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896254).length < 2 ^ (prefixWord ++ tailWord_896254).sum := by decide
  have hdescent : baseEnd_896254 < baseStart_896254 := by decide
  rcases family_descends (prefixWord ++ tailWord_896254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896282 : List Nat := [3, 1, 1, 3, 3, 2, 7]
def baseStart_896282 : Nat := 118140960795 + 896282 * 2 ^ 59
def prefixEnd_896282 : Nat := 4983230072969 + 3 ^ 40 * 896282 * 2
def baseEnd_896282 : Nat := 45454169676362224815119

theorem tailTrace_896282 : CollatzResearch.WordTrace tailWord_896282 prefixEnd_896282 45454169676362224815119 := by
  unfold tailWord_896282
  simp only [CollatzResearch.WordTrace]
  refine ⟨8172522534732715405990775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21793393425953907749308733 8172522534732715405990775)
  ·
    refine ⟨12258783802099073108986163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8172522534732715405990775 12258783802099073108986163)
    ·
      refine ⟨18388175703148609663479245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12258783802099073108986163 18388175703148609663479245)
      ·
        refine ⟨6895565888680728623804717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18388175703148609663479245 6895565888680728623804717)
        ·
          refine ⟨2585837208255273233926769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6895565888680728623804717 2585837208255273233926769)
          ·
            refine ⟨1939377906191454925445077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2585837208255273233926769 1939377906191454925445077)
            ·
              refine ⟨45454169676362224815119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1939377906191454925445077 45454169676362224815119)
              ·
                rfl

theorem cell20_896282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 7].length) (baseStart_896282 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_896282 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_896282 prefixEnd_896282 := by exact prefixLift 896282
  have htrace : WordTrace (prefixWord ++ tailWord_896282) baseStart_896282 baseEnd_896282 := by
    simpa [prefixWord, tailWord_896282, baseEnd_896282] using wordTrace_append hprefix tailTrace_896282
  have hstable : (prefixWord ++ tailWord_896282).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896282).length < 2 ^ (prefixWord ++ tailWord_896282).sum := by decide
  have hdescent : baseEnd_896282 < baseStart_896282 := by decide
  rcases family_descends (prefixWord ++ tailWord_896282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896285 : List Nat := [1, 4, 2, 3, 1, 1, 3, 2, 3]
def baseStart_896285 : Nat := 118140960795 + 896285 * 2 ^ 59
def prefixEnd_896285 : Nat := 4983230072969 + 3 ^ 40 * 896285 * 2
def baseEnd_896285 : Nat := 409088896369005346236059

theorem tailTrace_896285 : CollatzResearch.WordTrace tailWord_896285 prefixEnd_896285 409088896369005346236059 := by
  unfold tailWord_896285
  simp only [CollatzResearch.WordTrace]
  refine ⟨32690199557919993136322309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21793466371946662090881539 32690199557919993136322309)
  ·
    refine ⟨6129412417109998713060433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32690199557919993136322309 6129412417109998713060433)
    ·
      refine ⟨4597059312832499034795325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6129412417109998713060433 4597059312832499034795325)
      ·
        refine ⟨1723897242312187138048247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4597059312832499034795325 1723897242312187138048247)
        ·
          refine ⟨2585845863468280707072371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1723897242312187138048247 2585845863468280707072371)
          ·
            refine ⟨3878768795202421060608557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2585845863468280707072371 3878768795202421060608557)
            ·
              refine ⟨1454538298200907897728209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3878768795202421060608557 1454538298200907897728209)
              ·
                refine ⟨1090903723650680923296157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1454538298200907897728209 1090903723650680923296157)
                ·
                  refine ⟨409088896369005346236059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1090903723650680923296157 409088896369005346236059)
                  ·
                    rfl

theorem cell20_896285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 2, 3].length) (baseStart_896285 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_896285 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_896285 prefixEnd_896285 := by exact prefixLift 896285
  have htrace : WordTrace (prefixWord ++ tailWord_896285) baseStart_896285 baseEnd_896285 := by
    simpa [prefixWord, tailWord_896285, baseEnd_896285] using wordTrace_append hprefix tailTrace_896285
  have hstable : (prefixWord ++ tailWord_896285).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896285).length < 2 ^ (prefixWord ++ tailWord_896285).sum := by decide
  have hdescent : baseEnd_896285 < baseStart_896285 := by decide
  rcases family_descends (prefixWord ++ tailWord_896285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896292 : List Nat := [2, 3, 1, 3, 1, 1, 1, 6, 2]
def baseStart_896292 : Nat := 118140960795 + 896292 * 2 ^ 59
def prefixEnd_896292 : Nat := 4983230072969 + 3 ^ 40 * 896292 * 2
def baseEnd_896292 : Nat := 409092091359744433002697

theorem tailTrace_896292 : CollatzResearch.WordTrace tailWord_896292 prefixEnd_896292 409092091359744433002697 := by
  unfold tailWord_896292
  simp only [CollatzResearch.WordTrace]
  refine ⟨16345227434447316665913565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21793636579263088887884753 16345227434447316665913565)
  ·
    refine ⟨6129460287917743749717587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16345227434447316665913565 6129460287917743749717587)
    ·
      refine ⟨9194190431876615624576381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6129460287917743749717587 9194190431876615624576381)
      ·
        refine ⟨3447821411953730859216143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9194190431876615624576381 3447821411953730859216143)
        ·
          refine ⟨5171732117930596288824215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3447821411953730859216143 5171732117930596288824215)
          ·
            refine ⟨7757598176895894433236323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5171732117930596288824215 7757598176895894433236323)
            ·
              refine ⟨11636397265343841649854485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7757598176895894433236323 11636397265343841649854485)
              ·
                refine ⟨545456121812992577336929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11636397265343841649854485 545456121812992577336929)
                ·
                  refine ⟨409092091359744433002697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 545456121812992577336929 409092091359744433002697)
                  ·
                    rfl

theorem cell20_896292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 6, 2].length) (baseStart_896292 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_896292 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_896292 prefixEnd_896292 := by exact prefixLift 896292
  have htrace : WordTrace (prefixWord ++ tailWord_896292) baseStart_896292 baseEnd_896292 := by
    simpa [prefixWord, tailWord_896292, baseEnd_896292] using wordTrace_append hprefix tailTrace_896292
  have hstable : (prefixWord ++ tailWord_896292).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896292).length < 2 ^ (prefixWord ++ tailWord_896292).sum := by decide
  have hdescent : baseEnd_896292 < baseStart_896292 := by decide
  rcases family_descends (prefixWord ++ tailWord_896292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896303 : List Nat := [1, 1, 2, 1, 2, 1, 3, 9]
def baseStart_896303 : Nat := 118140960795 + 896303 * 2 ^ 59
def prefixEnd_896303 : Nat := 4983230072969 + 3 ^ 40 * 896303 * 2
def baseEnd_896303 : Nat := 136365704019825761211995

theorem tailTrace_896303 : CollatzResearch.WordTrace tailWord_896303 prefixEnd_896303 136365704019825761211995 := by
  unfold tailWord_896303
  simp only [CollatzResearch.WordTrace]
  refine ⟨32690856071854782210477563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21793904047903188140318375 32690856071854782210477563)
  ·
    refine ⟨49036284107782173315716345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32690856071854782210477563 49036284107782173315716345)
    ·
      refine ⟨36777213080836629986787259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49036284107782173315716345 36777213080836629986787259)
      ·
        refine ⟨55165819621254944980180889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36777213080836629986787259 55165819621254944980180889)
        ·
          refine ⟨41374364715941208735135667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55165819621254944980180889 41374364715941208735135667)
          ·
            refine ⟨62061547073911813102703501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41374364715941208735135667 62061547073911813102703501)
            ·
              refine ⟨23273080152716929913513813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62061547073911813102703501 23273080152716929913513813)
              ·
                refine ⟨136365704019825761211995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23273080152716929913513813 136365704019825761211995)
                ·
                  rfl

theorem cell20_896303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 9].length) (baseStart_896303 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_896303 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_896303 prefixEnd_896303 := by exact prefixLift 896303
  have htrace : WordTrace (prefixWord ++ tailWord_896303) baseStart_896303 baseEnd_896303 := by
    simpa [prefixWord, tailWord_896303, baseEnd_896303] using wordTrace_append hprefix tailTrace_896303
  have hstable : (prefixWord ++ tailWord_896303).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896303).length < 2 ^ (prefixWord ++ tailWord_896303).sum := by decide
  have hdescent : baseEnd_896303 < baseStart_896303 := by decide
  rcases family_descends (prefixWord ++ tailWord_896303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896327 : List Nat := [1, 1, 4, 1, 2, 3, 1, 2, 5]
def baseStart_896327 : Nat := 118140960795 + 896327 * 2 ^ 59
def prefixEnd_896327 : Nat := 4983230072969 + 3 ^ 40 * 896327 * 2
def baseEnd_896327 : Nat := 409108066313439866835887

theorem tailTrace_896327 : CollatzResearch.WordTrace tailWord_896327 prefixEnd_896327 409108066313439866835887 := by
  unfold tailWord_896327
  simp only [CollatzResearch.WordTrace]
  refine ⟨32691731423767834309351235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21794487615845222872900823 32691731423767834309351235)
  ·
    refine ⟨49037597135651751464026853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32691731423767834309351235 49037597135651751464026853)
    ·
      refine ⟨9194549462934703399505035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49037597135651751464026853 9194549462934703399505035)
      ·
        refine ⟨13791824194402055099257553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9194549462934703399505035 13791824194402055099257553)
        ·
          refine ⟨10343868145801541324443165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13791824194402055099257553 10343868145801541324443165)
          ·
            refine ⟨3878950554675577996666187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10343868145801541324443165 3878950554675577996666187)
            ·
              refine ⟨5818425832013366994999281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3878950554675577996666187 5818425832013366994999281)
              ·
                refine ⟨4363819374010025246249461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5818425832013366994999281 4363819374010025246249461)
                ·
                  refine ⟨409108066313439866835887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4363819374010025246249461 409108066313439866835887)
                  ·
                    rfl

theorem cell20_896327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 2, 5].length) (baseStart_896327 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_896327 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_896327 prefixEnd_896327 := by exact prefixLift 896327
  have htrace : WordTrace (prefixWord ++ tailWord_896327) baseStart_896327 baseEnd_896327 := by
    simpa [prefixWord, tailWord_896327, baseEnd_896327] using wordTrace_append hprefix tailTrace_896327
  have hstable : (prefixWord ++ tailWord_896327).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896327).length < 2 ^ (prefixWord ++ tailWord_896327).sum := by decide
  have hdescent : baseEnd_896327 < baseStart_896327 := by decide
  rcases family_descends (prefixWord ++ tailWord_896327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896333 : List Nat := [1, 6, 1, 3, 2, 1, 6]
def baseStart_896333 : Nat := 118140960795 + 896333 * 2 ^ 59
def prefixEnd_896333 : Nat := 4983230072969 + 3 ^ 40 * 896333 * 2
def baseEnd_896333 : Nat := 45456756097436723626207

theorem tailTrace_896333 : CollatzResearch.WordTrace tailWord_896333 prefixEnd_896333 45456756097436723626207 := by
  unfold tailWord_896333
  simp only [CollatzResearch.WordTrace]
  refine ⟨32691950261746097334069653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21794633507830731556046435 32691950261746097334069653)
  ·
    refine ⟨1532435168519348312534515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 32691950261746097334069653 1532435168519348312534515)
    ·
      refine ⟨2298652752779022468801773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1532435168519348312534515 2298652752779022468801773)
      ·
        refine ⟨861994782292133425800665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2298652752779022468801773 861994782292133425800665)
        ·
          refine ⟨646496086719100069350499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 861994782292133425800665 646496086719100069350499)
          ·
            refine ⟨969744130078650104025749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 646496086719100069350499 969744130078650104025749)
            ·
              refine ⟨45456756097436723626207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 969744130078650104025749 45456756097436723626207)
              ·
                rfl

theorem cell20_896333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 6].length) (baseStart_896333 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_896333 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_896333 prefixEnd_896333 := by exact prefixLift 896333
  have htrace : WordTrace (prefixWord ++ tailWord_896333) baseStart_896333 baseEnd_896333 := by
    simpa [prefixWord, tailWord_896333, baseEnd_896333] using wordTrace_append hprefix tailTrace_896333
  have hstable : (prefixWord ++ tailWord_896333).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896333).length < 2 ^ (prefixWord ++ tailWord_896333).sum := by decide
  have hdescent : baseEnd_896333 < baseStart_896333 := by decide
  rcases family_descends (prefixWord ++ tailWord_896333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896379 : List Nat := [1, 1, 1, 1, 1, 6, 1, 8]
def baseStart_896379 : Nat := 118140960795 + 896379 * 2 ^ 59
def prefixEnd_896379 : Nat := 4983230072969 + 3 ^ 40 * 896379 * 2
def baseEnd_896379 : Nat := 136377266843452932367447

theorem tailTrace_896379 : CollatzResearch.WordTrace tailWord_896379 prefixEnd_896379 136377266843452932367447 := by
  unfold tailWord_896379
  simp only [CollatzResearch.WordTrace]
  refine ⟨32693628019579447190244191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21795752013052964793496127 32693628019579447190244191)
  ·
    refine ⟨49040442029369170785366287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32693628019579447190244191 49040442029369170785366287)
    ·
      refine ⟨73560663044053756178049431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49040442029369170785366287 73560663044053756178049431)
      ·
        refine ⟨110340994566080634267074147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73560663044053756178049431 110340994566080634267074147)
        ·
          refine ⟨165511491849120951400611221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110340994566080634267074147 165511491849120951400611221)
          ·
            refine ⟨7758351180427544596903651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 165511491849120951400611221 7758351180427544596903651)
            ·
              refine ⟨11637526770641316895355477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7758351180427544596903651 11637526770641316895355477)
              ·
                refine ⟨136377266843452932367447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11637526770641316895355477 136377266843452932367447)
                ·
                  rfl

theorem cell20_896379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 8].length) (baseStart_896379 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_896379 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_896379 prefixEnd_896379 := by exact prefixLift 896379
  have htrace : WordTrace (prefixWord ++ tailWord_896379) baseStart_896379 baseEnd_896379 := by
    simpa [prefixWord, tailWord_896379, baseEnd_896379] using wordTrace_append hprefix tailTrace_896379
  have hstable : (prefixWord ++ tailWord_896379).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896379).length < 2 ^ (prefixWord ++ tailWord_896379).sum := by decide
  have hdescent : baseEnd_896379 < baseStart_896379 := by decide
  rcases family_descends (prefixWord ++ tailWord_896379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896402 : List Nat := [3, 2, 3, 3, 1, 1, 1, 4, 2]
def baseStart_896402 : Nat := 118140960795 + 896402 * 2 ^ 59
def prefixEnd_896402 : Nat := 4983230072969 + 3 ^ 40 * 896402 * 2
def baseEnd_896402 : Nat := 409142298357072939335581

theorem tailTrace_896402 : CollatzResearch.WordTrace tailWord_896402 prefixEnd_896402 409142298357072939335581 := by
  unfold tailWord_896402
  simp only [CollatzResearch.WordTrace]
  refine ⟨8173616724624030529582865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21796311265664081412220973 8173616724624030529582865)
  ·
    refine ⟨6130212543468022897187149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8173616724624030529582865 6130212543468022897187149)
    ·
      refine ⟨2298829703800508586445181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6130212543468022897187149 2298829703800508586445181)
      ·
        refine ⟨862061138925190719916943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2298829703800508586445181 862061138925190719916943)
        ·
          refine ⟨1293091708387786079875415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 862061138925190719916943 1293091708387786079875415)
          ·
            refine ⟨1939637562581679119813123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1293091708387786079875415 1939637562581679119813123)
            ·
              refine ⟨2909456343872518679719685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1939637562581679119813123 2909456343872518679719685)
              ·
                refine ⟨545523064476097252447441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2909456343872518679719685 545523064476097252447441)
                ·
                  refine ⟨409142298357072939335581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 545523064476097252447441 409142298357072939335581)
                  ·
                    rfl

theorem cell20_896402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 4, 2].length) (baseStart_896402 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_896402 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_896402 prefixEnd_896402 := by exact prefixLift 896402
  have htrace : WordTrace (prefixWord ++ tailWord_896402) baseStart_896402 baseEnd_896402 := by
    simpa [prefixWord, tailWord_896402, baseEnd_896402] using wordTrace_append hprefix tailTrace_896402
  have hstable : (prefixWord ++ tailWord_896402).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896402).length < 2 ^ (prefixWord ++ tailWord_896402).sum := by decide
  have hdescent : baseEnd_896402 < baseStart_896402 := by decide
  rcases family_descends (prefixWord ++ tailWord_896402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896413 : List Nat := [1, 4, 2, 1, 3, 3, 1, 5]
def baseStart_896413 : Nat := 118140960795 + 896413 * 2 ^ 59
def prefixEnd_896413 : Nat := 4983230072969 + 3 ^ 40 * 896413 * 2
def baseEnd_896413 : Nat := 136382439685601929989623

theorem tailTrace_896413 : CollatzResearch.WordTrace tailWord_896413 prefixEnd_896413 136382439685601929989623 := by
  unfold tailWord_896413
  simp only [CollatzResearch.WordTrace]
  refine ⟨32694868101456270996981893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21796578734304180664654595 32694868101456270996981893)
  ·
    refine ⟨6130287769023050811934105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32694868101456270996981893 6130287769023050811934105)
    ·
      refine ⟨4597715826767288108950579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6130287769023050811934105 4597715826767288108950579)
      ·
        refine ⟨6896573740150932163425869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4597715826767288108950579 6896573740150932163425869)
        ·
          refine ⟨2586215152556599561284701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6896573740150932163425869 2586215152556599561284701)
          ·
            refine ⟨969830682208724835481763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2586215152556599561284701 969830682208724835481763)
            ·
              refine ⟨1454746023313087253222645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 969830682208724835481763 1454746023313087253222645)
              ·
                refine ⟨136382439685601929989623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1454746023313087253222645 136382439685601929989623)
                ·
                  rfl

theorem cell20_896413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 5].length) (baseStart_896413 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_896413 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_896413 prefixEnd_896413 := by exact prefixLift 896413
  have htrace : WordTrace (prefixWord ++ tailWord_896413) baseStart_896413 baseEnd_896413 := by
    simpa [prefixWord, tailWord_896413, baseEnd_896413] using wordTrace_append hprefix tailTrace_896413
  have hstable : (prefixWord ++ tailWord_896413).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896413).length < 2 ^ (prefixWord ++ tailWord_896413).sum := by decide
  have hdescent : baseEnd_896413 < baseStart_896413 := by decide
  rcases family_descends (prefixWord ++ tailWord_896413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896455 : List Nat := [1, 1, 4, 1, 1, 3, 9]
def baseStart_896455 : Nat := 118140960795 + 896455 * 2 ^ 59
def prefixEnd_896455 : Nat := 4983230072969 + 3 ^ 40 * 896455 * 2
def baseEnd_896455 : Nat := 45462943222360034507633

theorem tailTrace_896455 : CollatzResearch.WordTrace tailWord_896455 prefixEnd_896455 45462943222360034507633 := by
  unfold tailWord_896455
  simp only [CollatzResearch.WordTrace]
  refine ⟨32696399967304112170010819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21797599978202741446673879 32696399967304112170010819)
  ·
    refine ⟨49044599950956168255016229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32696399967304112170010819 49044599950956168255016229)
    ·
      refine ⟨9195862490804281547815543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49044599950956168255016229 9195862490804281547815543)
      ·
        refine ⟨13793793736206422321723315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9195862490804281547815543 13793793736206422321723315)
        ·
          refine ⟨20690690604309633482584973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13793793736206422321723315 20690690604309633482584973)
          ·
            refine ⟨7759008976616112555969365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20690690604309633482584973 7759008976616112555969365)
            ·
              refine ⟨45462943222360034507633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7759008976616112555969365 45462943222360034507633)
              ·
                rfl

theorem cell20_896455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 9].length) (baseStart_896455 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_896455 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_896455 prefixEnd_896455 := by exact prefixLift 896455
  have htrace : WordTrace (prefixWord ++ tailWord_896455) baseStart_896455 baseEnd_896455 := by
    simpa [prefixWord, tailWord_896455, baseEnd_896455] using wordTrace_append hprefix tailTrace_896455
  have hstable : (prefixWord ++ tailWord_896455).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896455).length < 2 ^ (prefixWord ++ tailWord_896455).sum := by decide
  have hdescent : baseEnd_896455 < baseStart_896455 := by decide
  rcases family_descends (prefixWord ++ tailWord_896455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896458 : List Nat := [3, 1, 2, 1, 2, 3, 3, 2, 3]
def baseStart_896458 : Nat := 118140960795 + 896458 * 2 ^ 59
def prefixEnd_896458 : Nat := 4983230072969 + 3 ^ 40 * 896458 * 2
def baseEnd_896458 : Nat := 409167858282985633468685

theorem tailTrace_896458 : CollatzResearch.WordTrace tailWord_896458 prefixEnd_896458 409167858282985633468685 := by
  unfold tailWord_896458
  simp only [CollatzResearch.WordTrace]
  refine ⟨8174127346573310920592507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21797672924195495788246685 8174127346573310920592507)
  ·
    refine ⟨12261191019859966380888761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8174127346573310920592507 12261191019859966380888761)
    ·
      refine ⟨9195893264894974785666571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12261191019859966380888761 9195893264894974785666571)
      ·
        refine ⟨13793839897342462178499857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9195893264894974785666571 13793839897342462178499857)
        ·
          refine ⟨10345379923006846633874893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13793839897342462178499857 10345379923006846633874893)
          ·
            refine ⟨3879517471127567487703085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10345379923006846633874893 3879517471127567487703085)
            ·
              refine ⟨1454819051672837807888657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3879517471127567487703085 1454819051672837807888657)
              ·
                refine ⟨1091114288754628355916493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1454819051672837807888657 1091114288754628355916493)
                ·
                  refine ⟨409167858282985633468685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1091114288754628355916493 409167858282985633468685)
                  ·
                    rfl

theorem cell20_896458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 2, 3].length) (baseStart_896458 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_896458 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_896458 prefixEnd_896458 := by exact prefixLift 896458
  have htrace : WordTrace (prefixWord ++ tailWord_896458) baseStart_896458 baseEnd_896458 := by
    simpa [prefixWord, tailWord_896458, baseEnd_896458] using wordTrace_append hprefix tailTrace_896458
  have hstable : (prefixWord ++ tailWord_896458).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896458).length < 2 ^ (prefixWord ++ tailWord_896458).sum := by decide
  have hdescent : baseEnd_896458 < baseStart_896458 := by decide
  rcases family_descends (prefixWord ++ tailWord_896458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896503 : List Nat := [1, 1, 3, 1, 1, 1, 1, 9, 2]
def baseStart_896503 : Nat := 118140960795 + 896503 * 2 ^ 59
def prefixEnd_896503 : Nat := 4983230072969 + 3 ^ 40 * 896503 * 2
def baseEnd_896503 : Nat := 409188397509165476968501

theorem tailTrace_896503 : CollatzResearch.WordTrace tailWord_896503 prefixEnd_896503 409188397509165476968501 := by
  unfold tailWord_896503
  simp only [CollatzResearch.WordTrace]
  refine ⟨32698150671130216367758163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21798767114086810911838775 32698150671130216367758163)
  ·
    refine ⟨49047226006695324551637245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32698150671130216367758163 49047226006695324551637245)
    ·
      refine ⟨18392709752510746706863967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49047226006695324551637245 18392709752510746706863967)
      ·
        refine ⟨27589064628766120060295951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18392709752510746706863967 27589064628766120060295951)
        ·
          refine ⟨41383596943149180090443927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27589064628766120060295951 41383596943149180090443927)
          ·
            refine ⟨62075395414723770135665891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41383596943149180090443927 62075395414723770135665891)
            ·
              refine ⟨93113093122085655203498837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62075395414723770135665891 93113093122085655203498837)
              ·
                refine ⟨545584530012220635958001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 93113093122085655203498837 545584530012220635958001)
                ·
                  refine ⟨409188397509165476968501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 545584530012220635958001 409188397509165476968501)
                  ·
                    rfl

theorem cell20_896503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 9, 2].length) (baseStart_896503 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_896503 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_896503 prefixEnd_896503 := by exact prefixLift 896503
  have htrace : WordTrace (prefixWord ++ tailWord_896503) baseStart_896503 baseEnd_896503 := by
    simpa [prefixWord, tailWord_896503, baseEnd_896503] using wordTrace_append hprefix tailTrace_896503
  have hstable : (prefixWord ++ tailWord_896503).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896503).length < 2 ^ (prefixWord ++ tailWord_896503).sum := by decide
  have hdescent : baseEnd_896503 < baseStart_896503 := by decide
  rcases family_descends (prefixWord ++ tailWord_896503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896516 : List Nat := [2, 3, 2, 3, 2, 1, 3, 2, 2]
def baseStart_896516 : Nat := 118140960795 + 896516 * 2 ^ 59
def prefixEnd_896516 : Nat := 4983230072969 + 3 ^ 40 * 896516 * 2
def baseEnd_896516 : Nat := 409194331063395209535115

theorem tailTrace_896516 : CollatzResearch.WordTrace tailWord_896516 prefixEnd_896516 409194331063395209535115 := by
  unfold tailWord_896516
  simp only [CollatzResearch.WordTrace]
  refine ⟨16349312410041559793990701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21799083213388746391987601 16349312410041559793990701)
  ·
    refine ⟨6130992153765584922746513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16349312410041559793990701 6130992153765584922746513)
    ·
      refine ⟨4598244115324188692059885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6130992153765584922746513 4598244115324188692059885)
      ·
        refine ⟨1724341543246570759522457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4598244115324188692059885 1724341543246570759522457)
        ·
          refine ⟨1293256157434928069641843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1724341543246570759522457 1293256157434928069641843)
          ·
            refine ⟨1939884236152392104462765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1293256157434928069641843 1939884236152392104462765)
            ·
              refine ⟨727456588557147039173537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1939884236152392104462765 727456588557147039173537)
              ·
                refine ⟨545592441417860279380153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 727456588557147039173537 545592441417860279380153)
                ·
                  refine ⟨409194331063395209535115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 545592441417860279380153 409194331063395209535115)
                  ·
                    rfl

theorem cell20_896516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 3, 2, 2].length) (baseStart_896516 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_896516 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_896516 prefixEnd_896516 := by exact prefixLift 896516
  have htrace : WordTrace (prefixWord ++ tailWord_896516) baseStart_896516 baseEnd_896516 := by
    simpa [prefixWord, tailWord_896516, baseEnd_896516] using wordTrace_append hprefix tailTrace_896516
  have hstable : (prefixWord ++ tailWord_896516).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896516).length < 2 ^ (prefixWord ++ tailWord_896516).sum := by decide
  have hdescent : baseEnd_896516 < baseStart_896516 := by decide
  rcases family_descends (prefixWord ++ tailWord_896516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896517 : List Nat := [1, 3, 1, 1, 2, 2, 1, 6, 3]
def baseStart_896517 : Nat := 118140960795 + 896517 * 2 ^ 59
def prefixEnd_896517 : Nat := 4983230072969 + 3 ^ 40 * 896517 * 2
def baseEnd_896517 : Nat := 409194787490643650501777

theorem tailTrace_896517 : CollatzResearch.WordTrace tailWord_896517 prefixEnd_896517 409194787490643650501777 := by
  unfold tailWord_896517
  simp only [CollatzResearch.WordTrace]
  refine ⟨32698661293079496758767805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21799107528719664505845203 32698661293079496758767805)
  ·
    refine ⟨12261997984904811284537927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32698661293079496758767805 12261997984904811284537927)
    ·
      refine ⟨18392996977357216926806891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12261997984904811284537927 18392996977357216926806891)
      ·
        refine ⟨27589495466035825390210337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18392996977357216926806891 27589495466035825390210337)
        ·
          refine ⟨20692121599526869042657753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27589495466035825390210337 20692121599526869042657753)
          ·
            refine ⟨15519091199645151781993315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20692121599526869042657753 15519091199645151781993315)
            ·
              refine ⟨23278636799467727672989973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15519091199645151781993315 23278636799467727672989973)
              ·
                refine ⟨1091186099975049734671405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23278636799467727672989973 1091186099975049734671405)
                ·
                  refine ⟨409194787490643650501777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1091186099975049734671405 409194787490643650501777)
                  ·
                    rfl

theorem cell20_896517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 6, 3].length) (baseStart_896517 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_896517 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_896517 prefixEnd_896517 := by exact prefixLift 896517
  have htrace : WordTrace (prefixWord ++ tailWord_896517) baseStart_896517 baseEnd_896517 := by
    simpa [prefixWord, tailWord_896517, baseEnd_896517] using wordTrace_append hprefix tailTrace_896517
  have hstable : (prefixWord ++ tailWord_896517).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896517).length < 2 ^ (prefixWord ++ tailWord_896517).sum := by decide
  have hdescent : baseEnd_896517 < baseStart_896517 := by decide
  rcases family_descends (prefixWord ++ tailWord_896517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896531 : List Nat := [1, 1, 1, 2, 1, 6, 1, 7]
def baseStart_896531 : Nat := 118140960795 + 896531 * 2 ^ 59
def prefixEnd_896531 : Nat := 4983230072969 + 3 ^ 40 * 896531 * 2
def baseEnd_896531 : Nat := 136400392490707274678351

theorem tailTrace_896531 : CollatzResearch.WordTrace tailWord_896531 prefixEnd_896531 136400392490707274678351 := by
  unfold tailWord_896531
  simp only [CollatzResearch.WordTrace]
  refine ⟨32699171915028777149777447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21799447943352518099851631 32699171915028777149777447)
  ·
    refine ⟨49048757872543165724666171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32699171915028777149777447 49048757872543165724666171)
    ·
      refine ⟨73573136808814748586999257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49048757872543165724666171 73573136808814748586999257)
      ·
        refine ⟨55179852606611061440249443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73573136808814748586999257 55179852606611061440249443)
        ·
          refine ⟨82769778909916592160374165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55179852606611061440249443 82769778909916592160374165)
          ·
            refine ⟨3879833386402340257517539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 82769778909916592160374165 3879833386402340257517539)
            ·
              refine ⟨5819750079603510386276309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3879833386402340257517539 5819750079603510386276309)
              ·
                refine ⟨136400392490707274678351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5819750079603510386276309 136400392490707274678351)
                ·
                  rfl

theorem cell20_896531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 7].length) (baseStart_896531 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_896531 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_896531 prefixEnd_896531 := by exact prefixLift 896531
  have htrace : WordTrace (prefixWord ++ tailWord_896531) baseStart_896531 baseEnd_896531 := by
    simpa [prefixWord, tailWord_896531, baseEnd_896531] using wordTrace_append hprefix tailTrace_896531
  have hstable : (prefixWord ++ tailWord_896531).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896531).length < 2 ^ (prefixWord ++ tailWord_896531).sum := by decide
  have hdescent : baseEnd_896531 < baseStart_896531 := by decide
  rcases family_descends (prefixWord ++ tailWord_896531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896569 : List Nat := [1, 2, 1, 5, 1, 10]
def baseStart_896569 : Nat := 118140960795 + 896569 * 2 ^ 59
def prefixEnd_896569 : Nat := 4983230072969 + 3 ^ 40 * 896569 * 2
def baseEnd_896569 : Nat := 15156241544724540028453

theorem tailTrace_896569 : CollatzResearch.WordTrace tailWord_896569 prefixEnd_896569 15156241544724540028453 := by
  unfold tailWord_896569
  simp only [CollatzResearch.WordTrace]
  refine ⟨32700557888891109639660761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21800371925927406426440507 32700557888891109639660761)
  ·
    refine ⟨24525418416668332229745571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32700557888891109639660761 24525418416668332229745571)
    ·
      refine ⟨36788127625002498344618357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24525418416668332229745571 36788127625002498344618357)
      ·
        refine ⟨3448886964843984219807971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36788127625002498344618357 3448886964843984219807971)
        ·
          refine ⟨5173330447265976329711957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3448886964843984219807971 5173330447265976329711957)
          ·
            refine ⟨15156241544724540028453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5173330447265976329711957 15156241544724540028453)
            ·
              rfl

theorem cell20_896569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 10].length) (baseStart_896569 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_896569 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_896569 prefixEnd_896569 := by exact prefixLift 896569
  have htrace : WordTrace (prefixWord ++ tailWord_896569) baseStart_896569 baseEnd_896569 := by
    simpa [prefixWord, tailWord_896569, baseEnd_896569] using wordTrace_append hprefix tailTrace_896569
  have hstable : (prefixWord ++ tailWord_896569).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896569).length < 2 ^ (prefixWord ++ tailWord_896569).sum := by decide
  have hdescent : baseEnd_896569 < baseStart_896569 := by decide
  rcases family_descends (prefixWord ++ tailWord_896569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896575 : List Nat := [1, 1, 2, 2, 3, 5, 2, 2, 2]
def baseStart_896575 : Nat := 118140960795 + 896575 * 2 ^ 59
def prefixEnd_896575 : Nat := 4983230072969 + 3 ^ 40 * 896575 * 2
def baseEnd_896575 : Nat := 409221260271053226568207

theorem tailTrace_896575 : CollatzResearch.WordTrace tailWord_896575 prefixEnd_896575 409221260271053226568207 := by
  unfold tailWord_896575
  simp only [CollatzResearch.WordTrace]
  refine ⟨32700776726869372664379179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21800517817912915109586119 32700776726869372664379179)
  ·
    refine ⟨49051165090304058996568769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32700776726869372664379179 49051165090304058996568769)
    ·
      refine ⟨36788373817728044247426577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49051165090304058996568769 36788373817728044247426577)
      ·
        refine ⟨27591280363296033185569933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36788373817728044247426577 27591280363296033185569933)
        ·
          refine ⟨10346730136236012444588725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27591280363296033185569933 10346730136236012444588725)
          ·
            refine ⟨970005950272126166680193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10346730136236012444588725 970005950272126166680193)
            ·
              refine ⟨727504462704094625010145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 970005950272126166680193 727504462704094625010145)
              ·
                refine ⟨545628347028070968757609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 727504462704094625010145 545628347028070968757609)
                ·
                  refine ⟨409221260271053226568207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 545628347028070968757609 409221260271053226568207)
                  ·
                    rfl

theorem cell20_896575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 2, 2, 2].length) (baseStart_896575 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_896575 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_896575 prefixEnd_896575 := by exact prefixLift 896575
  have htrace : WordTrace (prefixWord ++ tailWord_896575) baseStart_896575 baseEnd_896575 := by
    simpa [prefixWord, tailWord_896575, baseEnd_896575] using wordTrace_append hprefix tailTrace_896575
  have hstable : (prefixWord ++ tailWord_896575).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896575).length < 2 ^ (prefixWord ++ tailWord_896575).sum := by decide
  have hdescent : baseEnd_896575 < baseStart_896575 := by decide
  rcases family_descends (prefixWord ++ tailWord_896575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896593 : List Nat := [1, 2, 2, 1, 3, 2, 1, 5, 3]
def baseStart_896593 : Nat := 118140960795 + 896593 * 2 ^ 59
def prefixEnd_896593 : Nat := 4983230072969 + 3 ^ 40 * 896593 * 2
def baseEnd_896593 : Nat := 409229475961525163968133

theorem tailTrace_896593 : CollatzResearch.WordTrace tailWord_896593 prefixEnd_896593 409229475961525163968133 := by
  unfold tailWord_896593
  simp only [CollatzResearch.WordTrace]
  refine ⟨32701433240804161738534433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21800955493869441159022955 32701433240804161738534433)
  ·
    refine ⟨24526074930603121303900825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32701433240804161738534433 24526074930603121303900825)
    ·
      refine ⟨18394556197952340977925619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24526074930603121303900825 18394556197952340977925619)
      ·
        refine ⟨27591834296928511466888429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18394556197952340977925619 27591834296928511466888429)
        ·
          refine ⟨10346937861348191800083161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27591834296928511466888429 10346937861348191800083161)
          ·
            refine ⟨7760203396011143850062371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10346937861348191800083161 7760203396011143850062371)
            ·
              refine ⟨11640305094016715775093557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7760203396011143850062371 11640305094016715775093557)
              ·
                refine ⟨1091278602564067103915021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11640305094016715775093557 1091278602564067103915021)
                ·
                  refine ⟨409229475961525163968133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1091278602564067103915021 409229475961525163968133)
                  ·
                    rfl

theorem cell20_896593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 5, 3].length) (baseStart_896593 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_896593 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_896593 prefixEnd_896593 := by exact prefixLift 896593
  have htrace : WordTrace (prefixWord ++ tailWord_896593) baseStart_896593 baseEnd_896593 := by
    simpa [prefixWord, tailWord_896593, baseEnd_896593] using wordTrace_append hprefix tailTrace_896593
  have hstable : (prefixWord ++ tailWord_896593).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896593).length < 2 ^ (prefixWord ++ tailWord_896593).sum := by decide
  have hdescent : baseEnd_896593 < baseStart_896593 := by decide
  rcases family_descends (prefixWord ++ tailWord_896593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896617 : List Nat := [1, 2, 1, 1, 1, 4, 3, 5, 2]
def baseStart_896617 : Nat := 118140960795 + 896617 * 2 ^ 59
def prefixEnd_896617 : Nat := 4983230072969 + 3 ^ 40 * 896617 * 2
def baseEnd_896617 : Nat := 409240430215487747168035

theorem tailTrace_896617 : CollatzResearch.WordTrace tailWord_896617 prefixEnd_896617 409240430215487747168035 := by
  unfold tailWord_896617
  simp only [CollatzResearch.WordTrace]
  refine ⟨32702308592717213837408105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21801539061811475891605403 32702308592717213837408105)
  ·
    refine ⟨24526731444537910378056079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32702308592717213837408105 24526731444537910378056079)
    ·
      refine ⟨36790097166806865567084119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24526731444537910378056079 36790097166806865567084119)
      ·
        refine ⟨55185145750210298350626179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36790097166806865567084119 55185145750210298350626179)
        ·
          refine ⟨82777718625315447525939269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55185145750210298350626179 82777718625315447525939269)
          ·
            refine ⟨15520822242246646411113613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82777718625315447525939269 15520822242246646411113613)
            ·
              refine ⟨5820308340842492404167605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15520822242246646411113613 5820308340842492404167605)
              ·
                refine ⟨545653906953983662890713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5820308340842492404167605 545653906953983662890713)
                ·
                  refine ⟨409240430215487747168035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 545653906953983662890713 409240430215487747168035)
                  ·
                    rfl

theorem cell20_896617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 5, 2].length) (baseStart_896617 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_896617 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_896617 prefixEnd_896617 := by exact prefixLift 896617
  have htrace : WordTrace (prefixWord ++ tailWord_896617) baseStart_896617 baseEnd_896617 := by
    simpa [prefixWord, tailWord_896617, baseEnd_896617] using wordTrace_append hprefix tailTrace_896617
  have hstable : (prefixWord ++ tailWord_896617).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896617).length < 2 ^ (prefixWord ++ tailWord_896617).sum := by decide
  have hdescent : baseEnd_896617 < baseStart_896617 := by decide
  rcases family_descends (prefixWord ++ tailWord_896617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896645 : List Nat := [1, 3, 1, 1, 4, 1, 2, 7]
def baseStart_896645 : Nat := 118140960795 + 896645 * 2 ^ 59
def prefixEnd_896645 : Nat := 4983230072969 + 3 ^ 40 * 896645 * 2
def baseEnd_896645 : Nat := 136417736726148031411529

theorem tailTrace_896645 : CollatzResearch.WordTrace tailWord_896645 prefixEnd_896645 136417736726148031411529 := by
  unfold tailWord_896645
  simp only [CollatzResearch.WordTrace]
  refine ⟨32703329836615774619427389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21802219891077183079618259 32703329836615774619427389)
  ·
    refine ⟨12263748688730915482285271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32703329836615774619427389 12263748688730915482285271)
    ·
      refine ⟨18395623033096373223427907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12263748688730915482285271 18395623033096373223427907)
      ·
        refine ⟨27593434549644559835141861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18395623033096373223427907 27593434549644559835141861)
        ·
          refine ⟨5173768978058354969089099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27593434549644559835141861 5173768978058354969089099)
          ·
            refine ⟨7760653467087532453633649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5173768978058354969089099 7760653467087532453633649)
            ·
              refine ⟨5820490100315649340225237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7760653467087532453633649 5820490100315649340225237)
              ·
                refine ⟨136417736726148031411529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5820490100315649340225237 136417736726148031411529)
                ·
                  rfl

theorem cell20_896645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 7].length) (baseStart_896645 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_896645 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_896645 prefixEnd_896645 := by exact prefixLift 896645
  have htrace : WordTrace (prefixWord ++ tailWord_896645) baseStart_896645 baseEnd_896645 := by
    simpa [prefixWord, tailWord_896645, baseEnd_896645] using wordTrace_append hprefix tailTrace_896645
  have hstable : (prefixWord ++ tailWord_896645).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896645).length < 2 ^ (prefixWord ++ tailWord_896645).sum := by decide
  have hdescent : baseEnd_896645 < baseStart_896645 := by decide
  rcases family_descends (prefixWord ++ tailWord_896645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896658 : List Nat := [3, 2, 3, 1, 3, 2, 2, 4]
def baseStart_896658 : Nat := 118140960795 + 896658 * 2 ^ 59
def prefixEnd_896658 : Nat := 4983230072969 + 3 ^ 40 * 896658 * 2
def baseEnd_896658 : Nat := 136419714577557942267067

theorem tailTrace_896658 : CollatzResearch.WordTrace tailWord_896658 prefixEnd_896658 136419714577557942267067 := by
  unfold tailWord_896658
  simp only [CollatzResearch.WordTrace]
  refine ⟨8175950996392169459912657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21802535990379118559767085 8175950996392169459912657)
  ·
    refine ⟨6131963247294127094934493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8175950996392169459912657 6131963247294127094934493)
    ·
      refine ⟨2299486217735297660600435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6131963247294127094934493 2299486217735297660600435)
      ·
        refine ⟨3449229326602946490900653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2299486217735297660600435 3449229326602946490900653)
        ·
          refine ⟨1293460997476104934087745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3449229326602946490900653 1293460997476104934087745)
          ·
            refine ⟨970095748107078700565809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1293460997476104934087745 970095748107078700565809)
            ·
              refine ⟨727571811080309025424357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 970095748107078700565809 727571811080309025424357)
              ·
                refine ⟨136419714577557942267067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 727571811080309025424357 136419714577557942267067)
                ·
                  rfl

theorem cell20_896658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 2, 4].length) (baseStart_896658 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_896658 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_896658 prefixEnd_896658 := by exact prefixLift 896658
  have htrace : WordTrace (prefixWord ++ tailWord_896658) baseStart_896658 baseEnd_896658 := by
    simpa [prefixWord, tailWord_896658, baseEnd_896658] using wordTrace_append hprefix tailTrace_896658
  have hstable : (prefixWord ++ tailWord_896658).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896658).length < 2 ^ (prefixWord ++ tailWord_896658).sum := by decide
  have hdescent : baseEnd_896658 < baseStart_896658 := by decide
  rcases family_descends (prefixWord ++ tailWord_896658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896668 : List Nat := [2, 2, 3, 2, 4, 1, 1, 3, 2]
def baseStart_896668 : Nat := 118140960795 + 896668 * 2 ^ 59
def prefixEnd_896668 : Nat := 4983230072969 + 3 ^ 40 * 896668 * 2
def baseEnd_896668 : Nat := 409263708005158236467827

theorem tailTrace_896668 : CollatzResearch.WordTrace tailWord_896668 prefixEnd_896668 409263708005158236467827 := by
  unfold tailWord_896668
  simp only [CollatzResearch.WordTrace]
  refine ⟨16352084357766224773757329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21802779143688299698343105 16352084357766224773757329)
  ·
    refine ⟨12264063268324668580317997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16352084357766224773757329 12264063268324668580317997)
    ·
      refine ⟨4599023725621750717619249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12264063268324668580317997 4599023725621750717619249)
      ·
        refine ⟨3449267794216313038214437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4599023725621750717619249 3449267794216313038214437)
        ·
          refine ⟨646737711415558694665207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3449267794216313038214437 646737711415558694665207)
          ·
            refine ⟨970106567123338041997811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 646737711415558694665207 970106567123338041997811)
            ·
              refine ⟨1455159850685007062996717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 970106567123338041997811 1455159850685007062996717)
              ·
                refine ⟨545684944006877648623769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1455159850685007062996717 545684944006877648623769)
                ·
                  refine ⟨409263708005158236467827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 545684944006877648623769 409263708005158236467827)
                  ·
                    rfl

theorem cell20_896668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 3, 2].length) (baseStart_896668 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_896668 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_896668 prefixEnd_896668 := by exact prefixLift 896668
  have htrace : WordTrace (prefixWord ++ tailWord_896668) baseStart_896668 baseEnd_896668 := by
    simpa [prefixWord, tailWord_896668, baseEnd_896668] using wordTrace_append hprefix tailTrace_896668
  have hstable : (prefixWord ++ tailWord_896668).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896668).length < 2 ^ (prefixWord ++ tailWord_896668).sum := by decide
  have hdescent : baseEnd_896668 < baseStart_896668 := by decide
  rcases family_descends (prefixWord ++ tailWord_896668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896672 : List Nat := [2, 1, 1, 4, 3, 1, 3, 3, 2]
def baseStart_896672 : Nat := 118140960795 + 896672 * 2 ^ 59
def prefixEnd_896672 : Nat := 4983230072969 + 3 ^ 40 * 896672 * 2
def baseEnd_896672 : Nat := 409265533714152000334477

theorem tailTrace_896672 : CollatzResearch.WordTrace tailWord_896672 prefixEnd_896672 409265533714152000334477 := by
  unfold tailWord_896672
  simp only [CollatzResearch.WordTrace]
  refine ⟨16352157303758979115330135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21802876405011972153773513 16352157303758979115330135)
  ·
    refine ⟨24528235955638468672995203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16352157303758979115330135 24528235955638468672995203)
    ·
      refine ⟨36792353933457703009492805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24528235955638468672995203 36792353933457703009492805)
      ·
        refine ⟨6898566362523319314279901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36792353933457703009492805 6898566362523319314279901)
        ·
          refine ⟨2586962385946244742854963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6898566362523319314279901 2586962385946244742854963)
          ·
            refine ⟨3880443578919367114282445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2586962385946244742854963 3880443578919367114282445)
            ·
              refine ⟨1455166342094762667855917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3880443578919367114282445 1455166342094762667855917)
              ·
                refine ⟨545687378285536000445969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1455166342094762667855917 545687378285536000445969)
                ·
                  refine ⟨409265533714152000334477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 545687378285536000445969 409265533714152000334477)
                  ·
                    rfl

theorem cell20_896672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 3, 2].length) (baseStart_896672 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_896672 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_896672 prefixEnd_896672 := by exact prefixLift 896672
  have htrace : WordTrace (prefixWord ++ tailWord_896672) baseStart_896672 baseEnd_896672 := by
    simpa [prefixWord, tailWord_896672, baseEnd_896672] using wordTrace_append hprefix tailTrace_896672
  have hstable : (prefixWord ++ tailWord_896672).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896672).length < 2 ^ (prefixWord ++ tailWord_896672).sum := by decide
  have hdescent : baseEnd_896672 < baseStart_896672 := by decide
  rcases family_descends (prefixWord ++ tailWord_896672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896700 : List Nat := [2, 2, 2, 3, 1, 3, 2, 5]
def baseStart_896700 : Nat := 118140960795 + 896700 * 2 ^ 59
def prefixEnd_896700 : Nat := 4983230072969 + 3 ^ 40 * 896700 * 2
def baseEnd_896700 : Nat := 136426104559036115800343

theorem tailTrace_896700 : CollatzResearch.WordTrace tailWord_896700 prefixEnd_896700 136426104559036115800343 := by
  unfold tailWord_896700
  simp only [CollatzResearch.WordTrace]
  refine ⟨16352667925708259506339777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21803557234277679341786369 16352667925708259506339777)
  ·
    refine ⟨12264500944281194629754833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16352667925708259506339777 12264500944281194629754833)
    ·
      refine ⟨9198375708210895972316125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12264500944281194629754833 9198375708210895972316125)
      ·
        refine ⟨3449390890579085989618547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9198375708210895972316125 3449390890579085989618547)
        ·
          refine ⟨5174086335868628984427821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3449390890579085989618547 5174086335868628984427821)
          ·
            refine ⟨1940282375950735869160433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5174086335868628984427821 1940282375950735869160433)
            ·
              refine ⟨1455211781963051901870325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1940282375950735869160433 1455211781963051901870325)
              ·
                refine ⟨136426104559036115800343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1455211781963051901870325 136426104559036115800343)
                ·
                  rfl

theorem cell20_896700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 5].length) (baseStart_896700 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_896700 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_896700 prefixEnd_896700 := by exact prefixLift 896700
  have htrace : WordTrace (prefixWord ++ tailWord_896700) baseStart_896700 baseEnd_896700 := by
    simpa [prefixWord, tailWord_896700, baseEnd_896700] using wordTrace_append hprefix tailTrace_896700
  have hstable : (prefixWord ++ tailWord_896700).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896700).length < 2 ^ (prefixWord ++ tailWord_896700).sum := by decide
  have hdescent : baseEnd_896700 < baseStart_896700 := by decide
  rcases family_descends (prefixWord ++ tailWord_896700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896717 : List Nat := [1, 6, 2, 1, 1, 1, 2, 6]
def baseStart_896717 : Nat := 118140960795 + 896717 * 2 ^ 59
def prefixEnd_896717 : Nat := 4983230072969 + 3 ^ 40 * 896717 * 2
def baseEnd_896717 : Nat := 136428690980110614611431

theorem tailTrace_896717 : CollatzResearch.WordTrace tailWord_896717 prefixEnd_896717 136428690980110614611431 := by
  unfold tailWord_896717
  simp only [CollatzResearch.WordTrace]
  refine ⟨32705955892354930916048405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21803970594903287277365603 32705955892354930916048405)
  ·
    refine ⟨1533091682454137386689769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 32705955892354930916048405 1533091682454137386689769)
    ·
      refine ⟨1149818761840603040017327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1533091682454137386689769 1149818761840603040017327)
      ·
        refine ⟨1724728142760904560025991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1149818761840603040017327 1724728142760904560025991)
        ·
          refine ⟨2587092214141356840038987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1724728142760904560025991 2587092214141356840038987)
          ·
            refine ⟨3880638321212035260058481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2587092214141356840038987 3880638321212035260058481)
            ·
              refine ⟨2910478740909026445043861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3880638321212035260058481 2910478740909026445043861)
              ·
                refine ⟨136428690980110614611431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2910478740909026445043861 136428690980110614611431)
                ·
                  rfl

theorem cell20_896717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 6].length) (baseStart_896717 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_896717 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_896717 prefixEnd_896717 := by exact prefixLift 896717
  have htrace : WordTrace (prefixWord ++ tailWord_896717) baseStart_896717 baseEnd_896717 := by
    simpa [prefixWord, tailWord_896717, baseEnd_896717] using wordTrace_append hprefix tailTrace_896717
  have hstable : (prefixWord ++ tailWord_896717).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896717).length < 2 ^ (prefixWord ++ tailWord_896717).sum := by decide
  have hdescent : baseEnd_896717 < baseStart_896717 := by decide
  rcases family_descends (prefixWord ++ tailWord_896717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896721 : List Nat := [1, 2, 2, 1, 2, 4, 2, 6]
def baseStart_896721 : Nat := 118140960795 + 896721 * 2 ^ 59
def prefixEnd_896721 : Nat := 4983230072969 + 3 ^ 40 * 896721 * 2
def baseEnd_896721 : Nat := 136429299549775202566981

theorem tailTrace_896721 : CollatzResearch.WordTrace tailWord_896721 prefixEnd_896721 136429299549775202566981 := by
  unfold tailWord_896721
  simp only [CollatzResearch.WordTrace]
  refine ⟨32706101784340439599194017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21804067856226959732796011 32706101784340439599194017)
  ·
    refine ⟨24529576338255329699395513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32706101784340439599194017 24529576338255329699395513)
    ·
      refine ⟨18397182253691497274546635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24529576338255329699395513 18397182253691497274546635)
      ·
        refine ⟨27595773380537245911819953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18397182253691497274546635 27595773380537245911819953)
        ·
          refine ⟨20696830035402934433864965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27595773380537245911819953 20696830035402934433864965)
          ·
            refine ⟨3880655631638050206349681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20696830035402934433864965 3880655631638050206349681)
            ·
              refine ⟨2910491723728537654762261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3880655631638050206349681 2910491723728537654762261)
              ·
                refine ⟨136429299549775202566981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2910491723728537654762261 136429299549775202566981)
                ·
                  rfl

theorem cell20_896721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 6].length) (baseStart_896721 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_896721 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_896721 prefixEnd_896721 := by exact prefixLift 896721
  have htrace : WordTrace (prefixWord ++ tailWord_896721) baseStart_896721 baseEnd_896721 := by
    simpa [prefixWord, tailWord_896721, baseEnd_896721] using wordTrace_append hprefix tailTrace_896721
  have hstable : (prefixWord ++ tailWord_896721).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896721).length < 2 ^ (prefixWord ++ tailWord_896721).sum := by decide
  have hdescent : baseEnd_896721 < baseStart_896721 := by decide
  rcases family_descends (prefixWord ++ tailWord_896721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896748 : List Nat := [2, 2, 1, 1, 2, 2, 6, 2, 2]
def baseStart_896748 : Nat := 118140960795 + 896748 * 2 ^ 59
def prefixEnd_896748 : Nat := 4983230072969 + 3 ^ 40 * 896748 * 2
def baseEnd_896748 : Nat := 409300222185033513800833

theorem tailTrace_896748 : CollatzResearch.WordTrace tailWord_896748 prefixEnd_896748 409300222185033513800833 := by
  unfold tailWord_896748
  simp only [CollatzResearch.WordTrace]
  refine ⟨16353543277621311605213449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21804724370161748806951265 16353543277621311605213449)
  ·
    refine ⟨12265157458215983703910087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16353543277621311605213449 12265157458215983703910087)
    ·
      refine ⟨18397736187323975555865131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12265157458215983703910087 18397736187323975555865131)
      ·
        refine ⟨27596604280985963333797697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18397736187323975555865131 27596604280985963333797697)
        ·
          refine ⟨20697453210739472500348273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27596604280985963333797697 20697453210739472500348273)
          ·
            refine ⟨15523089908054604375261205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20697453210739472500348273 15523089908054604375261205)
            ·
              refine ⟨727644839440059580090369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15523089908054604375261205 727644839440059580090369)
              ·
                refine ⟨545733629580044685067777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 727644839440059580090369 545733629580044685067777)
                ·
                  refine ⟨409300222185033513800833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 545733629580044685067777 409300222185033513800833)
                  ·
                    rfl

theorem cell20_896748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 6, 2, 2].length) (baseStart_896748 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_896748 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_896748 prefixEnd_896748 := by exact prefixLift 896748
  have htrace : WordTrace (prefixWord ++ tailWord_896748) baseStart_896748 baseEnd_896748 := by
    simpa [prefixWord, tailWord_896748, baseEnd_896748] using wordTrace_append hprefix tailTrace_896748
  have hstable : (prefixWord ++ tailWord_896748).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896748).length < 2 ^ (prefixWord ++ tailWord_896748).sum := by decide
  have hdescent : baseEnd_896748 < baseStart_896748 := by decide
  rcases family_descends (prefixWord ++ tailWord_896748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896759 : List Nat := [1, 1, 3, 1, 1, 1, 7, 5]
def baseStart_896759 : Nat := 118140960795 + 896759 * 2 ^ 59
def prefixEnd_896759 : Nat := 4983230072969 + 3 ^ 40 * 896759 * 2
def baseEnd_896759 : Nat := 136435080961588788144707

theorem tailTrace_896759 : CollatzResearch.WordTrace tailWord_896759 prefixEnd_896759 136435080961588788144707 := by
  unfold tailWord_896759
  simp only [CollatzResearch.WordTrace]
  refine ⟨32707487758202772089077331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21804991838801848059384887 32707487758202772089077331)
  ·
    refine ⟨49061231637304158133615997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32707487758202772089077331 49061231637304158133615997)
    ·
      refine ⟨18397961863989059300105999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49061231637304158133615997 18397961863989059300105999)
      ·
        refine ⟨27596942795983588950158999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18397961863989059300105999 27596942795983588950158999)
        ·
          refine ⟨41395414193975383425238499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27596942795983588950158999 41395414193975383425238499)
          ·
            refine ⟨62093121290963075137857749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41395414193975383425238499 62093121290963075137857749)
            ·
              refine ⟨1455307530256947073543541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 62093121290963075137857749 1455307530256947073543541)
              ·
                refine ⟨136435080961588788144707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1455307530256947073543541 136435080961588788144707)
                ·
                  rfl

theorem cell20_896759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 5].length) (baseStart_896759 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_896759 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_896759 prefixEnd_896759 := by exact prefixLift 896759
  have htrace : WordTrace (prefixWord ++ tailWord_896759) baseStart_896759 baseEnd_896759 := by
    simpa [prefixWord, tailWord_896759, baseEnd_896759] using wordTrace_append hprefix tailTrace_896759
  have hstable : (prefixWord ++ tailWord_896759).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896759).length < 2 ^ (prefixWord ++ tailWord_896759).sum := by decide
  have hdescent : baseEnd_896759 < baseStart_896759 := by decide
  rcases family_descends (prefixWord ++ tailWord_896759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896776 : List Nat := [2, 1, 3, 2, 2, 1, 5, 4]
def baseStart_896776 : Nat := 118140960795 + 896776 * 2 ^ 59
def prefixEnd_896776 : Nat := 4983230072969 + 3 ^ 40 * 896776 * 2
def baseEnd_896776 : Nat := 136437667382663286955795

theorem tailTrace_896776 : CollatzResearch.WordTrace tailWord_896776 prefixEnd_896776 136437667382663286955795 := by
  unfold tailWord_896776
  simp only [CollatzResearch.WordTrace]
  refine ⟨16354053899570591996223091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21805405199427455994964121 16354053899570591996223091)
  ·
    refine ⟨24531080849355887994334637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16354053899570591996223091 24531080849355887994334637)
    ·
      refine ⟨9199155318508457997875489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24531080849355887994334637 9199155318508457997875489)
      ·
        refine ⟨6899366488881343498406617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9199155318508457997875489 6899366488881343498406617)
        ·
          refine ⟨5174524866661007623804963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6899366488881343498406617 5174524866661007623804963)
          ·
            refine ⟨7761787299991511435707445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5174524866661007623804963 7761787299991511435707445)
            ·
              refine ⟨727667559374204197097573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7761787299991511435707445 727667559374204197097573)
              ·
                refine ⟨136437667382663286955795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 727667559374204197097573 136437667382663286955795)
                ·
                  rfl

theorem cell20_896776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 5, 4].length) (baseStart_896776 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_896776 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_896776 prefixEnd_896776 := by exact prefixLift 896776
  have htrace : WordTrace (prefixWord ++ tailWord_896776) baseStart_896776 baseEnd_896776 := by
    simpa [prefixWord, tailWord_896776, baseEnd_896776] using wordTrace_append hprefix tailTrace_896776
  have hstable : (prefixWord ++ tailWord_896776).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896776).length < 2 ^ (prefixWord ++ tailWord_896776).sum := by decide
  have hdescent : baseEnd_896776 < baseStart_896776 := by decide
  rcases family_descends (prefixWord ++ tailWord_896776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896828 : List Nat := [2, 2, 2, 2, 1, 1, 4, 2, 4]
def baseStart_896828 : Nat := 118140960795 + 896828 * 2 ^ 59
def prefixEnd_896828 : Nat := 4983230072969 + 3 ^ 40 * 896828 * 2
def baseEnd_896828 : Nat := 409336736364908791133839

theorem tailTrace_896828 : CollatzResearch.WordTrace tailWord_896828 prefixEnd_896828 409336736364908791133839 := by
  unfold tailWord_896828
  simp only [CollatzResearch.WordTrace]
  refine ⟨16355002197476398436669569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21806669596635197915559425 16355002197476398436669569)
  ·
    refine ⟨12266251648107298827502177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16355002197476398436669569 12266251648107298827502177)
    ·
      refine ⟨9199688736080474120626633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12266251648107298827502177 9199688736080474120626633)
      ·
        refine ⟨6899766552060355590469975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9199688736080474120626633 6899766552060355590469975)
        ·
          refine ⟨10349649828090533385704963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6899766552060355590469975 10349649828090533385704963)
          ·
            refine ⟨15524474742135800078557445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10349649828090533385704963 15524474742135800078557445)
            ·
              refine ⟨2910839014150462514729521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15524474742135800078557445 2910839014150462514729521)
              ·
                refine ⟨2183129260612846886047141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2910839014150462514729521 2183129260612846886047141)
                ·
                  refine ⟨409336736364908791133839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2183129260612846886047141 409336736364908791133839)
                  ·
                    rfl

theorem cell20_896828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 2, 4].length) (baseStart_896828 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_896828 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_896828 prefixEnd_896828 := by exact prefixLift 896828
  have htrace : WordTrace (prefixWord ++ tailWord_896828) baseStart_896828 baseEnd_896828 := by
    simpa [prefixWord, tailWord_896828, baseEnd_896828] using wordTrace_append hprefix tailTrace_896828
  have hstable : (prefixWord ++ tailWord_896828).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896828).length < 2 ^ (prefixWord ++ tailWord_896828).sum := by decide
  have hdescent : baseEnd_896828 < baseStart_896828 := by decide
  rcases family_descends (prefixWord ++ tailWord_896828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896831 : List Nat := [1, 1, 2, 2, 6, 2, 2, 4]
def baseStart_896831 : Nat := 118140960795 + 896831 * 2 ^ 59
def prefixEnd_896831 : Nat := 4983230072969 + 3 ^ 40 * 896831 * 2
def baseEnd_896831 : Nat := 136446035215551371344609

theorem tailTrace_896831 : CollatzResearch.WordTrace tailWord_896831 prefixEnd_896831 136446035215551371344609 := by
  unfold tailWord_896831
  simp only [CollatzResearch.WordTrace]
  refine ⟨32710113813941928385698347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21806742542627952257132231 32710113813941928385698347)
  ·
    refine ⟨49065170720912892578547521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32710113813941928385698347 49065170720912892578547521)
    ·
      refine ⟨36798878040684669433910641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49065170720912892578547521 36798878040684669433910641)
      ·
        refine ⟨27599158530513502075432981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36798878040684669433910641 27599158530513502075432981)
        ·
          refine ⟨1293710556117820409785921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 27599158530513502075432981 1293710556117820409785921)
          ·
            refine ⟨970282917088365307339441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1293710556117820409785921 970282917088365307339441)
            ·
              refine ⟨727712187816273980504581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 970282917088365307339441 727712187816273980504581)
              ·
                refine ⟨136446035215551371344609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 727712187816273980504581 136446035215551371344609)
                ·
                  rfl

theorem cell20_896831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 2, 4].length) (baseStart_896831 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_896831 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_896831 prefixEnd_896831 := by exact prefixLift 896831
  have htrace : WordTrace (prefixWord ++ tailWord_896831) baseStart_896831 baseEnd_896831 := by
    simpa [prefixWord, tailWord_896831, baseEnd_896831] using wordTrace_append hprefix tailTrace_896831
  have hstable : (prefixWord ++ tailWord_896831).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896831).length < 2 ^ (prefixWord ++ tailWord_896831).sum := by decide
  have hdescent : baseEnd_896831 < baseStart_896831 := by decide
  rcases family_descends (prefixWord ++ tailWord_896831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896835 : List Nat := [1, 1, 1, 3, 1, 6, 1, 6]
def baseStart_896835 : Nat := 118140960795 + 896835 * 2 ^ 59
def prefixEnd_896835 : Nat := 4983230072969 + 3 ^ 40 * 896835 * 2
def baseEnd_896835 : Nat := 136446643785215959300159

theorem tailTrace_896835 : CollatzResearch.WordTrace tailWord_896835 prefixEnd_896835 136446643785215959300159 := by
  unfold tailWord_896835
  simp only [CollatzResearch.WordTrace]
  refine ⟨32710259705927437068843959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21806839803951624712562639 32710259705927437068843959)
  ·
    refine ⟨49065389558891155603265939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32710259705927437068843959 49065389558891155603265939)
    ·
      refine ⟨73598084338336733404898909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49065389558891155603265939 73598084338336733404898909)
      ·
        refine ⟨27599281626876275026837091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73598084338336733404898909 27599281626876275026837091)
        ·
          refine ⟨41398922440314412540255637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27599281626876275026837091 41398922440314412540255637)
          ·
            refine ⟨1940574489389738087824483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 41398922440314412540255637 1940574489389738087824483)
            ·
              refine ⟨2910861734084607131736725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1940574489389738087824483 2910861734084607131736725)
              ·
                refine ⟨136446643785215959300159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2910861734084607131736725 136446643785215959300159)
                ·
                  rfl

theorem cell20_896835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 6].length) (baseStart_896835 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_896835 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_896835 prefixEnd_896835 := by exact prefixLift 896835
  have htrace : WordTrace (prefixWord ++ tailWord_896835) baseStart_896835 baseEnd_896835 := by
    simpa [prefixWord, tailWord_896835, baseEnd_896835] using wordTrace_append hprefix tailTrace_896835
  have hstable : (prefixWord ++ tailWord_896835).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896835).length < 2 ^ (prefixWord ++ tailWord_896835).sum := by decide
  have hdescent : baseEnd_896835 < baseStart_896835 := by decide
  rcases family_descends (prefixWord ++ tailWord_896835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896842 : List Nat := [3, 1, 2, 1, 1, 1, 3, 1, 7]
def baseStart_896842 : Nat := 118140960795 + 896842 * 2 ^ 59
def prefixEnd_896842 : Nat := 4983230072969 + 3 ^ 40 * 896842 * 2
def baseEnd_896842 : Nat := 409343126346386964667115

theorem tailTrace_896842 : CollatzResearch.WordTrace tailWord_896842 prefixEnd_896842 409343126346386964667115 := by
  unfold tailWord_896842
  simp only [CollatzResearch.WordTrace]
  refine ⟨8177628754225519316087195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21807010011268051509565853 8177628754225519316087195)
  ·
    refine ⟨12266443131338278974130793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8177628754225519316087195 12266443131338278974130793)
    ·
      refine ⟨9199832348503709230598095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12266443131338278974130793 9199832348503709230598095)
      ·
        refine ⟨13799748522755563845897143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9199832348503709230598095 13799748522755563845897143)
        ·
          refine ⟨20699622784133345768845715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13799748522755563845897143 20699622784133345768845715)
          ·
            refine ⟨31049434176200018653268573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20699622784133345768845715 31049434176200018653268573)
            ·
              refine ⟨11643537816075006994975715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31049434176200018653268573 11643537816075006994975715)
              ·
                refine ⟨17465306724112510492463573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11643537816075006994975715 17465306724112510492463573)
                ·
                  refine ⟨409343126346386964667115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17465306724112510492463573 409343126346386964667115)
                  ·
                    rfl

theorem cell20_896842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 7].length) (baseStart_896842 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_896842 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_896842 prefixEnd_896842 := by exact prefixLift 896842
  have htrace : WordTrace (prefixWord ++ tailWord_896842) baseStart_896842 baseEnd_896842 := by
    simpa [prefixWord, tailWord_896842, baseEnd_896842] using wordTrace_append hprefix tailTrace_896842
  have hstable : (prefixWord ++ tailWord_896842).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896842).length < 2 ^ (prefixWord ++ tailWord_896842).sum := by decide
  have hdescent : baseEnd_896842 < baseStart_896842 := by decide
  rcases family_descends (prefixWord ++ tailWord_896842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896852 : List Nat := [2, 4, 1, 1, 3, 3, 6]
def baseStart_896852 : Nat := 118140960795 + 896852 * 2 ^ 59
def prefixEnd_896852 : Nat := 4983230072969 + 3 ^ 40 * 896852 * 2
def baseEnd_896852 : Nat := 45483076735430152703749

theorem tailTrace_896852 : CollatzResearch.WordTrace tailWord_896852 prefixEnd_896852 45483076735430152703749 := by
  unfold tailWord_896852
  simp only [CollatzResearch.WordTrace]
  refine ⟨16355439873432924486106405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21807253164577232648141873 16355439873432924486106405)
  ·
    refine ⟨3066644976268673341144951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16355439873432924486106405 3066644976268673341144951)
    ·
      refine ⟨4599967464403010011717427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3066644976268673341144951 4599967464403010011717427)
      ·
        refine ⟨6899951196604515017576141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4599967464403010011717427 6899951196604515017576141)
        ·
          refine ⟨2587481698726693131591053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6899951196604515017576141 2587481698726693131591053)
          ·
            refine ⟨970305637022509924346645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2587481698726693131591053 970305637022509924346645)
            ·
              refine ⟨45483076735430152703749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 970305637022509924346645 45483076735430152703749)
              ·
                rfl

theorem cell20_896852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 6].length) (baseStart_896852 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_896852 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_896852 prefixEnd_896852 := by exact prefixLift 896852
  have htrace : WordTrace (prefixWord ++ tailWord_896852) baseStart_896852 baseEnd_896852 := by
    simpa [prefixWord, tailWord_896852, baseEnd_896852] using wordTrace_append hprefix tailTrace_896852
  have hstable : (prefixWord ++ tailWord_896852).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896852).length < 2 ^ (prefixWord ++ tailWord_896852).sum := by decide
  have hdescent : baseEnd_896852 < baseStart_896852 := by decide
  rcases family_descends (prefixWord ++ tailWord_896852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896876 : List Nat := [2, 2, 1, 1, 4, 2, 4, 1, 3]
def baseStart_896876 : Nat := 118140960795 + 896876 * 2 ^ 59
def prefixEnd_896876 : Nat := 4983230072969 + 3 ^ 40 * 896876 * 2
def baseEnd_896876 : Nat := 409358644872833957533643

theorem tailTrace_896876 : CollatzResearch.WordTrace tailWord_896876 prefixEnd_896876 409358644872833957533643 := by
  unfold tailWord_896876
  simp only [CollatzResearch.WordTrace]
  refine ⟨16355877549389450535543241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21807836732519267380724321 16355877549389450535543241)
  ·
    refine ⟨12266908162042087901657431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16355877549389450535543241 12266908162042087901657431)
    ·
      refine ⟨18400362243063131852486147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12266908162042087901657431 18400362243063131852486147)
      ·
        refine ⟨27600543364594697778729221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18400362243063131852486147 27600543364594697778729221)
        ·
          refine ⟨5175101880861505833511729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27600543364594697778729221 5175101880861505833511729)
          ·
            refine ⟨3881326410646129375133797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5175101880861505833511729 3881326410646129375133797)
            ·
              refine ⟨727748701996149257837587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3881326410646129375133797 727748701996149257837587)
              ·
                refine ⟨1091623052994223886756381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 727748701996149257837587 1091623052994223886756381)
                ·
                  refine ⟨409358644872833957533643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1091623052994223886756381 409358644872833957533643)
                  ·
                    rfl

theorem cell20_896876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 3].length) (baseStart_896876 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_896876 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_896876 prefixEnd_896876 := by exact prefixLift 896876
  have htrace : WordTrace (prefixWord ++ tailWord_896876) baseStart_896876 baseEnd_896876 := by
    simpa [prefixWord, tailWord_896876, baseEnd_896876] using wordTrace_append hprefix tailTrace_896876
  have hstable : (prefixWord ++ tailWord_896876).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896876).length < 2 ^ (prefixWord ++ tailWord_896876).sum := by decide
  have hdescent : baseEnd_896876 < baseStart_896876 := by decide
  rcases family_descends (prefixWord ++ tailWord_896876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896914 : List Nat := [3, 2, 3, 2, 1, 1, 1, 4, 3]
def baseStart_896914 : Nat := 118140960795 + 896914 * 2 ^ 59
def prefixEnd_896914 : Nat := 4983230072969 + 3 ^ 40 * 896914 * 2
def baseEnd_896914 : Nat := 409375989108274714266821

theorem tailTrace_896914 : CollatzResearch.WordTrace tailWord_896914 prefixEnd_896914 409375989108274714266821 := by
  unfold tailWord_896914
  simp only [CollatzResearch.WordTrace]
  refine ⟨8178285268160308390242449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21808760715094155707313197 8178285268160308390242449)
  ·
    refine ⟨6133713951120231292681837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8178285268160308390242449 6133713951120231292681837)
    ·
      refine ⟨2300142731670086734755689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6133713951120231292681837 2300142731670086734755689)
      ·
        refine ⟨1725107048752565051066767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2300142731670086734755689 1725107048752565051066767)
        ·
          refine ⟨2587660573128847576600151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1725107048752565051066767 2587660573128847576600151)
          ·
            refine ⟨3881490859693271364900227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2587660573128847576600151 3881490859693271364900227)
            ·
              refine ⟨5822236289539907047350341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3881490859693271364900227 5822236289539907047350341)
              ·
                refine ⟨1091669304288732571378189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5822236289539907047350341 1091669304288732571378189)
                ·
                  refine ⟨409375989108274714266821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1091669304288732571378189 409375989108274714266821)
                  ·
                    rfl

theorem cell20_896914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 4, 3].length) (baseStart_896914 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_896914 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_896914 prefixEnd_896914 := by exact prefixLift 896914
  have htrace : WordTrace (prefixWord ++ tailWord_896914) baseStart_896914 baseEnd_896914 := by
    simpa [prefixWord, tailWord_896914, baseEnd_896914] using wordTrace_append hprefix tailTrace_896914
  have hstable : (prefixWord ++ tailWord_896914).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896914).length < 2 ^ (prefixWord ++ tailWord_896914).sum := by decide
  have hdescent : baseEnd_896914 < baseStart_896914 := by decide
  rcases family_descends (prefixWord ++ tailWord_896914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896959 : List Nat := [1, 1, 2, 2, 2, 1, 6, 3, 2]
def baseStart_896959 : Nat := 118140960795 + 896959 * 2 ^ 59
def prefixEnd_896959 : Nat := 4983230072969 + 3 ^ 40 * 896959 * 2
def baseEnd_896959 : Nat := 409396528334454557766637

theorem tailTrace_896959 : CollatzResearch.WordTrace tailWord_896959 prefixEnd_896959 409396528334454557766637 := by
  unfold tailWord_896959
  simp only [CollatzResearch.WordTrace]
  refine ⟨32714782357478206246357931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21809854904985470830905287 32714782357478206246357931)
  ·
    refine ⟨49072173536217309369536897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32714782357478206246357931 49072173536217309369536897)
    ·
      refine ⟨36804130152162982027152673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49072173536217309369536897 36804130152162982027152673)
      ·
        refine ⟨27603097614122236520364505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36804130152162982027152673 27603097614122236520364505)
        ·
          refine ⟨20702323210591677390273379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27603097614122236520364505 20702323210591677390273379)
          ·
            refine ⟨31053484815887516085410069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20702323210591677390273379 31053484815887516085410069)
            ·
              refine ⟨1455632100744727316503597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 31053484815887516085410069 1455632100744727316503597)
              ·
                refine ⟨545862037779272743688849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1455632100744727316503597 545862037779272743688849)
                ·
                  refine ⟨409396528334454557766637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 545862037779272743688849 409396528334454557766637)
                  ·
                    rfl

theorem cell20_896959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 3, 2].length) (baseStart_896959 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_896959 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_896959 prefixEnd_896959 := by exact prefixLift 896959
  have htrace : WordTrace (prefixWord ++ tailWord_896959) baseStart_896959 baseEnd_896959 := by
    simpa [prefixWord, tailWord_896959, baseEnd_896959] using wordTrace_append hprefix tailTrace_896959
  have hstable : (prefixWord ++ tailWord_896959).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896959).length < 2 ^ (prefixWord ++ tailWord_896959).sum := by decide
  have hdescent : baseEnd_896959 < baseStart_896959 := by decide
  rcases family_descends (prefixWord ++ tailWord_896959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897032 : List Nat := [2, 1, 3, 2, 1, 2, 1, 3, 5]
def baseStart_897032 : Nat := 118140960795 + 897032 * 2 ^ 59
def prefixEnd_897032 : Nat := 4983230072969 + 3 ^ 40 * 897032 * 2
def baseEnd_897032 : Nat := 409429847523590748333005

theorem tailTrace_897032 : CollatzResearch.WordTrace tailWord_897032 prefixEnd_897032 409429847523590748333005 := by
  unfold tailWord_897032
  simp only [CollatzResearch.WordTrace]
  refine ⟨16358722443106869856882675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21811629924142493142510233 16358722443106869856882675)
  ·
    refine ⟨24538083664660304785324013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16358722443106869856882675 24538083664660304785324013)
    ·
      refine ⟨9201781374247614294496505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24538083664660304785324013 9201781374247614294496505)
      ·
        refine ⟨6901336030685710720872379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9201781374247614294496505 6901336030685710720872379)
        ·
          refine ⟨10352004046028566081308569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6901336030685710720872379 10352004046028566081308569)
          ·
            refine ⟨7764003034521424560981427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10352004046028566081308569 7764003034521424560981427)
            ·
              refine ⟨11646004551782136841472141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7764003034521424560981427 11646004551782136841472141)
              ·
                refine ⟨4367251706918301315552053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11646004551782136841472141 4367251706918301315552053)
                ·
                  refine ⟨409429847523590748333005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4367251706918301315552053 409429847523590748333005)
                  ·
                    rfl

theorem cell20_897032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 3, 5].length) (baseStart_897032 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_897032 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_897032 prefixEnd_897032 := by exact prefixLift 897032
  have htrace : WordTrace (prefixWord ++ tailWord_897032) baseStart_897032 baseEnd_897032 := by
    simpa [prefixWord, tailWord_897032, baseEnd_897032] using wordTrace_append hprefix tailTrace_897032
  have hstable : (prefixWord ++ tailWord_897032).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897032).length < 2 ^ (prefixWord ++ tailWord_897032).sum := by decide
  have hdescent : baseEnd_897032 < baseStart_897032 := by decide
  rcases family_descends (prefixWord ++ tailWord_897032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897045 : List Nat := [1, 3, 2, 1, 5, 2, 2, 1, 3]
def baseStart_897045 : Nat := 118140960795 + 897045 * 2 ^ 59
def prefixEnd_897045 : Nat := 4983230072969 + 3 ^ 40 * 897045 * 2
def baseEnd_897045 : Nat := 409435781077820480899619

theorem tailTrace_897045 : CollatzResearch.WordTrace tailWord_897045 prefixEnd_897045 409435781077820480899619 := by
  unfold tailWord_897045
  simp only [CollatzResearch.WordTrace]
  refine ⟨32717919035166642933988589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21811946023444428622659059 32717919035166642933988589)
  ·
    refine ⟨12269219638187491100245721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32717919035166642933988589 12269219638187491100245721)
    ·
      refine ⟨9201914728640618325184291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12269219638187491100245721 9201914728640618325184291)
      ·
        refine ⟨13802872092960927487776437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9201914728640618325184291 13802872092960927487776437)
        ·
          refine ⟨1294019258715086951979041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13802872092960927487776437 1294019258715086951979041)
          ·
            refine ⟨970514444036315213984281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1294019258715086951979041 970514444036315213984281)
            ·
              refine ⟨727885833027236410488211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 970514444036315213984281 727885833027236410488211)
              ·
                refine ⟨1091828749540854615732317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 727885833027236410488211 1091828749540854615732317)
                ·
                  refine ⟨409435781077820480899619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1091828749540854615732317 409435781077820480899619)
                  ·
                    rfl

theorem cell20_897045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 2, 1, 3].length) (baseStart_897045 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_897045 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_897045 prefixEnd_897045 := by exact prefixLift 897045
  have htrace : WordTrace (prefixWord ++ tailWord_897045) baseStart_897045 baseEnd_897045 := by
    simpa [prefixWord, tailWord_897045, baseEnd_897045] using wordTrace_append hprefix tailTrace_897045
  have hstable : (prefixWord ++ tailWord_897045).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897045).length < 2 ^ (prefixWord ++ tailWord_897045).sum := by decide
  have hdescent : baseEnd_897045 < baseStart_897045 := by decide
  rcases family_descends (prefixWord ++ tailWord_897045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897086 : List Nat := [4, 2, 1, 3, 2, 2, 2, 2, 2]
def baseStart_897086 : Nat := 118140960795 + 897086 * 2 ^ 59
def prefixEnd_897086 : Nat := 4983230072969 + 3 ^ 40 * 897086 * 2
def baseEnd_897086 : Nat := 409454494595006560532785

theorem tailTrace_897086 : CollatzResearch.WordTrace tailWord_897086 prefixEnd_897086 409454494595006560532785 := by
  unfold tailWord_897086
  simp only [CollatzResearch.WordTrace]
  refine ⟨4089926803502263367028889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21812942952012071290820741 4089926803502263367028889)
  ·
    refine ⟨3067445102626697525271667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4089926803502263367028889 3067445102626697525271667)
    ·
      refine ⟨4601167653940046287907501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3067445102626697525271667 4601167653940046287907501)
      ·
        refine ⟨1725437870227517357965313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4601167653940046287907501 1725437870227517357965313)
        ·
          refine ⟨1294078402670638018473985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1725437870227517357965313 1294078402670638018473985)
          ·
            refine ⟨970558802002978513855489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1294078402670638018473985 970558802002978513855489)
            ·
              refine ⟨727919101502233885391617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 970558802002978513855489 727919101502233885391617)
              ·
                refine ⟨545939326126675414043713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 727919101502233885391617 545939326126675414043713)
                ·
                  refine ⟨409454494595006560532785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 545939326126675414043713 409454494595006560532785)
                  ·
                    rfl

theorem cell20_897086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 2, 2, 2].length) (baseStart_897086 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_897086 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_897086 prefixEnd_897086 := by exact prefixLift 897086
  have htrace : WordTrace (prefixWord ++ tailWord_897086) baseStart_897086 baseEnd_897086 := by
    simpa [prefixWord, tailWord_897086, baseEnd_897086] using wordTrace_append hprefix tailTrace_897086
  have hstable : (prefixWord ++ tailWord_897086).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897086).length < 2 ^ (prefixWord ++ tailWord_897086).sum := by decide
  have hdescent : baseEnd_897086 < baseStart_897086 := by decide
  rcases family_descends (prefixWord ++ tailWord_897086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897108 : List Nat := [2, 4, 1, 1, 1, 1, 1, 2, 7]
def baseStart_897108 : Nat := 118140960795 + 897108 * 2 ^ 59
def prefixEnd_897108 : Nat := 4983230072969 + 3 ^ 40 * 897108 * 2
def baseEnd_897108 : Nat := 409464535994472261799361

theorem tailTrace_897108 : CollatzResearch.WordTrace tailWord_897108 prefixEnd_897108 409464535994472261799361 := by
  unfold tailWord_897108
  simp only [CollatzResearch.WordTrace]
  refine ⟨16360108416969202346765989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21813477889292269795687985 16360108416969202346765989)
  ·
    refine ⟨3067520328181725440018623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16360108416969202346765989 3067520328181725440018623)
    ·
      refine ⟨4601280492272588160027935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3067520328181725440018623 4601280492272588160027935)
      ·
        refine ⟨6901920738408882240041903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4601280492272588160027935 6901920738408882240041903)
        ·
          refine ⟨10352881107613323360062855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6901920738408882240041903 10352881107613323360062855)
          ·
            refine ⟨15529321661419985040094283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10352881107613323360062855 15529321661419985040094283)
            ·
              refine ⟨23293982492129977560141425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15529321661419985040094283 23293982492129977560141425)
              ·
                refine ⟨17470486869097483170106069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23293982492129977560141425 17470486869097483170106069)
                ·
                  refine ⟨409464535994472261799361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17470486869097483170106069 409464535994472261799361)
                  ·
                    rfl

theorem cell20_897108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_897108 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_897108 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_897108 prefixEnd_897108 := by exact prefixLift 897108
  have htrace : WordTrace (prefixWord ++ tailWord_897108) baseStart_897108 baseEnd_897108 := by
    simpa [prefixWord, tailWord_897108, baseEnd_897108] using wordTrace_append hprefix tailTrace_897108
  have hstable : (prefixWord ++ tailWord_897108).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897108).length < 2 ^ (prefixWord ++ tailWord_897108).sum := by decide
  have hdescent : baseEnd_897108 < baseStart_897108 := by decide
  rcases family_descends (prefixWord ++ tailWord_897108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897142 : List Nat := [5, 1, 1, 2, 1, 2, 3, 2, 3]
def baseStart_897142 : Nat := 118140960795 + 897142 * 2 ^ 59
def prefixEnd_897142 : Nat := 4983230072969 + 3 ^ 40 * 897142 * 2
def baseEnd_897142 : Nat := 409480054520919254665889

theorem tailTrace_897142 : CollatzResearch.WordTrace tailWord_897142 prefixEnd_897142 409480054520919254665889 := by
  unfold tailWord_897142
  simp only [CollatzResearch.WordTrace]
  refine ⟨2045091057238451781266855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21814304610543485666846453 2045091057238451781266855)
  ·
    refine ⟨3067636585857677671900283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2045091057238451781266855 3067636585857677671900283)
    ·
      refine ⟨4601454878786516507850425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3067636585857677671900283 4601454878786516507850425)
      ·
        refine ⟨3451091159089887380887819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4601454878786516507850425 3451091159089887380887819)
        ·
          refine ⟨5176636738634831071331729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3451091159089887380887819 5176636738634831071331729)
          ·
            refine ⟨3882477553976123303498797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5176636738634831071331729 3882477553976123303498797)
            ·
              refine ⟨1455929082741046238812049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3882477553976123303498797 1455929082741046238812049)
              ·
                refine ⟨1091946812055784679109037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1455929082741046238812049 1091946812055784679109037)
                ·
                  refine ⟨409480054520919254665889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1091946812055784679109037 409480054520919254665889)
                  ·
                    rfl

theorem cell20_897142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_897142 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_897142 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_897142 prefixEnd_897142 := by exact prefixLift 897142
  have htrace : WordTrace (prefixWord ++ tailWord_897142) baseStart_897142 baseEnd_897142 := by
    simpa [prefixWord, tailWord_897142, baseEnd_897142] using wordTrace_append hprefix tailTrace_897142
  have hstable : (prefixWord ++ tailWord_897142).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897142).length < 2 ^ (prefixWord ++ tailWord_897142).sum := by decide
  have hdescent : baseEnd_897142 < baseStart_897142 := by decide
  rcases family_descends (prefixWord ++ tailWord_897142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897149 : List Nat := [1, 4, 1, 1, 3, 2, 2, 4, 2]
def baseStart_897149 : Nat := 118140960795 + 897149 * 2 ^ 59
def prefixEnd_897149 : Nat := 4983230072969 + 3 ^ 40 * 897149 * 2
def baseEnd_897149 : Nat := 409483249511658341432527

theorem tailTrace_897149 : CollatzResearch.WordTrace tailWord_897149 prefixEnd_897149 409483249511658341432527 := by
  unfold tailWord_897149
  simp only [CollatzResearch.WordTrace]
  refine ⟨32721712226789868695774501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21814474817859912463849667 32721712226789868695774501)
  ·
    refine ⟨6135321042523100380457719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32721712226789868695774501 6135321042523100380457719)
    ·
      refine ⟨9202981563784650570686579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6135321042523100380457719 9202981563784650570686579)
      ·
        refine ⟨13804472345676975856029869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9202981563784650570686579 13804472345676975856029869)
        ·
          refine ⟨5176677129628865946011201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13804472345676975856029869 5176677129628865946011201)
          ·
            refine ⟨3882507847221649459508401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5176677129628865946011201 3882507847221649459508401)
            ·
              refine ⟨2911880885416237094631301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3882507847221649459508401 2911880885416237094631301)
              ·
                refine ⟨545977666015544455243369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2911880885416237094631301 545977666015544455243369)
                ·
                  refine ⟨409483249511658341432527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 545977666015544455243369 409483249511658341432527)
                  ·
                    rfl

theorem cell20_897149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 4, 2].length) (baseStart_897149 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_897149 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_897149 prefixEnd_897149 := by exact prefixLift 897149
  have htrace : WordTrace (prefixWord ++ tailWord_897149) baseStart_897149 baseEnd_897149 := by
    simpa [prefixWord, tailWord_897149, baseEnd_897149] using wordTrace_append hprefix tailTrace_897149
  have hstable : (prefixWord ++ tailWord_897149).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897149).length < 2 ^ (prefixWord ++ tailWord_897149).sum := by decide
  have hdescent : baseEnd_897149 < baseStart_897149 := by decide
  rcases family_descends (prefixWord ++ tailWord_897149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897170 : List Nat := [3, 2, 3, 1, 1, 1, 1, 4, 4]
def baseStart_897170 : Nat := 118140960795 + 897170 * 2 ^ 59
def prefixEnd_897170 : Nat := 4983230072969 + 3 ^ 40 * 897170 * 2
def baseEnd_897170 : Nat := 409492834483875601732441

theorem tailTrace_897170 : CollatzResearch.WordTrace tailWord_897170 prefixEnd_897170 409492834483875601732441 := by
  unfold tailWord_897170
  simp only [CollatzResearch.WordTrace]
  refine ⟨8180619539928447320572241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21814985439809192854859309 8180619539928447320572241)
  ·
    refine ⟨6135464654946335490429181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8180619539928447320572241 6135464654946335490429181)
    ·
      refine ⟨2300799245604875808910943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6135464654946335490429181 2300799245604875808910943)
      ·
        refine ⟨3451198868407313713366415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2300799245604875808910943 3451198868407313713366415)
        ·
          refine ⟨5176798302610970570049623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3451198868407313713366415 5176798302610970570049623)
          ·
            refine ⟨7765197453916455855074435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5176798302610970570049623 7765197453916455855074435)
            ·
              refine ⟨11647796180874683782611653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7765197453916455855074435 11647796180874683782611653)
              ·
                refine ⟨2183961783914003209239685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11647796180874683782611653 2183961783914003209239685)
                ·
                  refine ⟨409492834483875601732441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2183961783914003209239685 409492834483875601732441)
                  ·
                    rfl

theorem cell20_897170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_897170 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_897170 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_897170 prefixEnd_897170 := by exact prefixLift 897170
  have htrace : WordTrace (prefixWord ++ tailWord_897170) baseStart_897170 baseEnd_897170 := by
    simpa [prefixWord, tailWord_897170, baseEnd_897170] using wordTrace_append hprefix tailTrace_897170
  have hstable : (prefixWord ++ tailWord_897170).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897170).length < 2 ^ (prefixWord ++ tailWord_897170).sum := by decide
  have hdescent : baseEnd_897170 < baseStart_897170 := by decide
  rcases family_descends (prefixWord ++ tailWord_897170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897184 : List Nat := [2, 1, 1, 4, 2, 2, 1, 2, 5]
def baseStart_897184 : Nat := 118140960795 + 897184 * 2 ^ 59
def prefixEnd_897184 : Nat := 4983230072969 + 3 ^ 40 * 897184 * 2
def baseEnd_897184 : Nat := 409499224465353775265717

theorem tailTrace_897184 : CollatzResearch.WordTrace tailWord_897184 prefixEnd_897184 409499224465353775265717 := by
  unfold tailWord_897184
  simp only [CollatzResearch.WordTrace]
  refine ⟨16361494390831534836649303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21815325854442046448865737 16361494390831534836649303)
  ·
    refine ⟨24542241586247302254973955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16361494390831534836649303 24542241586247302254973955)
    ·
      refine ⟨36813362379370953382460933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24542241586247302254973955 36813362379370953382460933)
      ·
        refine ⟨6902505446132053759211425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36813362379370953382460933 6902505446132053759211425)
        ·
          refine ⟨5176879084599040319408569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6902505446132053759211425 5176879084599040319408569)
          ·
            refine ⟨3882659313449280239556427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5176879084599040319408569 3882659313449280239556427)
            ·
              refine ⟨5823988970173920359334641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3882659313449280239556427 5823988970173920359334641)
              ·
                refine ⟨4367991727630440269500981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5823988970173920359334641 4367991727630440269500981)
                ·
                  refine ⟨409499224465353775265717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4367991727630440269500981 409499224465353775265717)
                  ·
                    rfl

theorem cell20_897184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 2, 5].length) (baseStart_897184 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_897184 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_897184 prefixEnd_897184 := by exact prefixLift 897184
  have htrace : WordTrace (prefixWord ++ tailWord_897184) baseStart_897184 baseEnd_897184 := by
    simpa [prefixWord, tailWord_897184, baseEnd_897184] using wordTrace_append hprefix tailTrace_897184
  have hstable : (prefixWord ++ tailWord_897184).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897184).length < 2 ^ (prefixWord ++ tailWord_897184).sum := by decide
  have hdescent : baseEnd_897184 < baseStart_897184 := by decide
  rcases family_descends (prefixWord ++ tailWord_897184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897214 : List Nat := [4, 2, 1, 1, 5, 1, 2, 1, 3]
def baseStart_897214 : Nat := 118140960795 + 897214 * 2 ^ 59
def prefixEnd_897214 : Nat := 4983230072969 + 3 ^ 40 * 897214 * 2
def baseEnd_897214 : Nat := 409512917282807004265595

theorem tailTrace_897214 : CollatzResearch.WordTrace tailWord_897214 prefixEnd_897214 409512917282807004265595 := by
  unfold tailWord_897214
  simp only [CollatzResearch.WordTrace]
  refine ⟨4090510371444298099611337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21816055314369589864593797 4090510371444298099611337)
  ·
    refine ⟨3067882778583223574708503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4090510371444298099611337 3067882778583223574708503)
    ·
      refine ⟨4601824167874835362062755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3067882778583223574708503 4601824167874835362062755)
      ·
        refine ⟨6902736251812253043094133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4601824167874835362062755 6902736251812253043094133)
        ·
          refine ⟨647131523607398722790075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6902736251812253043094133 647131523607398722790075)
          ·
            refine ⟨970697285411098084185113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 647131523607398722790075 970697285411098084185113)
            ·
              refine ⟨728022964058323563138835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 970697285411098084185113 728022964058323563138835)
              ·
                refine ⟨1092034446087485344708253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 728022964058323563138835 1092034446087485344708253)
                ·
                  refine ⟨409512917282807004265595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1092034446087485344708253 409512917282807004265595)
                  ·
                    rfl

theorem cell20_897214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 2, 1, 3].length) (baseStart_897214 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_897214 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_897214 prefixEnd_897214 := by exact prefixLift 897214
  have htrace : WordTrace (prefixWord ++ tailWord_897214) baseStart_897214 baseEnd_897214 := by
    simpa [prefixWord, tailWord_897214, baseEnd_897214] using wordTrace_append hprefix tailTrace_897214
  have hstable : (prefixWord ++ tailWord_897214).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897214).length < 2 ^ (prefixWord ++ tailWord_897214).sum := by decide
  have hdescent : baseEnd_897214 < baseStart_897214 := by decide
  rcases family_descends (prefixWord ++ tailWord_897214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897263 : List Nat := [1, 1, 2, 1, 6, 2, 1, 4, 2]
def baseStart_897263 : Nat := 118140960795 + 897263 * 2 ^ 59
def prefixEnd_897263 : Nat := 4983230072969 + 3 ^ 40 * 897263 * 2
def baseEnd_897263 : Nat := 409535282217980611632061

theorem tailTrace_897263 : CollatzResearch.WordTrace tailWord_897263 prefixEnd_897263 409535282217980611632061 := by
  unfold tailWord_897263
  simp only [CollatzResearch.WordTrace]
  refine ⟨32725870148376866165424443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21817246765584577443616295 32725870148376866165424443)
  ·
    refine ⟨49088805222565299248136665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32725870148376866165424443 49088805222565299248136665)
    ·
      refine ⟨36816603916923974436102499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49088805222565299248136665 36816603916923974436102499)
      ·
        refine ⟨55224905875385961654153749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36816603916923974436102499 55224905875385961654153749)
        ·
          refine ⟨2588667462908716952538457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 55224905875385961654153749 2588667462908716952538457)
          ·
            refine ⟨1941500597181537714403843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2588667462908716952538457 1941500597181537714403843)
            ·
              refine ⟨2912250895772306571605765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1941500597181537714403843 2912250895772306571605765)
              ·
                refine ⟨546047042957307482176081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2912250895772306571605765 546047042957307482176081)
                ·
                  refine ⟨409535282217980611632061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 546047042957307482176081 409535282217980611632061)
                  ·
                    rfl

theorem cell20_897263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 4, 2].length) (baseStart_897263 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_897263 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_897263 prefixEnd_897263 := by exact prefixLift 897263
  have htrace : WordTrace (prefixWord ++ tailWord_897263) baseStart_897263 baseEnd_897263 := by
    simpa [prefixWord, tailWord_897263, baseEnd_897263] using wordTrace_append hprefix tailTrace_897263
  have hstable : (prefixWord ++ tailWord_897263).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897263).length < 2 ^ (prefixWord ++ tailWord_897263).sum := by decide
  have hdescent : baseEnd_897263 < baseStart_897263 := by decide
  rcases family_descends (prefixWord ++ tailWord_897263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897267 : List Nat := [1, 1, 1, 2, 2, 4, 2, 3, 4]
def baseStart_897267 : Nat := 118140960795 + 897267 * 2 ^ 59
def prefixEnd_897267 : Nat := 4983230072969 + 3 ^ 40 * 897267 * 2
def baseEnd_897267 : Nat := 409537107926974375498711

theorem tailTrace_897267 : CollatzResearch.WordTrace tailWord_897267 prefixEnd_897267 409537107926974375498711 := by
  unfold tailWord_897267
  simp only [CollatzResearch.WordTrace]
  refine ⟨32726016040362374848570055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21817344026908249899046703 32726016040362374848570055)
  ·
    refine ⟨49089024060543562272855083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32726016040362374848570055 49089024060543562272855083)
    ·
      refine ⟨73633536090815343409282625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49089024060543562272855083 73633536090815343409282625)
      ·
        refine ⟨55225152068111507556961969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73633536090815343409282625 55225152068111507556961969)
        ·
          refine ⟨41418864051083630667721477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55225152068111507556961969 41418864051083630667721477)
          ·
            refine ⟨7766037009578180750197777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41418864051083630667721477 7766037009578180750197777)
            ·
              refine ⟨5824527757183635562648333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7766037009578180750197777 5824527757183635562648333)
              ·
                refine ⟨2184197908943863335993125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5824527757183635562648333 2184197908943863335993125)
                ·
                  refine ⟨409537107926974375498711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2184197908943863335993125 409537107926974375498711)
                  ·
                    rfl

theorem cell20_897267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 3, 4].length) (baseStart_897267 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_897267 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_897267 prefixEnd_897267 := by exact prefixLift 897267
  have htrace : WordTrace (prefixWord ++ tailWord_897267) baseStart_897267 baseEnd_897267 := by
    simpa [prefixWord, tailWord_897267, baseEnd_897267] using wordTrace_append hprefix tailTrace_897267
  have hstable : (prefixWord ++ tailWord_897267).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897267).length < 2 ^ (prefixWord ++ tailWord_897267).sum := by decide
  have hdescent : baseEnd_897267 < baseStart_897267 := by decide
  rcases family_descends (prefixWord ++ tailWord_897267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897287 : List Nat := [1, 1, 4, 5, 1, 1, 3, 4]
def baseStart_897287 : Nat := 118140960795 + 897287 * 2 ^ 59
def prefixEnd_897287 : Nat := 4983230072969 + 3 ^ 40 * 897287 * 2
def baseEnd_897287 : Nat := 136515412157314398277321

theorem tailTrace_897287 : CollatzResearch.WordTrace tailWord_897287 prefixEnd_897287 136515412157314398277321 := by
  unfold tailWord_897287
  simp only [CollatzResearch.WordTrace]
  refine ⟨32726745500289918264298115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21817830333526612176198743 32726745500289918264298115)
  ·
    refine ⟨49090118250434877396447173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32726745500289918264298115 49090118250434877396447173)
    ·
      refine ⟨9204397171956539511833845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49090118250434877396447173 9204397171956539511833845)
      ·
        refine ⟨862912234870925579234423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9204397171956539511833845 862912234870925579234423)
        ·
          refine ⟨1294368352306388368851635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 862912234870925579234423 1294368352306388368851635)
          ·
            refine ⟨1941552528459582553277453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1294368352306388368851635 1941552528459582553277453)
            ·
              refine ⟨728082198172343457479045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1941552528459582553277453 728082198172343457479045)
              ·
                refine ⟨136515412157314398277321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 728082198172343457479045 136515412157314398277321)
                ·
                  rfl

theorem cell20_897287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 3, 4].length) (baseStart_897287 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_897287 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_897287 prefixEnd_897287 := by exact prefixLift 897287
  have htrace : WordTrace (prefixWord ++ tailWord_897287) baseStart_897287 baseEnd_897287 := by
    simpa [prefixWord, tailWord_897287, baseEnd_897287] using wordTrace_append hprefix tailTrace_897287
  have hstable : (prefixWord ++ tailWord_897287).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897287).length < 2 ^ (prefixWord ++ tailWord_897287).sum := by decide
  have hdescent : baseEnd_897287 < baseStart_897287 := by decide
  rcases family_descends (prefixWord ++ tailWord_897287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897291 : List Nat := [1, 1, 1, 1, 5, 2, 5, 4]
def baseStart_897291 : Nat := 118140960795 + 897291 * 2 ^ 59
def prefixEnd_897291 : Nat := 4983230072969 + 3 ^ 40 * 897291 * 2
def baseEnd_897291 : Nat := 136516020726978986232871

theorem tailTrace_897291 : CollatzResearch.WordTrace tailWord_897291 prefixEnd_897291 136516020726978986232871 := by
  unfold tailWord_897291
  simp only [CollatzResearch.WordTrace]
  refine ⟨32726891392275426947443727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21817927594850284631629151 32726891392275426947443727)
  ·
    refine ⟨49090337088413140421165591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32726891392275426947443727 49090337088413140421165591)
    ·
      refine ⟨73635505632619710631748387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49090337088413140421165591 73635505632619710631748387)
      ·
        refine ⟨110453258448929565947622581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73635505632619710631748387 110453258448929565947622581)
        ·
          refine ⟨10354992979587146807589617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 110453258448929565947622581 10354992979587146807589617)
          ·
            refine ⟨7766244734690360105692213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10354992979587146807589617 7766244734690360105692213)
            ·
              refine ⟨728085443877221259908645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7766244734690360105692213 728085443877221259908645)
              ·
                refine ⟨136516020726978986232871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 728085443877221259908645 136516020726978986232871)
                ·
                  rfl

theorem cell20_897291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 5, 4].length) (baseStart_897291 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_897291 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_897291 prefixEnd_897291 := by exact prefixLift 897291
  have htrace : WordTrace (prefixWord ++ tailWord_897291) baseStart_897291 baseEnd_897291 := by
    simpa [prefixWord, tailWord_897291, baseEnd_897291] using wordTrace_append hprefix tailTrace_897291
  have hstable : (prefixWord ++ tailWord_897291).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897291).length < 2 ^ (prefixWord ++ tailWord_897291).sum := by decide
  have hdescent : baseEnd_897291 < baseStart_897291 := by decide
  rcases family_descends (prefixWord ++ tailWord_897291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897336 : List Nat := [2, 1, 2, 1, 3, 1, 2, 5, 3]
def baseStart_897336 : Nat := 118140960795 + 897336 * 2 ^ 59
def prefixEnd_897336 : Nat := 4983230072969 + 3 ^ 40 * 897336 * 2
def baseEnd_897336 : Nat := 409568601407116802198429

theorem tailTrace_897336 : CollatzResearch.WordTrace tailWord_897336 prefixEnd_897336 409568601407116802198429 := by
  unfold tailWord_897336
  simp only [CollatzResearch.WordTrace]
  refine ⟨16364266338556199816415931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21819021784741599755221241 16364266338556199816415931)
  ·
    refine ⟨24546399507834299724623897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16364266338556199816415931 24546399507834299724623897)
    ·
      refine ⟨18409799630875724793467923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24546399507834299724623897 18409799630875724793467923)
      ·
        refine ⟨27614699446313587190201885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18409799630875724793467923 27614699446313587190201885)
        ·
          refine ⟨10355512292367595196325707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27614699446313587190201885 10355512292367595196325707)
          ·
            refine ⟨15533268438551392794488561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10355512292367595196325707 15533268438551392794488561)
            ·
              refine ⟨11649951328913544595866421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15533268438551392794488561 11649951328913544595866421)
              ·
                refine ⟨1092182937085644805862477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11649951328913544595866421 1092182937085644805862477)
                ·
                  refine ⟨409568601407116802198429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1092182937085644805862477 409568601407116802198429)
                  ·
                    rfl

theorem cell20_897336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 5, 3].length) (baseStart_897336 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_897336 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_897336 prefixEnd_897336 := by exact prefixLift 897336
  have htrace : WordTrace (prefixWord ++ tailWord_897336) baseStart_897336 baseEnd_897336 := by
    simpa [prefixWord, tailWord_897336, baseEnd_897336] using wordTrace_append hprefix tailTrace_897336
  have hstable : (prefixWord ++ tailWord_897336).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897336).length < 2 ^ (prefixWord ++ tailWord_897336).sum := by decide
  have hdescent : baseEnd_897336 < baseStart_897336 := by decide
  rcases family_descends (prefixWord ++ tailWord_897336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897343 : List Nat := [1, 1, 2, 2, 4, 1, 1, 4, 4]
def baseStart_897343 : Nat := 118140960795 + 897343 * 2 ^ 59
def prefixEnd_897343 : Nat := 4983230072969 + 3 ^ 40 * 897343 * 2
def baseEnd_897343 : Nat := 409571796397855888965067

theorem tailTrace_897343 : CollatzResearch.WordTrace tailWord_897343 prefixEnd_897343 409571796397855888965067 := by
  unfold tailWord_897343
  simp only [CollatzResearch.WordTrace]
  refine ⟨32728787988087039828336683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21819191992058026552224455 32728787988087039828336683)
  ·
    refine ⟨49093181982130559742505025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32728787988087039828336683 49093181982130559742505025)
    ·
      refine ⟨36819886486597919806878769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49093181982130559742505025 36819886486597919806878769)
      ·
        refine ⟨27614914864948439855159077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36819886486597919806878769 27614914864948439855159077)
        ·
          refine ⟨5177796537177832472842327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27614914864948439855159077 5177796537177832472842327)
          ·
            refine ⟨7766694805766748709263491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5177796537177832472842327 7766694805766748709263491)
            ·
              refine ⟨11650042208650123063895237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7766694805766748709263491 11650042208650123063895237)
              ·
                refine ⟨2184382914121898074480357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11650042208650123063895237 2184382914121898074480357)
                ·
                  refine ⟨409571796397855888965067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2184382914121898074480357 409571796397855888965067)
                  ·
                    rfl

theorem cell20_897343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 4, 4].length) (baseStart_897343 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_897343 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_897343 prefixEnd_897343 := by exact prefixLift 897343
  have htrace : WordTrace (prefixWord ++ tailWord_897343) baseStart_897343 baseEnd_897343 := by
    simpa [prefixWord, tailWord_897343, baseEnd_897343] using wordTrace_append hprefix tailTrace_897343
  have hstable : (prefixWord ++ tailWord_897343).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897343).length < 2 ^ (prefixWord ++ tailWord_897343).sum := by decide
  have hdescent : baseEnd_897343 < baseStart_897343 := by decide
  rcases family_descends (prefixWord ++ tailWord_897343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897426 : List Nat := [3, 2, 3, 12]
def baseStart_897426 : Nat := 118140960795 + 897426 * 2 ^ 59
def prefixEnd_897426 : Nat := 4983230072969 + 3 ^ 40 * 897426 * 2
def baseEnd_897426 : Nat := 1685636542631590490527

theorem tailTrace_897426 : CollatzResearch.WordTrace tailWord_897426 prefixEnd_897426 1685636542631590490527 := by
  unfold tailWord_897426
  simp only [CollatzResearch.WordTrace]
  refine ⟨8182953811696586250902033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21821210164524230002405421 8182953811696586250902033)
  ·
    refine ⟨6137215358772439688176525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8182953811696586250902033 6137215358772439688176525)
    ·
      refine ⟨2301455759539664883066197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6137215358772439688176525 2301455759539664883066197)
      ·
        refine ⟨1685636542631590490527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 2301455759539664883066197 1685636542631590490527)
        ·
          rfl

theorem cell20_897426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 12].length) (baseStart_897426 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_897426 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_897426 prefixEnd_897426 := by exact prefixLift 897426
  have htrace : WordTrace (prefixWord ++ tailWord_897426) baseStart_897426 baseEnd_897426 := by
    simpa [prefixWord, tailWord_897426, baseEnd_897426] using wordTrace_append hprefix tailTrace_897426
  have hstable : (prefixWord ++ tailWord_897426).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897426).length < 2 ^ (prefixWord ++ tailWord_897426).sum := by decide
  have hdescent : baseEnd_897426 < baseStart_897426 := by decide
  rcases family_descends (prefixWord ++ tailWord_897426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897428 : List Nat := [2, 4, 2, 1, 4, 1, 2, 2, 2]
def baseStart_897428 : Nat := 118140960795 + 897428 * 2 ^ 59
def prefixEnd_897428 : Nat := 4983230072969 + 3 ^ 40 * 897428 * 2
def baseEnd_897428 : Nat := 409610592713973371131387

theorem tailTrace_897428 : CollatzResearch.WordTrace tailWord_897428 prefixEnd_897428 409610592713973371131387 := by
  unfold tailWord_897428
  simp only [CollatzResearch.WordTrace]
  refine ⟨16365944096389549672590469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21821258795186066230120625 16365944096389549672590469)
  ·
    refine ⟨3068614518073040563610713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16365944096389549672590469 3068614518073040563610713)
    ·
      refine ⟨2301460888554780422708035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3068614518073040563610713 2301460888554780422708035)
      ·
        refine ⟨3452191332832170634062053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2301460888554780422708035 3452191332832170634062053)
        ·
          refine ⟨647285874906031993886635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3452191332832170634062053 647285874906031993886635)
          ·
            refine ⟨970928812359047990829953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 647285874906031993886635 970928812359047990829953)
            ·
              refine ⟨728196609269285993122465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 970928812359047990829953 728196609269285993122465)
              ·
                refine ⟨546147456951964494841849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 728196609269285993122465 546147456951964494841849)
                ·
                  refine ⟨409610592713973371131387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 546147456951964494841849 409610592713973371131387)
                  ·
                    rfl

theorem cell20_897428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 2, 2, 2].length) (baseStart_897428 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_897428 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_897428 prefixEnd_897428 := by exact prefixLift 897428
  have htrace : WordTrace (prefixWord ++ tailWord_897428) baseStart_897428 baseEnd_897428 := by
    simpa [prefixWord, tailWord_897428, baseEnd_897428] using wordTrace_append hprefix tailTrace_897428
  have hstable : (prefixWord ++ tailWord_897428).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897428).length < 2 ^ (prefixWord ++ tailWord_897428).sum := by decide
  have hdescent : baseEnd_897428 < baseStart_897428 := by decide
  rcases family_descends (prefixWord ++ tailWord_897428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897432 : List Nat := [2, 1, 2, 5, 1, 1, 4, 2, 2]
def baseStart_897432 : Nat := 118140960795 + 897432 * 2 ^ 59
def prefixEnd_897432 : Nat := 4983230072969 + 3 ^ 40 * 897432 * 2
def baseEnd_897432 : Nat := 409612418422967134998037

theorem tailTrace_897432 : CollatzResearch.WordTrace tailWord_897432 prefixEnd_897432 409612418422967134998037 := by
  unfold tailWord_897432
  simp only [CollatzResearch.WordTrace]
  refine ⟨16366017042382304014163275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21821356056509738685551033 16366017042382304014163275)
  ·
    refine ⟨24549025563573456021244913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16366017042382304014163275 24549025563573456021244913)
    ·
      refine ⟨18411769172680092015933685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24549025563573456021244913 18411769172680092015933685)
      ·
        refine ⟨1726103359938758626493783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18411769172680092015933685 1726103359938758626493783)
        ·
          refine ⟨2589155039908137939740675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1726103359938758626493783 2589155039908137939740675)
          ·
            refine ⟨3883732559862206909611013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2589155039908137939740675 3883732559862206909611013)
            ·
              refine ⟨728199854974163795552065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3883732559862206909611013 728199854974163795552065)
              ·
                refine ⟨546149891230622846664049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 728199854974163795552065 546149891230622846664049)
                ·
                  refine ⟨409612418422967134998037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 546149891230622846664049 409612418422967134998037)
                  ·
                    rfl

theorem cell20_897432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 4, 2, 2].length) (baseStart_897432 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_897432 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_897432 prefixEnd_897432 := by exact prefixLift 897432
  have htrace : WordTrace (prefixWord ++ tailWord_897432) baseStart_897432 baseEnd_897432 := by
    simpa [prefixWord, tailWord_897432, baseEnd_897432] using wordTrace_append hprefix tailTrace_897432
  have hstable : (prefixWord ++ tailWord_897432).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897432).length < 2 ^ (prefixWord ++ tailWord_897432).sum := by decide
  have hdescent : baseEnd_897432 < baseStart_897432 := by decide
  rcases family_descends (prefixWord ++ tailWord_897432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897443 : List Nat := [1, 1, 1, 4, 1, 6, 1, 5]
def baseStart_897443 : Nat := 118140960795 + 897443 * 2 ^ 59
def prefixEnd_897443 : Nat := 4983230072969 + 3 ^ 40 * 897443 * 2
def baseEnd_897443 : Nat := 136539146374233328543775

theorem tailTrace_897443 : CollatzResearch.WordTrace tailWord_897443 prefixEnd_897443 136539146374233328543775 := by
  unfold tailWord_897443
  simp only [CollatzResearch.WordTrace]
  refine ⟨32732435287724756906976983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21821623525149837937984655 32732435287724756906976983)
  ·
    refine ⟨49098652931587135360465475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32732435287724756906976983 49098652931587135360465475)
    ·
      refine ⟨73647979397380703040698213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49098652931587135360465475 73647979397380703040698213)
      ·
        refine ⟨13808996137008881820130915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73647979397380703040698213 13808996137008881820130915)
        ·
          refine ⟨20713494205513322730196373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13808996137008881820130915 20713494205513322730196373)
          ·
            refine ⟨970945040883437002977955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 20713494205513322730196373 970945040883437002977955)
            ·
              refine ⟨1456417561325155504466933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 970945040883437002977955 1456417561325155504466933)
              ·
                refine ⟨136539146374233328543775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1456417561325155504466933 136539146374233328543775)
                ·
                  rfl

theorem cell20_897443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 5].length) (baseStart_897443 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_897443 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_897443 prefixEnd_897443 := by exact prefixLift 897443
  have htrace : WordTrace (prefixWord ++ tailWord_897443) baseStart_897443 baseEnd_897443 := by
    simpa [prefixWord, tailWord_897443, baseEnd_897443] using wordTrace_append hprefix tailTrace_897443
  have hstable : (prefixWord ++ tailWord_897443).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897443).length < 2 ^ (prefixWord ++ tailWord_897443).sum := by decide
  have hdescent : baseEnd_897443 < baseStart_897443 := by decide
  rcases family_descends (prefixWord ++ tailWord_897443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897453 : List Nat := [1, 5, 2, 2, 2, 1, 1, 2, 4]
def baseStart_897453 : Nat := 118140960795 + 897453 * 2 ^ 59
def prefixEnd_897453 : Nat := 4983230072969 + 3 ^ 40 * 897453 * 2
def baseEnd_897453 : Nat := 409622003395184395297951

theorem tailTrace_897453 : CollatzResearch.WordTrace tailWord_897453 prefixEnd_897453 409622003395184395297951 := by
  unfold tailWord_897453
  simp only [CollatzResearch.WordTrace]
  refine ⟨32732800017688528614841013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21821866678459019076560675 32732800017688528614841013)
  ·
    refine ⟨3068700001658299557641345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32732800017688528614841013 3068700001658299557641345)
    ·
      refine ⟨2301525001243724668231009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3068700001658299557641345 2301525001243724668231009)
      ·
        refine ⟨1726143750932793501173257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2301525001243724668231009 1726143750932793501173257)
        ·
          refine ⟨1294607813199595125879943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1726143750932793501173257 1294607813199595125879943)
          ·
            refine ⟨1941911719799392688819915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1294607813199595125879943 1941911719799392688819915)
            ·
              refine ⟨2912867579699089033229873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1941911719799392688819915 2912867579699089033229873)
              ·
                refine ⟨2184650684774316774922405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2912867579699089033229873 2184650684774316774922405)
                ·
                  refine ⟨409622003395184395297951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2184650684774316774922405 409622003395184395297951)
                  ·
                    rfl

theorem cell20_897453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_897453 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_897453 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_897453 prefixEnd_897453 := by exact prefixLift 897453
  have htrace : WordTrace (prefixWord ++ tailWord_897453) baseStart_897453 baseEnd_897453 := by
    simpa [prefixWord, tailWord_897453, baseEnd_897453] using wordTrace_append hprefix tailTrace_897453
  have hstable : (prefixWord ++ tailWord_897453).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897453).length < 2 ^ (prefixWord ++ tailWord_897453).sum := by decide
  have hdescent : baseEnd_897453 < baseStart_897453 := by decide
  rcases family_descends (prefixWord ++ tailWord_897453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897457 : List Nat := [1, 2, 2, 4, 1, 2, 1, 1, 6]
def baseStart_897457 : Nat := 118140960795 + 897457 * 2 ^ 59
def prefixEnd_897457 : Nat := 4983230072969 + 3 ^ 40 * 897457 * 2
def baseEnd_897457 : Nat := 409623829104178159164601

theorem tailTrace_897457 : CollatzResearch.WordTrace tailWord_897457 prefixEnd_897457 409623829104178159164601 := by
  unfold tailWord_897457
  simp only [CollatzResearch.WordTrace]
  refine ⟨32732945909674037297986625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21821963939782691531991083 32732945909674037297986625)
  ·
    refine ⟨24549709432255527973489969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32732945909674037297986625 24549709432255527973489969)
    ·
      refine ⟨18412282074191645980117477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24549709432255527973489969 18412282074191645980117477)
      ·
        refine ⟨3452302888910933621272027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18412282074191645980117477 3452302888910933621272027)
        ·
          refine ⟨5178454333366400431908041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3452302888910933621272027 5178454333366400431908041)
          ·
            refine ⟨3883840750024800323931031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5178454333366400431908041 3883840750024800323931031)
            ·
              refine ⟨5825761125037200485896547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3883840750024800323931031 5825761125037200485896547)
              ·
                refine ⟨8738641687555800728844821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5825761125037200485896547 8738641687555800728844821)
                ·
                  refine ⟨409623829104178159164601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8738641687555800728844821 409623829104178159164601)
                  ·
                    rfl

theorem cell20_897457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 6].length) (baseStart_897457 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_897457 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_897457 prefixEnd_897457 := by exact prefixLift 897457
  have htrace : WordTrace (prefixWord ++ tailWord_897457) baseStart_897457 baseEnd_897457 := by
    simpa [prefixWord, tailWord_897457, baseEnd_897457] using wordTrace_append hprefix tailTrace_897457
  have hstable : (prefixWord ++ tailWord_897457).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897457).length < 2 ^ (prefixWord ++ tailWord_897457).sum := by decide
  have hdescent : baseEnd_897457 < baseStart_897457 := by decide
  rcases family_descends (prefixWord ++ tailWord_897457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897484 : List Nat := [2, 2, 1, 4, 3, 2, 1, 2, 3]
def baseStart_897484 : Nat := 118140960795 + 897484 * 2 ^ 59
def prefixEnd_897484 : Nat := 4983230072969 + 3 ^ 40 * 897484 * 2
def baseEnd_897484 : Nat := 409636152639886065264491

theorem tailTrace_897484 : CollatzResearch.WordTrace tailWord_897484 prefixEnd_897484 409636152639886065264491 := by
  unfold tailWord_897484
  simp only [CollatzResearch.WordTrace]
  refine ⟨16366965340288110454609753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21822620453717480606146337 16366965340288110454609753)
  ·
    refine ⟨12275224005216082840957315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16366965340288110454609753 12275224005216082840957315)
    ·
      refine ⟨18412836007824124261435973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12275224005216082840957315 18412836007824124261435973)
      ·
        refine ⟨3452406751467023299019245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18412836007824124261435973 3452406751467023299019245)
        ·
          refine ⟨1294652531800133737132217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3452406751467023299019245 1294652531800133737132217)
          ·
            refine ⟨970989398850100302849163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1294652531800133737132217 970989398850100302849163)
            ·
              refine ⟨1456484098275150454273745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 970989398850100302849163 1456484098275150454273745)
              ·
                refine ⟨1092363073706362840705309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1456484098275150454273745 1092363073706362840705309)
                ·
                  refine ⟨409636152639886065264491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1092363073706362840705309 409636152639886065264491)
                  ·
                    rfl

theorem cell20_897484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 2, 3].length) (baseStart_897484 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_897484 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_897484 prefixEnd_897484 := by exact prefixLift 897484
  have htrace : WordTrace (prefixWord ++ tailWord_897484) baseStart_897484 baseEnd_897484 := by
    simpa [prefixWord, tailWord_897484, baseEnd_897484] using wordTrace_append hprefix tailTrace_897484
  have hstable : (prefixWord ++ tailWord_897484).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897484).length < 2 ^ (prefixWord ++ tailWord_897484).sum := by decide
  have hdescent : baseEnd_897484 < baseStart_897484 := by decide
  rcases family_descends (prefixWord ++ tailWord_897484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897505 : List Nat := [1, 2, 3, 1, 2, 2, 5, 1, 3]
def baseStart_897505 : Nat := 118140960795 + 897505 * 2 ^ 59
def prefixEnd_897505 : Nat := 4983230072969 + 3 ^ 40 * 897505 * 2
def baseEnd_897505 : Nat := 409645737612103325564405

theorem tailTrace_897505 : CollatzResearch.WordTrace tailWord_897505 prefixEnd_897505 409645737612103325564405 := by
  unfold tailWord_897505
  simp only [CollatzResearch.WordTrace]
  refine ⟨32734696613500141495733969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21823131075666760997155979 32734696613500141495733969)
  ·
    refine ⟨24551022460125106121800477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32734696613500141495733969 24551022460125106121800477)
    ·
      refine ⟨9206633422546914795675179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24551022460125106121800477 9206633422546914795675179)
      ·
        refine ⟨13809950133820372193512769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9206633422546914795675179 13809950133820372193512769)
        ·
          refine ⟨10357462600365279145134577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13809950133820372193512769 10357462600365279145134577)
          ·
            refine ⟨7768096950273959358850933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10357462600365279145134577 7768096950273959358850933)
            ·
              refine ⟨728259089088183689892275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7768096950273959358850933 728259089088183689892275)
              ·
                refine ⟨1092388633632275534838413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 728259089088183689892275 1092388633632275534838413)
                ·
                  refine ⟨409645737612103325564405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1092388633632275534838413 409645737612103325564405)
                  ·
                    rfl

theorem cell20_897505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 5, 1, 3].length) (baseStart_897505 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_897505 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_897505 prefixEnd_897505 := by exact prefixLift 897505
  have htrace : WordTrace (prefixWord ++ tailWord_897505) baseStart_897505 baseEnd_897505 := by
    simpa [prefixWord, tailWord_897505, baseEnd_897505] using wordTrace_append hprefix tailTrace_897505
  have hstable : (prefixWord ++ tailWord_897505).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897505).length < 2 ^ (prefixWord ++ tailWord_897505).sum := by decide
  have hdescent : baseEnd_897505 < baseStart_897505 := by decide
  rcases family_descends (prefixWord ++ tailWord_897505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897525 : List Nat := [1, 3, 5, 1, 2, 2, 1, 3, 2]
def baseStart_897525 : Nat := 118140960795 + 897525 * 2 ^ 59
def prefixEnd_897525 : Nat := 4983230072969 + 3 ^ 40 * 897525 * 2
def baseEnd_897525 : Nat := 409654866157072144897657

theorem tailTrace_897525 : CollatzResearch.WordTrace tailWord_897525 prefixEnd_897525 409654866157072144897657 := by
  unfold tailWord_897525
  simp only [CollatzResearch.WordTrace]
  refine ⟨32735426073427684911462029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21823617382285123274308019 32735426073427684911462029)
  ·
    refine ⟨12275784777535381841798261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32735426073427684911462029 12275784777535381841798261)
    ·
      refine ⟨1150854822893942047668587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12275784777535381841798261 1150854822893942047668587)
      ·
        refine ⟨1726282234340913071502881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1150854822893942047668587 1726282234340913071502881)
        ·
          refine ⟨1294711675755684803627161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1726282234340913071502881 1294711675755684803627161)
          ·
            refine ⟨971033756816763602720371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1294711675755684803627161 971033756816763602720371)
            ·
              refine ⟨1456550635225145404080557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 971033756816763602720371 1456550635225145404080557)
              ·
                refine ⟨546206488209429526530209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1456550635225145404080557 546206488209429526530209)
                ·
                  refine ⟨409654866157072144897657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 546206488209429526530209 409654866157072144897657)
                  ·
                    rfl

theorem cell20_897525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 3, 2].length) (baseStart_897525 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_897525 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_897525 prefixEnd_897525 := by exact prefixLift 897525
  have htrace : WordTrace (prefixWord ++ tailWord_897525) baseStart_897525 baseEnd_897525 := by
    simpa [prefixWord, tailWord_897525, baseEnd_897525] using wordTrace_append hprefix tailTrace_897525
  have hstable : (prefixWord ++ tailWord_897525).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897525).length < 2 ^ (prefixWord ++ tailWord_897525).sum := by decide
  have hdescent : baseEnd_897525 < baseStart_897525 := by decide
  rcases family_descends (prefixWord ++ tailWord_897525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897526 : List Nat := [5, 1, 1, 1, 2, 1, 1, 1, 7]
def baseStart_897526 : Nat := 118140960795 + 897526 * 2 ^ 59
def prefixEnd_897526 : Nat := 4983230072969 + 3 ^ 40 * 897526 * 2
def baseEnd_897526 : Nat := 409655322584320585864319

theorem tailTrace_897526 : CollatzResearch.WordTrace tailWord_897526 prefixEnd_897526 409655322584320585864319 := by
  unfold tailWord_897526
  simp only [CollatzResearch.WordTrace]
  refine ⟨2045966409151503880140527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21823641697616041388165621 2045966409151503880140527)
  ·
    refine ⟨3068949613727255820210791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2045966409151503880140527 3068949613727255820210791)
    ·
      refine ⟨4603424420590883730316187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3068949613727255820210791 4603424420590883730316187)
      ·
        refine ⟨6905136630886325595474281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4603424420590883730316187 6905136630886325595474281)
        ·
          refine ⟨5178852473164744196605711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6905136630886325595474281 5178852473164744196605711)
          ·
            refine ⟨7768278709747116294908567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5178852473164744196605711 7768278709747116294908567)
            ·
              refine ⟨11652418064620674442362851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7768278709747116294908567 11652418064620674442362851)
              ·
                refine ⟨17478627096931011663544277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11652418064620674442362851 17478627096931011663544277)
                ·
                  refine ⟨409655322584320585864319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17478627096931011663544277 409655322584320585864319)
                  ·
                    rfl

theorem cell20_897526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_897526 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_897526 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_897526 prefixEnd_897526 := by exact prefixLift 897526
  have htrace : WordTrace (prefixWord ++ tailWord_897526) baseStart_897526 baseEnd_897526 := by
    simpa [prefixWord, tailWord_897526, baseEnd_897526] using wordTrace_append hprefix tailTrace_897526
  have hstable : (prefixWord ++ tailWord_897526).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897526).length < 2 ^ (prefixWord ++ tailWord_897526).sum := by decide
  have hdescent : baseEnd_897526 < baseStart_897526 := by decide
  rcases family_descends (prefixWord ++ tailWord_897526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897550 : List Nat := [4, 1, 1, 2, 3, 1, 3, 1, 4]
def baseStart_897550 : Nat := 118140960795 + 897550 * 2 ^ 59
def prefixEnd_897550 : Nat := 4983230072969 + 3 ^ 40 * 897550 * 2
def baseEnd_897550 : Nat := 409666276838283169064221

theorem tailTrace_897550 : CollatzResearch.WordTrace tailWord_897550 prefixEnd_897550 409666276838283169064221 := by
  unfold tailWord_897550
  simp only [CollatzResearch.WordTrace]
  refine ⟨4092042237292139272640263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21824225265558076120748069 4092042237292139272640263)
  ·
    refine ⟨6138063355938208908960395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4092042237292139272640263 6138063355938208908960395)
    ·
      refine ⟨9207095033907313363440593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6138063355938208908960395 9207095033907313363440593)
      ·
        refine ⟨6905321275430485022580445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9207095033907313363440593 6905321275430485022580445)
        ·
          refine ⟨2589495478286431883467667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6905321275430485022580445 2589495478286431883467667)
          ·
            refine ⟨3884243217429647825201501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2589495478286431883467667 3884243217429647825201501)
            ·
              refine ⟨1456591206536117934450563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3884243217429647825201501 1456591206536117934450563)
              ·
                refine ⟨2184886809804176901675845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1456591206536117934450563 2184886809804176901675845)
                ·
                  refine ⟨409666276838283169064221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2184886809804176901675845 409666276838283169064221)
                  ·
                    rfl

theorem cell20_897550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_897550 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_897550 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_897550 prefixEnd_897550 := by exact prefixLift 897550
  have htrace : WordTrace (prefixWord ++ tailWord_897550) baseStart_897550 baseEnd_897550 := by
    simpa [prefixWord, tailWord_897550, baseEnd_897550] using wordTrace_append hprefix tailTrace_897550
  have hstable : (prefixWord ++ tailWord_897550).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897550).length < 2 ^ (prefixWord ++ tailWord_897550).sum := by decide
  have hdescent : baseEnd_897550 < baseStart_897550 := by decide
  rcases family_descends (prefixWord ++ tailWord_897550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897560 : List Nat := [2, 1, 2, 3, 3, 3, 2, 1, 3]
def baseStart_897560 : Nat := 118140960795 + 897560 * 2 ^ 59
def prefixEnd_897560 : Nat := 4983230072969 + 3 ^ 40 * 897560 * 2
def baseEnd_897560 : Nat := 409670841110767578730847

theorem tailTrace_897560 : CollatzResearch.WordTrace tailWord_897560 prefixEnd_897560 409670841110767578730847 := by
  unfold tailWord_897560
  simp only [CollatzResearch.WordTrace]
  refine ⟨16368351314150442944493067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21824468418867257259324089 16368351314150442944493067)
  ·
    refine ⟨24552526971225664416739601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16368351314150442944493067 24552526971225664416739601)
    ·
      refine ⟨18414395228419248312554701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24552526971225664416739601 18414395228419248312554701)
      ·
        refine ⟨6905398210657218117208013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18414395228419248312554701 6905398210657218117208013)
        ·
          refine ⟨2589524328996456793953005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6905398210657218117208013 2589524328996456793953005)
          ·
            refine ⟨971071623373671297732377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2589524328996456793953005 971071623373671297732377)
            ·
              refine ⟨728303717530253473299283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 971071623373671297732377 728303717530253473299283)
              ·
                refine ⟨1092455576295380209948925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 728303717530253473299283 1092455576295380209948925)
                ·
                  refine ⟨409670841110767578730847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1092455576295380209948925 409670841110767578730847)
                  ·
                    rfl

theorem cell20_897560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 2, 1, 3].length) (baseStart_897560 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_897560 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_897560 prefixEnd_897560 := by exact prefixLift 897560
  have htrace : WordTrace (prefixWord ++ tailWord_897560) baseStart_897560 baseEnd_897560 := by
    simpa [prefixWord, tailWord_897560, baseEnd_897560] using wordTrace_append hprefix tailTrace_897560
  have hstable : (prefixWord ++ tailWord_897560).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897560).length < 2 ^ (prefixWord ++ tailWord_897560).sum := by decide
  have hdescent : baseEnd_897560 < baseStart_897560 := by decide
  rcases family_descends (prefixWord ++ tailWord_897560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897585 : List Nat := [1, 2, 2, 3, 1, 1, 2, 1, 7]
def baseStart_897585 : Nat := 118140960795 + 897585 * 2 ^ 59
def prefixEnd_897585 : Nat := 4983230072969 + 3 ^ 40 * 897585 * 2
def baseEnd_897585 : Nat := 409682251791978602897411

theorem tailTrace_897585 : CollatzResearch.WordTrace tailWord_897585 prefixEnd_897585 409682251791978602897411 := by
  unfold tailWord_897585
  simp only [CollatzResearch.WordTrace]
  refine ⟨32737614453210315158646209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21825076302140210105764139 32737614453210315158646209)
  ·
    refine ⟨24553210839907736368984657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32737614453210315158646209 24553210839907736368984657)
    ·
      refine ⟨18414908129930802276738493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24553210839907736368984657 18414908129930802276738493)
      ·
        refine ⟨6905590548724050853776935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18414908129930802276738493 6905590548724050853776935)
        ·
          refine ⟨10358385823086076280665403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6905590548724050853776935 10358385823086076280665403)
          ·
            refine ⟨15537578734629114420998105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10358385823086076280665403 15537578734629114420998105)
            ·
              refine ⟨11653184050971835815748579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15537578734629114420998105 11653184050971835815748579)
              ·
                refine ⟨17479776076457753723622869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11653184050971835815748579 17479776076457753723622869)
                ·
                  refine ⟨409682251791978602897411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17479776076457753723622869 409682251791978602897411)
                  ·
                    rfl

theorem cell20_897585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 7].length) (baseStart_897585 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_897585 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_897585 prefixEnd_897585 := by exact prefixLift 897585
  have htrace : WordTrace (prefixWord ++ tailWord_897585) baseStart_897585 baseEnd_897585 := by
    simpa [prefixWord, tailWord_897585, baseEnd_897585] using wordTrace_append hprefix tailTrace_897585
  have hstable : (prefixWord ++ tailWord_897585).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897585).length < 2 ^ (prefixWord ++ tailWord_897585).sum := by decide
  have hdescent : baseEnd_897585 < baseStart_897585 := by decide
  rcases family_descends (prefixWord ++ tailWord_897585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897605 : List Nat := [1, 3, 1, 1, 1, 5, 4, 2, 2]
def baseStart_897605 : Nat := 118140960795 + 897605 * 2 ^ 59
def prefixEnd_897605 : Nat := 4983230072969 + 3 ^ 40 * 897605 * 2
def baseEnd_897605 : Nat := 409691380336947422230663

theorem tailTrace_897605 : CollatzResearch.WordTrace tailWord_897605 prefixEnd_897605 409691380336947422230663 := by
  unfold tailWord_897605
  simp only [CollatzResearch.WordTrace]
  refine ⟨32738343913137858574374269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21825562608758572382916179 32738343913137858574374269)
  ·
    refine ⟨12276878967426696965390351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32738343913137858574374269 12276878967426696965390351)
    ·
      refine ⟨18415318451140045448085527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12276878967426696965390351 18415318451140045448085527)
      ·
        refine ⟨27622977676710068172128291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18415318451140045448085527 27622977676710068172128291)
        ·
          refine ⟨41434466515065102258192437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27622977676710068172128291 41434466515065102258192437)
          ·
            refine ⟨3884481235787353336705541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41434466515065102258192437 3884481235787353336705541)
            ·
              refine ⟨728340231710128750632289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3884481235787353336705541 728340231710128750632289)
              ·
                refine ⟨546255173782596562974217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 728340231710128750632289 546255173782596562974217)
                ·
                  refine ⟨409691380336947422230663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 546255173782596562974217 409691380336947422230663)
                  ·
                    rfl

theorem cell20_897605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 4, 2, 2].length) (baseStart_897605 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_897605 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_897605 prefixEnd_897605 := by exact prefixLift 897605
  have htrace : WordTrace (prefixWord ++ tailWord_897605) baseStart_897605 baseEnd_897605 := by
    simpa [prefixWord, tailWord_897605, baseEnd_897605] using wordTrace_append hprefix tailTrace_897605
  have hstable : (prefixWord ++ tailWord_897605).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897605).length < 2 ^ (prefixWord ++ tailWord_897605).sum := by decide
  have hdescent : baseEnd_897605 < baseStart_897605 := by decide
  rcases family_descends (prefixWord ++ tailWord_897605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897633 : List Nat := [1, 2, 3, 1, 1, 5, 3, 4]
def baseStart_897633 : Nat := 118140960795 + 897633 * 2 ^ 59
def prefixEnd_897633 : Nat := 4983230072969 + 3 ^ 40 * 897633 * 2
def baseEnd_897633 : Nat := 136568053433301256432405

theorem tailTrace_897633 : CollatzResearch.WordTrace tailWord_897633 prefixEnd_897633 136568053433301256432405 := by
  unfold tailWord_897633
  simp only [CollatzResearch.WordTrace]
  refine ⟨32739365157036419356393553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21826243438024279570929035 32739365157036419356393553)
  ·
    refine ⟨24554523867777314517295165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32739365157036419356393553 24554523867777314517295165)
    ·
      refine ⟨9207946450416492943985687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24554523867777314517295165 9207946450416492943985687)
      ·
        refine ⟨13811919675624739415978531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9207946450416492943985687 13811919675624739415978531)
        ·
          refine ⟨20717879513437109123967797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13811919675624739415978531 20717879513437109123967797)
          ·
            refine ⟨1942301204384728980371981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20717879513437109123967797 1942301204384728980371981)
            ·
              refine ⟨728362951644273367639493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1942301204384728980371981 728362951644273367639493)
              ·
                refine ⟨136568053433301256432405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 728362951644273367639493 136568053433301256432405)
                ·
                  rfl

theorem cell20_897633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 3, 4].length) (baseStart_897633 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_897633 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_897633 prefixEnd_897633 := by exact prefixLift 897633
  have htrace : WordTrace (prefixWord ++ tailWord_897633) baseStart_897633 baseEnd_897633 := by
    simpa [prefixWord, tailWord_897633, baseEnd_897633] using wordTrace_append hprefix tailTrace_897633
  have hstable : (prefixWord ++ tailWord_897633).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897633).length < 2 ^ (prefixWord ++ tailWord_897633).sum := by decide
  have hdescent : baseEnd_897633 < baseStart_897633 := by decide
  rcases family_descends (prefixWord ++ tailWord_897633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897653 : List Nat := [1, 3, 4, 2, 3, 1, 1, 2, 3]
def baseStart_897653 : Nat := 118140960795 + 897653 * 2 ^ 59
def prefixEnd_897653 : Nat := 4983230072969 + 3 ^ 40 * 897653 * 2
def baseEnd_897653 : Nat := 409713288844872588630467

theorem tailTrace_897653 : CollatzResearch.WordTrace tailWord_897653 prefixEnd_897653 409713288844872588630467 := by
  unfold tailWord_897653
  simp only [CollatzResearch.WordTrace]
  refine ⟨32740094616963962772121613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21826729744642641848081075 32740094616963962772121613)
  ·
    refine ⟨12277535481361486039545605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32740094616963962772121613 12277535481361486039545605)
    ·
      refine ⟨2302037902755278632414801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12277535481361486039545605 2302037902755278632414801)
      ·
        refine ⟨1726528427066458974311101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2302037902755278632414801 1726528427066458974311101)
        ·
          refine ⟨647448160149922115366663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1726528427066458974311101 647448160149922115366663)
          ·
            refine ⟨971172240224883173049995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 647448160149922115366663 971172240224883173049995)
            ·
              refine ⟨1456758360337324759574993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 971172240224883173049995 1456758360337324759574993)
              ·
                refine ⟨1092568770252993569681245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1456758360337324759574993 1092568770252993569681245)
                ·
                  refine ⟨409713288844872588630467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1092568770252993569681245 409713288844872588630467)
                  ·
                    rfl

theorem cell20_897653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 2, 3].length) (baseStart_897653 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_897653 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_897653 prefixEnd_897653 := by exact prefixLift 897653
  have htrace : WordTrace (prefixWord ++ tailWord_897653) baseStart_897653 baseEnd_897653 := by
    simpa [prefixWord, tailWord_897653, baseEnd_897653] using wordTrace_append hprefix tailTrace_897653
  have hstable : (prefixWord ++ tailWord_897653).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897653).length < 2 ^ (prefixWord ++ tailWord_897653).sum := by decide
  have hdescent : baseEnd_897653 < baseStart_897653 := by decide
  rcases family_descends (prefixWord ++ tailWord_897653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897657 : List Nat := [1, 2, 1, 3, 3, 4, 1, 2, 3]
def baseStart_897657 : Nat := 118140960795 + 897657 * 2 ^ 59
def prefixEnd_897657 : Nat := 4983230072969 + 3 ^ 40 * 897657 * 2
def baseEnd_897657 : Nat := 409715114553866352497117

theorem tailTrace_897657 : CollatzResearch.WordTrace tailWord_897657 prefixEnd_897657 409715114553866352497117 := by
  unfold tailWord_897657
  simp only [CollatzResearch.WordTrace]
  refine ⟨32740240508949471455267225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21826827005966314303511483 32740240508949471455267225)
  ·
    refine ⟨24555180381712103591450419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32740240508949471455267225 24555180381712103591450419)
    ·
      refine ⟨36832770572568155387175629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24555180381712103591450419 36832770572568155387175629)
      ·
        refine ⟨13812288964713058270190861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36832770572568155387175629 13812288964713058270190861)
        ·
          refine ⟨5179608361767396851321573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13812288964713058270190861 5179608361767396851321573)
          ·
            refine ⟨971176567831386909622795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5179608361767396851321573 971176567831386909622795)
            ·
              refine ⟨1456764851747080364434193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 971176567831386909622795 1456764851747080364434193)
              ·
                refine ⟨1092573638810310273325645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1456764851747080364434193 1092573638810310273325645)
                ·
                  refine ⟨409715114553866352497117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1092573638810310273325645 409715114553866352497117)
                  ·
                    rfl

theorem cell20_897657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 2, 3].length) (baseStart_897657 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_897657 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_897657 prefixEnd_897657 := by exact prefixLift 897657
  have htrace : WordTrace (prefixWord ++ tailWord_897657) baseStart_897657 baseEnd_897657 := by
    simpa [prefixWord, tailWord_897657, baseEnd_897657] using wordTrace_append hprefix tailTrace_897657
  have hstable : (prefixWord ++ tailWord_897657).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897657).length < 2 ^ (prefixWord ++ tailWord_897657).sum := by decide
  have hdescent : baseEnd_897657 < baseStart_897657 := by decide
  rcases family_descends (prefixWord ++ tailWord_897657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897664 : List Nat := [2, 1, 1, 2, 1, 5, 2, 4, 2]
def baseStart_897664 : Nat := 118140960795 + 897664 * 2 ^ 59
def prefixEnd_897664 : Nat := 4983230072969 + 3 ^ 40 * 897664 * 2
def baseEnd_897664 : Nat := 409718309544605439263755

theorem tailTrace_897664 : CollatzResearch.WordTrace tailWord_897664 prefixEnd_897664 409718309544605439263755 := by
  unfold tailWord_897664
  simp only [CollatzResearch.WordTrace]
  refine ⟨16370247909962055825386023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21826997213282741100514697 16370247909962055825386023)
  ·
    refine ⟨24555371864943083738079035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16370247909962055825386023 24555371864943083738079035)
    ·
      refine ⟨36833057797414625607118553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24555371864943083738079035 36833057797414625607118553)
      ·
        refine ⟨27624793348060969205338915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36833057797414625607118553 27624793348060969205338915)
        ·
          refine ⟨41437190022091453808008373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27624793348060969205338915 41437190022091453808008373)
          ·
            refine ⟨3884736564571073794500785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41437190022091453808008373 3884736564571073794500785)
            ·
              refine ⟨2913552423428305345875589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3884736564571073794500785 2913552423428305345875589)
              ·
                refine ⟨546291079392807252351673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2913552423428305345875589 546291079392807252351673)
                ·
                  refine ⟨409718309544605439263755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 546291079392807252351673 409718309544605439263755)
                  ·
                    rfl

theorem cell20_897664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 4, 2].length) (baseStart_897664 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_897664 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_897664 prefixEnd_897664 := by exact prefixLift 897664
  have htrace : WordTrace (prefixWord ++ tailWord_897664) baseStart_897664 baseEnd_897664 := by
    simpa [prefixWord, tailWord_897664, baseEnd_897664] using wordTrace_append hprefix tailTrace_897664
  have hstable : (prefixWord ++ tailWord_897664).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897664).length < 2 ^ (prefixWord ++ tailWord_897664).sum := by decide
  have hdescent : baseEnd_897664 < baseStart_897664 := by decide
  rcases family_descends (prefixWord ++ tailWord_897664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897674 : List Nat := [3, 1, 2, 3, 3, 1, 3, 1, 3]
def baseStart_897674 : Nat := 118140960795 + 897674 * 2 ^ 59
def prefixEnd_897674 : Nat := 4983230072969 + 3 ^ 40 * 897674 * 2
def baseEnd_897674 : Nat := 409722873817089848930381

theorem tailTrace_897674 : CollatzResearch.WordTrace tailWord_897674 prefixEnd_897674 409722873817089848930381 := by
  unfold tailWord_897674
  simp only [CollatzResearch.WordTrace]
  refine ⟨8185215137471970839659019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21827240366591922239090717 8185215137471970839659019)
  ·
    refine ⟨12277822706207956259488529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8185215137471970839659019 12277822706207956259488529)
    ·
      refine ⟨9208367029655967194616397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12277822706207956259488529 9208367029655967194616397)
      ·
        refine ⟨3453137636120987697981149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9208367029655967194616397 3453137636120987697981149)
        ·
          refine ⟨1294926613545370386742931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3453137636120987697981149 1294926613545370386742931)
          ·
            refine ⟨1942389920318055580114397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1294926613545370386742931 1942389920318055580114397)
            ·
              refine ⟨728396220119270842542899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1942389920318055580114397 728396220119270842542899)
              ·
                refine ⟨1092594330178906263814349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 728396220119270842542899 1092594330178906263814349)
                ·
                  refine ⟨409722873817089848930381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1092594330178906263814349 409722873817089848930381)
                  ·
                    rfl

theorem cell20_897674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 3, 1, 3].length) (baseStart_897674 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_897674 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_897674 prefixEnd_897674 := by exact prefixLift 897674
  have htrace : WordTrace (prefixWord ++ tailWord_897674) baseStart_897674 baseEnd_897674 := by
    simpa [prefixWord, tailWord_897674, baseEnd_897674] using wordTrace_append hprefix tailTrace_897674
  have hstable : (prefixWord ++ tailWord_897674).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897674).length < 2 ^ (prefixWord ++ tailWord_897674).sum := by decide
  have hdescent : baseEnd_897674 < baseStart_897674 := by decide
  rcases family_descends (prefixWord ++ tailWord_897674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897709 : List Nat := [1, 5, 2, 1, 1, 4, 6]
def baseStart_897709 : Nat := 118140960795 + 897709 * 2 ^ 59
def prefixEnd_897709 : Nat := 4983230072969 + 3 ^ 40 * 897709 * 2
def baseEnd_897709 : Nat := 45526538752309475862619

theorem tailTrace_897709 : CollatzResearch.WordTrace tailWord_897709 prefixEnd_897709 45526538752309475862619 := by
  unfold tailWord_897709
  simp only [CollatzResearch.WordTrace]
  refine ⟨32742137104761084336160181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21828091403174056224106787 32742137104761084336160181)
  ·
    refine ⟨3069575353571351656515017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32742137104761084336160181 3069575353571351656515017)
    ·
      refine ⟨2302181515178513742386263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3069575353571351656515017 2302181515178513742386263)
      ·
        refine ⟨3453272272767770613579395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2302181515178513742386263 3453272272767770613579395)
        ·
          refine ⟨5179908409151655920369093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3453272272767770613579395 5179908409151655920369093)
          ·
            refine ⟨971232826715935485069205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5179908409151655920369093 971232826715935485069205)
            ·
              refine ⟨45526538752309475862619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 971232826715935485069205 45526538752309475862619)
              ·
                rfl

theorem cell20_897709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 6].length) (baseStart_897709 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_897709 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_897709 prefixEnd_897709 := by exact prefixLift 897709
  have htrace : WordTrace (prefixWord ++ tailWord_897709) baseStart_897709 baseEnd_897709 := by
    simpa [prefixWord, tailWord_897709, baseEnd_897709] using wordTrace_append hprefix tailTrace_897709
  have hstable : (prefixWord ++ tailWord_897709).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897709).length < 2 ^ (prefixWord ++ tailWord_897709).sum := by decide
  have hdescent : baseEnd_897709 < baseStart_897709 := by decide
  rcases family_descends (prefixWord ++ tailWord_897709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897719 : List Nat := [1, 1, 3, 1, 7, 1, 1, 1, 4]
def baseStart_897719 : Nat := 118140960795 + 897719 * 2 ^ 59
def prefixEnd_897719 : Nat := 4983230072969 + 3 ^ 40 * 897719 * 2
def baseEnd_897719 : Nat := 409743413043269692430197

theorem tailTrace_897719 : CollatzResearch.WordTrace tailWord_897719 prefixEnd_897719 409743413043269692430197 := by
  unfold tailWord_897719
  simp only [CollatzResearch.WordTrace]
  refine ⟨32742501834724856044024211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21828334556483237362682807 32742501834724856044024211)
  ·
    refine ⟨49113752752087284066036317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32742501834724856044024211 49113752752087284066036317)
    ·
      refine ⟨18417657282032731524763619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49113752752087284066036317 18417657282032731524763619)
      ·
        refine ⟨27626485923049097287145429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18417657282032731524763619 27626485923049097287145429)
        ·
          refine ⟨647495763821463217667471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 27626485923049097287145429 647495763821463217667471)
          ·
            refine ⟨971243645732194826501207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 647495763821463217667471 971243645732194826501207)
            ·
              refine ⟨1456865468598292239751811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 971243645732194826501207 1456865468598292239751811)
              ·
                refine ⟨2185298202897438359627717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1456865468598292239751811 2185298202897438359627717)
                ·
                  refine ⟨409743413043269692430197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2185298202897438359627717 409743413043269692430197)
                  ·
                    rfl

theorem cell20_897719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 1, 4].length) (baseStart_897719 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_897719 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_897719 prefixEnd_897719 := by exact prefixLift 897719
  have htrace : WordTrace (prefixWord ++ tailWord_897719) baseStart_897719 baseEnd_897719 := by
    simpa [prefixWord, tailWord_897719, baseEnd_897719] using wordTrace_append hprefix tailTrace_897719
  have hstable : (prefixWord ++ tailWord_897719).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897719).length < 2 ^ (prefixWord ++ tailWord_897719).sum := by decide
  have hdescent : baseEnd_897719 < baseStart_897719 := by decide
  rcases family_descends (prefixWord ++ tailWord_897719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897768 : List Nat := [2, 1, 4, 1, 4, 8]
def baseStart_897768 : Nat := 118140960795 + 897768 * 2 ^ 59
def prefixEnd_897768 : Nat := 4983230072969 + 3 ^ 40 * 897768 * 2
def baseEnd_897768 : Nat := 15176510295497899992469

theorem tailTrace_897768 : CollatzResearch.WordTrace tailWord_897768 prefixEnd_897768 15176510295497899992469 := by
  unfold tailWord_897768
  simp only [CollatzResearch.WordTrace]
  refine ⟨16372144505773668706278979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21829526007698224941705305 16372144505773668706278979)
  ·
    refine ⟨24558216758660503059418469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16372144505773668706278979 24558216758660503059418469)
    ·
      refine ⟨4604665642248844323640963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24558216758660503059418469 4604665642248844323640963)
      ·
        refine ⟨6906998463373266485461445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4604665642248844323640963 6906998463373266485461445)
        ·
          refine ⟨1295062211882487466024021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6906998463373266485461445 1295062211882487466024021)
          ·
            refine ⟨15176510295497899992469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1295062211882487466024021 15176510295497899992469)
            ·
              rfl

theorem cell20_897768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 8].length) (baseStart_897768 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_897768 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_897768 prefixEnd_897768 := by exact prefixLift 897768
  have htrace : WordTrace (prefixWord ++ tailWord_897768) baseStart_897768 baseEnd_897768 := by
    simpa [prefixWord, tailWord_897768, baseEnd_897768] using wordTrace_append hprefix tailTrace_897768
  have hstable : (prefixWord ++ tailWord_897768).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897768).length < 2 ^ (prefixWord ++ tailWord_897768).sum := by decide
  have hdescent : baseEnd_897768 < baseStart_897768 := by decide
  rcases family_descends (prefixWord ++ tailWord_897768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897774 : List Nat := [4, 1, 2, 1, 1, 5, 2, 2, 2]
def baseStart_897774 : Nat := 118140960795 + 897774 * 2 ^ 59
def prefixEnd_897774 : Nat := 4983230072969 + 3 ^ 40 * 897774 * 2
def baseEnd_897774 : Nat := 409768516541933945596639

theorem tailTrace_897774 : CollatzResearch.WordTrace tailWord_897774 prefixEnd_897774 409768516541933945596639 := by
  unfold tailWord_897774
  simp only [CollatzResearch.WordTrace]
  refine ⟨4093063481190700054659547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21829671899683733624850917 4093063481190700054659547)
  ·
    refine ⟨6139595221786050081989321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4093063481190700054659547 6139595221786050081989321)
    ·
      refine ⟨4604696416339537561491991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6139595221786050081989321 4604696416339537561491991)
      ·
        refine ⟨6907044624509306342237987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4604696416339537561491991 6907044624509306342237987)
        ·
          refine ⟨10360566936763959513356981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6907044624509306342237987 10360566936763959513356981)
          ·
            refine ⟨971303150321621204377217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10360566936763959513356981 971303150321621204377217)
            ·
              refine ⟨728477362741215903282913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 971303150321621204377217 728477362741215903282913)
              ·
                refine ⟨546358022055911927462185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 728477362741215903282913 546358022055911927462185)
                ·
                  refine ⟨409768516541933945596639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 546358022055911927462185 409768516541933945596639)
                  ·
                    rfl

theorem cell20_897774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 2, 2, 2].length) (baseStart_897774 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_897774 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_897774 prefixEnd_897774 := by exact prefixLift 897774
  have htrace : WordTrace (prefixWord ++ tailWord_897774) baseStart_897774 baseEnd_897774 := by
    simpa [prefixWord, tailWord_897774, baseEnd_897774] using wordTrace_append hprefix tailTrace_897774
  have hstable : (prefixWord ++ tailWord_897774).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897774).length < 2 ^ (prefixWord ++ tailWord_897774).sum := by decide
  have hdescent : baseEnd_897774 < baseStart_897774 := by decide
  rcases family_descends (prefixWord ++ tailWord_897774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897799 : List Nat := [1, 1, 4, 4, 1, 1, 1, 1, 6]
def baseStart_897799 : Nat := 118140960795 + 897799 * 2 ^ 59
def prefixEnd_897799 : Nat := 4983230072969 + 3 ^ 40 * 897799 * 2
def baseEnd_897799 : Nat := 409779927223144969763203

theorem tailTrace_897799 : CollatzResearch.WordTrace tailWord_897799 prefixEnd_897799 409779927223144969763203 := by
  unfold tailWord_897799
  simp only [CollatzResearch.WordTrace]
  refine ⟨32745419674435029706936451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21830279782956686471290967 32745419674435029706936451)
  ·
    refine ⟨49118129511652544560404677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32745419674435029706936451 49118129511652544560404677)
    ·
      refine ⟨9209649283434852105075877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49118129511652544560404677 9209649283434852105075877)
      ·
        refine ⟨1726809240644034769701727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9209649283434852105075877 1726809240644034769701727)
        ·
          refine ⟨2590213860966052154552591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1726809240644034769701727 2590213860966052154552591)
          ·
            refine ⟨3885320791449078231828887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2590213860966052154552591 3885320791449078231828887)
            ·
              refine ⟨5827981187173617347743331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3885320791449078231828887 5827981187173617347743331)
              ·
                refine ⟨8741971780760426021614997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5827981187173617347743331 8741971780760426021614997)
                ·
                  refine ⟨409779927223144969763203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8741971780760426021614997 409779927223144969763203)
                  ·
                    rfl

theorem cell20_897799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 6].length) (baseStart_897799 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_897799 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_897799 prefixEnd_897799 := by exact prefixLift 897799
  have htrace : WordTrace (prefixWord ++ tailWord_897799) baseStart_897799 baseEnd_897799 := by
    simpa [prefixWord, tailWord_897799, baseEnd_897799] using wordTrace_append hprefix tailTrace_897799
  have hstable : (prefixWord ++ tailWord_897799).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897799).length < 2 ^ (prefixWord ++ tailWord_897799).sum := by decide
  have hdescent : baseEnd_897799 < baseStart_897799 := by decide
  rcases family_descends (prefixWord ++ tailWord_897799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897813 : List Nat := [1, 3, 2, 1, 2, 2, 2, 2, 5]
def baseStart_897813 : Nat := 118140960795 + 897813 * 2 ^ 59
def prefixEnd_897813 : Nat := 4983230072969 + 3 ^ 40 * 897813 * 2
def baseEnd_897813 : Nat := 409786317204623143296479

theorem tailTrace_897813 : CollatzResearch.WordTrace tailWord_897813 prefixEnd_897813 409786317204623143296479 := by
  unfold tailWord_897813
  simp only [CollatzResearch.WordTrace]
  refine ⟨32745930296384310097946093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21830620197589540065297395 32745930296384310097946093)
  ·
    refine ⟨12279723861144116286729785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32745930296384310097946093 12279723861144116286729785)
    ·
      refine ⟨9209792895858087215047339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12279723861144116286729785 9209792895858087215047339)
      ·
        refine ⟨13814689343787130822571009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9209792895858087215047339 13814689343787130822571009)
        ·
          refine ⟨10361017007840348116928257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13814689343787130822571009 10361017007840348116928257)
          ·
            refine ⟨7770762755880261087696193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10361017007840348116928257 7770762755880261087696193)
            ·
              refine ⟨5828072066910195815772145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7770762755880261087696193 5828072066910195815772145)
              ·
                refine ⟨4371054050182646861829109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5828072066910195815772145 4371054050182646861829109)
                ·
                  refine ⟨409786317204623143296479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4371054050182646861829109 409786317204623143296479)
                  ·
                    rfl

theorem cell20_897813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 2, 5].length) (baseStart_897813 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_897813 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_897813 prefixEnd_897813 := by exact prefixLift 897813
  have htrace : WordTrace (prefixWord ++ tailWord_897813) baseStart_897813 baseEnd_897813 := by
    simpa [prefixWord, tailWord_897813, baseEnd_897813] using wordTrace_append hprefix tailTrace_897813
  have hstable : (prefixWord ++ tailWord_897813).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897813).length < 2 ^ (prefixWord ++ tailWord_897813).sum := by decide
  have hdescent : baseEnd_897813 < baseStart_897813 := by decide
  rcases family_descends (prefixWord ++ tailWord_897813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897857 : List Nat := [1, 2, 5, 3, 1, 2, 2, 4]
def baseStart_897857 : Nat := 118140960795 + 897857 * 2 ^ 59
def prefixEnd_897857 : Nat := 4983230072969 + 3 ^ 40 * 897857 * 2
def baseEnd_897857 : Nat := 136602133334518181943211

theorem tailTrace_897857 : CollatzResearch.WordTrace tailWord_897857 prefixEnd_897857 136602133334518181943211 := by
  unfold tailWord_897857
  simp only [CollatzResearch.WordTrace]
  refine ⟨32747535108224905612547825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21831690072149937075031883 32747535108224905612547825)
  ·
    refine ⟨24560651331168679209410869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32747535108224905612547825 24560651331168679209410869)
    ·
      refine ⟨2302561062297063675882269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24560651331168679209410869 2302561062297063675882269)
      ·
        refine ⟨863460398361398878455851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2302561062297063675882269 863460398361398878455851)
        ·
          refine ⟨1295190597542098317683777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 863460398361398878455851 1295190597542098317683777)
          ·
            refine ⟨971392948156573738262833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1295190597542098317683777 971392948156573738262833)
            ·
              refine ⟨728544711117430303697125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 971392948156573738262833 728544711117430303697125)
              ·
                refine ⟨136602133334518181943211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 728544711117430303697125 136602133334518181943211)
                ·
                  rfl

theorem cell20_897857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 2, 4].length) (baseStart_897857 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_897857 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_897857 prefixEnd_897857 := by exact prefixLift 897857
  have htrace : WordTrace (prefixWord ++ tailWord_897857) baseStart_897857 baseEnd_897857 := by
    simpa [prefixWord, tailWord_897857, baseEnd_897857] using wordTrace_append hprefix tailTrace_897857
  have hstable : (prefixWord ++ tailWord_897857).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897857).length < 2 ^ (prefixWord ++ tailWord_897857).sum := by decide
  have hdescent : baseEnd_897857 < baseStart_897857 := by decide
  rcases family_descends (prefixWord ++ tailWord_897857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897882 : List Nat := [3, 1, 1, 2, 1, 6, 6]
def baseStart_897882 : Nat := 118140960795 + 897882 * 2 ^ 59
def prefixEnd_897882 : Nat := 4983230072969 + 3 ^ 40 * 897882 * 2
def baseEnd_897882 : Nat := 45535312298307285555133

theorem tailTrace_897882 : CollatzResearch.WordTrace tailWord_897882 prefixEnd_897882 45535312298307285555133 := by
  unfold tailWord_897882
  simp only [CollatzResearch.WordTrace]
  refine ⟨8187111733283583720551975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21832297955422889921471933 8187111733283583720551975)
  ·
    refine ⟨12280667599925375580827963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8187111733283583720551975 12280667599925375580827963)
    ·
      refine ⟨18421001399888063371241945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12280667599925375580827963 18421001399888063371241945)
      ·
        refine ⟨13815751049916047528431459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18421001399888063371241945 13815751049916047528431459)
        ·
          refine ⟨20723626574874071292647189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13815751049916047528431459 20723626574874071292647189)
          ·
            refine ⟨971419995697222091842837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 20723626574874071292647189 971419995697222091842837)
            ·
              refine ⟨45535312298307285555133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 971419995697222091842837 45535312298307285555133)
              ·
                rfl

theorem cell20_897882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 6].length) (baseStart_897882 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_897882 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_897882 prefixEnd_897882 := by exact prefixLift 897882
  have htrace : WordTrace (prefixWord ++ tailWord_897882) baseStart_897882 baseEnd_897882 := by
    simpa [prefixWord, tailWord_897882, baseEnd_897882] using wordTrace_append hprefix tailTrace_897882
  have hstable : (prefixWord ++ tailWord_897882).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897882).length < 2 ^ (prefixWord ++ tailWord_897882).sum := by decide
  have hdescent : baseEnd_897882 < baseStart_897882 := by decide
  rcases family_descends (prefixWord ++ tailWord_897882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897892 : List Nat := [2, 3, 1, 1, 4, 3, 1, 1, 4]
def baseStart_897892 : Nat := 118140960795 + 897892 * 2 ^ 59
def prefixEnd_897892 : Nat := 4983230072969 + 3 ^ 40 * 897892 * 2
def baseEnd_897892 : Nat := 409822374957249979662823

theorem tailTrace_897892 : CollatzResearch.WordTrace tailWord_897892 prefixEnd_897892 409822374957249979662823 := by
  unfold tailWord_897892
  simp only [CollatzResearch.WordTrace]
  refine ⟨16374405831549053295035965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21832541108732071060047953 16374405831549053295035965)
  ·
    refine ⟨6140402186830894985638487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16374405831549053295035965 6140402186830894985638487)
    ·
      refine ⟨9210603280246342478457731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6140402186830894985638487 9210603280246342478457731)
      ·
        refine ⟨13815904920369513717686597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9210603280246342478457731 13815904920369513717686597)
        ·
          refine ⟨2590482172569283822066237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13815904920369513717686597 2590482172569283822066237)
          ·
            refine ⟨971430814713481433274839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2590482172569283822066237 971430814713481433274839)
            ·
              refine ⟨1457146222070222149912259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 971430814713481433274839 1457146222070222149912259)
              ·
                refine ⟨2185719333105333224868389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1457146222070222149912259 2185719333105333224868389)
                ·
                  refine ⟨409822374957249979662823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2185719333105333224868389 409822374957249979662823)
                  ·
                    rfl

theorem cell20_897892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 1, 4].length) (baseStart_897892 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_897892 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_897892 prefixEnd_897892 := by exact prefixLift 897892
  have htrace : WordTrace (prefixWord ++ tailWord_897892) baseStart_897892 baseEnd_897892 := by
    simpa [prefixWord, tailWord_897892, baseEnd_897892] using wordTrace_append hprefix tailTrace_897892
  have hstable : (prefixWord ++ tailWord_897892).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897892).length < 2 ^ (prefixWord ++ tailWord_897892).sum := by decide
  have hdescent : baseEnd_897892 < baseStart_897892 := by decide
  rcases family_descends (prefixWord ++ tailWord_897892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897941 : List Nat := [1, 3, 2, 1, 1, 12]
def baseStart_897941 : Nat := 118140960795 + 897941 * 2 ^ 59
def prefixEnd_897941 : Nat := 4983230072969 + 3 ^ 40 * 897941 * 2
def baseEnd_897941 : Nat := 15179434810830503223307

theorem tailTrace_897941 : CollatzResearch.WordTrace tailWord_897941 prefixEnd_897941 15179434810830503223307 := by
  unfold tailWord_897941
  simp only [CollatzResearch.WordTrace]
  refine ⟨32750598839920587958605677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21833732559947058639070451 32750598839920587958605677)
  ·
    refine ⟨12281474564970220484477129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32750598839920587958605677 12281474564970220484477129)
    ·
      refine ⟨9211105923727665363357847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12281474564970220484477129 9211105923727665363357847)
      ·
        refine ⟨13816658885591498045036771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9211105923727665363357847 13816658885591498045036771)
        ·
          refine ⟨20724988328387247067555157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13816658885591498045036771 20724988328387247067555157)
          ·
            refine ⟨15179434810830503223307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 20724988328387247067555157 15179434810830503223307)
            ·
              rfl

theorem cell20_897941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 12].length) (baseStart_897941 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_897941 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_897941 prefixEnd_897941 := by exact prefixLift 897941
  have htrace : WordTrace (prefixWord ++ tailWord_897941) baseStart_897941 baseEnd_897941 := by
    simpa [prefixWord, tailWord_897941, baseEnd_897941] using wordTrace_append hprefix tailTrace_897941
  have hstable : (prefixWord ++ tailWord_897941).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897941).length < 2 ^ (prefixWord ++ tailWord_897941).sum := by decide
  have hdescent : baseEnd_897941 < baseStart_897941 := by decide
  rcases family_descends (prefixWord ++ tailWord_897941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898006 : List Nat := [5, 2, 1, 1, 2, 1, 1, 3, 4]
def baseStart_898006 : Nat := 118140960795 + 898006 * 2 ^ 59
def prefixEnd_898006 : Nat := 4983230072969 + 3 ^ 40 * 898006 * 2
def baseEnd_898006 : Nat := 409874407663572249862357

theorem tailTrace_898006 : CollatzResearch.WordTrace tailWord_898006 prefixEnd_898006 409874407663572249862357 := by
  unfold tailWord_898006
  simp only [CollatzResearch.WordTrace]
  refine ⟨2047060599042819003732617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21835313056456736039814581 2047060599042819003732617)
  ·
    refine ⟨1535295449282114252799463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2047060599042819003732617 1535295449282114252799463)
    ·
      refine ⟨2302943173923171379199195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1535295449282114252799463 2302943173923171379199195)
      ·
        refine ⟨3454414760884757068798793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2302943173923171379199195 3454414760884757068798793)
        ·
          refine ⟨2590811070663567801599095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3454414760884757068798793 2590811070663567801599095)
          ·
            refine ⟨3886216605995351702398643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2590811070663567801599095 3886216605995351702398643)
            ·
              refine ⟨5829324908993027553597965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3886216605995351702398643 5829324908993027553597965)
              ·
                refine ⟨2185996840872385332599237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5829324908993027553597965 2185996840872385332599237)
                ·
                  refine ⟨409874407663572249862357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2185996840872385332599237 409874407663572249862357)
                  ·
                    rfl

theorem cell20_898006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_898006 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_898006 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_898006 prefixEnd_898006 := by exact prefixLift 898006
  have htrace : WordTrace (prefixWord ++ tailWord_898006) baseStart_898006 baseEnd_898006 := by
    simpa [prefixWord, tailWord_898006, baseEnd_898006] using wordTrace_append hprefix tailTrace_898006
  have hstable : (prefixWord ++ tailWord_898006).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898006).length < 2 ^ (prefixWord ++ tailWord_898006).sum := by decide
  have hdescent : baseEnd_898006 < baseStart_898006 := by decide
  rcases family_descends (prefixWord ++ tailWord_898006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898017 : List Nat := [1, 2, 3, 1, 2, 1, 1, 9]
def baseStart_898017 : Nat := 118140960795 + 898017 * 2 ^ 59
def prefixEnd_898017 : Nat := 4983230072969 + 3 ^ 40 * 898017 * 2
def baseEnd_898017 : Nat := 136626476121101700165215

theorem tailTrace_898017 : CollatzResearch.WordTrace tailWord_898017 prefixEnd_898017 136626476121101700165215 := by
  unfold tailWord_898017
  simp only [CollatzResearch.WordTrace]
  refine ⟨32753370787645252938372305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21835580525096835292248203 32753370787645252938372305)
  ·
    refine ⟨24565028090733939703779229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32753370787645252938372305 24565028090733939703779229)
    ·
      refine ⟨9211885534025227388917211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24565028090733939703779229 9211885534025227388917211)
      ·
        refine ⟨13817828301037841083375817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9211885534025227388917211 13817828301037841083375817)
        ·
          refine ⟨10363371225778380812531863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13817828301037841083375817 10363371225778380812531863)
          ·
            refine ⟨15545056838667571218797795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10363371225778380812531863 15545056838667571218797795)
            ·
              refine ⟨23317585258001356828196693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15545056838667571218797795 23317585258001356828196693)
              ·
                refine ⟨136626476121101700165215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23317585258001356828196693 136626476121101700165215)
                ·
                  rfl

theorem cell20_898017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 9].length) (baseStart_898017 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_898017 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_898017 prefixEnd_898017 := by exact prefixLift 898017
  have htrace : WordTrace (prefixWord ++ tailWord_898017) baseStart_898017 baseEnd_898017 := by
    simpa [prefixWord, tailWord_898017, baseEnd_898017] using wordTrace_append hprefix tailTrace_898017
  have hstable : (prefixWord ++ tailWord_898017).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898017).length < 2 ^ (prefixWord ++ tailWord_898017).sum := by decide
  have hdescent : baseEnd_898017 < baseStart_898017 := by decide
  rcases family_descends (prefixWord ++ tailWord_898017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898030 : List Nat := [4, 1, 2, 1, 4, 2, 2, 4]
def baseStart_898030 : Nat := 118140960795 + 898030 * 2 ^ 59
def prefixEnd_898030 : Nat := 4983230072969 + 3 ^ 40 * 898030 * 2
def baseEnd_898030 : Nat := 136628453972511611020753

theorem tailTrace_898030 : CollatzResearch.WordTrace tailWord_898030 prefixEnd_898030 136628453972511611020753 := by
  unfold tailWord_898030
  simp only [CollatzResearch.WordTrace]
  refine ⟨4094230617074769519824443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21835896624398770772397029 4094230617074769519824443)
  ·
    refine ⟨6141345925612154279736665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4094230617074769519824443 6141345925612154279736665)
    ·
      refine ⟨4606009444209115709802499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6141345925612154279736665 4606009444209115709802499)
      ·
        refine ⟨6909014166313673564703749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4606009444209115709802499 6909014166313673564703749)
        ·
          refine ⟨1295440156183813793381953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6909014166313673564703749 1295440156183813793381953)
          ·
            refine ⟨971580117137860345036465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1295440156183813793381953 971580117137860345036465)
            ·
              refine ⟨728685087853395258777349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 971580117137860345036465 728685087853395258777349)
              ·
                refine ⟨136628453972511611020753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 728685087853395258777349 136628453972511611020753)
                ·
                  rfl

theorem cell20_898030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 2, 4].length) (baseStart_898030 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_898030 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_898030 prefixEnd_898030 := by exact prefixLift 898030
  have htrace : WordTrace (prefixWord ++ tailWord_898030) baseStart_898030 baseEnd_898030 := by
    simpa [prefixWord, tailWord_898030, baseEnd_898030] using wordTrace_append hprefix tailTrace_898030
  have hstable : (prefixWord ++ tailWord_898030).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898030).length < 2 ^ (prefixWord ++ tailWord_898030).sum := by decide
  have hdescent : baseEnd_898030 < baseStart_898030 := by decide
  rcases family_descends (prefixWord ++ tailWord_898030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898044 : List Nat := [2, 2, 2, 1, 2, 3, 3, 3, 2]
def baseStart_898044 : Nat := 118140960795 + 898044 * 2 ^ 59
def prefixEnd_898044 : Nat := 4983230072969 + 3 ^ 40 * 898044 * 2
def baseEnd_898044 : Nat := 409891751899013006595535

theorem tailTrace_898044 : CollatzResearch.WordTrace tailWord_898044 prefixEnd_898044 409891751899013006595535 := by
  unfold tailWord_898044
  simp only [CollatzResearch.WordTrace]
  refine ⟨16377177779273718274802593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21836237039031624366403457 16377177779273718274802593)
  ·
    refine ⟨12282883334455288706101945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16377177779273718274802593 12282883334455288706101945)
    ·
      refine ⟨9212162500841466529576459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12282883334455288706101945 9212162500841466529576459)
      ·
        refine ⟨13818243751262199794364689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9212162500841466529576459 13818243751262199794364689)
        ·
          refine ⟨10363682813446649845773517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13818243751262199794364689 10363682813446649845773517)
          ·
            refine ⟨3886381055042493692165069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10363682813446649845773517 3886381055042493692165069)
            ·
              refine ⟨1457392895640935134561901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3886381055042493692165069 1457392895640935134561901)
              ·
                refine ⟨546522335865350675460713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1457392895640935134561901 546522335865350675460713)
                ·
                  refine ⟨409891751899013006595535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 546522335865350675460713 409891751899013006595535)
                  ·
                    rfl

theorem cell20_898044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 3, 2].length) (baseStart_898044 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_898044 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_898044 prefixEnd_898044 := by exact prefixLift 898044
  have htrace : WordTrace (prefixWord ++ tailWord_898044) baseStart_898044 baseEnd_898044 := by
    simpa [prefixWord, tailWord_898044, baseEnd_898044] using wordTrace_append hprefix tailTrace_898044
  have hstable : (prefixWord ++ tailWord_898044).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898044).length < 2 ^ (prefixWord ++ tailWord_898044).sum := by decide
  have hdescent : baseEnd_898044 < baseStart_898044 := by decide
  rcases family_descends (prefixWord ++ tailWord_898044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898065 : List Nat := [1, 2, 2, 1, 1, 2, 1, 8, 2]
def baseStart_898065 : Nat := 118140960795 + 898065 * 2 ^ 59
def prefixEnd_898065 : Nat := 4983230072969 + 3 ^ 40 * 898065 * 2
def baseEnd_898065 : Nat := 409901336871230266895449

theorem tailTrace_898065 : CollatzResearch.WordTrace tailWord_898065 prefixEnd_898065 409901336871230266895449 := by
  unfold tailWord_898065
  simp only [CollatzResearch.WordTrace]
  refine ⟨32755121491471357136119649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21836747660980904757413099 32755121491471357136119649)
  ·
    refine ⟨24566341118603517852089737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32755121491471357136119649 24566341118603517852089737)
    ·
      refine ⟨18424755838952638389067303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24566341118603517852089737 18424755838952638389067303)
      ·
        refine ⟨27637133758428957583600955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18424755838952638389067303 27637133758428957583600955)
        ·
          refine ⟨41455700637643436375401433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27637133758428957583600955 41455700637643436375401433)
          ·
            refine ⟨31091775478232577281551075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41455700637643436375401433 31091775478232577281551075)
            ·
              refine ⟨46637663217348865922326613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31091775478232577281551075 46637663217348865922326613)
              ·
                refine ⟨546535115828307022527265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 46637663217348865922326613 546535115828307022527265)
                ·
                  refine ⟨409901336871230266895449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 546535115828307022527265 409901336871230266895449)
                  ·
                    rfl

theorem cell20_898065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 8, 2].length) (baseStart_898065 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_898065 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_898065 prefixEnd_898065 := by exact prefixLift 898065
  have htrace : WordTrace (prefixWord ++ tailWord_898065) baseStart_898065 baseEnd_898065 := by
    simpa [prefixWord, tailWord_898065, baseEnd_898065] using wordTrace_append hprefix tailTrace_898065
  have hstable : (prefixWord ++ tailWord_898065).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898065).length < 2 ^ (prefixWord ++ tailWord_898065).sum := by decide
  have hdescent : baseEnd_898065 < baseStart_898065 := by decide
  rcases family_descends (prefixWord ++ tailWord_898065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898072 : List Nat := [2, 1, 2, 3, 2, 3, 2, 5]
def baseStart_898072 : Nat := 118140960795 + 898072 * 2 ^ 59
def prefixEnd_898072 : Nat := 4983230072969 + 3 ^ 40 * 898072 * 2
def baseEnd_898072 : Nat := 136634843953989784554029

theorem tailTrace_898072 : CollatzResearch.WordTrace tailWord_898072 prefixEnd_898072 136634843953989784554029 := by
  unfold tailWord_898072
  simp only [CollatzResearch.WordTrace]
  refine ⟨16377688401222998665812235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21836917868297331554416313 16377688401222998665812235)
  ·
    refine ⟨24566532601834497998718353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16377688401222998665812235 24566532601834497998718353)
    ·
      refine ⟨18424899451375873499038765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24566532601834497998718353 18424899451375873499038765)
      ·
        refine ⟨6909337294265952562139537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18424899451375873499038765 6909337294265952562139537)
        ·
          refine ⟨5182002970699464421604653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6909337294265952562139537 5182002970699464421604653)
          ·
            refine ⟨1943251114012299158101745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5182002970699464421604653 1943251114012299158101745)
            ·
              refine ⟨1457438335509224368576309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1943251114012299158101745 1457438335509224368576309)
              ·
                refine ⟨136634843953989784554029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1457438335509224368576309 136634843953989784554029)
                ·
                  rfl

theorem cell20_898072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 5].length) (baseStart_898072 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_898072 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_898072 prefixEnd_898072 := by exact prefixLift 898072
  have htrace : WordTrace (prefixWord ++ tailWord_898072) baseStart_898072 baseEnd_898072 := by
    simpa [prefixWord, tailWord_898072, baseEnd_898072] using wordTrace_append hprefix tailTrace_898072
  have hstable : (prefixWord ++ tailWord_898072).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898072).length < 2 ^ (prefixWord ++ tailWord_898072).sum := by decide
  have hdescent : baseEnd_898072 < baseStart_898072 := by decide
  rcases family_descends (prefixWord ++ tailWord_898072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898103 : List Nat := [1, 1, 3, 1, 2, 2, 1, 7, 2]
def baseStart_898103 : Nat := 118140960795 + 898103 * 2 ^ 59
def prefixEnd_898103 : Nat := 4983230072969 + 3 ^ 40 * 898103 * 2
def baseEnd_898103 : Nat := 409918681106671023628627

theorem tailTrace_898103 : CollatzResearch.WordTrace tailWord_898103 prefixEnd_898103 409918681106671023628627 := by
  unfold tailWord_898103
  simp only [CollatzResearch.WordTrace]
  refine ⟨32756507465333689626002963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21837671643555793084001975 32756507465333689626002963)
  ·
    refine ⟨49134761198000534439004445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32756507465333689626002963 49134761198000534439004445)
    ·
      refine ⟨18425535449250200414626667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49134761198000534439004445 18425535449250200414626667)
      ·
        refine ⟨27638303173875300621940001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18425535449250200414626667 27638303173875300621940001)
        ·
          refine ⟨20728727380406475466455001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27638303173875300621940001 20728727380406475466455001)
          ·
            refine ⟨15546545535304856599841251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20728727380406475466455001 15546545535304856599841251)
            ·
              refine ⟨23319818302957284899761877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15546545535304856599841251 23319818302957284899761877)
              ·
                refine ⟨546558241475561364838169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 23319818302957284899761877 546558241475561364838169)
                ·
                  refine ⟨409918681106671023628627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 546558241475561364838169 409918681106671023628627)
                  ·
                    rfl

theorem cell20_898103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 7, 2].length) (baseStart_898103 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_898103 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_898103 prefixEnd_898103 := by exact prefixLift 898103
  have htrace : WordTrace (prefixWord ++ tailWord_898103) baseStart_898103 baseEnd_898103 := by
    simpa [prefixWord, tailWord_898103, baseEnd_898103] using wordTrace_append hprefix tailTrace_898103
  have hstable : (prefixWord ++ tailWord_898103).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898103).length < 2 ^ (prefixWord ++ tailWord_898103).sum := by decide
  have hdescent : baseEnd_898103 < baseStart_898103 := by decide
  rcases family_descends (prefixWord ++ tailWord_898103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898110 : List Nat := [4, 2, 1, 3, 1, 9]
def baseStart_898110 : Nat := 118140960795 + 898110 * 2 ^ 59
def prefixEnd_898110 : Nat := 4983230072969 + 3 ^ 40 * 898110 * 2
def baseEnd_898110 : Nat := 15182291707311485570195

theorem tailTrace_898110 : CollatzResearch.WordTrace tailWord_898110 prefixEnd_898110 15182291707311485570195 := by
  unfold tailWord_898110
  simp only [CollatzResearch.WordTrace]
  refine ⟨4094595347038541227688473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21837841850872219881005189 4094595347038541227688473)
  ·
    refine ⟨3070946510278905920766355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4094595347038541227688473 3070946510278905920766355)
    ·
      refine ⟨4606419765418358881149533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3070946510278905920766355 4606419765418358881149533)
      ·
        refine ⟨1727407412031884580431075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4606419765418358881149533 1727407412031884580431075)
        ·
          refine ⟨2591111118047826870646613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1727407412031884580431075 2591111118047826870646613)
          ·
            refine ⟨15182291707311485570195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2591111118047826870646613 15182291707311485570195)
            ·
              rfl

theorem cell20_898110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 9].length) (baseStart_898110 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_898110 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_898110 prefixEnd_898110 := by exact prefixLift 898110
  have htrace : WordTrace (prefixWord ++ tailWord_898110) baseStart_898110 baseEnd_898110 := by
    simpa [prefixWord, tailWord_898110, baseEnd_898110] using wordTrace_append hprefix tailTrace_898110
  have hstable : (prefixWord ++ tailWord_898110).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898110).length < 2 ^ (prefixWord ++ tailWord_898110).sum := by decide
  have hdescent : baseEnd_898110 < baseStart_898110 := by decide
  rcases family_descends (prefixWord ++ tailWord_898110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898113 : List Nat := [1, 2, 5, 1, 3, 1, 2, 2, 3]
def baseStart_898113 : Nat := 118140960795 + 898113 * 2 ^ 59
def prefixEnd_898113 : Nat := 4983230072969 + 3 ^ 40 * 898113 * 2
def baseEnd_898113 : Nat := 409923245379155433295253

theorem tailTrace_898113 : CollatzResearch.WordTrace tailWord_898113 prefixEnd_898113 409923245379155433295253 := by
  unfold tailWord_898113
  simp only [CollatzResearch.WordTrace]
  refine ⟨32756872195297461333866993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21837914796864974222577995 32756872195297461333866993)
  ·
    refine ⟨24567654146473096000400245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32756872195297461333866993 24567654146473096000400245)
    ·
      refine ⟨2303217576231852750037523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24567654146473096000400245 2303217576231852750037523)
      ·
        refine ⟨3454826364347779125056285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2303217576231852750037523 3454826364347779125056285)
        ·
          refine ⟨1295559886630417171896107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3454826364347779125056285 1295559886630417171896107)
          ·
            refine ⟨1943339829945625757844161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1295559886630417171896107 1943339829945625757844161)
            ·
              refine ⟨1457504872459219318383121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1943339829945625757844161 1457504872459219318383121)
              ·
                refine ⟨1093128654344414488787341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1457504872459219318383121 1093128654344414488787341)
                ·
                  refine ⟨409923245379155433295253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1093128654344414488787341 409923245379155433295253)
                  ·
                    rfl

theorem cell20_898113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 2, 3].length) (baseStart_898113 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_898113 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_898113 prefixEnd_898113 := by exact prefixLift 898113
  have htrace : WordTrace (prefixWord ++ tailWord_898113) baseStart_898113 baseEnd_898113 := by
    simpa [prefixWord, tailWord_898113, baseEnd_898113] using wordTrace_append hprefix tailTrace_898113
  have hstable : (prefixWord ++ tailWord_898113).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898113).length < 2 ^ (prefixWord ++ tailWord_898113).sum := by decide
  have hdescent : baseEnd_898113 < baseStart_898113 := by decide
  rcases family_descends (prefixWord ++ tailWord_898113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898117 : List Nat := [1, 3, 1, 1, 1, 3, 3, 4, 3]
def baseStart_898117 : Nat := 118140960795 + 898117 * 2 ^ 59
def prefixEnd_898117 : Nat := 4983230072969 + 3 ^ 40 * 898117 * 2
def baseEnd_898117 : Nat := 409925071088149197161903

theorem tailTrace_898117 : CollatzResearch.WordTrace tailWord_898117 prefixEnd_898117 409925071088149197161903 := by
  unfold tailWord_898117
  simp only [CollatzResearch.WordTrace]
  refine ⟨32757018087282970017012605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21838012058188646678008403 32757018087282970017012605)
  ·
    refine ⟨12283881782731113756379727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32757018087282970017012605 12283881782731113756379727)
    ·
      refine ⟨18425822674096670634569591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12283881782731113756379727 18425822674096670634569591)
      ·
        refine ⟨27638734011145005951854387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18425822674096670634569591 27638734011145005951854387)
        ·
          refine ⟨41458101016717508927781581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27638734011145005951854387 41458101016717508927781581)
          ·
            refine ⟨15546787881269065847918093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41458101016717508927781581 15546787881269065847918093)
            ·
              refine ⟨5830045455475899692969285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15546787881269065847918093 5830045455475899692969285)
              ·
                refine ⟨1093133522901731192431741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5830045455475899692969285 1093133522901731192431741)
                ·
                  refine ⟨409925071088149197161903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1093133522901731192431741 409925071088149197161903)
                  ·
                    rfl

theorem cell20_898117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 4, 3].length) (baseStart_898117 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_898117 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_898117 prefixEnd_898117 := by exact prefixLift 898117
  have htrace : WordTrace (prefixWord ++ tailWord_898117) baseStart_898117 baseEnd_898117 := by
    simpa [prefixWord, tailWord_898117, baseEnd_898117] using wordTrace_append hprefix tailTrace_898117
  have hstable : (prefixWord ++ tailWord_898117).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898117).length < 2 ^ (prefixWord ++ tailWord_898117).sum := by decide
  have hdescent : baseEnd_898117 < baseStart_898117 := by decide
  rcases family_descends (prefixWord ++ tailWord_898117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898124 : List Nat := [2, 2, 1, 3, 1, 1, 1, 5, 4]
def baseStart_898124 : Nat := 118140960795 + 898124 * 2 ^ 59
def prefixEnd_898124 : Nat := 4983230072969 + 3 ^ 40 * 898124 * 2
def baseEnd_898124 : Nat := 409928266078888283928541

theorem tailTrace_898124 : CollatzResearch.WordTrace tailWord_898124 prefixEnd_898124 409928266078888283928541 := by
  unfold tailWord_898124
  simp only [CollatzResearch.WordTrace]
  refine ⟨16378636699128805106258713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21838182265505073475011617 16378636699128805106258713)
  ·
    refine ⟨12283977524346603829694035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16378636699128805106258713 12283977524346603829694035)
    ·
      refine ⟨18425966286519905744541053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12283977524346603829694035 18425966286519905744541053)
      ·
        refine ⟨6909737357444964654202895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18425966286519905744541053 6909737357444964654202895)
        ·
          refine ⟨10364606036167446981304343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6909737357444964654202895 10364606036167446981304343)
          ·
            refine ⟨15546909054251170471956515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10364606036167446981304343 15546909054251170471956515)
            ·
              refine ⟨23320363581376755707934773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15546909054251170471956515 23320363581376755707934773)
              ·
                refine ⟨2186284085754070847618885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23320363581376755707934773 2186284085754070847618885)
                ·
                  refine ⟨409928266078888283928541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2186284085754070847618885 409928266078888283928541)
                  ·
                    rfl

theorem cell20_898124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 5, 4].length) (baseStart_898124 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_898124 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_898124 prefixEnd_898124 := by exact prefixLift 898124
  have htrace : WordTrace (prefixWord ++ tailWord_898124) baseStart_898124 baseEnd_898124 := by
    simpa [prefixWord, tailWord_898124, baseEnd_898124] using wordTrace_append hprefix tailTrace_898124
  have hstable : (prefixWord ++ tailWord_898124).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898124).length < 2 ^ (prefixWord ++ tailWord_898124).sum := by decide
  have hdescent : baseEnd_898124 < baseStart_898124 := by decide
  rcases family_descends (prefixWord ++ tailWord_898124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898158 : List Nat := [4, 1, 2, 2, 1, 2, 1, 5, 2]
def baseStart_898158 : Nat := 118140960795 + 898158 * 2 ^ 59
def prefixEnd_898158 : Nat := 4983230072969 + 3 ^ 40 * 898158 * 2
def baseEnd_898158 : Nat := 409943784605335276795069

theorem tailTrace_898158 : CollatzResearch.WordTrace tailWord_898158 prefixEnd_898158 409943784605335276795069 := by
  unfold tailWord_898158
  simp only [CollatzResearch.WordTrace]
  refine ⟨4094814185016804252406891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21839008986756289346170085 4094814185016804252406891)
  ·
    refine ⟨6142221277525206378610337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4094814185016804252406891 6142221277525206378610337)
    ·
      refine ⟨4606665958143904783957753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6142221277525206378610337 4606665958143904783957753)
      ·
        refine ⟨3454999468607928587968315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4606665958143904783957753 3454999468607928587968315)
        ·
          refine ⟨5182499202911892881952473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3454999468607928587968315 5182499202911892881952473)
          ·
            refine ⟨3886874402183919661464355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5182499202911892881952473 3886874402183919661464355)
            ·
              refine ⟨5830311603275879492196533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3886874402183919661464355 5830311603275879492196533)
              ·
                refine ⟨546591712807113702393425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5830311603275879492196533 546591712807113702393425)
                ·
                  refine ⟨409943784605335276795069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 546591712807113702393425 409943784605335276795069)
                  ·
                    rfl

theorem cell20_898158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 5, 2].length) (baseStart_898158 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_898158 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_898158 prefixEnd_898158 := by exact prefixLift 898158
  have htrace : WordTrace (prefixWord ++ tailWord_898158) baseStart_898158 baseEnd_898158 := by
    simpa [prefixWord, tailWord_898158, baseEnd_898158] using wordTrace_append hprefix tailTrace_898158
  have hstable : (prefixWord ++ tailWord_898158).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898158).length < 2 ^ (prefixWord ++ tailWord_898158).sum := by decide
  have hdescent : baseEnd_898158 < baseStart_898158 := by decide
  rcases family_descends (prefixWord ++ tailWord_898158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898162 : List Nat := [3, 2, 1, 2, 2, 1, 1, 2, 6]
def baseStart_898162 : Nat := 118140960795 + 898162 * 2 ^ 59
def prefixEnd_898162 : Nat := 4983230072969 + 3 ^ 40 * 898162 * 2
def baseEnd_898162 : Nat := 409945610314329040661719

theorem tailTrace_898162 : CollatzResearch.WordTrace tailWord_898162 prefixEnd_898162 409945610314329040661719 := by
  unfold tailWord_898162
  simp only [CollatzResearch.WordTrace]
  refine ⟨8189664843029985675600185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21839106248079961801600493 8189664843029985675600185)
  ·
    refine ⟨6142248632272489256700139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8189664843029985675600185 6142248632272489256700139)
    ·
      refine ⟨9213372948408733885050209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6142248632272489256700139 9213372948408733885050209)
      ·
        refine ⟨6910029711306550413787657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9213372948408733885050209 6910029711306550413787657)
        ·
          refine ⟨5182522283479912810340743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6910029711306550413787657 5182522283479912810340743)
          ·
            refine ⟨7773783425219869215511115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5182522283479912810340743 7773783425219869215511115)
            ·
              refine ⟨11660675137829803823266673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7773783425219869215511115 11660675137829803823266673)
              ·
                refine ⟨8745506353372352867450005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11660675137829803823266673 8745506353372352867450005)
                ·
                  refine ⟨409945610314329040661719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8745506353372352867450005 409945610314329040661719)
                  ·
                    rfl

theorem cell20_898162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_898162 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_898162 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_898162 prefixEnd_898162 := by exact prefixLift 898162
  have htrace : WordTrace (prefixWord ++ tailWord_898162) baseStart_898162 baseEnd_898162 := by
    simpa [prefixWord, tailWord_898162, baseEnd_898162] using wordTrace_append hprefix tailTrace_898162
  have hstable : (prefixWord ++ tailWord_898162).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898162).length < 2 ^ (prefixWord ++ tailWord_898162).sum := by decide
  have hdescent : baseEnd_898162 < baseStart_898162 := by decide
  rcases family_descends (prefixWord ++ tailWord_898162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898165 : List Nat := [1, 3, 4, 3, 1, 1, 7]
def baseStart_898165 : Nat := 118140960795 + 898165 * 2 ^ 59
def prefixEnd_898165 : Nat := 4983230072969 + 3 ^ 40 * 898165 * 2
def baseEnd_898165 : Nat := 45549664399563818173523

theorem tailTrace_898165 : CollatzResearch.WordTrace tailWord_898165 prefixEnd_898165 45549664399563818173523 := by
  unfold tailWord_898165
  simp only [CollatzResearch.WordTrace]
  refine ⟨32758768791109074214759949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21839179194072716143173299 32758768791109074214759949)
  ·
    refine ⟨12284538296665902830534981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32758768791109074214759949 12284538296665902830534981)
    ·
      refine ⟨2303350930624856780725309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12284538296665902830534981 2303350930624856780725309)
      ·
        refine ⟨863756598984321292771991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2303350930624856780725309 863756598984321292771991)
        ·
          refine ⟨1295634898476481939157987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 863756598984321292771991 1295634898476481939157987)
          ·
            refine ⟨1943452347714722908736981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1295634898476481939157987 1943452347714722908736981)
            ·
              refine ⟨45549664399563818173523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1943452347714722908736981 45549664399563818173523)
              ·
                rfl

theorem cell20_898165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 7].length) (baseStart_898165 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_898165 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_898165 prefixEnd_898165 := by exact prefixLift 898165
  have htrace : WordTrace (prefixWord ++ tailWord_898165) baseStart_898165 baseEnd_898165 := by
    simpa [prefixWord, tailWord_898165, baseEnd_898165] using wordTrace_append hprefix tailTrace_898165
  have hstable : (prefixWord ++ tailWord_898165).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898165).length < 2 ^ (prefixWord ++ tailWord_898165).sum := by decide
  have hdescent : baseEnd_898165 < baseStart_898165 := by decide
  rcases family_descends (prefixWord ++ tailWord_898165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898179 : List Nat := [1, 1, 1, 3, 3, 2, 1, 6, 2]
def baseStart_898179 : Nat := 118140960795 + 898179 * 2 ^ 59
def prefixEnd_898179 : Nat := 4983230072969 + 3 ^ 40 * 898179 * 2
def baseEnd_898179 : Nat := 409953369577552537094983

theorem tailTrace_898179 : CollatzResearch.WordTrace tailWord_898179 prefixEnd_898179 409953369577552537094983 := by
  unfold tailWord_898179
  simp only [CollatzResearch.WordTrace]
  refine ⟨32759279413058354605769591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21839519608705569737179727 32759279413058354605769591)
  ·
    refine ⟨49138919119587531908654387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32759279413058354605769591 49138919119587531908654387)
    ·
      refine ⟨73708378679381297862981581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49138919119587531908654387 73708378679381297862981581)
      ·
        refine ⟨27640642004767986698618093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73708378679381297862981581 27640642004767986698618093)
        ·
          refine ⟨10365240751787995011981785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27640642004767986698618093 10365240751787995011981785)
          ·
            refine ⟨7773930563840996258986339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10365240751787995011981785 7773930563840996258986339)
            ·
              refine ⟨11660895845761494388479509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7773930563840996258986339 11660895845761494388479509)
              ·
                refine ⟨546604492770070049459977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11660895845761494388479509 546604492770070049459977)
                ·
                  refine ⟨409953369577552537094983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 546604492770070049459977 409953369577552537094983)
                  ·
                    rfl

theorem cell20_898179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 6, 2].length) (baseStart_898179 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_898179 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_898179 prefixEnd_898179 := by exact prefixLift 898179
  have htrace : WordTrace (prefixWord ++ tailWord_898179) baseStart_898179 baseEnd_898179 := by
    simpa [prefixWord, tailWord_898179, baseEnd_898179] using wordTrace_append hprefix tailTrace_898179
  have hstable : (prefixWord ++ tailWord_898179).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898179).length < 2 ^ (prefixWord ++ tailWord_898179).sum := by decide
  have hdescent : baseEnd_898179 < baseStart_898179 := by decide
  rcases family_descends (prefixWord ++ tailWord_898179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898230 : List Nat := [5, 1, 3, 2, 1, 2, 1, 1, 4]
def baseStart_898230 : Nat := 118140960795 + 898230 * 2 ^ 59
def prefixEnd_898230 : Nat := 4983230072969 + 3 ^ 40 * 898230 * 2
def baseEnd_898230 : Nat := 409976647367223026394775

theorem tailTrace_898230 : CollatzResearch.WordTrace tailWord_898230 prefixEnd_898230 409976647367223026394775 := by
  unfold tailWord_898230
  simp only [CollatzResearch.WordTrace]
  refine ⟨2047571220992099394742259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21840759690582393543917429 2047571220992099394742259)
  ·
    refine ⟨3071356831488149092113389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2047571220992099394742259 3071356831488149092113389)
    ·
      refine ⟨1151758811808055909542521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3071356831488149092113389 1151758811808055909542521)
      ·
        refine ⟨863819108856041932156891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1151758811808055909542521 863819108856041932156891)
        ·
          refine ⟨1295728663284062898235337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 863819108856041932156891 1295728663284062898235337)
          ·
            refine ⟨971796497463047173676503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1295728663284062898235337 971796497463047173676503)
            ·
              refine ⟨1457694746194570760514755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 971796497463047173676503 1457694746194570760514755)
              ·
                refine ⟨2186542119291856140772133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1457694746194570760514755 2186542119291856140772133)
                ·
                  refine ⟨409976647367223026394775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2186542119291856140772133 409976647367223026394775)
                  ·
                    rfl

theorem cell20_898230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_898230 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_898230 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_898230 prefixEnd_898230 := by exact prefixLift 898230
  have htrace : WordTrace (prefixWord ++ tailWord_898230) baseStart_898230 baseEnd_898230 := by
    simpa [prefixWord, tailWord_898230, baseEnd_898230] using wordTrace_append hprefix tailTrace_898230
  have hstable : (prefixWord ++ tailWord_898230).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898230).length < 2 ^ (prefixWord ++ tailWord_898230).sum := by decide
  have hdescent : baseEnd_898230 < baseStart_898230 := by decide
  rcases family_descends (prefixWord ++ tailWord_898230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898231 : List Nat := [1, 1, 3, 1, 4, 1, 2, 4, 3]
def baseStart_898231 : Nat := 118140960795 + 898231 * 2 ^ 59
def prefixEnd_898231 : Nat := 4983230072969 + 3 ^ 40 * 898231 * 2
def baseEnd_898231 : Nat := 409977103794471467361437

theorem tailTrace_898231 : CollatzResearch.WordTrace tailWord_898231 prefixEnd_898231 409977103794471467361437 := by
  unfold tailWord_898231
  simp only [CollatzResearch.WordTrace]
  refine ⟨32761176008869967486662547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21840784005913311657775031 32761176008869967486662547)
  ·
    refine ⟨49141764013304951229993821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32761176008869967486662547 49141764013304951229993821)
    ·
      refine ⟨18428161504989356711247683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49141764013304951229993821 18428161504989356711247683)
      ·
        refine ⟨27642242257484035066871525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18428161504989356711247683 27642242257484035066871525)
        ·
          refine ⟨5182920423278256575038411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27642242257484035066871525 5182920423278256575038411)
          ·
            refine ⟨7774380634917384862557617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5182920423278256575038411 7774380634917384862557617)
            ·
              refine ⟨5830785476188038646918213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7774380634917384862557617 5830785476188038646918213)
              ·
                refine ⟨1093272276785257246297165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5830785476188038646918213 1093272276785257246297165)
                ·
                  refine ⟨409977103794471467361437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1093272276785257246297165 409977103794471467361437)
                  ·
                    rfl

theorem cell20_898231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 4, 3].length) (baseStart_898231 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_898231 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_898231 prefixEnd_898231 := by exact prefixLift 898231
  have htrace : WordTrace (prefixWord ++ tailWord_898231) baseStart_898231 baseEnd_898231 := by
    simpa [prefixWord, tailWord_898231, baseEnd_898231] using wordTrace_append hprefix tailTrace_898231
  have hstable : (prefixWord ++ tailWord_898231).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898231).length < 2 ^ (prefixWord ++ tailWord_898231).sum := by decide
  have hdescent : baseEnd_898231 < baseStart_898231 := by decide
  rcases family_descends (prefixWord ++ tailWord_898231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898241 : List Nat := [1, 2, 6, 1, 1, 2, 2, 5]
def baseStart_898241 : Nat := 118140960795 + 898241 * 2 ^ 59
def prefixEnd_898241 : Nat := 4983230072969 + 3 ^ 40 * 898241 * 2
def baseEnd_898241 : Nat := 136660556022318625676021

theorem tailTrace_898241 : CollatzResearch.WordTrace tailWord_898241 prefixEnd_898241 136660556022318625676021 := by
  unfold tailWord_898241
  simp only [CollatzResearch.WordTrace]
  refine ⟨32761540738833739194526577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21841027159222492796351051 32761540738833739194526577)
  ·
    refine ⟨24571155554125304395894933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32761540738833739194526577 24571155554125304395894933)
    ·
      refine ⟨1151772916599623643557575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 24571155554125304395894933 1151772916599623643557575)
      ·
        refine ⟨1727659374899435465336363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1151772916599623643557575 1727659374899435465336363)
        ·
          refine ⟨2591489062349153198004545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1727659374899435465336363 2591489062349153198004545)
          ·
            refine ⟨1943616796761864898503409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2591489062349153198004545 1943616796761864898503409)
            ·
              refine ⟨1457712597571398673877557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1943616796761864898503409 1457712597571398673877557)
              ·
                refine ⟨136660556022318625676021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1457712597571398673877557 136660556022318625676021)
                ·
                  rfl

theorem cell20_898241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 5].length) (baseStart_898241 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_898241 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_898241 prefixEnd_898241 := by exact prefixLift 898241
  have htrace : WordTrace (prefixWord ++ tailWord_898241) baseStart_898241 baseEnd_898241 := by
    simpa [prefixWord, tailWord_898241, baseEnd_898241] using wordTrace_append hprefix tailTrace_898241
  have hstable : (prefixWord ++ tailWord_898241).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898241).length < 2 ^ (prefixWord ++ tailWord_898241).sum := by decide
  have hdescent : baseEnd_898241 < baseStart_898241 := by decide
  rcases family_descends (prefixWord ++ tailWord_898241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898244 : List Nat := [2, 3, 3, 1, 3, 2, 2, 1, 3]
def baseStart_898244 : Nat := 118140960795 + 898244 * 2 ^ 59
def prefixEnd_898244 : Nat := 4983230072969 + 3 ^ 40 * 898244 * 2
def baseEnd_898244 : Nat := 409983037348701199928051

theorem tailTrace_898244 : CollatzResearch.WordTrace tailWord_898244 prefixEnd_898244 409983037348701199928051 := by
  unfold tailWord_898244
  simp only [CollatzResearch.WordTrace]
  refine ⟨16380825078911435353442893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21841100105215247137923857 16380825078911435353442893)
  ·
    refine ⟨6142809404591788257541085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16380825078911435353442893 6142809404591788257541085)
    ·
      refine ⟨2303553526721920596577907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6142809404591788257541085 2303553526721920596577907)
      ·
        refine ⟨3455330290082880894866861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2303553526721920596577907 3455330290082880894866861)
        ·
          refine ⟨1295748858781080335575073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3455330290082880894866861 1295748858781080335575073)
          ·
            refine ⟨971811644085810251681305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1295748858781080335575073 971811644085810251681305)
            ·
              refine ⟨728858733064357688760979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 971811644085810251681305 728858733064357688760979)
              ·
                refine ⟨1093288099596536533141469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 728858733064357688760979 1093288099596536533141469)
                ·
                  refine ⟨409983037348701199928051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1093288099596536533141469 409983037348701199928051)
                  ·
                    rfl

theorem cell20_898244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 2, 1, 3].length) (baseStart_898244 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_898244 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_898244 prefixEnd_898244 := by exact prefixLift 898244
  have htrace : WordTrace (prefixWord ++ tailWord_898244) baseStart_898244 baseEnd_898244 := by
    simpa [prefixWord, tailWord_898244, baseEnd_898244] using wordTrace_append hprefix tailTrace_898244
  have hstable : (prefixWord ++ tailWord_898244).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898244).length < 2 ^ (prefixWord ++ tailWord_898244).sum := by decide
  have hdescent : baseEnd_898244 < baseStart_898244 := by decide
  rcases family_descends (prefixWord ++ tailWord_898244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898248 : List Nat := [2, 1, 3, 1, 2, 1, 6, 1, 3]
def baseStart_898248 : Nat := 118140960795 + 898248 * 2 ^ 59
def prefixEnd_898248 : Nat := 4983230072969 + 3 ^ 40 * 898248 * 2
def baseEnd_898248 : Nat := 409984863057694963794701

theorem tailTrace_898248 : CollatzResearch.WordTrace tailWord_898248 prefixEnd_898248 409984863057694963794701 := by
  unfold tailWord_898248
  simp only [CollatzResearch.WordTrace]
  refine ⟨16380898024904189695015699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21841197366538919593354265 16380898024904189695015699)
  ·
    refine ⟨24571347037356284542523549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16380898024904189695015699 24571347037356284542523549)
    ·
      refine ⟨9214255139008606703446331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24571347037356284542523549 9214255139008606703446331)
      ·
        refine ⟨13821382708512910055169497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9214255139008606703446331 13821382708512910055169497)
        ·
          refine ⟨10366037031384682541377123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13821382708512910055169497 10366037031384682541377123)
          ·
            refine ⟨15549055547077023812065685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10366037031384682541377123 15549055547077023812065685)
            ·
              refine ⟨728861978769235491190579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15549055547077023812065685 728861978769235491190579)
              ·
                refine ⟨1093292968153853236785869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 728861978769235491190579 1093292968153853236785869)
                ·
                  refine ⟨409984863057694963794701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1093292968153853236785869 409984863057694963794701)
                  ·
                    rfl

theorem cell20_898248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 6, 1, 3].length) (baseStart_898248 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_898248 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_898248 prefixEnd_898248 := by exact prefixLift 898248
  have htrace : WordTrace (prefixWord ++ tailWord_898248) baseStart_898248 baseEnd_898248 := by
    simpa [prefixWord, tailWord_898248, baseEnd_898248] using wordTrace_append hprefix tailTrace_898248
  have hstable : (prefixWord ++ tailWord_898248).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898248).length < 2 ^ (prefixWord ++ tailWord_898248).sum := by decide
  have hdescent : baseEnd_898248 < baseStart_898248 := by decide
  rcases family_descends (prefixWord ++ tailWord_898248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898292 : List Nat := [2, 6, 1, 2, 2, 1, 1, 5]
def baseStart_898292 : Nat := 118140960795 + 898292 * 2 ^ 59
def prefixEnd_898292 : Nat := 4983230072969 + 3 ^ 40 * 898292 * 2
def baseEnd_898292 : Nat := 136668315285542122109285

theorem tailTrace_898292 : CollatzResearch.WordTrace tailWord_898292 prefixEnd_898292 136668315285542122109285 := by
  unfold tailWord_898292
  simp only [CollatzResearch.WordTrace]
  refine ⟨16381700430824487452316565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21842267241099316603088753 16381700430824487452316565)
  ·
    refine ⟨767892207694897849327339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 16381700430824487452316565 767892207694897849327339)
    ·
      refine ⟨1151838311542346773991009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 767892207694897849327339 1151838311542346773991009)
      ·
        refine ⟨863878733656760080493257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1151838311542346773991009 863878733656760080493257)
        ·
          refine ⟨647909050242570060369943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 863878733656760080493257 647909050242570060369943)
          ·
            refine ⟨971863575363855090554915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 647909050242570060369943 971863575363855090554915)
            ·
              refine ⟨1457795363045782635832373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 971863575363855090554915 1457795363045782635832373)
              ·
                refine ⟨136668315285542122109285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1457795363045782635832373 136668315285542122109285)
                ·
                  rfl

theorem cell20_898292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 5].length) (baseStart_898292 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_898292 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_898292 prefixEnd_898292 := by exact prefixLift 898292
  have htrace : WordTrace (prefixWord ++ tailWord_898292) baseStart_898292 baseEnd_898292 := by
    simpa [prefixWord, tailWord_898292, baseEnd_898292] using wordTrace_append hprefix tailTrace_898292
  have hstable : (prefixWord ++ tailWord_898292).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898292).length < 2 ^ (prefixWord ++ tailWord_898292).sum := by decide
  have hdescent : baseEnd_898292 < baseStart_898292 := by decide
  rcases family_descends (prefixWord ++ tailWord_898292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898307 : List Nat := [1, 1, 1, 3, 2, 4, 2, 3, 3]
def baseStart_898307 : Nat := 118140960795 + 898307 * 2 ^ 59
def prefixEnd_898307 : Nat := 4983230072969 + 3 ^ 40 * 898307 * 2
def baseEnd_898307 : Nat := 410011792265352980827793

theorem tailTrace_898307 : CollatzResearch.WordTrace tailWord_898307 prefixEnd_898307 410011792265352980827793 := by
  unfold tailWord_898307
  simp only [CollatzResearch.WordTrace]
  refine ⟨32763947956594632466429175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21842631971063088310952783 32763947956594632466429175)
  ·
    refine ⟨49145921934891948699643763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32763947956594632466429175 49145921934891948699643763)
    ·
      refine ⟨73718882902337923049465645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49145921934891948699643763 73718882902337923049465645)
      ·
        refine ⟨27644581088376721143549617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73718882902337923049465645 27644581088376721143549617)
        ·
          refine ⟨20733435816282540857662213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27644581088376721143549617 20733435816282540857662213)
          ·
            refine ⟨3887519215552976410811665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20733435816282540857662213 3887519215552976410811665)
            ·
              refine ⟨2915639411664732308108749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3887519215552976410811665 2915639411664732308108749)
              ·
                refine ⟨1093364779374274615540781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2915639411664732308108749 1093364779374274615540781)
                ·
                  refine ⟨410011792265352980827793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1093364779374274615540781 410011792265352980827793)
                  ·
                    rfl

theorem cell20_898307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 3, 3].length) (baseStart_898307 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_898307 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_898307 prefixEnd_898307 := by exact prefixLift 898307
  have htrace : WordTrace (prefixWord ++ tailWord_898307) baseStart_898307 baseEnd_898307 := by
    simpa [prefixWord, tailWord_898307, baseEnd_898307] using wordTrace_append hprefix tailTrace_898307
  have hstable : (prefixWord ++ tailWord_898307).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898307).length < 2 ^ (prefixWord ++ tailWord_898307).sum := by decide
  have hdescent : baseEnd_898307 < baseStart_898307 := by decide
  rcases family_descends (prefixWord ++ tailWord_898307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898338 : List Nat := [3, 3, 1, 1, 4, 1, 7]
def baseStart_898338 : Nat := 118140960795 + 898338 * 2 ^ 59
def prefixEnd_898338 : Nat := 4983230072969 + 3 ^ 40 * 898338 * 2
def baseEnd_898338 : Nat := 45558437945561627866037

theorem tailTrace_898338 : CollatzResearch.WordTrace tailWord_898338 prefixEnd_898338 45558437945561627866037 := by
  unfold tailWord_898338
  simp only [CollatzResearch.WordTrace]
  refine ⟨8191269654870581190201917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21843385746321549840538445 8191269654870581190201917)
  ·
    refine ⟨3071726120576467946325719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8191269654870581190201917 3071726120576467946325719)
    ·
      refine ⟨4607589180864701919488579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3071726120576467946325719 4607589180864701919488579)
      ·
        refine ⟨6911383771297052879232869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4607589180864701919488579 6911383771297052879232869)
        ·
          refine ⟨1295884457118197414856163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6911383771297052879232869 1295884457118197414856163)
          ·
            refine ⟨1943826685677296122284245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1295884457118197414856163 1943826685677296122284245)
            ·
              refine ⟨45558437945561627866037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1943826685677296122284245 45558437945561627866037)
              ·
                rfl

theorem cell20_898338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 7].length) (baseStart_898338 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_898338 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_898338 prefixEnd_898338 := by exact prefixLift 898338
  have htrace : WordTrace (prefixWord ++ tailWord_898338) baseStart_898338 baseEnd_898338 := by
    simpa [prefixWord, tailWord_898338, baseEnd_898338] using wordTrace_append hprefix tailTrace_898338
  have hstable : (prefixWord ++ tailWord_898338).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898338).length < 2 ^ (prefixWord ++ tailWord_898338).sum := by decide
  have hdescent : baseEnd_898338 < baseStart_898338 := by decide
  rcases family_descends (prefixWord ++ tailWord_898338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898352 : List Nat := [2, 1, 1, 1, 2, 2, 6, 1, 4]
def baseStart_898352 : Nat := 118140960795 + 898352 * 2 ^ 59
def prefixEnd_898352 : Nat := 4983230072969 + 3 ^ 40 * 898352 * 2
def baseEnd_898352 : Nat := 410032331491532824327609

theorem tailTrace_898352 : CollatzResearch.WordTrace tailWord_898352 prefixEnd_898352 410032331491532824327609 := by
  unfold tailWord_898352
  simp only [CollatzResearch.WordTrace]
  refine ⟨16382794620715802575908655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21843726160954403434544873 16382794620715802575908655)
  ·
    refine ⟨24574191931073703863862983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16382794620715802575908655 24574191931073703863862983)
    ·
      refine ⟨36861287896610555795794475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24574191931073703863862983 36861287896610555795794475)
      ·
        refine ⟨55291931844915833693691713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36861287896610555795794475 55291931844915833693691713)
        ·
          refine ⟨41468948883686875270268785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55291931844915833693691713 41468948883686875270268785)
          ·
            refine ⟨31101711662765156452701589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41468948883686875270268785 31101711662765156452701589)
            ·
              refine ⟨1457892734192116708720387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 31101711662765156452701589 1457892734192116708720387)
              ·
                refine ⟨2186839101288175063080581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1457892734192116708720387 2186839101288175063080581)
                ·
                  refine ⟨410032331491532824327609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2186839101288175063080581 410032331491532824327609)
                  ·
                    rfl

theorem cell20_898352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 1, 4].length) (baseStart_898352 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_898352 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_898352 prefixEnd_898352 := by exact prefixLift 898352
  have htrace : WordTrace (prefixWord ++ tailWord_898352) baseStart_898352 baseEnd_898352 := by
    simpa [prefixWord, tailWord_898352, baseEnd_898352] using wordTrace_append hprefix tailTrace_898352
  have hstable : (prefixWord ++ tailWord_898352).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898352).length < 2 ^ (prefixWord ++ tailWord_898352).sum := by decide
  have hdescent : baseEnd_898352 < baseStart_898352 := by decide
  rcases family_descends (prefixWord ++ tailWord_898352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898362 : List Nat := [3, 1, 1, 1, 4, 1, 5, 1, 3]
def baseStart_898362 : Nat := 118140960795 + 898362 * 2 ^ 59
def prefixEnd_898362 : Nat := 4983230072969 + 3 ^ 40 * 898362 * 2
def baseEnd_898362 : Nat := 410036895764017233994235

theorem tailTrace_898362 : CollatzResearch.WordTrace tailWord_898362 prefixEnd_898362 410036895764017233994235 := by
  unfold tailWord_898362
  simp only [CollatzResearch.WordTrace]
  refine ⟨8191488492848844214920335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21843969314263584573120893 8191488492848844214920335)
  ·
    refine ⟨12287232739273266322380503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8191488492848844214920335 12287232739273266322380503)
    ·
      refine ⟨18430849108909899483570755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12287232739273266322380503 18430849108909899483570755)
      ·
        refine ⟨27646273663364849225356133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18430849108909899483570755 27646273663364849225356133)
        ·
          refine ⟨5183676311880909229754275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27646273663364849225356133 5183676311880909229754275)
          ·
            refine ⟨7775514467821363844631413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5183676311880909229754275 7775514467821363844631413)
            ·
              refine ⟨728954481358252860434195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7775514467821363844631413 728954481358252860434195)
              ·
                refine ⟨1093431722037379290651293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 728954481358252860434195 1093431722037379290651293)
                ·
                  refine ⟨410036895764017233994235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1093431722037379290651293 410036895764017233994235)
                  ·
                    rfl

theorem cell20_898362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 5, 1, 3].length) (baseStart_898362 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_898362 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_898362 prefixEnd_898362 := by exact prefixLift 898362
  have htrace : WordTrace (prefixWord ++ tailWord_898362) baseStart_898362 baseEnd_898362 := by
    simpa [prefixWord, tailWord_898362, baseEnd_898362] using wordTrace_append hprefix tailTrace_898362
  have hstable : (prefixWord ++ tailWord_898362).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898362).length < 2 ^ (prefixWord ++ tailWord_898362).sum := by decide
  have hdescent : baseEnd_898362 < baseStart_898362 := by decide
  rcases family_descends (prefixWord ++ tailWord_898362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898369 : List Nat := [1, 2, 5, 2, 1, 1, 2, 2, 4]
def baseStart_898369 : Nat := 118140960795 + 898369 * 2 ^ 59
def prefixEnd_898369 : Nat := 4983230072969 + 3 ^ 40 * 898369 * 2
def baseEnd_898369 : Nat := 410040090754756320760873

theorem tailTrace_898369 : CollatzResearch.WordTrace tailWord_898369 prefixEnd_898369 410040090754756320760873 := by
  unfold tailWord_898369
  simp only [CollatzResearch.WordTrace]
  refine ⟨32766209282370017055186161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21844139521580011370124107 32766209282370017055186161)
  ·
    refine ⟨24574656961777512791389621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32766209282370017055186161 24574656961777512791389621)
    ·
      refine ⟨2303874090166641824192777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24574656961777512791389621 2303874090166641824192777)
      ·
        refine ⟨1727905567624981368144583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2303874090166641824192777 1727905567624981368144583)
        ·
          refine ⟨2591858351437472052216875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1727905567624981368144583 2591858351437472052216875)
          ·
            refine ⟨3887787527156208078325313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2591858351437472052216875 3887787527156208078325313)
            ·
              refine ⟨2915840645367156058743985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3887787527156208078325313 2915840645367156058743985)
              ·
                refine ⟨2186880484025367044057989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2915840645367156058743985 2186880484025367044057989)
                ·
                  refine ⟨410040090754756320760873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2186880484025367044057989 410040090754756320760873)
                  ·
                    rfl

theorem cell20_898369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 2, 4].length) (baseStart_898369 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_898369 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_898369 prefixEnd_898369 := by exact prefixLift 898369
  have htrace : WordTrace (prefixWord ++ tailWord_898369) baseStart_898369 baseEnd_898369 := by
    simpa [prefixWord, tailWord_898369, baseEnd_898369] using wordTrace_append hprefix tailTrace_898369
  have hstable : (prefixWord ++ tailWord_898369).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898369).length < 2 ^ (prefixWord ++ tailWord_898369).sum := by decide
  have hdescent : baseEnd_898369 < baseStart_898369 := by decide
  rcases family_descends (prefixWord ++ tailWord_898369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898372 : List Nat := [2, 3, 4, 1, 1, 3, 2, 4]
def baseStart_898372 : Nat := 118140960795 + 898372 * 2 ^ 59
def prefixEnd_898372 : Nat := 4983230072969 + 3 ^ 40 * 898372 * 2
def baseEnd_898372 : Nat := 136680486678833881220287

theorem tailTrace_898372 : CollatzResearch.WordTrace tailWord_898372 prefixEnd_898372 136680486678833881220287 := by
  unfold tailWord_898372
  simp only [CollatzResearch.WordTrace]
  refine ⟨16383159350679574283772685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21844212467572765711696913 16383159350679574283772685)
  ·
    refine ⟨6143684756504840356414757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16383159350679574283772685 6143684756504840356414757)
    ·
      refine ⟨1151940891844657566827767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6143684756504840356414757 1151940891844657566827767)
      ·
        refine ⟨1727911337766986350241651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1151940891844657566827767 1727911337766986350241651)
        ·
          refine ⟨2591867006650479525362477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1727911337766986350241651 2591867006650479525362477)
          ·
            refine ⟨971950127493929822010929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2591867006650479525362477 971950127493929822010929)
            ·
              refine ⟨728962595620447366508197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 971950127493929822010929 728962595620447366508197)
              ·
                refine ⟨136680486678833881220287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 728962595620447366508197 136680486678833881220287)
                ·
                  rfl

theorem cell20_898372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 2, 4].length) (baseStart_898372 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_898372 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_898372 prefixEnd_898372 := by exact prefixLift 898372
  have htrace : WordTrace (prefixWord ++ tailWord_898372) baseStart_898372 baseEnd_898372 := by
    simpa [prefixWord, tailWord_898372, baseEnd_898372] using wordTrace_append hprefix tailTrace_898372
  have hstable : (prefixWord ++ tailWord_898372).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898372).length < 2 ^ (prefixWord ++ tailWord_898372).sum := by decide
  have hdescent : baseEnd_898372 < baseStart_898372 := by decide
  rcases family_descends (prefixWord ++ tailWord_898372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898435 : List Nat := [1, 1, 1, 3, 5, 1, 2, 6]
def baseStart_898435 : Nat := 118140960795 + 898435 * 2 ^ 59
def prefixEnd_898435 : Nat := 4983230072969 + 3 ^ 40 * 898435 * 2
def baseEnd_898435 : Nat := 136690071651051141520201

theorem tailTrace_898435 : CollatzResearch.WordTrace tailWord_898435 prefixEnd_898435 136690071651051141520201 := by
  unfold tailWord_898435
  simp only [CollatzResearch.WordTrace]
  refine ⟨32768616500130910327088759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21845744333420606884725839 32768616500130910327088759)
  ·
    refine ⟨49152924750196365490633139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32768616500130910327088759 49152924750196365490633139)
    ·
      refine ⟨73729387125294548235949709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49152924750196365490633139 73729387125294548235949709)
      ·
        refine ⟨27648520171985455588481141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73729387125294548235949709 27648520171985455588481141)
        ·
          refine ⟨2592048766123636461420107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27648520171985455588481141 2592048766123636461420107)
          ·
            refine ⟨3888073149185454692130161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2592048766123636461420107 3888073149185454692130161)
            ·
              refine ⟨2916054861889091019097621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3888073149185454692130161 2916054861889091019097621)
              ·
                refine ⟨136690071651051141520201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2916054861889091019097621 136690071651051141520201)
                ·
                  rfl

theorem cell20_898435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 6].length) (baseStart_898435 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_898435 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_898435 prefixEnd_898435 := by exact prefixLift 898435
  have htrace : WordTrace (prefixWord ++ tailWord_898435) baseStart_898435 baseEnd_898435 := by
    simpa [prefixWord, tailWord_898435, baseEnd_898435] using wordTrace_append hprefix tailTrace_898435
  have hstable : (prefixWord ++ tailWord_898435).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898435).length < 2 ^ (prefixWord ++ tailWord_898435).sum := by decide
  have hdescent : baseEnd_898435 < baseStart_898435 := by decide
  rcases family_descends (prefixWord ++ tailWord_898435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898449 : List Nat := [1, 2, 2, 1, 1, 1, 2, 4, 6]
def baseStart_898449 : Nat := 118140960795 + 898449 * 2 ^ 59
def prefixEnd_898449 : Nat := 4983230072969 + 3 ^ 40 * 898449 * 2
def baseEnd_898449 : Nat := 410076604934631598093879

theorem tailTrace_898449 : CollatzResearch.WordTrace tailWord_898449 prefixEnd_898449 410076604934631598093879 := by
  unfold tailWord_898449
  simp only [CollatzResearch.WordTrace]
  refine ⟨32769127122080190718098401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21846084748053460478732267 32769127122080190718098401)
  ·
    refine ⟨24576845341560143038573801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32769127122080190718098401 24576845341560143038573801)
    ·
      refine ⟨18432634006170107278930351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24576845341560143038573801 18432634006170107278930351)
      ·
        refine ⟨27648951009255160918395527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18432634006170107278930351 27648951009255160918395527)
        ·
          refine ⟨41473426513882741377593291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27648951009255160918395527 41473426513882741377593291)
          ·
            refine ⟨62210139770824112066389937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41473426513882741377593291 62210139770824112066389937)
            ·
              refine ⟨46657604828118084049792453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62210139770824112066389937 46657604828118084049792453)
              ·
                refine ⟨8748300905272140759336085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46657604828118084049792453 8748300905272140759336085)
                ·
                  refine ⟨410076604934631598093879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8748300905272140759336085 410076604934631598093879)
                  ·
                    rfl

theorem cell20_898449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 6].length) (baseStart_898449 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_898449 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_898449 prefixEnd_898449 := by exact prefixLift 898449
  have htrace : WordTrace (prefixWord ++ tailWord_898449) baseStart_898449 baseEnd_898449 := by
    simpa [prefixWord, tailWord_898449, baseEnd_898449] using wordTrace_append hprefix tailTrace_898449
  have hstable : (prefixWord ++ tailWord_898449).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898449).length < 2 ^ (prefixWord ++ tailWord_898449).sum := by decide
  have hdescent : baseEnd_898449 < baseStart_898449 := by decide
  rcases family_descends (prefixWord ++ tailWord_898449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898500 : List Nat := [2, 3, 3, 2, 1, 1, 1, 5, 2]
def baseStart_898500 : Nat := 118140960795 + 898500 * 2 ^ 59
def prefixEnd_898500 : Nat := 4983230072969 + 3 ^ 40 * 898500 * 2
def baseEnd_898500 : Nat := 410099882724302087393671

theorem tailTrace_898500 : CollatzResearch.WordTrace tailWord_898500 prefixEnd_898500 410099882724302087393671 := by
  unfold tailWord_898500
  simp only [CollatzResearch.WordTrace]
  refine ⟨16385493622447713214102477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21847324829930284285469969 16385493622447713214102477)
  ·
    refine ⟨6144560108417892455288429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16385493622447713214102477 6144560108417892455288429)
    ·
      refine ⟨2304210040656709670733161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6144560108417892455288429 2304210040656709670733161)
      ·
        refine ⟨1728157530492532253049871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2304210040656709670733161 1728157530492532253049871)
        ·
          refine ⟨2592236295738798379574807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1728157530492532253049871 2592236295738798379574807)
          ·
            refine ⟨3888354443608197569362211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2592236295738798379574807 3888354443608197569362211)
            ·
              refine ⟨5832531665412296354043317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3888354443608197569362211 5832531665412296354043317)
              ·
                refine ⟨546799843632402783191561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5832531665412296354043317 546799843632402783191561)
                ·
                  refine ⟨410099882724302087393671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 546799843632402783191561 410099882724302087393671)
                  ·
                    rfl

theorem cell20_898500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 5, 2].length) (baseStart_898500 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_898500 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_898500 prefixEnd_898500 := by exact prefixLift 898500
  have htrace : WordTrace (prefixWord ++ tailWord_898500) baseStart_898500 baseEnd_898500 := by
    simpa [prefixWord, tailWord_898500, baseEnd_898500] using wordTrace_append hprefix tailTrace_898500
  have hstable : (prefixWord ++ tailWord_898500).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898500).length < 2 ^ (prefixWord ++ tailWord_898500).sum := by decide
  have hdescent : baseEnd_898500 < baseStart_898500 := by decide
  rcases family_descends (prefixWord ++ tailWord_898500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898521 : List Nat := [1, 2, 1, 2, 4, 2, 2, 4, 2]
def baseStart_898521 : Nat := 118140960795 + 898521 * 2 ^ 59
def prefixEnd_898521 : Nat := 4983230072969 + 3 ^ 40 * 898521 * 2
def baseEnd_898521 : Nat := 410109467696519347693585

theorem tailTrace_898521 : CollatzResearch.WordTrace tailWord_898521 prefixEnd_898521 410109467696519347693585 := by
  unfold tailWord_898521
  simp only [CollatzResearch.WordTrace]
  refine ⟨32771753177819347014719417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21847835451879564676479611 32771753177819347014719417)
  ·
    refine ⟨24578814883364510261039563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32771753177819347014719417 24578814883364510261039563)
    ·
      refine ⟨36868222325046765391559345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24578814883364510261039563 36868222325046765391559345)
      ·
        refine ⟨27651166743785074043669509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36868222325046765391559345 27651166743785074043669509)
        ·
          refine ⟨5184593764459701383188033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27651166743785074043669509 5184593764459701383188033)
          ·
            refine ⟨3888445323344776037391025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5184593764459701383188033 3888445323344776037391025)
            ·
              refine ⟨2916333992508582028043269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3888445323344776037391025 2916333992508582028043269)
              ·
                refine ⟨546812623595359130258113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2916333992508582028043269 546812623595359130258113)
                ·
                  refine ⟨410109467696519347693585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 546812623595359130258113 410109467696519347693585)
                  ·
                    rfl

theorem cell20_898521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 4, 2].length) (baseStart_898521 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_898521 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_898521 prefixEnd_898521 := by exact prefixLift 898521
  have htrace : WordTrace (prefixWord ++ tailWord_898521) baseStart_898521 baseEnd_898521 := by
    simpa [prefixWord, tailWord_898521, baseEnd_898521] using wordTrace_append hprefix tailTrace_898521
  have hstable : (prefixWord ++ tailWord_898521).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898521).length < 2 ^ (prefixWord ++ tailWord_898521).sum := by decide
  have hdescent : baseEnd_898521 < baseStart_898521 := by decide
  rcases family_descends (prefixWord ++ tailWord_898521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898542 : List Nat := [4, 1, 2, 1, 2, 1, 1, 4, 4]
def baseStart_898542 : Nat := 118140960795 + 898542 * 2 ^ 59
def prefixEnd_898542 : Nat := 4983230072969 + 3 ^ 40 * 898542 * 2
def baseEnd_898542 : Nat := 410119052668736607993499

theorem tailTrace_898542 : CollatzResearch.WordTrace tailWord_898542 prefixEnd_898542 410119052668736607993499 := by
  unfold tailWord_898542
  simp only [CollatzResearch.WordTrace]
  refine ⟨4096564888842908450154235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21848346073828845067489253 4096564888842908450154235)
  ·
    refine ⟨6144847333264362675231353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4096564888842908450154235 6144847333264362675231353)
    ·
      refine ⟨4608635499948272006423515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6144847333264362675231353 4608635499948272006423515)
      ·
        refine ⟨6912953249922408009635273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4608635499948272006423515 6912953249922408009635273)
        ·
          refine ⟨5184714937441806007226455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6912953249922408009635273 5184714937441806007226455)
          ·
            refine ⟨7777072406162709010839683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5184714937441806007226455 7777072406162709010839683)
            ·
              refine ⟨11665608609244063516259525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7777072406162709010839683 11665608609244063516259525)
              ·
                refine ⟨2187301614233261909298661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11665608609244063516259525 2187301614233261909298661)
                ·
                  refine ⟨410119052668736607993499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2187301614233261909298661 410119052668736607993499)
                  ·
                    rfl

theorem cell20_898542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_898542 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_898542 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_898542 prefixEnd_898542 := by exact prefixLift 898542
  have htrace : WordTrace (prefixWord ++ tailWord_898542) baseStart_898542 baseEnd_898542 := by
    simpa [prefixWord, tailWord_898542, baseEnd_898542] using wordTrace_append hprefix tailTrace_898542
  have hstable : (prefixWord ++ tailWord_898542).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898542).length < 2 ^ (prefixWord ++ tailWord_898542).sum := by decide
  have hdescent : baseEnd_898542 < baseStart_898542 := by decide
  rcases family_descends (prefixWord ++ tailWord_898542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898556 : List Nat := [2, 2, 2, 1, 2, 1, 3, 2, 5]
def baseStart_898556 : Nat := 118140960795 + 898556 * 2 ^ 59
def prefixEnd_898556 : Nat := 4983230072969 + 3 ^ 40 * 898556 * 2
def baseEnd_898556 : Nat := 410125442650214781526775

theorem tailTrace_898556 : CollatzResearch.WordTrace tailWord_898556 prefixEnd_898556 410125442650214781526775 := by
  unfold tailWord_898556
  simp only [CollatzResearch.WordTrace]
  refine ⟨16386514866346273996121761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21848686488461698661495681 16386514866346273996121761)
  ·
    refine ⟨12289886149759705497091321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16386514866346273996121761 12289886149759705497091321)
    ·
      refine ⟨9217414612319779122818491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12289886149759705497091321 9217414612319779122818491)
      ·
        refine ⟨13826121918479668684227737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9217414612319779122818491 13826121918479668684227737)
        ·
          refine ⟨10369591438859751513170803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13826121918479668684227737 10369591438859751513170803)
          ·
            refine ⟨15554387158289627269756205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10369591438859751513170803 15554387158289627269756205)
            ·
              refine ⟨5832895184358610226158577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15554387158289627269756205 5832895184358610226158577)
              ·
                refine ⟨4374671388268957669618933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5832895184358610226158577 4374671388268957669618933)
                ·
                  refine ⟨410125442650214781526775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4374671388268957669618933 410125442650214781526775)
                  ·
                    rfl

theorem cell20_898556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 2, 5].length) (baseStart_898556 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_898556 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_898556 prefixEnd_898556 := by exact prefixLift 898556
  have htrace : WordTrace (prefixWord ++ tailWord_898556) baseStart_898556 baseEnd_898556 := by
    simpa [prefixWord, tailWord_898556, baseEnd_898556] using wordTrace_append hprefix tailTrace_898556
  have hstable : (prefixWord ++ tailWord_898556).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898556).length < 2 ^ (prefixWord ++ tailWord_898556).sum := by decide
  have hdescent : baseEnd_898556 < baseStart_898556 := by decide
  rcases family_descends (prefixWord ++ tailWord_898556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898631 : List Nat := [1, 1, 4, 1, 5, 2, 2, 2, 2]
def baseStart_898631 : Nat := 118140960795 + 898631 * 2 ^ 59
def prefixEnd_898631 : Nat := 4983230072969 + 3 ^ 40 * 898631 * 2
def baseEnd_898631 : Nat := 410159674693847854026469

theorem tailTrace_898631 : CollatzResearch.WordTrace tailWord_898631 prefixEnd_898631 410159674693847854026469 := by
  unfold tailWord_898631
  simp only [CollatzResearch.WordTrace]
  refine ⟨32775765207420835801223747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21850510138280557200815831 32775765207420835801223747)
  ·
    refine ⟨49163647811131253701835621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32775765207420835801223747 49163647811131253701835621)
    ·
      refine ⟨9218183964587110069094179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49163647811131253701835621 9218183964587110069094179)
      ·
        refine ⟨13827275946880665103641269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9218183964587110069094179 13827275946880665103641269)
        ·
          refine ⟨1296307120020062353466369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13827275946880665103641269 1296307120020062353466369)
          ·
            refine ⟨972230340015046765099777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1296307120020062353466369 972230340015046765099777)
            ·
              refine ⟨729172755011285073824833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 972230340015046765099777 729172755011285073824833)
              ·
                refine ⟨546879566258463805368625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 729172755011285073824833 546879566258463805368625)
                ·
                  refine ⟨410159674693847854026469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 546879566258463805368625 410159674693847854026469)
                  ·
                    rfl

theorem cell20_898631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 2, 2, 2].length) (baseStart_898631 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_898631 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_898631 prefixEnd_898631 := by exact prefixLift 898631
  have htrace : WordTrace (prefixWord ++ tailWord_898631) baseStart_898631 baseEnd_898631 := by
    simpa [prefixWord, tailWord_898631, baseEnd_898631] using wordTrace_append hprefix tailTrace_898631
  have hstable : (prefixWord ++ tailWord_898631).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898631).length < 2 ^ (prefixWord ++ tailWord_898631).sum := by decide
  have hdescent : baseEnd_898631 < baseStart_898631 := by decide
  rcases family_descends (prefixWord ++ tailWord_898631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898639 : List Nat := [1, 1, 2, 1, 1, 2, 3, 5, 4]
def baseStart_898639 : Nat := 118140960795 + 898639 * 2 ^ 59
def prefixEnd_898639 : Nat := 4983230072969 + 3 ^ 40 * 898639 * 2
def baseEnd_898639 : Nat := 410163326111835381759769

theorem tailTrace_898639 : CollatzResearch.WordTrace tailWord_898639 prefixEnd_898639 410163326111835381759769 := by
  unfold tailWord_898639
  simp only [CollatzResearch.WordTrace]
  refine ⟨32776056991391853167514971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21850704660927902111676647 32776056991391853167514971)
  ·
    refine ⟨49164085487087779751272457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32776056991391853167514971 49164085487087779751272457)
    ·
      refine ⟨36873064115315834813454343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49164085487087779751272457 36873064115315834813454343)
      ·
        refine ⟨55309596172973752220181515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36873064115315834813454343 55309596172973752220181515)
        ·
          refine ⟨82964394259460628330272273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55309596172973752220181515 82964394259460628330272273)
          ·
            refine ⟨62223295694595471247704205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82964394259460628330272273 62223295694595471247704205)
            ·
              refine ⟨23333735885473301717889077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62223295694595471247704205 23333735885473301717889077)
              ·
                refine ⟨2187537739263122036052101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23333735885473301717889077 2187537739263122036052101)
                ·
                  refine ⟨410163326111835381759769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2187537739263122036052101 410163326111835381759769)
                  ·
                    rfl

theorem cell20_898639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 5, 4].length) (baseStart_898639 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_898639 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_898639 prefixEnd_898639 := by exact prefixLift 898639
  have htrace : WordTrace (prefixWord ++ tailWord_898639) baseStart_898639 baseEnd_898639 := by
    simpa [prefixWord, tailWord_898639, baseEnd_898639] using wordTrace_append hprefix tailTrace_898639
  have hstable : (prefixWord ++ tailWord_898639).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898639).length < 2 ^ (prefixWord ++ tailWord_898639).sum := by decide
  have hdescent : baseEnd_898639 < baseStart_898639 := by decide
  rcases family_descends (prefixWord ++ tailWord_898639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898642 : List Nat := [3, 2, 2, 1, 2, 4, 1, 5]
def baseStart_898642 : Nat := 118140960795 + 898642 * 2 ^ 59
def prefixEnd_898642 : Nat := 4983230072969 + 3 ^ 40 * 898642 * 2
def baseEnd_898642 : Nat := 136721565131193568219919

theorem tailTrace_898642 : CollatzResearch.WordTrace tailWord_898642 prefixEnd_898642 136721565131193568219919 := by
  unfold tailWord_898642
  simp only [CollatzResearch.WordTrace]
  refine ⟨8194041602595246169968545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21850777606920656453249453 8194041602595246169968545)
  ·
    refine ⟨6145531201946434627476409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8194041602595246169968545 6145531201946434627476409)
    ·
      refine ⟨4609148401459825970607307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6145531201946434627476409 4609148401459825970607307)
      ·
        refine ⟨6913722602189738955910961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4609148401459825970607307 6913722602189738955910961)
        ·
          refine ⟨5185291951642304216933221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6913722602189738955910961 5185291951642304216933221)
          ·
            refine ⟨972242240932932040674979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5185291951642304216933221 972242240932932040674979)
            ·
              refine ⟨1458363361399398061012469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 972242240932932040674979 1458363361399398061012469)
              ·
                refine ⟨136721565131193568219919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1458363361399398061012469 136721565131193568219919)
                ·
                  rfl

theorem cell20_898642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 5].length) (baseStart_898642 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_898642 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_898642 prefixEnd_898642 := by exact prefixLift 898642
  have htrace : WordTrace (prefixWord ++ tailWord_898642) baseStart_898642 baseEnd_898642 := by
    simpa [prefixWord, tailWord_898642, baseEnd_898642] using wordTrace_append hprefix tailTrace_898642
  have hstable : (prefixWord ++ tailWord_898642).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898642).length < 2 ^ (prefixWord ++ tailWord_898642).sum := by decide
  have hdescent : baseEnd_898642 < baseStart_898642 := by decide
  rcases family_descends (prefixWord ++ tailWord_898642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898718 : List Nat := [4, 3, 1, 1, 1, 3, 1, 6]
def baseStart_898718 : Nat := 118140960795 + 898718 * 2 ^ 59
def prefixEnd_898718 : Nat := 4983230072969 + 3 ^ 40 * 898718 * 2
def baseEnd_898718 : Nat := 136733127954820739375371

theorem tailTrace_898718 : CollatzResearch.WordTrace tailWord_898718 prefixEnd_898718 136733127954820739375371 := by
  unfold tailWord_898718
  simp only [CollatzResearch.WordTrace]
  refine ⟨4097367294763206207455101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21852625572070433106427205 4097367294763206207455101)
  ·
    refine ⟨1536512735536202327795663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4097367294763206207455101 1536512735536202327795663)
    ·
      refine ⟨2304769103304303491693495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1536512735536202327795663 2304769103304303491693495)
      ·
        refine ⟨3457153654956455237540243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2304769103304303491693495 3457153654956455237540243)
        ·
          refine ⟨5185730482434682856310365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3457153654956455237540243 5185730482434682856310365)
          ·
            refine ⟨1944648930913006071116387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5185730482434682856310365 1944648930913006071116387)
            ·
              refine ⟨2916973396369509106674581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1944648930913006071116387 2916973396369509106674581)
              ·
                refine ⟨136733127954820739375371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2916973396369509106674581 136733127954820739375371)
                ·
                  rfl

theorem cell20_898718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 6].length) (baseStart_898718 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_898718 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_898718 prefixEnd_898718 := by exact prefixLift 898718
  have htrace : WordTrace (prefixWord ++ tailWord_898718) baseStart_898718 baseEnd_898718 := by
    simpa [prefixWord, tailWord_898718, baseEnd_898718] using wordTrace_append hprefix tailTrace_898718
  have hstable : (prefixWord ++ tailWord_898718).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898718).length < 2 ^ (prefixWord ++ tailWord_898718).sum := by decide
  have hdescent : baseEnd_898718 < baseStart_898718 := by decide
  rcases family_descends (prefixWord ++ tailWord_898718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898742 : List Nat := [5, 1, 3, 1, 1, 1, 2, 1, 5]
def baseStart_898742 : Nat := 118140960795 + 898742 * 2 ^ 59
def prefixEnd_898742 : Nat := 4983230072969 + 3 ^ 40 * 898742 * 2
def baseEnd_898742 : Nat := 410210338118424801326015

theorem tailTrace_898742 : CollatzResearch.WordTrace tailWord_898742 prefixEnd_898742 410210338118424801326015 := by
  unfold tailWord_898742
  simp only [CollatzResearch.WordTrace]
  refine ⟨2048738356876168859907155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21853209140012467839009653 2048738356876168859907155)
  ·
    refine ⟨3073107535314253289860733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2048738356876168859907155 3073107535314253289860733)
    ·
      refine ⟨1152415325742844983697775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3073107535314253289860733 1152415325742844983697775)
      ·
        refine ⟨1728622988614267475546663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1152415325742844983697775 1728622988614267475546663)
        ·
          refine ⟨2592934482921401213319995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1728622988614267475546663 2592934482921401213319995)
          ·
            refine ⟨3889401724382101819979993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2592934482921401213319995 3889401724382101819979993)
            ·
              refine ⟨2917051293286576364984995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3889401724382101819979993 2917051293286576364984995)
              ·
                refine ⟨4375576939929864547477493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2917051293286576364984995 4375576939929864547477493)
                ·
                  refine ⟨410210338118424801326015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4375576939929864547477493 410210338118424801326015)
                  ·
                    rfl

theorem cell20_898742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_898742 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_898742 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_898742 prefixEnd_898742 := by exact prefixLift 898742
  have htrace : WordTrace (prefixWord ++ tailWord_898742) baseStart_898742 baseEnd_898742 := by
    simpa [prefixWord, tailWord_898742, baseEnd_898742] using wordTrace_append hprefix tailTrace_898742
  have hstable : (prefixWord ++ tailWord_898742).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898742).length < 2 ^ (prefixWord ++ tailWord_898742).sum := by decide
  have hdescent : baseEnd_898742 < baseStart_898742 := by decide
  rcases family_descends (prefixWord ++ tailWord_898742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898746 : List Nat := [3, 1, 1, 1, 2, 4, 2, 1, 5]
def baseStart_898746 : Nat := 118140960795 + 898746 * 2 ^ 59
def prefixEnd_898746 : Nat := 4983230072969 + 3 ^ 40 * 898746 * 2
def baseEnd_898746 : Nat := 410212163827418565192665

theorem tailTrace_898746 : CollatzResearch.WordTrace tailWord_898746 prefixEnd_898746 410212163827418565192665 := by
  unfold tailWord_898746
  simp only [CollatzResearch.WordTrace]
  refine ⟨8194989900501052610415023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21853306401336140294440061 8194989900501052610415023)
  ·
    refine ⟨12292484850751578915622535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8194989900501052610415023 12292484850751578915622535)
    ·
      refine ⟨18438727276127368373433803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12292484850751578915622535 18438727276127368373433803)
      ·
        refine ⟨27658090914191052560150705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18438727276127368373433803 27658090914191052560150705)
        ·
          refine ⟨20743568185643289420113029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27658090914191052560150705 20743568185643289420113029)
          ·
            refine ⟨3889419034808116766271193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20743568185643289420113029 3889419034808116766271193)
            ·
              refine ⟨2917064276106087574703395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3889419034808116766271193 2917064276106087574703395)
              ·
                refine ⟨4375596414159131362055093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2917064276106087574703395 4375596414159131362055093)
                ·
                  refine ⟨410212163827418565192665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4375596414159131362055093 410212163827418565192665)
                  ·
                    rfl

theorem cell20_898746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 1, 5].length) (baseStart_898746 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_898746 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_898746 prefixEnd_898746 := by exact prefixLift 898746
  have htrace : WordTrace (prefixWord ++ tailWord_898746) baseStart_898746 baseEnd_898746 := by
    simpa [prefixWord, tailWord_898746, baseEnd_898746] using wordTrace_append hprefix tailTrace_898746
  have hstable : (prefixWord ++ tailWord_898746).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898746).length < 2 ^ (prefixWord ++ tailWord_898746).sum := by decide
  have hdescent : baseEnd_898746 < baseStart_898746 := by decide
  rcases family_descends (prefixWord ++ tailWord_898746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898801 : List Nat := [1, 2, 2, 2, 2, 4, 2, 2, 3]
def baseStart_898801 : Nat := 118140960795 + 898801 * 2 ^ 59
def prefixEnd_898801 : Nat := 4983230072969 + 3 ^ 40 * 898801 * 2
def baseEnd_898801 : Nat := 410237267326082818359107

theorem tailTrace_898801 : CollatzResearch.WordTrace tailWord_898801 prefixEnd_898801 410237267326082818359107 := by
  unfold tailWord_898801
  simp only [CollatzResearch.WordTrace]
  refine ⟨32781965616804954834912257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21854643744536636556608171 32781965616804954834912257)
  ·
    refine ⟨24586474212603716126184193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32781965616804954834912257 24586474212603716126184193)
    ·
      refine ⟨18439855659452787094638145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24586474212603716126184193 18439855659452787094638145)
      ·
        refine ⟨13829891744589590320978609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18439855659452787094638145 13829891744589590320978609)
        ·
          refine ⟨10372418808442192740733957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13829891744589590320978609 10372418808442192740733957)
          ·
            refine ⟨1944828526582911138887617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10372418808442192740733957 1944828526582911138887617)
            ·
              refine ⟨1458621394937183354165713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1944828526582911138887617 1458621394937183354165713)
              ·
                refine ⟨1093966046202887515624285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1458621394937183354165713 1093966046202887515624285)
                ·
                  refine ⟨410237267326082818359107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1093966046202887515624285 410237267326082818359107)
                  ·
                    rfl

theorem cell20_898801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 2, 3].length) (baseStart_898801 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_898801 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_898801 prefixEnd_898801 := by exact prefixLift 898801
  have htrace : WordTrace (prefixWord ++ tailWord_898801) baseStart_898801 baseEnd_898801 := by
    simpa [prefixWord, tailWord_898801, baseEnd_898801] using wordTrace_append hprefix tailTrace_898801
  have hstable : (prefixWord ++ tailWord_898801).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898801).length < 2 ^ (prefixWord ++ tailWord_898801).sum := by decide
  have hdescent : baseEnd_898801 < baseStart_898801 := by decide
  rcases family_descends (prefixWord ++ tailWord_898801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898843 : List Nat := [1, 1, 1, 1, 1, 1, 4, 3, 7]
def baseStart_898843 : Nat := 118140960795 + 898843 * 2 ^ 59
def prefixEnd_898843 : Nat := 4983230072969 + 3 ^ 40 * 898843 * 2
def baseEnd_898843 : Nat := 410256437270517338958935

theorem tailTrace_898843 : CollatzResearch.WordTrace tailWord_898843 prefixEnd_898843 410256437270517338958935 := by
  unfold tailWord_898843
  simp only [CollatzResearch.WordTrace]
  refine ⟨32783497482652796007941183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21855664988435197338627455 32783497482652796007941183)
  ·
    refine ⟨49175246223979194011911775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32783497482652796007941183 49175246223979194011911775)
    ·
      refine ⟨73762869335968791017867663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49175246223979194011911775 73762869335968791017867663)
      ·
        refine ⟨110644304003953186526801495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73762869335968791017867663 110644304003953186526801495)
        ·
          refine ⟨165966456005929779790202243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110644304003953186526801495 165966456005929779790202243)
          ·
            refine ⟨248949684008894669685303365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165966456005929779790202243 248949684008894669685303365)
            ·
              refine ⟨46678065751667750565994381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 248949684008894669685303365 46678065751667750565994381)
              ·
                refine ⟨17504274656875406462247893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46678065751667750565994381 17504274656875406462247893)
                ·
                  refine ⟨410256437270517338958935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17504274656875406462247893 410256437270517338958935)
                  ·
                    rfl

theorem cell20_898843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 7].length) (baseStart_898843 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_898843 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_898843 prefixEnd_898843 := by exact prefixLift 898843
  have htrace : WordTrace (prefixWord ++ tailWord_898843) baseStart_898843 baseEnd_898843 := by
    simpa [prefixWord, tailWord_898843, baseEnd_898843] using wordTrace_append hprefix tailTrace_898843
  have hstable : (prefixWord ++ tailWord_898843).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898843).length < 2 ^ (prefixWord ++ tailWord_898843).sum := by decide
  have hdescent : baseEnd_898843 < baseStart_898843 := by decide
  rcases family_descends (prefixWord ++ tailWord_898843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898856 : List Nat := [2, 1, 5, 1, 1, 4, 1, 2, 3]
def baseStart_898856 : Nat := 118140960795 + 898856 * 2 ^ 59
def prefixEnd_898856 : Nat := 4983230072969 + 3 ^ 40 * 898856 * 2
def baseEnd_898856 : Nat := 410262370824747071525549

theorem tailTrace_898856 : CollatzResearch.WordTrace tailWord_898856 prefixEnd_898856 410262370824747071525549 := by
  unfold tailWord_898856
  simp only [CollatzResearch.WordTrace]
  refine ⟨16391985815802849614082211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21855981087737132818776281 16391985815802849614082211)
  ·
    refine ⟨24587978723704274421123317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16391985815802849614082211 24587978723704274421123317)
    ·
      refine ⟨2305123005347275726980311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24587978723704274421123317 2305123005347275726980311)
      ·
        refine ⟨3457684508020913590470467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2305123005347275726980311 3457684508020913590470467)
        ·
          refine ⟨5186526762031370385705701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3457684508020913590470467 5186526762031370385705701)
          ·
            refine ⟨972473767880881947319819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5186526762031370385705701 972473767880881947319819)
            ·
              refine ⟨1458710651821322920979729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 972473767880881947319819 1458710651821322920979729)
              ·
                refine ⟨1094032988865992190734797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1458710651821322920979729 1094032988865992190734797)
                ·
                  refine ⟨410262370824747071525549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1094032988865992190734797 410262370824747071525549)
                  ·
                    rfl

theorem cell20_898856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 2, 3].length) (baseStart_898856 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_898856 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_898856 prefixEnd_898856 := by exact prefixLift 898856
  have htrace : WordTrace (prefixWord ++ tailWord_898856) baseStart_898856 baseEnd_898856 := by
    simpa [prefixWord, tailWord_898856, baseEnd_898856] using wordTrace_append hprefix tailTrace_898856
  have hstable : (prefixWord ++ tailWord_898856).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898856).length < 2 ^ (prefixWord ++ tailWord_898856).sum := by decide
  have hdescent : baseEnd_898856 < baseStart_898856 := by decide
  rcases family_descends (prefixWord ++ tailWord_898856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898860 : List Nat := [2, 2, 1, 1, 1, 6, 1, 1, 5]
def baseStart_898860 : Nat := 118140960795 + 898860 * 2 ^ 59
def prefixEnd_898860 : Nat := 4983230072969 + 3 ^ 40 * 898860 * 2
def baseEnd_898860 : Nat := 410264196533740835392199

theorem tailTrace_898860 : CollatzResearch.WordTrace tailWord_898860 prefixEnd_898860 410264196533740835392199 := by
  unfold tailWord_898860
  simp only [CollatzResearch.WordTrace]
  refine ⟨16392058761795603955655017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21856078349060805274206689 16392058761795603955655017)
  ·
    refine ⟨12294044071346702966741263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16392058761795603955655017 12294044071346702966741263)
    ·
      refine ⟨18441066107020054450111895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12294044071346702966741263 18441066107020054450111895)
      ·
        refine ⟨27661599160530081675167843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18441066107020054450111895 27661599160530081675167843)
        ·
          refine ⟨41492398740795122512751765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27661599160530081675167843 41492398740795122512751765)
          ·
            refine ⟨1944956190974771367785239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 41492398740795122512751765 1944956190974771367785239)
            ·
              refine ⟨2917434286462157051677859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1944956190974771367785239 2917434286462157051677859)
              ·
                refine ⟨4376151429693235577516789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2917434286462157051677859 4376151429693235577516789)
                ·
                  refine ⟨410264196533740835392199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4376151429693235577516789 410264196533740835392199)
                  ·
                    rfl

theorem cell20_898860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 5].length) (baseStart_898860 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_898860 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_898860 prefixEnd_898860 := by exact prefixLift 898860
  have htrace : WordTrace (prefixWord ++ tailWord_898860) baseStart_898860 baseEnd_898860 := by
    simpa [prefixWord, tailWord_898860, baseEnd_898860] using wordTrace_append hprefix tailTrace_898860
  have hstable : (prefixWord ++ tailWord_898860).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898860).length < 2 ^ (prefixWord ++ tailWord_898860).sum := by decide
  have hdescent : baseEnd_898860 < baseStart_898860 := by decide
  rcases family_descends (prefixWord ++ tailWord_898860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898873 : List Nat := [1, 2, 1, 7, 1, 1, 3, 1, 3]
def baseStart_898873 : Nat := 118140960795 + 898873 * 2 ^ 59
def prefixEnd_898873 : Nat := 4983230072969 + 3 ^ 40 * 898873 * 2
def baseEnd_898873 : Nat := 410270130087970567958813

theorem tailTrace_898873 : CollatzResearch.WordTrace tailWord_898873 prefixEnd_898873 410270130087970567958813 := by
  unfold tailWord_898873
  simp only [CollatzResearch.WordTrace]
  refine ⟨32784591672544111131533273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21856394448362740754355515 32784591672544111131533273)
  ·
    refine ⟨24588443754408083348649955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32784591672544111131533273 24588443754408083348649955)
    ·
      refine ⟨36882665631612125022974933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24588443754408083348649955 36882665631612125022974933)
      ·
        refine ⟨864437475740909180225975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 36882665631612125022974933 864437475740909180225975)
        ·
          refine ⟨1296656213611363770338963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 864437475740909180225975 1296656213611363770338963)
          ·
            refine ⟨1944984320417045655508445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1296656213611363770338963 1944984320417045655508445)
            ·
              refine ⟨729369120156392120815667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1944984320417045655508445 729369120156392120815667)
              ·
                refine ⟨1094053680234588181223501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 729369120156392120815667 1094053680234588181223501)
                ·
                  refine ⟨410270130087970567958813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1094053680234588181223501 410270130087970567958813)
                  ·
                    rfl

theorem cell20_898873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 3, 1, 3].length) (baseStart_898873 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_898873 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_898873 prefixEnd_898873 := by exact prefixLift 898873
  have htrace : WordTrace (prefixWord ++ tailWord_898873) baseStart_898873 baseEnd_898873 := by
    simpa [prefixWord, tailWord_898873, baseEnd_898873] using wordTrace_append hprefix tailTrace_898873
  have hstable : (prefixWord ++ tailWord_898873).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898873).length < 2 ^ (prefixWord ++ tailWord_898873).sum := by decide
  have hdescent : baseEnd_898873 < baseStart_898873 := by decide
  rcases family_descends (prefixWord ++ tailWord_898873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898898 : List Nat := [3, 2, 2, 1, 1, 3, 1, 2, 5]
def baseStart_898898 : Nat := 118140960795 + 898898 * 2 ^ 59
def prefixEnd_898898 : Nat := 4983230072969 + 3 ^ 40 * 898898 * 2
def baseEnd_898898 : Nat := 410281540769181592125377

theorem tailTrace_898898 : CollatzResearch.WordTrace tailWord_898898 prefixEnd_898898 410281540769181592125377 := by
  unfold tailWord_898898
  simp only [CollatzResearch.WordTrace]
  refine ⟨8196375874363385100298337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21857002331635693600795565 8196375874363385100298337)
  ·
    refine ⟨6147281905772538825223753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8196375874363385100298337 6147281905772538825223753)
    ·
      refine ⟨4610461429329404118917815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6147281905772538825223753 4610461429329404118917815)
      ·
        refine ⟨6915692143994106178376723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4610461429329404118917815 6915692143994106178376723)
        ·
          refine ⟨10373538215991159267565085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6915692143994106178376723 10373538215991159267565085)
          ·
            refine ⟨3890076830996684725336907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10373538215991159267565085 3890076830996684725336907)
            ·
              refine ⟨5835115246495027088005361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3890076830996684725336907 5835115246495027088005361)
              ·
                refine ⟨4376336434871270316004021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5835115246495027088005361 4376336434871270316004021)
                ·
                  refine ⟨410281540769181592125377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4376336434871270316004021 410281540769181592125377)
                  ·
                    rfl

theorem cell20_898898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_898898 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_898898 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_898898 prefixEnd_898898 := by exact prefixLift 898898
  have htrace : WordTrace (prefixWord ++ tailWord_898898) baseStart_898898 baseEnd_898898 := by
    simpa [prefixWord, tailWord_898898, baseEnd_898898] using wordTrace_append hprefix tailTrace_898898
  have hstable : (prefixWord ++ tailWord_898898).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898898).length < 2 ^ (prefixWord ++ tailWord_898898).sum := by decide
  have hdescent : baseEnd_898898 < baseStart_898898 := by decide
  rcases family_descends (prefixWord ++ tailWord_898898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898901 : List Nat := [1, 3, 2, 2, 2, 2, 3, 3, 2]
def baseStart_898901 : Nat := 118140960795 + 898901 * 2 ^ 59
def prefixEnd_898901 : Nat := 4983230072969 + 3 ^ 40 * 898901 * 2
def baseEnd_898901 : Nat := 410282910050926915025365

theorem tailTrace_898901 : CollatzResearch.WordTrace tailWord_898901 prefixEnd_898901 410282910050926915025365 := by
  unfold tailWord_898901
  simp only [CollatzResearch.WordTrace]
  refine ⟨32785612916442671913552557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21857075277628447942368371 32785612916442671913552557)
  ·
    refine ⟨12294604843666001967582209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32785612916442671913552557 12294604843666001967582209)
    ·
      refine ⟨9220953632749501475686657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12294604843666001967582209 9220953632749501475686657)
      ·
        refine ⟨6915715224562126106764993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9220953632749501475686657 6915715224562126106764993)
        ·
          refine ⟨5186786418421594580073745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6915715224562126106764993 5186786418421594580073745)
          ·
            refine ⟨3890089813816195935055309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5186786418421594580073745 3890089813816195935055309)
            ·
              refine ⟨1458783680181073475645741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3890089813816195935055309 1458783680181073475645741)
              ·
                refine ⟨547043880067902553367153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1458783680181073475645741 547043880067902553367153)
                ·
                  refine ⟨410282910050926915025365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 547043880067902553367153 410282910050926915025365)
                  ·
                    rfl

theorem cell20_898901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 3, 2].length) (baseStart_898901 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_898901 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_898901 prefixEnd_898901 := by exact prefixLift 898901
  have htrace : WordTrace (prefixWord ++ tailWord_898901) baseStart_898901 baseEnd_898901 := by
    simpa [prefixWord, tailWord_898901, baseEnd_898901] using wordTrace_append hprefix tailTrace_898901
  have hstable : (prefixWord ++ tailWord_898901).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898901).length < 2 ^ (prefixWord ++ tailWord_898901).sum := by decide
  have hdescent : baseEnd_898901 < baseStart_898901 := by decide
  rcases family_descends (prefixWord ++ tailWord_898901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898908 : List Nat := [2, 2, 4, 2, 2, 2, 6]
def baseStart_898908 : Nat := 118140960795 + 898908 * 2 ^ 59
def prefixEnd_898908 : Nat := 4983230072969 + 3 ^ 40 * 898908 * 2
def baseEnd_898908 : Nat := 45587345004629555754667

theorem tailTrace_898908 : CollatzResearch.WordTrace tailWord_898908 prefixEnd_898908 45587345004629555754667 := by
  unfold tailWord_898908
  simp only [CollatzResearch.WordTrace]
  refine ⟨16392934113708656054528689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21857245484944874739371585 16392934113708656054528689)
  ·
    refine ⟨12294700585281492040896517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16392934113708656054528689 12294700585281492040896517)
    ·
      refine ⟨2305256359740279757668097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12294700585281492040896517 2305256359740279757668097)
      ·
        refine ⟨1728942269805209818251073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2305256359740279757668097 1728942269805209818251073)
        ·
          refine ⟨1296706702353907363688305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1728942269805209818251073 1296706702353907363688305)
          ·
            refine ⟨972530026765430522766229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1296706702353907363688305 972530026765430522766229)
            ·
              refine ⟨45587345004629555754667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 972530026765430522766229 45587345004629555754667)
              ·
                rfl

theorem cell20_898908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 6].length) (baseStart_898908 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_898908 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_898908 prefixEnd_898908 := by exact prefixLift 898908
  have htrace : WordTrace (prefixWord ++ tailWord_898908) baseStart_898908 baseEnd_898908 := by
    simpa [prefixWord, tailWord_898908, baseEnd_898908] using wordTrace_append hprefix tailTrace_898908
  have hstable : (prefixWord ++ tailWord_898908).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898908).length < 2 ^ (prefixWord ++ tailWord_898908).sum := by decide
  have hdescent : baseEnd_898908 < baseStart_898908 := by decide
  rcases family_descends (prefixWord ++ tailWord_898908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898912 : List Nat := [2, 1, 1, 3, 3, 2, 8]
def baseStart_898912 : Nat := 118140960795 + 898912 * 2 ^ 59
def prefixEnd_898912 : Nat := 4983230072969 + 3 ^ 40 * 898912 * 2
def baseEnd_898912 : Nat := 45587547861184418406517

theorem tailTrace_898912 : CollatzResearch.WordTrace tailWord_898912 prefixEnd_898912 45587547861184418406517 := by
  unfold tailWord_898912
  simp only [CollatzResearch.WordTrace]
  refine ⟨16393007059701410396101495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21857342746268547194801993 16393007059701410396101495)
  ·
    refine ⟨24589510589552115594152243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16393007059701410396101495 24589510589552115594152243)
    ·
      refine ⟨36884265884328173391228365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24589510589552115594152243 36884265884328173391228365)
      ·
        refine ⟨13831599706623065021710637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36884265884328173391228365 13831599706623065021710637)
        ·
          refine ⟨5186849889983649383141489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13831599706623065021710637 5186849889983649383141489)
          ·
            refine ⟨3890137417487737037356117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5186849889983649383141489 3890137417487737037356117)
            ·
              refine ⟨45587547861184418406517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3890137417487737037356117 45587547861184418406517)
              ·
                rfl

theorem cell20_898912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 8].length) (baseStart_898912 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_898912 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_898912 prefixEnd_898912 := by exact prefixLift 898912
  have htrace : WordTrace (prefixWord ++ tailWord_898912) baseStart_898912 baseEnd_898912 := by
    simpa [prefixWord, tailWord_898912, baseEnd_898912] using wordTrace_append hprefix tailTrace_898912
  have hstable : (prefixWord ++ tailWord_898912).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898912).length < 2 ^ (prefixWord ++ tailWord_898912).sum := by decide
  have hdescent : baseEnd_898912 < baseStart_898912 := by decide
  rcases family_descends (prefixWord ++ tailWord_898912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898966 : List Nat := [5, 3, 1, 1, 2, 1, 2, 2, 3]
def baseStart_898966 : Nat := 118140960795 + 898966 * 2 ^ 59
def prefixEnd_898966 : Nat := 4983230072969 + 3 ^ 40 * 898966 * 2
def baseEnd_898966 : Nat := 410312577822075577858433

theorem tailTrace_898966 : CollatzResearch.WordTrace tailWord_898966 prefixEnd_898966 410312577822075577858433 := by
  unfold tailWord_898966
  simp only [CollatzResearch.WordTrace]
  refine ⟨2049248978825449250916797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21858655774138125343112501 2049248978825449250916797)
  ·
    refine ⟨768468367059543469093799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2049248978825449250916797 768468367059543469093799)
    ·
      refine ⟨1152702550589315203640699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 768468367059543469093799 1152702550589315203640699)
      ·
        refine ⟨1729053825883972805461049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1152702550589315203640699 1729053825883972805461049)
        ·
          refine ⟨1296790369412979604095787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1729053825883972805461049 1296790369412979604095787)
          ·
            refine ⟨1945185554119469406143681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1296790369412979604095787 1945185554119469406143681)
            ·
              refine ⟨1458889165589602054607761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1945185554119469406143681 1458889165589602054607761)
              ·
                refine ⟨1094166874192201540955821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1458889165589602054607761 1094166874192201540955821)
                ·
                  refine ⟨410312577822075577858433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1094166874192201540955821 410312577822075577858433)
                  ·
                    rfl

theorem cell20_898966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_898966 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_898966 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_898966 prefixEnd_898966 := by exact prefixLift 898966
  have htrace : WordTrace (prefixWord ++ tailWord_898966) baseStart_898966 baseEnd_898966 := by
    simpa [prefixWord, tailWord_898966, baseEnd_898966] using wordTrace_append hprefix tailTrace_898966
  have hstable : (prefixWord ++ tailWord_898966).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898966).length < 2 ^ (prefixWord ++ tailWord_898966).sum := by decide
  have hdescent : baseEnd_898966 < baseStart_898966 := by decide
  rcases family_descends (prefixWord ++ tailWord_898966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899029 : List Nat := [1, 3, 2, 3, 2, 1, 3, 2, 3]
def baseStart_899029 : Nat := 118140960795 + 899029 * 2 ^ 59
def prefixEnd_899029 : Nat := 4983230072969 + 3 ^ 40 * 899029 * 2
def baseEnd_899029 : Nat := 410341332738727358758175

theorem tailTrace_899029 : CollatzResearch.WordTrace tailWord_899029 prefixEnd_899029 410341332738727358758175 := by
  unfold tailWord_899029
  simp only [CollatzResearch.WordTrace]
  refine ⟨32790281459978949774212141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21860187639985966516141427 32790281459978949774212141)
  ·
    refine ⟨12296355547492106165329553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32790281459978949774212141 12296355547492106165329553)
    ·
      refine ⟨9222266660619079623997165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12296355547492106165329553 9222266660619079623997165)
      ·
        refine ⟨3458349997732154858998937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9222266660619079623997165 3458349997732154858998937)
        ·
          refine ⟨2593762498299116144249203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3458349997732154858998937 2593762498299116144249203)
          ·
            refine ⟨3890643747448674216373805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2593762498299116144249203 3890643747448674216373805)
            ·
              refine ⟨1458991405293252831140177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3890643747448674216373805 1458991405293252831140177)
              ·
                refine ⟨1094243553969939623355133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1458991405293252831140177 1094243553969939623355133)
                ·
                  refine ⟨410341332738727358758175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1094243553969939623355133 410341332738727358758175)
                  ·
                    rfl

theorem cell20_899029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 2, 3].length) (baseStart_899029 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_899029 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_899029 prefixEnd_899029 := by exact prefixLift 899029
  have htrace : WordTrace (prefixWord ++ tailWord_899029) baseStart_899029 baseEnd_899029 := by
    simpa [prefixWord, tailWord_899029, baseEnd_899029] using wordTrace_append hprefix tailTrace_899029
  have hstable : (prefixWord ++ tailWord_899029).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899029).length < 2 ^ (prefixWord ++ tailWord_899029).sum := by decide
  have hdescent : baseEnd_899029 < baseStart_899029 := by decide
  rcases family_descends (prefixWord ++ tailWord_899029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899070 : List Nat := [4, 2, 2, 2, 1, 1, 3, 3, 2]
def baseStart_899070 : Nat := 118140960795 + 899070 * 2 ^ 59
def prefixEnd_899070 : Nat := 4983230072969 + 3 ^ 40 * 899070 * 2
def baseEnd_899070 : Nat := 410360046255913438391341

theorem tailTrace_899070 : CollatzResearch.WordTrace tailWord_899070 prefixEnd_899070 410360046255913438391341 := by
  unfold tailWord_899070
  simp only [CollatzResearch.WordTrace]
  refine ⟨4098972106603801722056833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21861184568553609184303109 4098972106603801722056833)
  ·
    refine ⟨3074229079952851291542625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4098972106603801722056833 3074229079952851291542625)
    ·
      refine ⟨2305671809964638468656969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3074229079952851291542625 2305671809964638468656969)
      ·
        refine ⟨1729253857473478851492727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2305671809964638468656969 1729253857473478851492727)
        ·
          refine ⟨2593880786210218277239091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1729253857473478851492727 2593880786210218277239091)
          ·
            refine ⟨3890821179315327415858637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2593880786210218277239091 3890821179315327415858637)
            ·
              refine ⟨1459057942243247780946989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3890821179315327415858637 1459057942243247780946989)
              ·
                refine ⟨547146728341217917855121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1459057942243247780946989 547146728341217917855121)
                ·
                  refine ⟨410360046255913438391341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 547146728341217917855121 410360046255913438391341)
                  ·
                    rfl

theorem cell20_899070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 3, 2].length) (baseStart_899070 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_899070 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_899070 prefixEnd_899070 := by exact prefixLift 899070
  have htrace : WordTrace (prefixWord ++ tailWord_899070) baseStart_899070 baseEnd_899070 := by
    simpa [prefixWord, tailWord_899070, baseEnd_899070] using wordTrace_append hprefix tailTrace_899070
  have hstable : (prefixWord ++ tailWord_899070).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899070).length < 2 ^ (prefixWord ++ tailWord_899070).sum := by decide
  have hdescent : baseEnd_899070 < baseStart_899070 := by decide
  rcases family_descends (prefixWord ++ tailWord_899070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899105 : List Nat := [1, 2, 3, 2, 4, 1, 1, 3, 3]
def baseStart_899105 : Nat := 118140960795 + 899105 * 2 ^ 59
def prefixEnd_899105 : Nat := 4983230072969 + 3 ^ 40 * 899105 * 2
def baseEnd_899105 : Nat := 410376021209608872224531

theorem tailTrace_899105 : CollatzResearch.WordTrace tailWord_899105 prefixEnd_899105 410376021209608872224531 := by
  unfold tailWord_899105
  simp only [CollatzResearch.WordTrace]
  refine ⟨32793053407703614753978769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21862035605135743169319179 32793053407703614753978769)
  ·
    refine ⟨24594790055777711065484077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32793053407703614753978769 24594790055777711065484077)
    ·
      refine ⟨9223046270916641649556529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24594790055777711065484077 9223046270916641649556529)
      ·
        refine ⟨6917284703187481237167397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9223046270916641649556529 6917284703187481237167397)
        ·
          refine ⟨1296990881847652731968887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6917284703187481237167397 1296990881847652731968887)
          ·
            refine ⟨1945486322771479097953331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1296990881847652731968887 1945486322771479097953331)
            ·
              refine ⟨2918229484157218646929997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1945486322771479097953331 2918229484157218646929997)
              ·
                refine ⟨1094336056558956992598749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2918229484157218646929997 1094336056558956992598749)
                ·
                  refine ⟨410376021209608872224531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1094336056558956992598749 410376021209608872224531)
                  ·
                    rfl

theorem cell20_899105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 3, 3].length) (baseStart_899105 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_899105 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_899105 prefixEnd_899105 := by exact prefixLift 899105
  have htrace : WordTrace (prefixWord ++ tailWord_899105) baseStart_899105 baseEnd_899105 := by
    simpa [prefixWord, tailWord_899105, baseEnd_899105] using wordTrace_append hprefix tailTrace_899105
  have hstable : (prefixWord ++ tailWord_899105).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899105).length < 2 ^ (prefixWord ++ tailWord_899105).sum := by decide
  have hdescent : baseEnd_899105 < baseStart_899105 := by decide
  rcases family_descends (prefixWord ++ tailWord_899105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899157 : List Nat := [1, 3, 2, 2, 1, 5, 1, 5]
def baseStart_899157 : Nat := 118140960795 + 899157 * 2 ^ 59
def prefixEnd_899157 : Nat := 4983230072969 + 3 ^ 40 * 899157 * 2
def baseEnd_899157 : Nat := 136799918475509267496995

theorem tailTrace_899157 : CollatzResearch.WordTrace tailWord_899157 prefixEnd_899157 136799918475509267496995 := by
  unfold tailWord_899157
  simp only [CollatzResearch.WordTrace]
  refine ⟨32794950003515227634871725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21863300002343485089914483 32794950003515227634871725)
  ·
    refine ⟨12298106251318210363076897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32794950003515227634871725 12298106251318210363076897)
    ·
      refine ⟨9223579688488657772307673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12298106251318210363076897 9223579688488657772307673)
      ·
        refine ⟨6917684766366493329230755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9223579688488657772307673 6917684766366493329230755)
        ·
          refine ⟨10376527149549739993846133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6917684766366493329230755 10376527149549739993846133)
          ·
            refine ⟨972799420270288124423075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10376527149549739993846133 972799420270288124423075)
            ·
              refine ⟨1459199130405432186634613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 972799420270288124423075 1459199130405432186634613)
              ·
                refine ⟨136799918475509267496995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1459199130405432186634613 136799918475509267496995)
                ·
                  rfl

theorem cell20_899157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 5].length) (baseStart_899157 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_899157 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_899157 prefixEnd_899157 := by exact prefixLift 899157
  have htrace : WordTrace (prefixWord ++ tailWord_899157) baseStart_899157 baseEnd_899157 := by
    simpa [prefixWord, tailWord_899157, baseEnd_899157] using wordTrace_append hprefix tailTrace_899157
  have hstable : (prefixWord ++ tailWord_899157).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899157).length < 2 ^ (prefixWord ++ tailWord_899157).sum := by decide
  have hdescent : baseEnd_899157 < baseStart_899157 := by decide
  rcases family_descends (prefixWord ++ tailWord_899157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899185 : List Nat := [1, 2, 2, 2, 1, 1, 4, 2, 5]
def baseStart_899185 : Nat := 118140960795 + 899185 * 2 ^ 59
def prefixEnd_899185 : Nat := 4983230072969 + 3 ^ 40 * 899185 * 2
def baseEnd_899185 : Nat := 410412535389484149557537

theorem tailTrace_899185 : CollatzResearch.WordTrace tailWord_899185 prefixEnd_899185 410412535389484149557537 := by
  unfold tailWord_899185
  simp only [CollatzResearch.WordTrace]
  refine ⟨32795971247413788416891009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21863980831609192277927339 32795971247413788416891009)
  ·
    refine ⟨24596978435560341312668257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32795971247413788416891009 24596978435560341312668257)
    ·
      refine ⟨18447733826670255984501193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24596978435560341312668257 18447733826670255984501193)
      ·
        refine ⟨13835800370002691988375895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18447733826670255984501193 13835800370002691988375895)
        ·
          refine ⟨20753700555004037982563843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13835800370002691988375895 20753700555004037982563843)
          ·
            refine ⟨31130550832506056973845765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20753700555004037982563843 31130550832506056973845765)
            ·
              refine ⟨5836978281094885682596081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31130550832506056973845765 5836978281094885682596081)
              ·
                refine ⟨4377733710821164261947061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5836978281094885682596081 4377733710821164261947061)
                ·
                  refine ⟨410412535389484149557537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4377733710821164261947061 410412535389484149557537)
                  ·
                    rfl

theorem cell20_899185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 2, 5].length) (baseStart_899185 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_899185 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_899185 prefixEnd_899185 := by exact prefixLift 899185
  have htrace : WordTrace (prefixWord ++ tailWord_899185) baseStart_899185 baseEnd_899185 := by
    simpa [prefixWord, tailWord_899185, baseEnd_899185] using wordTrace_append hprefix tailTrace_899185
  have hstable : (prefixWord ++ tailWord_899185).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899185).length < 2 ^ (prefixWord ++ tailWord_899185).sum := by decide
  have hdescent : baseEnd_899185 < baseStart_899185 := by decide
  rcases family_descends (prefixWord ++ tailWord_899185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899192 : List Nat := [2, 1, 2, 1, 1, 1, 3, 1, 8]
def baseStart_899192 : Nat := 118140960795 + 899192 * 2 ^ 59
def prefixEnd_899192 : Nat := 4983230072969 + 3 ^ 40 * 899192 * 2
def baseEnd_899192 : Nat := 410415730380223236324175

theorem tailTrace_899192 : CollatzResearch.WordTrace tailWord_899192 prefixEnd_899192 410415730380223236324175 := by
  unfold tailWord_899192
  simp only [CollatzResearch.WordTrace]
  refine ⟨16398113279194214306197915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21864151038925619074930553 16398113279194214306197915)
  ·
    refine ⟨24597169918791321459296873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16398113279194214306197915 24597169918791321459296873)
    ·
      refine ⟨18447877439093491094472655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24597169918791321459296873 18447877439093491094472655)
      ·
        refine ⟨27671816158640236641708983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18447877439093491094472655 27671816158640236641708983)
        ·
          refine ⟨41507724237960354962563475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27671816158640236641708983 41507724237960354962563475)
          ·
            refine ⟨62261586356940532443845213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41507724237960354962563475 62261586356940532443845213)
            ·
              refine ⟨23348094883852699666441955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62261586356940532443845213 23348094883852699666441955)
              ·
                refine ⟨35022142325779049499662933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23348094883852699666441955 35022142325779049499662933)
                ·
                  refine ⟨410415730380223236324175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35022142325779049499662933 410415730380223236324175)
                  ·
                    rfl

theorem cell20_899192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 8].length) (baseStart_899192 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_899192 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_899192 prefixEnd_899192 := by exact prefixLift 899192
  have htrace : WordTrace (prefixWord ++ tailWord_899192) baseStart_899192 baseEnd_899192 := by
    simpa [prefixWord, tailWord_899192, baseEnd_899192] using wordTrace_append hprefix tailTrace_899192
  have hstable : (prefixWord ++ tailWord_899192).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899192).length < 2 ^ (prefixWord ++ tailWord_899192).sum := by decide
  have hdescent : baseEnd_899192 < baseStart_899192 := by decide
  rcases family_descends (prefixWord ++ tailWord_899192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899209 : List Nat := [1, 2, 1, 1, 4, 2, 4, 1, 4]
def baseStart_899209 : Nat := 118140960795 + 899209 * 2 ^ 59
def prefixEnd_899209 : Nat := 4983230072969 + 3 ^ 40 * 899209 * 2
def baseEnd_899209 : Nat := 410423489643446732757439

theorem tailTrace_899209 : CollatzResearch.WordTrace tailWord_899209 prefixEnd_899209 410423489643446732757439 := by
  unfold tailWord_899209
  simp only [CollatzResearch.WordTrace]
  refine ⟨32796846599326840515764681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21864564399551227010509787 32796846599326840515764681)
  ·
    refine ⟨24597634949495130386823511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32796846599326840515764681 24597634949495130386823511)
    ·
      refine ⟨36896452424242695580235267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24597634949495130386823511 36896452424242695580235267)
      ·
        refine ⟨55344678636364043370352901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36896452424242695580235267 55344678636364043370352901)
        ·
          refine ⟨10377127244318258131941169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55344678636364043370352901 10377127244318258131941169)
          ·
            refine ⟨7782845433238693598955877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10377127244318258131941169 7782845433238693598955877)
            ·
              refine ⟨1459283518732255049804227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7782845433238693598955877 1459283518732255049804227)
              ·
                refine ⟨2188925278098382574706341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1459283518732255049804227 2188925278098382574706341)
                ·
                  refine ⟨410423489643446732757439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2188925278098382574706341 410423489643446732757439)
                  ·
                    rfl

theorem cell20_899209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 1, 4].length) (baseStart_899209 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_899209 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_899209 prefixEnd_899209 := by exact prefixLift 899209
  have htrace : WordTrace (prefixWord ++ tailWord_899209) baseStart_899209 baseEnd_899209 := by
    simpa [prefixWord, tailWord_899209, baseEnd_899209] using wordTrace_append hprefix tailTrace_899209
  have hstable : (prefixWord ++ tailWord_899209).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899209).length < 2 ^ (prefixWord ++ tailWord_899209).sum := by decide
  have hdescent : baseEnd_899209 < baseStart_899209 := by decide
  rcases family_descends (prefixWord ++ tailWord_899209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899233 : List Nat := [1, 2, 3, 3, 1, 2, 4, 4]
def baseStart_899233 : Nat := 118140960795 + 899233 * 2 ^ 59
def prefixEnd_899233 : Nat := 4983230072969 + 3 ^ 40 * 899233 * 2
def baseEnd_899233 : Nat := 136811481299136438652447

theorem tailTrace_899233 : CollatzResearch.WordTrace tailWord_899233 prefixEnd_899233 136811481299136438652447 := by
  unfold tailWord_899233
  simp only [CollatzResearch.WordTrace]
  refine ⟨32797721951239892614638353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21865147967493261743092235 32797721951239892614638353)
  ·
    refine ⟨24598291463429919460978765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32797721951239892614638353 24598291463429919460978765)
    ·
      refine ⟨9224359298786219797867037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24598291463429919460978765 9224359298786219797867037)
      ·
        refine ⟨3459134737044832424200139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9224359298786219797867037 3459134737044832424200139)
        ·
          refine ⟨5188702105567248636300209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3459134737044832424200139 5188702105567248636300209)
          ·
            refine ⟨3891526579175436477225157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5188702105567248636300209 3891526579175436477225157)
            ·
              refine ⟨729661233595394339479717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3891526579175436477225157 729661233595394339479717)
              ·
                refine ⟨136811481299136438652447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 729661233595394339479717 136811481299136438652447)
                ·
                  rfl

theorem cell20_899233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 4, 4].length) (baseStart_899233 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_899233 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_899233 prefixEnd_899233 := by exact prefixLift 899233
  have htrace : WordTrace (prefixWord ++ tailWord_899233) baseStart_899233 baseEnd_899233 := by
    simpa [prefixWord, tailWord_899233, baseEnd_899233] using wordTrace_append hprefix tailTrace_899233
  have hstable : (prefixWord ++ tailWord_899233).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899233).length < 2 ^ (prefixWord ++ tailWord_899233).sum := by decide
  have hdescent : baseEnd_899233 < baseStart_899233 := by decide
  rcases family_descends (prefixWord ++ tailWord_899233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899239 : List Nat := [1, 1, 6, 2, 3, 1, 1, 3, 2]
def baseStart_899239 : Nat := 118140960795 + 899239 * 2 ^ 59
def prefixEnd_899239 : Nat := 4983230072969 + 3 ^ 40 * 899239 * 2
def baseEnd_899239 : Nat := 410437182460899961757317

theorem tailTrace_899239 : CollatzResearch.WordTrace tailWord_899239 prefixEnd_899239 410437182460899961757317 := by
  unfold tailWord_899239
  simp only [CollatzResearch.WordTrace]
  refine ⟨32797940789218155639356771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21865293859478770426237847 32797940789218155639356771)
  ·
    refine ⟨49196911183827233459035157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32797940789218155639356771 49196911183827233459035157)
    ·
      refine ⟨2306105211741901568392273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 49196911183827233459035157 2306105211741901568392273)
      ·
        refine ⟨1729578908806426176294205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2306105211741901568392273 1729578908806426176294205)
        ·
          refine ⟨648592090802409816110327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1729578908806426176294205 648592090802409816110327)
          ·
            refine ⟨972888136203614724165491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 648592090802409816110327 972888136203614724165491)
            ·
              refine ⟨1459332204305422086248237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 972888136203614724165491 1459332204305422086248237)
              ·
                refine ⟨547249576614533282343089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1459332204305422086248237 547249576614533282343089)
                ·
                  refine ⟨410437182460899961757317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 547249576614533282343089 410437182460899961757317)
                  ·
                    rfl

theorem cell20_899239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 3, 2].length) (baseStart_899239 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_899239 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_899239 prefixEnd_899239 := by exact prefixLift 899239
  have htrace : WordTrace (prefixWord ++ tailWord_899239) baseStart_899239 baseEnd_899239 := by
    simpa [prefixWord, tailWord_899239, baseEnd_899239] using wordTrace_append hprefix tailTrace_899239
  have hstable : (prefixWord ++ tailWord_899239).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899239).length < 2 ^ (prefixWord ++ tailWord_899239).sum := by decide
  have hdescent : baseEnd_899239 < baseStart_899239 := by decide
  rcases family_descends (prefixWord ++ tailWord_899239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899260 : List Nat := [2, 2, 2, 3, 3, 1, 3, 2, 2]
def baseStart_899260 : Nat := 118140960795 + 899260 * 2 ^ 59
def prefixEnd_899260 : Nat := 4983230072969 + 3 ^ 40 * 899260 * 2
def baseEnd_899260 : Nat := 410446767433117222057231

theorem tailTrace_899260 : CollatzResearch.WordTrace tailWord_899260 prefixEnd_899260 410446767433117222057231 := by
  unfold tailWord_899260
  simp only [CollatzResearch.WordTrace]
  refine ⟨16399353361071038112935617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21865804481428050817247489 16399353361071038112935617)
  ·
    refine ⟨12299515020803278584701713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16399353361071038112935617 12299515020803278584701713)
    ·
      refine ⟨9224636265602458938526285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12299515020803278584701713 9224636265602458938526285)
      ·
        refine ⟨3459238599600922101947357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9224636265602458938526285 3459238599600922101947357)
        ·
          refine ⟨1297214474850345788230259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3459238599600922101947357 1297214474850345788230259)
          ·
            refine ⟨1945821712275518682345389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1297214474850345788230259 1945821712275518682345389)
            ·
              refine ⟨729683142103319505879521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1945821712275518682345389 729683142103319505879521)
              ·
                refine ⟨547262356577489629409641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 729683142103319505879521 547262356577489629409641)
                ·
                  refine ⟨410446767433117222057231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 547262356577489629409641 410446767433117222057231)
                  ·
                    rfl

theorem cell20_899260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 3, 2, 2].length) (baseStart_899260 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_899260 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_899260 prefixEnd_899260 := by exact prefixLift 899260
  have htrace : WordTrace (prefixWord ++ tailWord_899260) baseStart_899260 baseEnd_899260 := by
    simpa [prefixWord, tailWord_899260, baseEnd_899260] using wordTrace_append hprefix tailTrace_899260
  have hstable : (prefixWord ++ tailWord_899260).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899260).length < 2 ^ (prefixWord ++ tailWord_899260).sum := by decide
  have hdescent : baseEnd_899260 < baseStart_899260 := by decide
  rcases family_descends (prefixWord ++ tailWord_899260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899264 : List Nat := [2, 1, 1, 2, 5, 3, 1, 1, 4]
def baseStart_899264 : Nat := 118140960795 + 899264 * 2 ^ 59
def prefixEnd_899264 : Nat := 4983230072969 + 3 ^ 40 * 899264 * 2
def baseEnd_899264 : Nat := 410448593142110985923881

theorem tailTrace_899264 : CollatzResearch.WordTrace tailWord_899264 prefixEnd_899264 410448593142110985923881 := by
  unfold tailWord_899264
  simp only [CollatzResearch.WordTrace]
  refine ⟨16399426307063792454508423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21865901742751723272677897 16399426307063792454508423)
  ·
    refine ⟨24599139460595688681762635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16399426307063792454508423 24599139460595688681762635)
    ·
      refine ⟨36898709190893533022643953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24599139460595688681762635 36898709190893533022643953)
      ·
        refine ⟨27674031893170149766982965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36898709190893533022643953 27674031893170149766982965)
        ·
          refine ⟨2594440489984701540654653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27674031893170149766982965 2594440489984701540654653)
          ·
            refine ⟨972915183744263077745495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2594440489984701540654653 972915183744263077745495)
            ·
              refine ⟨1459372775616394616618243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 972915183744263077745495 1459372775616394616618243)
              ·
                refine ⟨2189059163424591924927365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1459372775616394616618243 2189059163424591924927365)
                ·
                  refine ⟨410448593142110985923881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2189059163424591924927365 410448593142110985923881)
                  ·
                    rfl

theorem cell20_899264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 1, 4].length) (baseStart_899264 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_899264 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_899264 prefixEnd_899264 := by exact prefixLift 899264
  have htrace : WordTrace (prefixWord ++ tailWord_899264) baseStart_899264 baseEnd_899264 := by
    simpa [prefixWord, tailWord_899264, baseEnd_899264] using wordTrace_append hprefix tailTrace_899264
  have hstable : (prefixWord ++ tailWord_899264).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899264).length < 2 ^ (prefixWord ++ tailWord_899264).sum := by decide
  have hdescent : baseEnd_899264 < baseStart_899264 := by decide
  rcases family_descends (prefixWord ++ tailWord_899264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899309 : List Nat := [1, 5, 1, 2, 4, 7]
def baseStart_899309 : Nat := 118140960795 + 899309 * 2 ^ 59
def prefixEnd_899309 : Nat := 4983230072969 + 3 ^ 40 * 899309 * 2
def baseEnd_899309 : Nat := 15202560458084845534211

theorem tailTrace_899309 : CollatzResearch.WordTrace tailWord_899309 prefixEnd_899309 15202560458084845534211 := by
  unfold tailWord_899309
  simp only [CollatzResearch.WordTrace]
  refine ⟨32800493898964557594404981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21866995932643038396269987 32800493898964557594404981)
  ·
    refine ⟨3075046303027927274475467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32800493898964557594404981 3075046303027927274475467)
    ·
      refine ⟨4612569454541890911713201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3075046303027927274475467 4612569454541890911713201)
      ·
        refine ⟨3459427090906418183784901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4612569454541890911713201 3459427090906418183784901)
        ·
          refine ⟨648642579544953409459669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3459427090906418183784901 648642579544953409459669)
          ·
            refine ⟨15202560458084845534211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 648642579544953409459669 15202560458084845534211)
            ·
              rfl

theorem cell20_899309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 7].length) (baseStart_899309 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_899309 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_899309 prefixEnd_899309 := by exact prefixLift 899309
  have htrace : WordTrace (prefixWord ++ tailWord_899309) baseStart_899309 baseEnd_899309 := by
    simpa [prefixWord, tailWord_899309, baseEnd_899309] using wordTrace_append hprefix tailTrace_899309
  have hstable : (prefixWord ++ tailWord_899309).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899309).length < 2 ^ (prefixWord ++ tailWord_899309).sum := by decide
  have hdescent : baseEnd_899309 < baseStart_899309 := by decide
  rcases family_descends (prefixWord ++ tailWord_899309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899378 : List Nat := [3, 2, 1, 1, 5, 1, 2, 1, 4]
def baseStart_899378 : Nat := 118140960795 + 899378 * 2 ^ 59
def prefixEnd_899378 : Nat := 4983230072969 + 3 ^ 40 * 899378 * 2
def baseEnd_899378 : Nat := 410500625848433256123415

theorem tailTrace_899378 : CollatzResearch.WordTrace tailWord_899378 prefixEnd_899378 410500625848433256123415 := by
  unfold tailWord_899378
  simp only [CollatzResearch.WordTrace]
  refine ⟨8200752633928645594666697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21868673690476388252444525 8200752633928645594666697)
  ·
    refine ⟨6150564475446484196000023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8200752633928645594666697 6150564475446484196000023)
    ·
      refine ⟨9225846713169726294000035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6150564475446484196000023 9225846713169726294000035)
      ·
        refine ⟨13838770069754589441000053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9225846713169726294000035 13838770069754589441000053)
        ·
          refine ⟨1297384694039492760093755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13838770069754589441000053 1297384694039492760093755)
          ·
            refine ⟨1946077041059239140140633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1297384694039492760093755 1946077041059239140140633)
            ·
              refine ⟨1459557780794429355105475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1946077041059239140140633 1459557780794429355105475)
              ·
                refine ⟨2189336671191644032658213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1459557780794429355105475 2189336671191644032658213)
                ·
                  refine ⟨410500625848433256123415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2189336671191644032658213 410500625848433256123415)
                  ·
                    rfl

theorem cell20_899378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 1, 4].length) (baseStart_899378 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_899378 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_899378 prefixEnd_899378 := by exact prefixLift 899378
  have htrace : WordTrace (prefixWord ++ tailWord_899378) baseStart_899378 baseEnd_899378 := by
    simpa [prefixWord, tailWord_899378, baseEnd_899378] using wordTrace_append hprefix tailTrace_899378
  have hstable : (prefixWord ++ tailWord_899378).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899378).length < 2 ^ (prefixWord ++ tailWord_899378).sum := by decide
  have hdescent : baseEnd_899378 < baseStart_899378 := by decide
  rcases family_descends (prefixWord ++ tailWord_899378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899478 : List Nat := [5, 3, 1, 2, 9]
def baseStart_899478 : Nat := 118140960795 + 899478 * 2 ^ 59
def prefixEnd_899478 : Nat := 4983230072969 + 3 ^ 40 * 899478 * 2
def baseEnd_899478 : Nat := 5068472451521942627033

theorem tailTrace_899478 : CollatzResearch.WordTrace tailWord_899478 prefixEnd_899478 5068472451521942627033 := by
  unfold tailWord_899478
  simp only [CollatzResearch.WordTrace]
  refine ⟨2050416114709518716081693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21871105223568199638204725 2050416114709518716081693)
  ·
    refine ⟨768906043016069518530635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2050416114709518716081693 768906043016069518530635)
    ·
      refine ⟨1153359064524104277795953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 768906043016069518530635 1153359064524104277795953)
      ·
        refine ⟨865019298393078208346965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1153359064524104277795953 865019298393078208346965)
        ·
          refine ⟨5068472451521942627033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 865019298393078208346965 5068472451521942627033)
          ·
            rfl

theorem cell20_899478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 9].length) (baseStart_899478 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_899478 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_899478 prefixEnd_899478 := by exact prefixLift 899478
  have htrace : WordTrace (prefixWord ++ tailWord_899478) baseStart_899478 baseEnd_899478 := by
    simpa [prefixWord, tailWord_899478, baseEnd_899478] using wordTrace_append hprefix tailTrace_899478
  have hstable : (prefixWord ++ tailWord_899478).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899478).length < 2 ^ (prefixWord ++ tailWord_899478).sum := by decide
  have hdescent : baseEnd_899478 < baseStart_899478 := by decide
  rcases family_descends (prefixWord ++ tailWord_899478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899485 : List Nat := [1, 4, 2, 1, 4, 1, 2, 2, 3]
def baseStart_899485 : Nat := 118140960795 + 899485 * 2 ^ 59
def prefixEnd_899485 : Nat := 4983230072969 + 3 ^ 40 * 899485 * 2
def baseEnd_899485 : Nat := 410549463564016439556311

theorem tailTrace_899485 : CollatzResearch.WordTrace tailWord_899485 prefixEnd_899485 410549463564016439556311 := by
  unfold tailWord_899485
  simp only [CollatzResearch.WordTrace]
  refine ⟨32806913146326939652811909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21871275430884626435207939 32806913146326939652811909)
  ·
    refine ⟨6151296214936301184902233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32806913146326939652811909 6151296214936301184902233)
    ·
      refine ⟨4613472161202225888676675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6151296214936301184902233 4613472161202225888676675)
      ·
        refine ⟨6920208241803338833015013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4613472161202225888676675 6920208241803338833015013)
        ·
          refine ⟨1297539045338126031190315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6920208241803338833015013 1297539045338126031190315)
          ·
            refine ⟨1946308568007189046785473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1297539045338126031190315 1946308568007189046785473)
            ·
              refine ⟨1459731426005391785089105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1946308568007189046785473 1459731426005391785089105)
              ·
                refine ⟨1094798569504043838816829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1459731426005391785089105 1094798569504043838816829)
                ·
                  refine ⟨410549463564016439556311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1094798569504043838816829 410549463564016439556311)
                  ·
                    rfl

theorem cell20_899485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 2, 3].length) (baseStart_899485 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_899485 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_899485 prefixEnd_899485 := by exact prefixLift 899485
  have htrace : WordTrace (prefixWord ++ tailWord_899485) baseStart_899485 baseEnd_899485 := by
    simpa [prefixWord, tailWord_899485, baseEnd_899485] using wordTrace_append hprefix tailTrace_899485
  have hstable : (prefixWord ++ tailWord_899485).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899485).length < 2 ^ (prefixWord ++ tailWord_899485).sum := by decide
  have hdescent : baseEnd_899485 < baseStart_899485 := by decide
  rcases family_descends (prefixWord ++ tailWord_899485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899513 : List Nat := [1, 2, 1, 4, 3, 2, 1, 2, 4]
def baseStart_899513 : Nat := 118140960795 + 899513 * 2 ^ 59
def prefixEnd_899513 : Nat := 4983230072969 + 3 ^ 40 * 899513 * 2
def baseEnd_899513 : Nat := 410562243526972786622863

theorem tailTrace_899513 : CollatzResearch.WordTrace tailWord_899513 prefixEnd_899513 410562243526972786622863 := by
  unfold tailWord_899513
  simp only [CollatzResearch.WordTrace]
  refine ⟨32807934390225500434831193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21871956260150333623220795 32807934390225500434831193)
  ·
    refine ⟨24605950792669125326123395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32807934390225500434831193 24605950792669125326123395)
    ·
      refine ⟨36908926189003687989185093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24605950792669125326123395 36908926189003687989185093)
      ·
        refine ⟨6920423660438191497972205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36908926189003687989185093 6920423660438191497972205)
        ·
          refine ⟨2595158872664321811739577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6920423660438191497972205 2595158872664321811739577)
          ·
            refine ⟨1946369154498241358804683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2595158872664321811739577 1946369154498241358804683)
            ·
              refine ⟨2919553731747362038207025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1946369154498241358804683 2919553731747362038207025)
              ·
                refine ⟨2189665298810521528655269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2919553731747362038207025 2189665298810521528655269)
                ·
                  refine ⟨410562243526972786622863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2189665298810521528655269 410562243526972786622863)
                  ·
                    rfl

theorem cell20_899513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 2, 4].length) (baseStart_899513 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_899513 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_899513 prefixEnd_899513 := by exact prefixLift 899513
  have htrace : WordTrace (prefixWord ++ tailWord_899513) baseStart_899513 baseEnd_899513 := by
    simpa [prefixWord, tailWord_899513, baseEnd_899513] using wordTrace_append hprefix tailTrace_899513
  have hstable : (prefixWord ++ tailWord_899513).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899513).length < 2 ^ (prefixWord ++ tailWord_899513).sum := by decide
  have hdescent : baseEnd_899513 < baseStart_899513 := by decide
  rcases family_descends (prefixWord ++ tailWord_899513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899530 : List Nat := [3, 1, 2, 1, 2, 2, 4, 3, 2]
def baseStart_899530 : Nat := 118140960795 + 899530 * 2 ^ 59
def prefixEnd_899530 : Nat := 4983230072969 + 3 ^ 40 * 899530 * 2
def baseEnd_899530 : Nat := 410570002790196283056127

theorem tailTrace_899530 : CollatzResearch.WordTrace tailWord_899530 prefixEnd_899530 410570002790196283056127 := by
  unfold tailWord_899530
  simp only [CollatzResearch.WordTrace]
  refine ⟨8202138607790978084550011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21872369620775941558800029 8202138607790978084550011)
  ·
    refine ⟨12303207911686467126825017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8202138607790978084550011 12303207911686467126825017)
    ·
      refine ⟨9227405933764850345118763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12303207911686467126825017 9227405933764850345118763)
      ·
        refine ⟨13841108900647275517678145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9227405933764850345118763 13841108900647275517678145)
        ·
          refine ⟨10380831675485456638258609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13841108900647275517678145 10380831675485456638258609)
          ·
            refine ⟨7785623756614092478693957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10380831675485456638258609 7785623756614092478693957)
            ·
              refine ⟨1459804454365142339755117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7785623756614092478693957 1459804454365142339755117)
              ·
                refine ⟨547426670386928377408169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1459804454365142339755117 547426670386928377408169)
                ·
                  refine ⟨410570002790196283056127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 547426670386928377408169 410570002790196283056127)
                  ·
                    rfl

theorem cell20_899530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 3, 2].length) (baseStart_899530 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_899530 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_899530 prefixEnd_899530 := by exact prefixLift 899530
  have htrace : WordTrace (prefixWord ++ tailWord_899530) baseStart_899530 baseEnd_899530 := by
    simpa [prefixWord, tailWord_899530, baseEnd_899530] using wordTrace_append hprefix tailTrace_899530
  have hstable : (prefixWord ++ tailWord_899530).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899530).length < 2 ^ (prefixWord ++ tailWord_899530).sum := by decide
  have hdescent : baseEnd_899530 < baseStart_899530 := by decide
  rcases family_descends (prefixWord ++ tailWord_899530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899534 : List Nat := [4, 1, 1, 1, 2, 1, 1, 1, 8]
def baseStart_899534 : Nat := 118140960795 + 899534 * 2 ^ 59
def prefixEnd_899534 : Nat := 4983230072969 + 3 ^ 40 * 899534 * 2
def baseEnd_899534 : Nat := 410571828499190046922777

theorem tailTrace_899534 : CollatzResearch.WordTrace tailWord_899534 prefixEnd_899534 410571828499190046922777 := by
  unfold tailWord_899534
  simp only [CollatzResearch.WordTrace]
  refine ⟨4101087540393677627668207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21872466882099614014230437 4101087540393677627668207)
  ·
    refine ⟨6151631310590516441502311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4101087540393677627668207 6151631310590516441502311)
    ·
      refine ⟨9227446965885774662253467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6151631310590516441502311 9227446965885774662253467)
      ·
        refine ⟨13841170448828661993380201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9227446965885774662253467 13841170448828661993380201)
        ·
          refine ⟨10380877836621496495035151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13841170448828661993380201 10380877836621496495035151)
          ·
            refine ⟨15571316754932244742552727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10380877836621496495035151 15571316754932244742552727)
            ·
              refine ⟨23356975132398367113829091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15571316754932244742552727 23356975132398367113829091)
              ·
                refine ⟨35035462698597550670743637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23356975132398367113829091 35035462698597550670743637)
                ·
                  refine ⟨410571828499190046922777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35035462698597550670743637 410571828499190046922777)
                  ·
                    rfl

theorem cell20_899534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_899534 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_899534 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_899534 prefixEnd_899534 := by exact prefixLift 899534
  have htrace : WordTrace (prefixWord ++ tailWord_899534) baseStart_899534 baseEnd_899534 := by
    simpa [prefixWord, tailWord_899534, baseEnd_899534] using wordTrace_append hprefix tailTrace_899534
  have hstable : (prefixWord ++ tailWord_899534).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899534).length < 2 ^ (prefixWord ++ tailWord_899534).sum := by decide
  have hdescent : baseEnd_899534 < baseStart_899534 := by decide
  rcases family_descends (prefixWord ++ tailWord_899534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899551 : List Nat := [1, 1, 2, 3, 3, 3, 2, 1, 4]
def baseStart_899551 : Nat := 118140960795 + 899551 * 2 ^ 59
def prefixEnd_899551 : Nat := 4983230072969 + 3 ^ 40 * 899551 * 2
def baseEnd_899551 : Nat := 410579587762413543356041

theorem tailTrace_899551 : CollatzResearch.WordTrace tailWord_899551 prefixEnd_899551 410579587762413543356041 := by
  unfold tailWord_899551
  simp only [CollatzResearch.WordTrace]
  refine ⟨32809320364087832924714507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21872880242725221949809671 32809320364087832924714507)
  ·
    refine ⟨49213980546131749387071761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32809320364087832924714507 49213980546131749387071761)
    ·
      refine ⟨36910485409598812040303821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49213980546131749387071761 36910485409598812040303821)
      ·
        refine ⟨13841432028599554515113933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36910485409598812040303821 13841432028599554515113933)
        ·
          refine ⟨5190537010724832943167725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13841432028599554515113933 5190537010724832943167725)
          ·
            refine ⟨1946451379021812353687897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5190537010724832943167725 1946451379021812353687897)
            ·
              refine ⟨1459838534266359265265923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1946451379021812353687897 1459838534266359265265923)
              ·
                refine ⟨2189757801399538897898885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1459838534266359265265923 2189757801399538897898885)
                ·
                  refine ⟨410579587762413543356041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2189757801399538897898885 410579587762413543356041)
                  ·
                    rfl

theorem cell20_899551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 1, 4].length) (baseStart_899551 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_899551 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_899551 prefixEnd_899551 := by exact prefixLift 899551
  have htrace : WordTrace (prefixWord ++ tailWord_899551) baseStart_899551 baseEnd_899551 := by
    simpa [prefixWord, tailWord_899551, baseEnd_899551] using wordTrace_append hprefix tailTrace_899551
  have hstable : (prefixWord ++ tailWord_899551).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899551).length < 2 ^ (prefixWord ++ tailWord_899551).sum := by decide
  have hdescent : baseEnd_899551 < baseStart_899551 := by decide
  rcases family_descends (prefixWord ++ tailWord_899551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899585 : List Nat := [1, 2, 4, 1, 3, 3, 1, 3, 2]
def baseStart_899585 : Nat := 118140960795 + 899585 * 2 ^ 59
def prefixEnd_899585 : Nat := 4983230072969 + 3 ^ 40 * 899585 * 2
def baseEnd_899585 : Nat := 410595106288860536222569

theorem tailTrace_899585 : CollatzResearch.WordTrace tailWord_899585 prefixEnd_899585 410595106288860536222569 := by
  unfold tailWord_899585
  simp only [CollatzResearch.WordTrace]
  refine ⟨32810560445964656731452209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21873706963976437820968139 32810560445964656731452209)
  ·
    refine ⟨24607920334473492548589157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32810560445964656731452209 24607920334473492548589157)
    ·
      refine ⟨4613985062713779852860467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24607920334473492548589157 4613985062713779852860467)
      ·
        refine ⟨6920977594070669779290701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4613985062713779852860467 6920977594070669779290701)
        ·
          refine ⟨2595366597776501167234013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6920977594070669779290701 2595366597776501167234013)
          ·
            refine ⟨973262474166187937712755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2595366597776501167234013 973262474166187937712755)
            ·
              refine ⟨1459893711249281906569133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 973262474166187937712755 1459893711249281906569133)
              ·
                refine ⟨547460141718480714963425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1459893711249281906569133 547460141718480714963425)
                ·
                  refine ⟨410595106288860536222569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 547460141718480714963425 410595106288860536222569)
                  ·
                    rfl

theorem cell20_899585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 3, 2].length) (baseStart_899585 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_899585 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_899585 prefixEnd_899585 := by exact prefixLift 899585
  have htrace : WordTrace (prefixWord ++ tailWord_899585) baseStart_899585 baseEnd_899585 := by
    simpa [prefixWord, tailWord_899585, baseEnd_899585] using wordTrace_append hprefix tailTrace_899585
  have hstable : (prefixWord ++ tailWord_899585).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899585).length < 2 ^ (prefixWord ++ tailWord_899585).sum := by decide
  have hdescent : baseEnd_899585 < baseStart_899585 := by decide
  rcases family_descends (prefixWord ++ tailWord_899585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899596 : List Nat := [2, 2, 1, 2, 4, 3, 6]
def baseStart_899596 : Nat := 118140960795 + 899596 * 2 ^ 59
def prefixEnd_899596 : Nat := 4983230072969 + 3 ^ 40 * 899596 * 2
def baseEnd_899596 : Nat := 45622236332065931872873

theorem tailTrace_899596 : CollatzResearch.WordTrace tailWord_899596 prefixEnd_899596 45622236332065931872873 := by
  unfold tailWord_899596
  simp only [CollatzResearch.WordTrace]
  refine ⟨16405480824462402805051321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21873974432616537073401761 16405480824462402805051321)
  ·
    refine ⟨12304110618346802103788491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16405480824462402805051321 12304110618346802103788491)
    ·
      refine ⟨18456165927520203155682737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12304110618346802103788491 18456165927520203155682737)
      ·
        refine ⟨13842124445640152366762053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18456165927520203155682737 13842124445640152366762053)
        ·
          refine ⟨2595398333557528568767885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13842124445640152366762053 2595398333557528568767885)
          ·
            refine ⟨973274375084073213287957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2595398333557528568767885 973274375084073213287957)
            ·
              refine ⟨45622236332065931872873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 973274375084073213287957 45622236332065931872873)
              ·
                rfl

theorem cell20_899596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 6].length) (baseStart_899596 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_899596 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_899596 prefixEnd_899596 := by exact prefixLift 899596
  have htrace : WordTrace (prefixWord ++ tailWord_899596) baseStart_899596 baseEnd_899596 := by
    simpa [prefixWord, tailWord_899596, baseEnd_899596] using wordTrace_append hprefix tailTrace_899596
  have hstable : (prefixWord ++ tailWord_899596).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899596).length < 2 ^ (prefixWord ++ tailWord_899596).sum := by decide
  have hdescent : baseEnd_899596 < baseStart_899596 := by decide
  rcases family_descends (prefixWord ++ tailWord_899596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899603 : List Nat := [1, 1, 1, 2, 1, 5, 2, 4, 3]
def baseStart_899603 : Nat := 118140960795 + 899603 * 2 ^ 59
def prefixEnd_899603 : Nat := 4983230072969 + 3 ^ 40 * 899603 * 2
def baseEnd_899603 : Nat := 410603321979332473622495

theorem tailTrace_899603 : CollatzResearch.WordTrace tailWord_899603 prefixEnd_899603 410603321979332473622495 := by
  unfold tailWord_899603
  simp only [CollatzResearch.WordTrace]
  refine ⟨32811216959899445805607463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21874144639932963870404975 32811216959899445805607463)
  ·
    refine ⟨49216825439849168708411195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32811216959899445805607463 49216825439849168708411195)
    ·
      refine ⟨73825238159773753062616793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49216825439849168708411195 73825238159773753062616793)
      ·
        refine ⟨55368928619830314796962595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73825238159773753062616793 55368928619830314796962595)
        ·
          refine ⟨83053392929745472195443893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55368928619830314796962595 83053392929745472195443893)
          ·
            refine ⟨7786255587163638018322865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 83053392929745472195443893 7786255587163638018322865)
            ·
              refine ⟨5839691690372728513742149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7786255587163638018322865 5839691690372728513742149)
              ·
                refine ⟨1094942191944886596326653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5839691690372728513742149 1094942191944886596326653)
                ·
                  refine ⟨410603321979332473622495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1094942191944886596326653 410603321979332473622495)
                  ·
                    rfl

theorem cell20_899603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 4, 3].length) (baseStart_899603 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_899603 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_899603 prefixEnd_899603 := by exact prefixLift 899603
  have htrace : WordTrace (prefixWord ++ tailWord_899603) baseStart_899603 baseEnd_899603 := by
    simpa [prefixWord, tailWord_899603, baseEnd_899603] using wordTrace_append hprefix tailTrace_899603
  have hstable : (prefixWord ++ tailWord_899603).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899603).length < 2 ^ (prefixWord ++ tailWord_899603).sum := by decide
  have hdescent : baseEnd_899603 < baseStart_899603 := by decide
  rcases family_descends (prefixWord ++ tailWord_899603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899616 : List Nat := [2, 1, 1, 6, 2, 2, 2, 1, 3]
def baseStart_899616 : Nat := 118140960795 + 899616 * 2 ^ 59
def prefixEnd_899616 : Nat := 4983230072969 + 3 ^ 40 * 899616 * 2
def baseEnd_899616 : Nat := 410609255533562206189109

theorem tailTrace_899616 : CollatzResearch.WordTrace tailWord_899616 prefixEnd_899616 410609255533562206189109 := by
  unfold tailWord_899616
  simp only [CollatzResearch.WordTrace]
  refine ⟨16405845554426174512915351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21874460739234899350553801 16405845554426174512915351)
  ·
    refine ⟨24608768331639261769373027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16405845554426174512915351 24608768331639261769373027)
    ·
      refine ⟨36913152497458892654059541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24608768331639261769373027 36913152497458892654059541)
      ·
        refine ⟨1730304023318385593159041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 36913152497458892654059541 1730304023318385593159041)
        ·
          refine ⟨1297728017488789194869281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1730304023318385593159041 1297728017488789194869281)
          ·
            refine ⟨973296013116591896151961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1297728017488789194869281 973296013116591896151961)
            ·
              refine ⟨729972009837443922113971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 973296013116591896151961 729972009837443922113971)
              ·
                refine ⟨1094958014756165883170957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 729972009837443922113971 1094958014756165883170957)
                ·
                  refine ⟨410609255533562206189109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1094958014756165883170957 410609255533562206189109)
                  ·
                    rfl

theorem cell20_899616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 2, 1, 3].length) (baseStart_899616 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_899616 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_899616 prefixEnd_899616 := by exact prefixLift 899616
  have htrace : WordTrace (prefixWord ++ tailWord_899616) baseStart_899616 baseEnd_899616 := by
    simpa [prefixWord, tailWord_899616, baseEnd_899616] using wordTrace_append hprefix tailTrace_899616
  have hstable : (prefixWord ++ tailWord_899616).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899616).length < 2 ^ (prefixWord ++ tailWord_899616).sum := by decide
  have hdescent : baseEnd_899616 < baseStart_899616 := by decide
  rcases family_descends (prefixWord ++ tailWord_899616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899654 : List Nat := [6, 1, 1, 1, 2, 2, 2, 2, 3]
def baseStart_899654 : Nat := 118140960795 + 899654 * 2 ^ 59
def prefixEnd_899654 : Nat := 4983230072969 + 3 ^ 40 * 899654 * 2
def baseEnd_899654 : Nat := 410626599769002962922287

theorem tailTrace_899654 : CollatzResearch.WordTrace tailWord_899654 prefixEnd_899654 410626599769002962922287 := by
  unfold tailWord_899654
  simp only [CollatzResearch.WordTrace]
  refine ⟨1025408658834833797366063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 21875384721809787677142677 1025408658834833797366063)
  ·
    refine ⟨1538112988252250696049095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1025408658834833797366063 1538112988252250696049095)
    ·
      refine ⟨2307169482378376044073643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1538112988252250696049095 2307169482378376044073643)
      ·
        refine ⟨3460754223567564066110465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2307169482378376044073643 3460754223567564066110465)
        ·
          refine ⟨2595565667675673049582849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3460754223567564066110465 2595565667675673049582849)
          ·
            refine ⟨1946674250756754787187137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2595565667675673049582849 1946674250756754787187137)
            ·
              refine ⟨1460005688067566090390353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1946674250756754787187137 1460005688067566090390353)
              ·
                refine ⟨1095004266050674567792765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1460005688067566090390353 1095004266050674567792765)
                ·
                  refine ⟨410626599769002962922287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1095004266050674567792765 410626599769002962922287)
                  ·
                    rfl

theorem cell20_899654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_899654 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_899654 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_899654 prefixEnd_899654 := by exact prefixLift 899654
  have htrace : WordTrace (prefixWord ++ tailWord_899654) baseStart_899654 baseEnd_899654 := by
    simpa [prefixWord, tailWord_899654, baseEnd_899654] using wordTrace_append hprefix tailTrace_899654
  have hstable : (prefixWord ++ tailWord_899654).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899654).length < 2 ^ (prefixWord ++ tailWord_899654).sum := by decide
  have hdescent : baseEnd_899654 < baseStart_899654 := by decide
  rcases family_descends (prefixWord ++ tailWord_899654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899655 : List Nat := [1, 1, 4, 1, 4, 9]
def baseStart_899655 : Nat := 118140960795 + 899655 * 2 ^ 59
def prefixEnd_899655 : Nat := 4983230072969 + 3 ^ 40 * 899655 * 2
def baseEnd_899655 : Nat := 15208409488750051995887

theorem tailTrace_899655 : CollatzResearch.WordTrace tailWord_899655 prefixEnd_899655 15208409488750051995887 := by
  unfold tailWord_899655
  simp only [CollatzResearch.WordTrace]
  refine ⟨32813113555711058686500419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21875409037140705791000279 32813113555711058686500419)
  ·
    refine ⟨49219670333566588029750629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32813113555711058686500419 49219670333566588029750629)
    ·
      refine ⟨9228688187543735255578243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49219670333566588029750629 9228688187543735255578243)
      ·
        refine ⟨13843032281315602883367365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9228688187543735255578243 13843032281315602883367365)
        ·
          refine ⟨2595568552746675540631381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13843032281315602883367365 2595568552746675540631381)
          ·
            refine ⟨15208409488750051995887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2595568552746675540631381 15208409488750051995887)
            ·
              rfl

theorem cell20_899655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 9].length) (baseStart_899655 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_899655 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_899655 prefixEnd_899655 := by exact prefixLift 899655
  have htrace : WordTrace (prefixWord ++ tailWord_899655) baseStart_899655 baseEnd_899655 := by
    simpa [prefixWord, tailWord_899655, baseEnd_899655] using wordTrace_append hprefix tailTrace_899655
  have hstable : (prefixWord ++ tailWord_899655).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899655).length < 2 ^ (prefixWord ++ tailWord_899655).sum := by decide
  have hdescent : baseEnd_899655 < baseStart_899655 := by decide
  rcases family_descends (prefixWord ++ tailWord_899655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899658 : List Nat := [3, 1, 2, 1, 1, 5, 2, 2, 3]
def baseStart_899658 : Nat := 118140960795 + 899658 * 2 ^ 59
def prefixEnd_899658 : Nat := 4983230072969 + 3 ^ 40 * 899658 * 2
def baseEnd_899658 : Nat := 410628425477996726788937

theorem tailTrace_899658 : CollatzResearch.WordTrace tailWord_899658 prefixEnd_899658 410628425477996726788937 := by
  unfold tailWord_899658
  simp only [CollatzResearch.WordTrace]
  refine ⟨8203305743675047549714907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21875481983133460132573085 8203305743675047549714907)
  ·
    refine ⟨12304958615512571324572361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8203305743675047549714907 12304958615512571324572361)
    ·
      refine ⟨9228718961634428493429271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12304958615512571324572361 9228718961634428493429271)
      ·
        refine ⟨13843078442451642740143907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9228718961634428493429271 13843078442451642740143907)
        ·
          refine ⟨20764617663677464110215861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13843078442451642740143907 20764617663677464110215861)
          ·
            refine ⟨1946682905969762260332737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20764617663677464110215861 1946682905969762260332737)
            ·
              refine ⟨1460012179477321695249553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1946682905969762260332737 1460012179477321695249553)
              ·
                refine ⟨1095009134607991271437165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1460012179477321695249553 1095009134607991271437165)
                ·
                  refine ⟨410628425477996726788937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1095009134607991271437165 410628425477996726788937)
                  ·
                    rfl

theorem cell20_899658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 2, 3].length) (baseStart_899658 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_899658 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_899658 prefixEnd_899658 := by exact prefixLift 899658
  have htrace : WordTrace (prefixWord ++ tailWord_899658) baseStart_899658 baseEnd_899658 := by
    simpa [prefixWord, tailWord_899658, baseEnd_899658] using wordTrace_append hprefix tailTrace_899658
  have hstable : (prefixWord ++ tailWord_899658).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899658).length < 2 ^ (prefixWord ++ tailWord_899658).sum := by decide
  have hdescent : baseEnd_899658 < baseStart_899658 := by decide
  rcases family_descends (prefixWord ++ tailWord_899658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899661 : List Nat := [1, 6, 1, 1, 2, 2, 1, 4, 2]
def baseStart_899661 : Nat := 118140960795 + 899661 * 2 ^ 59
def prefixEnd_899661 : Nat := 4983230072969 + 3 ^ 40 * 899661 * 2
def baseEnd_899661 : Nat := 410629794759742049688925

theorem tailTrace_899661 : CollatzResearch.WordTrace tailWord_899661 prefixEnd_899661 410629794759742049688925 := by
  unfold tailWord_899661
  simp only [CollatzResearch.WordTrace]
  refine ⟨32813332393689321711218837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21875554929126214474145891 32813332393689321711218837)
  ·
    refine ⟨1538124955954186955213383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 32813332393689321711218837 1538124955954186955213383)
    ·
      refine ⟨2307187433931280432820075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1538124955954186955213383 2307187433931280432820075)
      ·
        refine ⟨3460781150896920649230113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2307187433931280432820075 3460781150896920649230113)
        ·
          refine ⟨2595585863172690486922585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3460781150896920649230113 2595585863172690486922585)
          ·
            refine ⟨1946689397379517865191939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2595585863172690486922585 1946689397379517865191939)
            ·
              refine ⟨2920034096069276797787909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1946689397379517865191939 2920034096069276797787909)
              ·
                refine ⟨547506393012989399585233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2920034096069276797787909 547506393012989399585233)
                ·
                  refine ⟨410629794759742049688925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 547506393012989399585233 410629794759742049688925)
                  ·
                    rfl

theorem cell20_899661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_899661 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_899661 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_899661 prefixEnd_899661 := by exact prefixLift 899661
  have htrace : WordTrace (prefixWord ++ tailWord_899661) baseStart_899661 baseEnd_899661 := by
    simpa [prefixWord, tailWord_899661, baseEnd_899661] using wordTrace_append hprefix tailTrace_899661
  have hstable : (prefixWord ++ tailWord_899661).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899661).length < 2 ^ (prefixWord ++ tailWord_899661).sum := by decide
  have hdescent : baseEnd_899661 < baseStart_899661 := by decide
  rcases family_descends (prefixWord ++ tailWord_899661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899678 : List Nat := [4, 4, 1, 2, 1, 1, 1, 2, 4]
def baseStart_899678 : Nat := 118140960795 + 899678 * 2 ^ 59
def prefixEnd_899678 : Nat := 4983230072969 + 3 ^ 40 * 899678 * 2
def baseEnd_899678 : Nat := 410637554022965546122189

theorem tailTrace_899678 : CollatzResearch.WordTrace tailWord_899678 prefixEnd_899678 410637554022965546122189 := by
  unfold tailWord_899678
  simp only [CollatzResearch.WordTrace]
  refine ⟨4101744054328466701823461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21875968289751822409725125 4101744054328466701823461)
  ·
    refine ⟨769077010186587506591899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4101744054328466701823461 769077010186587506591899)
    ·
      refine ⟨1153615515279881259887849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 769077010186587506591899 1153615515279881259887849)
      ·
        refine ⟨865211636459910944915887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1153615515279881259887849 865211636459910944915887)
        ·
          refine ⟨1297817454689866417373831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 865211636459910944915887 1297817454689866417373831)
          ·
            refine ⟨1946726182034799626060747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1297817454689866417373831 1946726182034799626060747)
            ·
              refine ⟨2920089273052199439091121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1946726182034799626060747 2920089273052199439091121)
              ·
                refine ⟨2190066954789149579318341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2920089273052199439091121 2190066954789149579318341)
                ·
                  refine ⟨410637554022965546122189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2190066954789149579318341 410637554022965546122189)
                  ·
                    rfl

theorem cell20_899678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_899678 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_899678 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_899678 prefixEnd_899678 := by exact prefixLift 899678
  have htrace : WordTrace (prefixWord ++ tailWord_899678) baseStart_899678 baseEnd_899678 := by
    simpa [prefixWord, tailWord_899678, baseEnd_899678] using wordTrace_append hprefix tailTrace_899678
  have hstable : (prefixWord ++ tailWord_899678).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899678).length < 2 ^ (prefixWord ++ tailWord_899678).sum := by decide
  have hdescent : baseEnd_899678 < baseStart_899678 := by decide
  rcases family_descends (prefixWord ++ tailWord_899678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899703 : List Nat := [1, 1, 3, 1, 1, 3, 3, 5, 2]
def baseStart_899703 : Nat := 118140960795 + 899703 * 2 ^ 59
def prefixEnd_899703 : Nat := 4983230072969 + 3 ^ 40 * 899703 * 2
def baseEnd_899703 : Nat := 410648964704176570288753

theorem tailTrace_899703 : CollatzResearch.WordTrace tailWord_899703 prefixEnd_899703 410648964704176570288753 := by
  unfold tailWord_899703
  simp only [CollatzResearch.WordTrace]
  refine ⟨32814864259537162884247763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21876576173024775256165175 32814864259537162884247763)
  ·
    refine ⟨49222296389305744326371645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32814864259537162884247763 49222296389305744326371645)
    ·
      refine ⟨18458361145989654122389367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49222296389305744326371645 18458361145989654122389367)
      ·
        refine ⟨27687541718984481183584051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18458361145989654122389367 27687541718984481183584051)
        ·
          refine ⟨41531312578476721775376077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27687541718984481183584051 41531312578476721775376077)
          ·
            refine ⟨15574242216928770665766029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41531312578476721775376077 15574242216928770665766029)
            ·
              refine ⟨5840340831348288999662261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15574242216928770665766029 5840340831348288999662261)
              ·
                refine ⟨547531952938902093718337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5840340831348288999662261 547531952938902093718337)
                ·
                  refine ⟨410648964704176570288753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 547531952938902093718337 410648964704176570288753)
                  ·
                    rfl

theorem cell20_899703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 5, 2].length) (baseStart_899703 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_899703 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_899703 prefixEnd_899703 := by exact prefixLift 899703
  have htrace : WordTrace (prefixWord ++ tailWord_899703) baseStart_899703 baseEnd_899703 := by
    simpa [prefixWord, tailWord_899703, baseEnd_899703] using wordTrace_append hprefix tailTrace_899703
  have hstable : (prefixWord ++ tailWord_899703).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899703).length < 2 ^ (prefixWord ++ tailWord_899703).sum := by decide
  have hdescent : baseEnd_899703 < baseStart_899703 := by decide
  rcases family_descends (prefixWord ++ tailWord_899703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899717 : List Nat := [1, 3, 1, 1, 4, 3, 1, 1, 5]
def baseStart_899717 : Nat := 118140960795 + 899717 * 2 ^ 59
def prefixEnd_899717 : Nat := 4983230072969 + 3 ^ 40 * 899717 * 2
def baseEnd_899717 : Nat := 410655354685654743822029

theorem tailTrace_899717 : CollatzResearch.WordTrace tailWord_899717 prefixEnd_899717 410655354685654743822029 := by
  unfold tailWord_899717
  simp only [CollatzResearch.WordTrace]
  refine ⟨32815374881486443275257405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21876916587657628850171603 32815374881486443275257405)
  ·
    refine ⟨12305765580557416228221527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32815374881486443275257405 12305765580557416228221527)
    ·
      refine ⟨18458648370836124342332291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12305765580557416228221527 18458648370836124342332291)
      ·
        refine ⟨27687972556254186513498437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18458648370836124342332291 27687972556254186513498437)
        ·
          refine ⟨5191494854297659971280957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27687972556254186513498437 5191494854297659971280957)
          ·
            refine ⟨1946810570361622489230359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5191494854297659971280957 1946810570361622489230359)
            ·
              refine ⟨2920215855542433733845539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1946810570361622489230359 2920215855542433733845539)
              ·
                refine ⟨4380323783313650600768309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2920215855542433733845539 4380323783313650600768309)
                ·
                  refine ⟨410655354685654743822029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4380323783313650600768309 410655354685654743822029)
                  ·
                    rfl

theorem cell20_899717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 1, 5].length) (baseStart_899717 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_899717 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_899717 prefixEnd_899717 := by exact prefixLift 899717
  have htrace : WordTrace (prefixWord ++ tailWord_899717) baseStart_899717 baseEnd_899717 := by
    simpa [prefixWord, tailWord_899717, baseEnd_899717] using wordTrace_append hprefix tailTrace_899717
  have hstable : (prefixWord ++ tailWord_899717).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899717).length < 2 ^ (prefixWord ++ tailWord_899717).sum := by decide
  have hdescent : baseEnd_899717 < baseStart_899717 := by decide
  rcases family_descends (prefixWord ++ tailWord_899717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899744 : List Nat := [2, 1, 1, 4, 5, 1, 2, 4]
def baseStart_899744 : Nat := 118140960795 + 899744 * 2 ^ 59
def prefixEnd_899744 : Nat := 4983230072969 + 3 ^ 40 * 899744 * 2
def baseEnd_899744 : Nat := 136889226073787549973973

theorem tailTrace_899744 : CollatzResearch.WordTrace tailWord_899744 prefixEnd_899744 136889226073787549973973 := by
  unfold tailWord_899744
  simp only [CollatzResearch.WordTrace]
  refine ⟨16408179826194313443245143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21877573101592417924326857 16408179826194313443245143)
  ·
    refine ⟨24612269739291470164867715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16408179826194313443245143 24612269739291470164867715)
    ·
      refine ⟨36918404608937205247301573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24612269739291470164867715 36918404608937205247301573)
      ·
        refine ⟨6922200864175725983869045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36918404608937205247301573 6922200864175725983869045)
        ·
          refine ⟨648956331016474310987723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6922200864175725983869045 648956331016474310987723)
          ·
            refine ⟨973434496524711466481585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 648956331016474310987723 973434496524711466481585)
            ·
              refine ⟨730075872393533599861189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 973434496524711466481585 730075872393533599861189)
              ·
                refine ⟨136889226073787549973973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 730075872393533599861189 136889226073787549973973)
                ·
                  rfl

theorem cell20_899744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 2, 4].length) (baseStart_899744 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_899744 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_899744 prefixEnd_899744 := by exact prefixLift 899744
  have htrace : WordTrace (prefixWord ++ tailWord_899744) baseStart_899744 baseEnd_899744 := by
    simpa [prefixWord, tailWord_899744, baseEnd_899744] using wordTrace_append hprefix tailTrace_899744
  have hstable : (prefixWord ++ tailWord_899744).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899744).length < 2 ^ (prefixWord ++ tailWord_899744).sum := by decide
  have hdescent : baseEnd_899744 < baseStart_899744 := by decide
  rcases family_descends (prefixWord ++ tailWord_899744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899786 : List Nat := [3, 1, 2, 1, 4, 2, 2, 5]
def baseStart_899786 : Nat := 118140960795 + 899786 * 2 ^ 59
def prefixEnd_899786 : Nat := 4983230072969 + 3 ^ 40 * 899786 * 2
def baseEnd_899786 : Nat := 136895616055265723507249

theorem tailTrace_899786 : CollatzResearch.WordTrace tailWord_899786 prefixEnd_899786 136895616055265723507249 := by
  unfold tailWord_899786
  simp only [CollatzResearch.WordTrace]
  refine ⟨8204472879559117014879803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21878594345490978706346141 8204472879559117014879803)
  ·
    refine ⟨12306709319338675522319705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8204472879559117014879803 12306709319338675522319705)
    ·
      refine ⟨9230031989504006641739779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12306709319338675522319705 9230031989504006641739779)
      ·
        refine ⟨13845047984256009962609669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9230031989504006641739779 13845047984256009962609669)
        ·
          refine ⟨2595946497048001867989313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13845047984256009962609669 2595946497048001867989313)
          ·
            refine ⟨1946959872786001400991985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2595946497048001867989313 1946959872786001400991985)
            ·
              refine ⟨1460219904589501050743989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1946959872786001400991985 1460219904589501050743989)
              ·
                refine ⟨136895616055265723507249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1460219904589501050743989 136895616055265723507249)
                ·
                  rfl

theorem cell20_899786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 5].length) (baseStart_899786 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_899786 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_899786 prefixEnd_899786 := by exact prefixLift 899786
  have htrace : WordTrace (prefixWord ++ tailWord_899786) baseStart_899786 baseEnd_899786 := by
    simpa [prefixWord, tailWord_899786, baseEnd_899786] using wordTrace_append hprefix tailTrace_899786
  have hstable : (prefixWord ++ tailWord_899786).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899786).length < 2 ^ (prefixWord ++ tailWord_899786).sum := by decide
  have hdescent : baseEnd_899786 < baseStart_899786 := by decide
  rcases family_descends (prefixWord ++ tailWord_899786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899793 : List Nat := [1, 2, 2, 1, 2, 3, 3, 3, 3]
def baseStart_899793 : Nat := 118140960795 + 899793 * 2 ^ 59
def prefixEnd_899793 : Nat := 4983230072969 + 3 ^ 40 * 899793 * 2
def baseEnd_899793 : Nat := 410690043156536257288385

theorem tailTrace_899793 : CollatzResearch.WordTrace tailWord_899793 prefixEnd_899793 410690043156536257288385 := by
  unfold tailWord_899793
  simp only [CollatzResearch.WordTrace]
  refine ⟨32818146829211108255024033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21878764552807405503349355 32818146829211108255024033)
  ·
    refine ⟨24613610121908331191268025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32818146829211108255024033 24613610121908331191268025)
    ·
      refine ⟨18460207591431248393451019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24613610121908331191268025 18460207591431248393451019)
      ·
        refine ⟨27690311387146872590176529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18460207591431248393451019 27690311387146872590176529)
        ·
          refine ⟨20767733540360154442632397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27690311387146872590176529 20767733540360154442632397)
          ·
            refine ⟨7787900077635057915987149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20767733540360154442632397 7787900077635057915987149)
            ·
              refine ⟨2920462529113146718495181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7787900077635057915987149 2920462529113146718495181)
              ·
                refine ⟨1095173448417430019435693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2920462529113146718495181 1095173448417430019435693)
                ·
                  refine ⟨410690043156536257288385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1095173448417430019435693 410690043156536257288385)
                  ·
                    rfl

theorem cell20_899793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 3, 3].length) (baseStart_899793 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_899793 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_899793 prefixEnd_899793 := by exact prefixLift 899793
  have htrace : WordTrace (prefixWord ++ tailWord_899793) baseStart_899793 baseEnd_899793 := by
    simpa [prefixWord, tailWord_899793, baseEnd_899793] using wordTrace_append hprefix tailTrace_899793
  have hstable : (prefixWord ++ tailWord_899793).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899793).length < 2 ^ (prefixWord ++ tailWord_899793).sum := by decide
  have hdescent : baseEnd_899793 < baseStart_899793 := by decide
  rcases family_descends (prefixWord ++ tailWord_899793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899807 : List Nat := [1, 1, 2, 3, 2, 3, 2, 6]
def baseStart_899807 : Nat := 118140960795 + 899807 * 2 ^ 59
def prefixEnd_899807 : Nat := 4983230072969 + 3 ^ 40 * 899807 * 2
def baseEnd_899807 : Nat := 136898811046004810273887

theorem tailTrace_899807 : CollatzResearch.WordTrace tailWord_899807 prefixEnd_899807 136898811046004810273887 := by
  unfold tailWord_899807
  simp only [CollatzResearch.WordTrace]
  refine ⟨32818657451160388646033675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21879104967440259097355783 32818657451160388646033675)
  ·
    refine ⟨49227986176740582969050513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32818657451160388646033675 49227986176740582969050513)
    ·
      refine ⟨36920989632555437226787885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49227986176740582969050513 36920989632555437226787885)
      ·
        refine ⟨13845371112208288960045457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36920989632555437226787885 13845371112208288960045457)
        ·
          refine ⟨10384028334156216720034093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13845371112208288960045457 10384028334156216720034093)
          ·
            refine ⟨3894010625308581270012785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10384028334156216720034093 3894010625308581270012785)
            ·
              refine ⟨2920507968981435952509589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3894010625308581270012785 2920507968981435952509589)
              ·
                refine ⟨136898811046004810273887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2920507968981435952509589 136898811046004810273887)
                ·
                  rfl

theorem cell20_899807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 6].length) (baseStart_899807 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_899807 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_899807 prefixEnd_899807 := by exact prefixLift 899807
  have htrace : WordTrace (prefixWord ++ tailWord_899807) baseStart_899807 baseEnd_899807 := by
    simpa [prefixWord, tailWord_899807, baseEnd_899807] using wordTrace_append hprefix tailTrace_899807
  have hstable : (prefixWord ++ tailWord_899807).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899807).length < 2 ^ (prefixWord ++ tailWord_899807).sum := by decide
  have hdescent : baseEnd_899807 < baseStart_899807 := by decide
  rcases family_descends (prefixWord ++ tailWord_899807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899834 : List Nat := [3, 1, 1, 1, 1, 3, 6, 2, 2]
def baseStart_899834 : Nat := 118140960795 + 899834 * 2 ^ 59
def prefixEnd_899834 : Nat := 4983230072969 + 3 ^ 40 * 899834 * 2
def baseEnd_899834 : Nat := 410708756673722336921551

theorem tailTrace_899834 : CollatzResearch.WordTrace tailWord_899834 prefixEnd_899834 410708756673722336921551 := by
  unfold tailWord_899834
  simp only [CollatzResearch.WordTrace]
  refine ⟨8204910555515643064316639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21879761481375048171511037 8204910555515643064316639)
  ·
    refine ⟨12307365833273464596474959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8204910555515643064316639 12307365833273464596474959)
    ·
      refine ⟨18461048749910196894712439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12307365833273464596474959 18461048749910196894712439)
      ·
        refine ⟨27691573124865295342068659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18461048749910196894712439 27691573124865295342068659)
        ·
          refine ⟨41537359687297943013102989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27691573124865295342068659 41537359687297943013102989)
          ·
            refine ⟨15576509882736728629913621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41537359687297943013102989 15576509882736728629913621)
            ·
              refine ⟨730148900753284154527201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15576509882736728629913621 730148900753284154527201)
              ·
                refine ⟨547611675564963115895401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 730148900753284154527201 547611675564963115895401)
                ·
                  refine ⟨410708756673722336921551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 547611675564963115895401 410708756673722336921551)
                  ·
                    rfl

theorem cell20_899834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 6, 2, 2].length) (baseStart_899834 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_899834 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_899834 prefixEnd_899834 := by exact prefixLift 899834
  have htrace : WordTrace (prefixWord ++ tailWord_899834) baseStart_899834 baseEnd_899834 := by
    simpa [prefixWord, tailWord_899834, baseEnd_899834] using wordTrace_append hprefix tailTrace_899834
  have hstable : (prefixWord ++ tailWord_899834).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899834).length < 2 ^ (prefixWord ++ tailWord_899834).sum := by decide
  have hdescent : baseEnd_899834 < baseStart_899834 := by decide
  rcases family_descends (prefixWord ++ tailWord_899834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899852 : List Nat := [2, 2, 1, 2, 2, 1, 1, 2, 7]
def baseStart_899852 : Nat := 118140960795 + 899852 * 2 ^ 59
def prefixEnd_899852 : Nat := 4983230072969 + 3 ^ 40 * 899852 * 2
def baseEnd_899852 : Nat := 410716972364194274321477

theorem tailTrace_899852 : CollatzResearch.WordTrace tailWord_899852 prefixEnd_899852 410716972364194274321477 := by
  unfold tailWord_899852
  simp only [CollatzResearch.WordTrace]
  refine ⟨16410149367998680665710905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21880199157331574220947873 16410149367998680665710905)
  ·
    refine ⟨12307612025999010499283179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16410149367998680665710905 12307612025999010499283179)
    ·
      refine ⟨18461418038998515748924769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12307612025999010499283179 18461418038998515748924769)
      ·
        refine ⟨13846063529248886811693577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18461418038998515748924769 13846063529248886811693577)
        ·
          refine ⟨10384547646936665108770183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13846063529248886811693577 10384547646936665108770183)
          ·
            refine ⟨15576821470404997663155275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10384547646936665108770183 15576821470404997663155275)
            ·
              refine ⟨23365232205607496494732913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15576821470404997663155275 23365232205607496494732913)
              ·
                refine ⟨17523924154205622371049685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23365232205607496494732913 17523924154205622371049685)
                ·
                  refine ⟨410716972364194274321477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17523924154205622371049685 410716972364194274321477)
                  ·
                    rfl

theorem cell20_899852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 7].length) (baseStart_899852 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_899852 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_899852 prefixEnd_899852 := by exact prefixLift 899852
  have htrace : WordTrace (prefixWord ++ tailWord_899852) baseStart_899852 baseEnd_899852 := by
    simpa [prefixWord, tailWord_899852, baseEnd_899852] using wordTrace_append hprefix tailTrace_899852
  have hstable : (prefixWord ++ tailWord_899852).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899852).length < 2 ^ (prefixWord ++ tailWord_899852).sum := by decide
  have hdescent : baseEnd_899852 < baseStart_899852 := by decide
  rcases family_descends (prefixWord ++ tailWord_899852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899858 : List Nat := [3, 2, 4, 1, 2, 1, 3, 4]
def baseStart_899858 : Nat := 118140960795 + 899858 * 2 ^ 59
def prefixEnd_899858 : Nat := 4983230072969 + 3 ^ 40 * 899858 * 2
def baseEnd_899858 : Nat := 136906570309228306707151

theorem tailTrace_899858 : CollatzResearch.WordTrace tailWord_899858 prefixEnd_899858 136906570309228306707151 := by
  unfold tailWord_899858
  simp only [CollatzResearch.WordTrace]
  refine ⟨8205129393493906089035057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21880345049317082904093485 8205129393493906089035057)
  ·
    refine ⟨6153847045120429566776293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8205129393493906089035057 6153847045120429566776293)
    ·
      refine ⟨1153846320960080543770555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6153847045120429566776293 1153846320960080543770555)
      ·
        refine ⟨1730769481440120815655833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1153846320960080543770555 1730769481440120815655833)
        ·
          refine ⟨1298077111080090611741875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1730769481440120815655833 1298077111080090611741875)
          ·
            refine ⟨1947115666620135917612813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1298077111080090611741875 1947115666620135917612813)
            ·
              refine ⟨730168374982550969104805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1947115666620135917612813 730168374982550969104805)
              ·
                refine ⟨136906570309228306707151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 730168374982550969104805 136906570309228306707151)
                ·
                  rfl

theorem cell20_899858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 3, 4].length) (baseStart_899858 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_899858 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_899858 prefixEnd_899858 := by exact prefixLift 899858
  have htrace : WordTrace (prefixWord ++ tailWord_899858) baseStart_899858 baseEnd_899858 := by
    simpa [prefixWord, tailWord_899858, baseEnd_899858] using wordTrace_append hprefix tailTrace_899858
  have hstable : (prefixWord ++ tailWord_899858).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899858).length < 2 ^ (prefixWord ++ tailWord_899858).sum := by decide
  have hdescent : baseEnd_899858 < baseStart_899858 := by decide
  rcases family_descends (prefixWord ++ tailWord_899858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899872 : List Nat := [2, 1, 1, 5, 1, 3, 2, 3, 2]
def baseStart_899872 : Nat := 118140960795 + 899872 * 2 ^ 59
def prefixEnd_899872 : Nat := 4983230072969 + 3 ^ 40 * 899872 * 2
def baseEnd_899872 : Nat := 410726100909163093654729

theorem tailTrace_899872 : CollatzResearch.WordTrace tailWord_899872 prefixEnd_899872 410726100909163093654729 := by
  unfold tailWord_899872
  simp only [CollatzResearch.WordTrace]
  refine ⟨16410514097962452373574935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21880685463949936498099913 16410514097962452373574935)
  ·
    refine ⟨24615771146943678560362403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16410514097962452373574935 24615771146943678560362403)
    ·
      refine ⟨36923656720415517840543605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24615771146943678560362403 36923656720415517840543605)
      ·
        refine ⟨3461592817538954797550963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36923656720415517840543605 3461592817538954797550963)
        ·
          refine ⟨5192389226308432196326445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3461592817538954797550963 5192389226308432196326445)
          ·
            refine ⟨1947145959865662073622417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5192389226308432196326445 1947145959865662073622417)
            ·
              refine ⟨1460359469899246555216813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1947145959865662073622417 1460359469899246555216813)
              ·
                refine ⟨547634801212217458206305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1460359469899246555216813 547634801212217458206305)
                ·
                  refine ⟨410726100909163093654729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 547634801212217458206305 410726100909163093654729)
                  ·
                    rfl

theorem cell20_899872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 3, 2].length) (baseStart_899872 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_899872 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_899872 prefixEnd_899872 := by exact prefixLift 899872
  have htrace : WordTrace (prefixWord ++ tailWord_899872) baseStart_899872 baseEnd_899872 := by
    simpa [prefixWord, tailWord_899872, baseEnd_899872] using wordTrace_append hprefix tailTrace_899872
  have hstable : (prefixWord ++ tailWord_899872).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899872).length < 2 ^ (prefixWord ++ tailWord_899872).sum := by decide
  have hdescent : baseEnd_899872 < baseStart_899872 := by decide
  rcases family_descends (prefixWord ++ tailWord_899872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899882 : List Nat := [3, 1, 4, 3, 1, 2, 1, 2, 3]
def baseStart_899882 : Nat := 118140960795 + 899882 * 2 ^ 59
def prefixEnd_899882 : Nat := 4983230072969 + 3 ^ 40 * 899882 * 2
def baseEnd_899882 : Nat := 410730665181647503321355

theorem tailTrace_899882 : CollatzResearch.WordTrace tailWord_899882 prefixEnd_899882 410730665181647503321355 := by
  unfold tailWord_899882
  simp only [CollatzResearch.WordTrace]
  refine ⟨8205348231472169113753475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21880928617259117636675933 8205348231472169113753475)
  ·
    refine ⟨12308022347208253670630213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8205348231472169113753475 12308022347208253670630213)
    ·
      refine ⟨2307754190101547563243165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12308022347208253670630213 2307754190101547563243165)
      ·
        refine ⟨865407821288080336216187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2307754190101547563243165 865407821288080336216187)
        ·
          refine ⟨1298111731932120504324281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 865407821288080336216187 1298111731932120504324281)
          ·
            refine ⟨973583798949090378243211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1298111731932120504324281 973583798949090378243211)
            ·
              refine ⟨1460375698423635567364817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 973583798949090378243211 1460375698423635567364817)
              ·
                refine ⟨1095281773817726675523613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1460375698423635567364817 1095281773817726675523613)
                ·
                  refine ⟨410730665181647503321355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1095281773817726675523613 410730665181647503321355)
                  ·
                    rfl

theorem cell20_899882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 2, 3].length) (baseStart_899882 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_899882 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_899882 prefixEnd_899882 := by exact prefixLift 899882
  have htrace : WordTrace (prefixWord ++ tailWord_899882) baseStart_899882 baseEnd_899882 := by
    simpa [prefixWord, tailWord_899882, baseEnd_899882] using wordTrace_append hprefix tailTrace_899882
  have hstable : (prefixWord ++ tailWord_899882).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899882).length < 2 ^ (prefixWord ++ tailWord_899882).sum := by decide
  have hdescent : baseEnd_899882 < baseStart_899882 := by decide
  rcases family_descends (prefixWord ++ tailWord_899882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899886 : List Nat := [4, 1, 3, 2, 1, 2, 1, 1, 5]
def baseStart_899886 : Nat := 118140960795 + 899886 * 2 ^ 59
def prefixEnd_899886 : Nat := 4983230072969 + 3 ^ 40 * 899886 * 2
def baseEnd_899886 : Nat := 410732490890641267188005

theorem tailTrace_899886 : CollatzResearch.WordTrace tailWord_899886 prefixEnd_899886 410732490890641267188005 := by
  unfold tailWord_899886
  simp only [CollatzResearch.WordTrace]
  refine ⟨4102692352234273142269939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21881025878582790092106341 4102692352234273142269939)
  ·
    refine ⟨6154038528351409713404909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4102692352234273142269939 6154038528351409713404909)
    ·
      refine ⟨2307764448131778642526841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6154038528351409713404909 2307764448131778642526841)
      ·
        refine ⟨1730823336098833981895131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2307764448131778642526841 1730823336098833981895131)
        ·
          refine ⟨2596235004148250972842697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1730823336098833981895131 2596235004148250972842697)
          ·
            refine ⟨1947176253111188229632023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2596235004148250972842697 1947176253111188229632023)
            ·
              refine ⟨2920764379666782344448035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1947176253111188229632023 2920764379666782344448035)
              ·
                refine ⟨4381146569500173516672053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2920764379666782344448035 4381146569500173516672053)
                ·
                  refine ⟨410732490890641267188005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4381146569500173516672053 410732490890641267188005)
                  ·
                    rfl

theorem cell20_899886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_899886 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_899886 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_899886 prefixEnd_899886 := by exact prefixLift 899886
  have htrace : WordTrace (prefixWord ++ tailWord_899886) baseStart_899886 baseEnd_899886 := by
    simpa [prefixWord, tailWord_899886, baseEnd_899886] using wordTrace_append hprefix tailTrace_899886
  have hstable : (prefixWord ++ tailWord_899886).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899886).length < 2 ^ (prefixWord ++ tailWord_899886).sum := by decide
  have hdescent : baseEnd_899886 < baseStart_899886 := by decide
  rcases family_descends (prefixWord ++ tailWord_899886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899893 : List Nat := [1, 3, 3, 1, 3, 2, 2, 1, 4]
def baseStart_899893 : Nat := 118140960795 + 899893 * 2 ^ 59
def prefixEnd_899893 : Nat := 4983230072969 + 3 ^ 40 * 899893 * 2
def baseEnd_899893 : Nat := 410735685881380353954643

theorem tailTrace_899893 : CollatzResearch.WordTrace tailWord_899893 prefixEnd_899893 410735685881380353954643 := by
  unfold tailWord_899893
  simp only [CollatzResearch.WordTrace]
  refine ⟨32821794128848825333664333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21881196085899216889109555 32821794128848825333664333)
  ·
    refine ⟨12308172798318309500124125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32821794128848825333664333 12308172798318309500124125)
    ·
      refine ⟨4615564799369366062546547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12308172798318309500124125 4615564799369366062546547)
      ·
        refine ⟨6923347199054049093819821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4615564799369366062546547 6923347199054049093819821)
        ·
          refine ⟨2596255199645268410182433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6923347199054049093819821 2596255199645268410182433)
          ·
            refine ⟨1947191399733951307636825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2596255199645268410182433 1947191399733951307636825)
            ·
              refine ⟨1460393549800463480727619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1947191399733951307636825 1460393549800463480727619)
              ·
                refine ⟨2190590324700695221091429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1460393549800463480727619 2190590324700695221091429)
                ·
                  refine ⟨410735685881380353954643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2190590324700695221091429 410735685881380353954643)
                  ·
                    rfl

theorem cell20_899893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 1, 4].length) (baseStart_899893 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_899893 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_899893 prefixEnd_899893 := by exact prefixLift 899893
  have htrace : WordTrace (prefixWord ++ tailWord_899893) baseStart_899893 baseEnd_899893 := by
    simpa [prefixWord, tailWord_899893, baseEnd_899893] using wordTrace_append hprefix tailTrace_899893
  have hstable : (prefixWord ++ tailWord_899893).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899893).length < 2 ^ (prefixWord ++ tailWord_899893).sum := by decide
  have hdescent : baseEnd_899893 < baseStart_899893 := by decide
  rcases family_descends (prefixWord ++ tailWord_899893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
