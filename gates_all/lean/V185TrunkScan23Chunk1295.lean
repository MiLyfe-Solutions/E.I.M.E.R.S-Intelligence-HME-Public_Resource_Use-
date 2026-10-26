import V185TrunkScan23Chunk1294

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7670066 : List Nat := [3, 2, 1, 1, 5, 2, 1, 3, 1, 4]
def baseStart_7670066 : Nat := 118140960795 + 7670066 * 2 ^ 59
def prefixEnd_7670066 : Nat := 4983230072969 + 3 ^ 40 * 7670066 * 2
def baseEnd_7670066 : Nat := 1312810169902764355067005

theorem tailTrace_7670066 : CollatzResearch.WordTrace tailWord_7670066 prefixEnd_7670066 1312810169902764355067005 := by
  unfold tailWord_7670066
  simp only [CollatzResearch.WordTrace]
  refine ⟨69937572357667074957005513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186500192953778866552014701 69937572357667074957005513)
  ·
    refine ⟨52453179268250306217754135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69937572357667074957005513 52453179268250306217754135)
    ·
      refine ⟨78679768902375459326631203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52453179268250306217754135 78679768902375459326631203)
      ·
        refine ⟨118019653353563188989946805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78679768902375459326631203 118019653353563188989946805)
        ·
          refine ⟨11064342501896548967807513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 118019653353563188989946805 11064342501896548967807513)
          ·
            refine ⟨8298256876422411725855635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11064342501896548967807513 8298256876422411725855635)
            ·
              refine ⟨12447385314633617588783453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8298256876422411725855635 12447385314633617588783453)
              ·
                refine ⟨4667769492987606595793795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12447385314633617588783453 4667769492987606595793795)
                ·
                  refine ⟨7001654239481409893690693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4667769492987606595793795 7001654239481409893690693)
                  ·
                    refine ⟨1312810169902764355067005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7001654239481409893690693 1312810169902764355067005)
                    ·
                      rfl

theorem cell23_7670066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 3, 1, 4].length) (baseStart_7670066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7670066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7670066 prefixEnd_7670066 := by exact prefixLift 7670066
  have htrace : WordTrace (prefixWord ++ tailWord_7670066) baseStart_7670066 baseEnd_7670066 := by
    simpa [prefixWord, tailWord_7670066, baseEnd_7670066] using wordTrace_append hprefix tailTrace_7670066
  have hstable : (prefixWord ++ tailWord_7670066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7670066).length < 2 ^ (prefixWord ++ tailWord_7670066).sum := by decide
  have hdescent : baseEnd_7670066 < baseStart_7670066 := by decide
  rcases family_descends (prefixWord ++ tailWord_7670066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7670095 : List Nat := [1, 1, 2, 1, 1, 2, 1, 4, 2, 6, 2]
def baseStart_7670095 : Nat := 118140960795 + 7670095 * 2 ^ 59
def prefixEnd_7670095 : Nat := 4983230072969 + 3 ^ 40 * 7670095 * 2
def baseEnd_7670095 : Nat := 3938445400647273451738381

theorem tailTrace_7670095 : CollatzResearch.WordTrace tailWord_7670095 prefixEnd_7670095 3938445400647273451738381 := by
  unfold tailWord_7670095
  simp only [CollatzResearch.WordTrace]
  refine ⟨279751347147563237780827739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186500898098375491853885159 279751347147563237780827739)
  ·
    refine ⟨419627020721344856671241609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279751347147563237780827739 419627020721344856671241609)
    ·
      refine ⟨314720265541008642503431207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 419627020721344856671241609 314720265541008642503431207)
      ·
        refine ⟨472080398311512963755146811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314720265541008642503431207 472080398311512963755146811)
        ·
          refine ⟨708120597467269445632720217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 472080398311512963755146811 708120597467269445632720217)
          ·
            refine ⟨531090448100452084224540163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 708120597467269445632720217 531090448100452084224540163)
            ·
              refine ⟨796635672150678126336810245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 531090448100452084224540163 796635672150678126336810245)
              ·
                refine ⟨149369188528252148688151921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 796635672150678126336810245 149369188528252148688151921)
                ·
                  refine ⟨112026891396189111516113941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 149369188528252148688151921 112026891396189111516113941)
                  ·
                    refine ⟨5251260534196364602317841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 112026891396189111516113941 5251260534196364602317841)
                    ·
                      refine ⟨3938445400647273451738381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5251260534196364602317841 3938445400647273451738381)
                      ·
                        rfl

theorem cell23_7670095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 6, 2].length) (baseStart_7670095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7670095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7670095 prefixEnd_7670095 := by exact prefixLift 7670095
  have htrace : WordTrace (prefixWord ++ tailWord_7670095) baseStart_7670095 baseEnd_7670095 := by
    simpa [prefixWord, tailWord_7670095, baseEnd_7670095] using wordTrace_append hprefix tailTrace_7670095
  have hstable : (prefixWord ++ tailWord_7670095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7670095).length < 2 ^ (prefixWord ++ tailWord_7670095).sum := by decide
  have hdescent : baseEnd_7670095 < baseStart_7670095 := by decide
  rcases family_descends (prefixWord ++ tailWord_7670095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7670110 : List Nat := [4, 4, 2, 1, 1, 1, 2, 1, 2, 2, 3]
def baseStart_7670110 : Nat := 118140960795 + 7670110 * 2 ^ 59
def prefixEnd_7670110 : Nat := 4983230072969 + 3 ^ 40 * 7670110 * 2
def baseEnd_7670110 : Nat := 3938453102857090893050813

theorem tailTrace_7670110 : CollatzResearch.WordTrace tailWord_7670110 prefixEnd_7670110 3938453102857090893050813 := by
  unfold tailWord_7670110
  simp only [CollatzResearch.WordTrace]
  refine ⟨34968986780313611917827973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186501262828339263561749189 34968986780313611917827973)
  ·
    refine ⟨6556685021308802234592745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34968986780313611917827973 6556685021308802234592745)
    ·
      refine ⟨4917513765981601675944559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6556685021308802234592745 4917513765981601675944559)
      ·
        refine ⟨7376270648972402513916839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4917513765981601675944559 7376270648972402513916839)
        ·
          refine ⟨11064405973458603770875259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7376270648972402513916839 11064405973458603770875259)
          ·
            refine ⟨16596608960187905656312889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11064405973458603770875259 16596608960187905656312889)
            ·
              refine ⟨12447456720140929242234667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16596608960187905656312889 12447456720140929242234667)
              ·
                refine ⟨18671185080211393863352001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12447456720140929242234667 18671185080211393863352001)
                ·
                  refine ⟨14003388810158545397514001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18671185080211393863352001 14003388810158545397514001)
                  ·
                    refine ⟨10502541607618909048135501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14003388810158545397514001 10502541607618909048135501)
                    ·
                      refine ⟨3938453102857090893050813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10502541607618909048135501 3938453102857090893050813)
                      ·
                        rfl

theorem cell23_7670110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_7670110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7670110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7670110 prefixEnd_7670110 := by exact prefixLift 7670110
  have htrace : WordTrace (prefixWord ++ tailWord_7670110) baseStart_7670110 baseEnd_7670110 := by
    simpa [prefixWord, tailWord_7670110, baseEnd_7670110] using wordTrace_append hprefix tailTrace_7670110
  have hstable : (prefixWord ++ tailWord_7670110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7670110).length < 2 ^ (prefixWord ++ tailWord_7670110).sum := by decide
  have hdescent : baseEnd_7670110 < baseStart_7670110 := by decide
  rcases family_descends (prefixWord ++ tailWord_7670110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7670112 : List Nat := [2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 4]
def baseStart_7670112 : Nat := 118140960795 + 7670112 * 2 ^ 59
def prefixEnd_7670112 : Nat := 4983230072969 + 3 ^ 40 * 7670112 * 2
def baseEnd_7670112 : Nat := 3938454129818399885225803

theorem tailTrace_7670112 : CollatzResearch.WordTrace tailWord_7670112 prefixEnd_7670112 3938454129818399885225803 := by
  unfold tailWord_7670112
  simp only [CollatzResearch.WordTrace]
  refine ⟨139875983594250824842098295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186501311459001099789464393 139875983594250824842098295)
  ·
    refine ⟨209813975391376237263147443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139875983594250824842098295 209813975391376237263147443)
    ·
      refine ⟨314720963087064355894721165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209813975391376237263147443 314720963087064355894721165)
      ·
        refine ⟨118020361157649133460520437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 314720963087064355894721165 118020361157649133460520437)
        ·
          refine ⟨11064408858529606261923791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 118020361157649133460520437 11064408858529606261923791)
          ·
            refine ⟨16596613287794409392885687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11064408858529606261923791 16596613287794409392885687)
            ·
              refine ⟨24894919931691614089328531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16596613287794409392885687 24894919931691614089328531)
              ·
                refine ⟨37342379897537421133992797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24894919931691614089328531 37342379897537421133992797)
                ·
                  refine ⟨14003392461576532925247299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37342379897537421133992797 14003392461576532925247299)
                  ·
                    refine ⟨21005088692364799387870949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14003392461576532925247299 21005088692364799387870949)
                    ·
                      refine ⟨3938454129818399885225803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21005088692364799387870949 3938454129818399885225803)
                      ·
                        rfl

theorem cell23_7670112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 4].length) (baseStart_7670112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7670112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7670112 prefixEnd_7670112 := by exact prefixLift 7670112
  have htrace : WordTrace (prefixWord ++ tailWord_7670112) baseStart_7670112 baseEnd_7670112 := by
    simpa [prefixWord, tailWord_7670112, baseEnd_7670112] using wordTrace_append hprefix tailTrace_7670112
  have hstable : (prefixWord ++ tailWord_7670112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7670112).length < 2 ^ (prefixWord ++ tailWord_7670112).sum := by decide
  have hdescent : baseEnd_7670112 < baseStart_7670112 := by decide
  rcases family_descends (prefixWord ++ tailWord_7670112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7670122 : List Nat := [3, 1, 3, 3, 1, 2, 1, 2, 1, 6]
def baseStart_7670122 : Nat := 118140960795 + 7670122 * 2 ^ 59
def prefixEnd_7670122 : Nat := 4983230072969 + 3 ^ 40 * 7670122 * 2
def baseEnd_7670122 : Nat := 1312819754874981615366919

theorem tailTrace_7670122 : CollatzResearch.WordTrace tailWord_7670122 prefixEnd_7670122 1312819754874981615366919 := by
  unfold tailWord_7670122
  simp only [CollatzResearch.WordTrace]
  refine ⟨69938082979616355348015155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186501554612310280928040413 69938082979616355348015155)
  ·
    refine ⟨104907124469424533022022733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69938082979616355348015155 104907124469424533022022733)
    ·
      refine ⟨39340171676034199883258525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104907124469424533022022733 39340171676034199883258525)
      ·
        refine ⟨14752564378512824956221947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39340171676034199883258525 14752564378512824956221947)
        ·
          refine ⟨22128846567769237434332921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14752564378512824956221947 22128846567769237434332921)
          ·
            refine ⟨16596634925826928075749691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22128846567769237434332921 16596634925826928075749691)
            ·
              refine ⟨24894952388740392113624537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16596634925826928075749691 24894952388740392113624537)
              ·
                refine ⟨18671214291555294085218403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24894952388740392113624537 18671214291555294085218403)
                ·
                  refine ⟨28006821437332941127827605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18671214291555294085218403 28006821437332941127827605)
                  ·
                    refine ⟨1312819754874981615366919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28006821437332941127827605 1312819754874981615366919)
                    ·
                      rfl

theorem cell23_7670122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 2, 1, 6].length) (baseStart_7670122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7670122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7670122 prefixEnd_7670122 := by exact prefixLift 7670122
  have htrace : WordTrace (prefixWord ++ tailWord_7670122) baseStart_7670122 baseEnd_7670122 := by
    simpa [prefixWord, tailWord_7670122, baseEnd_7670122] using wordTrace_append hprefix tailTrace_7670122
  have hstable : (prefixWord ++ tailWord_7670122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7670122).length < 2 ^ (prefixWord ++ tailWord_7670122).sum := by decide
  have hdescent : baseEnd_7670122 < baseStart_7670122 := by decide
  rcases family_descends (prefixWord ++ tailWord_7670122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7670175 : List Nat := [1, 1, 2, 5, 1, 1, 2, 1, 2, 2, 5]
def baseStart_7670175 : Nat := 118140960795 + 7670175 * 2 ^ 59
def prefixEnd_7670175 : Nat := 4983230072969 + 3 ^ 40 * 7670175 * 2
def baseEnd_7670175 : Nat := 3938486479099633138738013

theorem tailTrace_7670175 : CollatzResearch.WordTrace tailWord_7670175 prefixEnd_7670175 3938486479099633138738013 := by
  unfold tailWord_7670175
  simp only [CollatzResearch.WordTrace]
  refine ⟨279754264987273411443739979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186502843324848940962493319 279754264987273411443739979)
  ·
    refine ⟨419631397480910117165609969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279754264987273411443739979 419631397480910117165609969)
    ·
      refine ⟨314723548110682587874207477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 419631397480910117165609969 314723548110682587874207477)
      ·
        refine ⟨29505332635376492613206951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 314723548110682587874207477 29505332635376492613206951)
        ·
          refine ⟨44257998953064738919810427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29505332635376492613206951 44257998953064738919810427)
          ·
            refine ⟨66386998429597108379715641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44257998953064738919810427 66386998429597108379715641)
            ·
              refine ⟨49790248822197831284786731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66386998429597108379715641 49790248822197831284786731)
              ·
                refine ⟨74685373233296746927180097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49790248822197831284786731 74685373233296746927180097)
                ·
                  refine ⟨56014029924972560195385073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74685373233296746927180097 56014029924972560195385073)
                  ·
                    refine ⟨42010522443729420146538805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56014029924972560195385073 42010522443729420146538805)
                    ·
                      refine ⟨3938486479099633138738013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42010522443729420146538805 3938486479099633138738013)
                      ·
                        rfl

theorem cell23_7670175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_7670175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7670175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7670175 prefixEnd_7670175 := by exact prefixLift 7670175
  have htrace : WordTrace (prefixWord ++ tailWord_7670175) baseStart_7670175 baseEnd_7670175 := by
    simpa [prefixWord, tailWord_7670175, baseEnd_7670175] using wordTrace_append hprefix tailTrace_7670175
  have hstable : (prefixWord ++ tailWord_7670175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7670175).length < 2 ^ (prefixWord ++ tailWord_7670175).sum := by decide
  have hdescent : baseEnd_7670175 < baseStart_7670175 := by decide
  rcases family_descends (prefixWord ++ tailWord_7670175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7670202 : List Nat := [3, 1, 1, 1, 2, 1, 1, 4, 3, 4, 2]
def baseStart_7670202 : Nat := 118140960795 + 7670202 * 2 ^ 59
def prefixEnd_7670202 : Nat := 4983230072969 + 3 ^ 40 * 7670202 * 2
def baseEnd_7670202 : Nat := 3938500343077304533100389

theorem tailTrace_7670202 : CollatzResearch.WordTrace tailWord_7670202 prefixEnd_7670202 3938500343077304533100389 := by
  unfold tailWord_7670202
  simp only [CollatzResearch.WordTrace]
  refine ⟨69938812439543898763743215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186503499838783730036648573 69938812439543898763743215)
  ·
    refine ⟨104908218659315848145614823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69938812439543898763743215 104908218659315848145614823)
    ·
      refine ⟨157362327988973772218422235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104908218659315848145614823 157362327988973772218422235)
      ·
        refine ⟨236043491983460658327633353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157362327988973772218422235 236043491983460658327633353)
        ·
          refine ⟨177032618987595493745725015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236043491983460658327633353 177032618987595493745725015)
          ·
            refine ⟨265548928481393240618587523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177032618987595493745725015 265548928481393240618587523)
            ·
              refine ⟨398323392722089860927881285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265548928481393240618587523 398323392722089860927881285)
              ·
                refine ⟨74685636135391848923977741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 398323392722089860927881285 74685636135391848923977741)
                ·
                  refine ⟨28007113550771943346491653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74685636135391848923977741 28007113550771943346491653)
                  ·
                    refine ⟨5251333790769739377467185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28007113550771943346491653 5251333790769739377467185)
                    ·
                      refine ⟨3938500343077304533100389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5251333790769739377467185 3938500343077304533100389)
                      ·
                        rfl

theorem cell23_7670202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 3, 4, 2].length) (baseStart_7670202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7670202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7670202 prefixEnd_7670202 := by exact prefixLift 7670202
  have htrace : WordTrace (prefixWord ++ tailWord_7670202) baseStart_7670202 baseEnd_7670202 := by
    simpa [prefixWord, tailWord_7670202, baseEnd_7670202] using wordTrace_append hprefix tailTrace_7670202
  have hstable : (prefixWord ++ tailWord_7670202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7670202).length < 2 ^ (prefixWord ++ tailWord_7670202).sum := by decide
  have hdescent : baseEnd_7670202 < baseStart_7670202 := by decide
  rcases family_descends (prefixWord ++ tailWord_7670202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7670235 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 2, 9, 3]
def baseStart_7670235 : Nat := 118140960795 + 7670235 * 2 ^ 59
def prefixEnd_7670235 : Nat := 4983230072969 + 3 ^ 40 * 7670235 * 2
def baseEnd_7670235 : Nat := 3938517287938902903987737

theorem tailTrace_7670235 : CollatzResearch.WordTrace tailWord_7670235 prefixEnd_7670235 3938517287938902903987737 := by
  unfold tailWord_7670235
  simp only [CollatzResearch.WordTrace]
  refine ⟨279756453367056041690924159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186504302244704027793949439 279756453367056041690924159)
  ·
    refine ⟨419634680050584062536386239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279756453367056041690924159 419634680050584062536386239)
    ·
      refine ⟨629452020075876093804579359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419634680050584062536386239 629452020075876093804579359)
      ·
        refine ⟨944178030113814140706869039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 629452020075876093804579359 944178030113814140706869039)
        ·
          refine ⟨1416267045170721211060303559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 944178030113814140706869039 1416267045170721211060303559)
          ·
            refine ⟨2124400567756081816590455339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1416267045170721211060303559 2124400567756081816590455339)
            ·
              refine ⟨3186600851634122724885683009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2124400567756081816590455339 3186600851634122724885683009)
              ·
                refine ⟨2389950638725592043664262257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3186600851634122724885683009 2389950638725592043664262257)
                ·
                  refine ⟨1792462979044194032748196693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2389950638725592043664262257 1792462979044194032748196693)
                  ·
                    refine ⟨10502712767837074410633965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 1792462979044194032748196693 10502712767837074410633965)
                    ·
                      refine ⟨3938517287938902903987737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10502712767837074410633965 3938517287938902903987737)
                      ·
                        rfl

theorem cell23_7670235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 9, 3].length) (baseStart_7670235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7670235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7670235 prefixEnd_7670235 := by exact prefixLift 7670235
  have htrace : WordTrace (prefixWord ++ tailWord_7670235) baseStart_7670235 baseEnd_7670235 := by
    simpa [prefixWord, tailWord_7670235, baseEnd_7670235] using wordTrace_append hprefix tailTrace_7670235
  have hstable : (prefixWord ++ tailWord_7670235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7670235).length < 2 ^ (prefixWord ++ tailWord_7670235).sum := by decide
  have hdescent : baseEnd_7670235 < baseStart_7670235 := by decide
  rcases family_descends (prefixWord ++ tailWord_7670235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7670259 : List Nat := [1, 1, 1, 2, 2, 2, 7, 2, 5]
def baseStart_7670259 : Nat := 118140960795 + 7670259 * 2 ^ 59
def prefixEnd_7670259 : Nat := 4983230072969 + 3 ^ 40 * 7670259 * 2
def baseEnd_7670259 : Nat := 437614401274956756676403

theorem tailTrace_7670259 : CollatzResearch.WordTrace tailWord_7670259 prefixEnd_7670259 437614401274956756676403 := by
  unfold tailWord_7670259
  simp only [CollatzResearch.WordTrace]
  refine ⟨279757328718969093789797831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186504885812646062526531887 279757328718969093789797831)
  ·
    refine ⟨419635993078453640684696747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279757328718969093789797831 419635993078453640684696747)
    ·
      refine ⟨629453989617680461027045121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419635993078453640684696747 629453989617680461027045121)
      ·
        refine ⟨472090492213260345770283841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 629453989617680461027045121 472090492213260345770283841)
        ·
          refine ⟨354067869159945259327712881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 472090492213260345770283841 354067869159945259327712881)
          ·
            refine ⟨265550901869958944495784661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 354067869159945259327712881 265550901869958944495784661)
            ·
              refine ⟨6223849262577162761619953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 265550901869958944495784661 6223849262577162761619953)
              ·
                refine ⟨4667886946932872071214965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6223849262577162761619953 4667886946932872071214965)
                ·
                  refine ⟨437614401274956756676403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4667886946932872071214965 437614401274956756676403)
                  ·
                    rfl

theorem cell23_7670259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 7, 2, 5].length) (baseStart_7670259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7670259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7670259 prefixEnd_7670259 := by exact prefixLift 7670259
  have htrace : WordTrace (prefixWord ++ tailWord_7670259) baseStart_7670259 baseEnd_7670259 := by
    simpa [prefixWord, tailWord_7670259, baseEnd_7670259] using wordTrace_append hprefix tailTrace_7670259
  have hstable : (prefixWord ++ tailWord_7670259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7670259).length < 2 ^ (prefixWord ++ tailWord_7670259).sum := by decide
  have hdescent : baseEnd_7670259 < baseStart_7670259 := by decide
  rcases family_descends (prefixWord ++ tailWord_7670259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7670265 : List Nat := [1, 2, 1, 3, 1, 2, 3, 1, 1, 1, 7]
def baseStart_7670265 : Nat := 118140960795 + 7670265 * 2 ^ 59
def prefixEnd_7670265 : Nat := 4983230072969 + 3 ^ 40 * 7670265 * 2
def baseEnd_7670265 : Nat := 3938532692358537786612599

theorem tailTrace_7670265 : CollatzResearch.WordTrace tailWord_7670265 prefixEnd_7670265 3938532692358537786612599 := by
  unfold tailWord_7670265
  simp only [CollatzResearch.WordTrace]
  refine ⟨279757547556947356814516249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186505031704631571209677499 279757547556947356814516249)
  ·
    refine ⟨209818160667710517610887187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279757547556947356814516249 209818160667710517610887187)
    ·
      refine ⟨314727241001565776416330781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209818160667710517610887187 314727241001565776416330781)
      ·
        refine ⟨118022715375587166156124043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 314727241001565776416330781 118022715375587166156124043)
        ·
          refine ⟨177034073063380749234186065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118022715375587166156124043 177034073063380749234186065)
          ·
            refine ⟨132775554797535561925639549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177034073063380749234186065 132775554797535561925639549)
            ·
              refine ⟨49790833049075835722114831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132775554797535561925639549 49790833049075835722114831)
              ·
                refine ⟨74686249573613753583172247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49790833049075835722114831 74686249573613753583172247)
                ·
                  refine ⟨112029374360420630374758371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74686249573613753583172247 112029374360420630374758371)
                  ·
                    refine ⟨168044061540630945562137557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 112029374360420630374758371 168044061540630945562137557)
                    ·
                      refine ⟨3938532692358537786612599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 168044061540630945562137557 3938532692358537786612599)
                      ·
                        rfl

theorem cell23_7670265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 1, 7].length) (baseStart_7670265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7670265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7670265 prefixEnd_7670265 := by exact prefixLift 7670265
  have htrace : WordTrace (prefixWord ++ tailWord_7670265) baseStart_7670265 baseEnd_7670265 := by
    simpa [prefixWord, tailWord_7670265, baseEnd_7670265] using wordTrace_append hprefix tailTrace_7670265
  have hstable : (prefixWord ++ tailWord_7670265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7670265).length < 2 ^ (prefixWord ++ tailWord_7670265).sum := by decide
  have hdescent : baseEnd_7670265 < baseStart_7670265 := by decide
  rcases family_descends (prefixWord ++ tailWord_7670265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7670315 : List Nat := [1, 1, 1, 1, 2, 1, 3, 5, 8]
def baseStart_7670315 : Nat := 118140960795 + 7670315 * 2 ^ 59
def prefixEnd_7670315 : Nat := 4983230072969 + 3 ^ 40 * 7670315 * 2
def baseEnd_7670315 : Nat := 437617596265695843443041

theorem tailTrace_7670315 : CollatzResearch.WordTrace tailWord_7670315 prefixEnd_7670315 437617596265695843443041 := by
  unfold tailWord_7670315
  simp only [CollatzResearch.WordTrace]
  refine ⟨279759371206766215353836399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186506247471177476902557599 279759371206766215353836399)
  ·
    refine ⟨419639056810149323030754599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279759371206766215353836399 419639056810149323030754599)
    ·
      refine ⟨629458585215223984546131899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419639056810149323030754599 629458585215223984546131899)
      ·
        refine ⟨944187877822835976819197849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 629458585215223984546131899 944187877822835976819197849)
        ·
          refine ⟨708140908367126982614398387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 944187877822835976819197849 708140908367126982614398387)
          ·
            refine ⟨1062211362550690473921597581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 708140908367126982614398387 1062211362550690473921597581)
            ·
              refine ⟨398329260956508927720599093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1062211362550690473921597581 398329260956508927720599093)
              ·
                refine ⟨37343368214672711973806165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 398329260956508927720599093 37343368214672711973806165)
                ·
                  refine ⟨437617596265695843443041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37343368214672711973806165 437617596265695843443041)
                  ·
                    rfl

theorem cell23_7670315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 5, 8].length) (baseStart_7670315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7670315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7670315 prefixEnd_7670315 := by exact prefixLift 7670315
  have htrace : WordTrace (prefixWord ++ tailWord_7670315) baseStart_7670315 baseEnd_7670315 := by
    simpa [prefixWord, tailWord_7670315, baseEnd_7670315] using wordTrace_append hprefix tailTrace_7670315
  have hstable : (prefixWord ++ tailWord_7670315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7670315).length < 2 ^ (prefixWord ++ tailWord_7670315).sum := by decide
  have hdescent : baseEnd_7670315 < baseStart_7670315 := by decide
  rcases family_descends (prefixWord ++ tailWord_7670315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7670326 : List Nat := [5, 1, 2, 1, 2, 1, 1, 1, 1, 6, 2]
def baseStart_7670326 : Nat := 118140960795 + 7670326 * 2 ^ 59
def prefixEnd_7670326 : Nat := 4983230072969 + 3 ^ 40 * 7670326 * 2
def baseEnd_7670326 : Nat := 3938564014678462047949819

theorem tailTrace_7670326 : CollatzResearch.WordTrace tailWord_7670326 prefixEnd_7670326 3938564014678462047949819 := by
  unfold tailWord_7670326
  simp only [CollatzResearch.WordTrace]
  refine ⟨17484985775607897764530427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 186506514939817576154991221 17484985775607897764530427)
  ·
    refine ⟨26227478663411846646795641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17484985775607897764530427 26227478663411846646795641)
    ·
      refine ⟨19670608997558884985096731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26227478663411846646795641 19670608997558884985096731)
      ·
        refine ⟨29505913496338327477645097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19670608997558884985096731 29505913496338327477645097)
        ·
          refine ⟨22129435122253745608233823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29505913496338327477645097 22129435122253745608233823)
          ·
            refine ⟨33194152683380618412350735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22129435122253745608233823 33194152683380618412350735)
            ·
              refine ⟨49791229025070927618526103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33194152683380618412350735 49791229025070927618526103)
              ·
                refine ⟨74686843537606391427789155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49791229025070927618526103 74686843537606391427789155)
                ·
                  refine ⟨112030265306409587141683733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74686843537606391427789155 112030265306409587141683733)
                  ·
                    refine ⟨5251418686237949397266425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 112030265306409587141683733 5251418686237949397266425)
                    ·
                      refine ⟨3938564014678462047949819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5251418686237949397266425 3938564014678462047949819)
                      ·
                        rfl

theorem cell23_7670326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 1, 6, 2].length) (baseStart_7670326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7670326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7670326 prefixEnd_7670326 := by exact prefixLift 7670326
  have htrace : WordTrace (prefixWord ++ tailWord_7670326) baseStart_7670326 baseEnd_7670326 := by
    simpa [prefixWord, tailWord_7670326, baseEnd_7670326] using wordTrace_append hprefix tailTrace_7670326
  have hstable : (prefixWord ++ tailWord_7670326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7670326).length < 2 ^ (prefixWord ++ tailWord_7670326).sum := by decide
  have hdescent : baseEnd_7670326 < baseStart_7670326 := by decide
  rcases family_descends (prefixWord ++ tailWord_7670326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7670340 : List Nat := [2, 3, 5, 1, 1, 2, 1, 1, 2, 5]
def baseStart_7670340 : Nat := 118140960795 + 7670340 * 2 ^ 59
def prefixEnd_7670340 : Nat := 4983230072969 + 3 ^ 40 * 7670340 * 2
def baseEnd_7670340 : Nat := 1312857067802541664391585

theorem tailTrace_7670340 : CollatzResearch.WordTrace tailWord_7670340 prefixEnd_7670340 1312857067802541664391585 := by
  unfold tailWord_7670340
  simp only [CollatzResearch.WordTrace]
  refine ⟨139880141515837822311748237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186506855354450429748997649 139880141515837822311748237)
  ·
    refine ⟨52455053068439183366905589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139880141515837822311748237 52455053068439183366905589)
    ·
      refine ⟨4917661225166173440647399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52455053068439183366905589 4917661225166173440647399)
      ·
        refine ⟨7376491837749260160971099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4917661225166173440647399 7376491837749260160971099)
        ·
          refine ⟨11064737756623890241456649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7376491837749260160971099 11064737756623890241456649)
          ·
            refine ⟨8298553317467917681092487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11064737756623890241456649 8298553317467917681092487)
            ·
              refine ⟨12447829976201876521638731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8298553317467917681092487 12447829976201876521638731)
              ·
                refine ⟨18671744964302814782458097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12447829976201876521638731 18671744964302814782458097)
                ·
                  refine ⟨14003808723227111086843573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18671744964302814782458097 14003808723227111086843573)
                  ·
                    refine ⟨1312857067802541664391585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14003808723227111086843573 1312857067802541664391585)
                    ·
                      rfl

theorem cell23_7670340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_7670340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7670340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7670340 prefixEnd_7670340 := by exact prefixLift 7670340
  have htrace : WordTrace (prefixWord ++ tailWord_7670340) baseStart_7670340 baseEnd_7670340 := by
    simpa [prefixWord, tailWord_7670340, baseEnd_7670340] using wordTrace_append hprefix tailTrace_7670340
  have hstable : (prefixWord ++ tailWord_7670340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7670340).length < 2 ^ (prefixWord ++ tailWord_7670340).sum := by decide
  have hdescent : baseEnd_7670340 < baseStart_7670340 := by decide
  rcases family_descends (prefixWord ++ tailWord_7670340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7670346 : List Nat := [3, 1, 2, 1, 1, 6, 1, 1, 2, 2, 3]
def baseStart_7670346 : Nat := 118140960795 + 7670346 * 2 ^ 59
def prefixEnd_7670346 : Nat := 4983230072969 + 3 ^ 40 * 7670346 * 2
def baseEnd_7670346 : Nat := 3938574284291551969699727

theorem tailTrace_7670346 : CollatzResearch.WordTrace tailWord_7670346 prefixEnd_7670346 3938574284291551969699727 := by
  unfold tailWord_7670346
  simp only [CollatzResearch.WordTrace]
  refine ⟨69940125467413476912053723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186507001246435938432143261 69940125467413476912053723)
  ·
    refine ⟨104910188201120215368080585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69940125467413476912053723 104910188201120215368080585)
    ·
      refine ⟨78682641150840161526060439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104910188201120215368080585 78682641150840161526060439)
      ·
        refine ⟨118023961726260242289090659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78682641150840161526060439 118023961726260242289090659)
        ·
          refine ⟨177035942589390363433635989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118023961726260242289090659 177035942589390363433635989)
          ·
            refine ⟨8298559808877673285951687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 177035942589390363433635989 8298559808877673285951687)
            ·
              refine ⟨12447839713316509928927531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8298559808877673285951687 12447839713316509928927531)
              ·
                refine ⟨18671759569974764893391297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12447839713316509928927531 18671759569974764893391297)
                ·
                  refine ⟨14003819677481073670043473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18671759569974764893391297 14003819677481073670043473)
                  ·
                    refine ⟨10502864758110805252532605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14003819677481073670043473 10502864758110805252532605)
                    ·
                      refine ⟨3938574284291551969699727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10502864758110805252532605 3938574284291551969699727)
                      ·
                        rfl

theorem cell23_7670346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 1, 2, 2, 3].length) (baseStart_7670346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7670346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7670346 prefixEnd_7670346 := by exact prefixLift 7670346
  have htrace : WordTrace (prefixWord ++ tailWord_7670346) baseStart_7670346 baseEnd_7670346 := by
    simpa [prefixWord, tailWord_7670346, baseEnd_7670346] using wordTrace_append hprefix tailTrace_7670346
  have hstable : (prefixWord ++ tailWord_7670346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7670346).length < 2 ^ (prefixWord ++ tailWord_7670346).sum := by decide
  have hdescent : baseEnd_7670346 < baseStart_7670346 := by decide
  rcases family_descends (prefixWord ++ tailWord_7670346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7670359 : List Nat := [1, 1, 3, 2, 2, 2, 1, 2, 5, 1, 3]
def baseStart_7670359 : Nat := 118140960795 + 7670359 * 2 ^ 59
def prefixEnd_7670359 : Nat := 4983230072969 + 3 ^ 40 * 7670359 * 2
def baseEnd_7670359 : Nat := 3938580959540060418837167

theorem tailTrace_7670359 : CollatzResearch.WordTrace tailWord_7670359 prefixEnd_7670359 3938580959540060418837167 := by
  unfold tailWord_7670359
  simp only [CollatzResearch.WordTrace]
  refine ⟨279760976018606810868438131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186507317345737873912292087 279760976018606810868438131)
  ·
    refine ⟨419641464027910216302657197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279760976018606810868438131 419641464027910216302657197)
    ·
      refine ⟨157365549010466331113496449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 419641464027910216302657197 157365549010466331113496449)
      ·
        refine ⟨118024161757849748335122337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157365549010466331113496449 118024161757849748335122337)
        ·
          refine ⟨88518121318387311251341753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118024161757849748335122337 88518121318387311251341753)
          ·
            refine ⟨66388590988790483438506315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88518121318387311251341753 66388590988790483438506315)
            ·
              refine ⟨99582886483185725157759473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66388590988790483438506315 99582886483185725157759473)
              ·
                refine ⟨74687164862389293868319605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99582886483185725157759473 74687164862389293868319605)
                ·
                  refine ⟨7001921705848996300154963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74687164862389293868319605 7001921705848996300154963)
                  ·
                    refine ⟨10502882558773494450232445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7001921705848996300154963 10502882558773494450232445)
                    ·
                      refine ⟨3938580959540060418837167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10502882558773494450232445 3938580959540060418837167)
                      ·
                        rfl

theorem cell23_7670359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 5, 1, 3].length) (baseStart_7670359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7670359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7670359 prefixEnd_7670359 := by exact prefixLift 7670359
  have htrace : WordTrace (prefixWord ++ tailWord_7670359) baseStart_7670359 baseEnd_7670359 := by
    simpa [prefixWord, tailWord_7670359, baseEnd_7670359] using wordTrace_append hprefix tailTrace_7670359
  have hstable : (prefixWord ++ tailWord_7670359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7670359).length < 2 ^ (prefixWord ++ tailWord_7670359).sum := by decide
  have hdescent : baseEnd_7670359 < baseStart_7670359 := by decide
  rcases family_descends (prefixWord ++ tailWord_7670359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7670446 : List Nat := [4, 1, 4, 1, 1, 1, 2, 1, 1, 1, 6]
def baseStart_7670446 : Nat := 118140960795 + 7670446 * 2 ^ 59
def prefixEnd_7670446 : Nat := 4983230072969 + 3 ^ 40 * 7670446 * 2
def baseEnd_7670446 : Nat := 3938625632357001578449267

theorem tailTrace_7670446 : CollatzResearch.WordTrace tailWord_7670446 prefixEnd_7670446 3938625632357001578449267 := by
  unfold tailWord_7670446
  simp only [CollatzResearch.WordTrace]
  refine ⟨34970518646161453090856899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186509432779527749817903461 34970518646161453090856899)
  ·
    refine ⟨52455777969242179636285349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34970518646161453090856899 52455777969242179636285349)
    ·
      refine ⟨9835458369232908681803503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52455777969242179636285349 9835458369232908681803503)
      ·
        refine ⟨14753187553849363022705255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9835458369232908681803503 14753187553849363022705255)
        ·
          refine ⟨22129781330774044534057883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14753187553849363022705255 22129781330774044534057883)
          ·
            refine ⟨33194671996161066801086825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22129781330774044534057883 33194671996161066801086825)
            ·
              refine ⟨24896003997120800100815119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33194671996161066801086825 24896003997120800100815119)
              ·
                refine ⟨37344005995681200151222679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24896003997120800100815119 37344005995681200151222679)
                ·
                  refine ⟨56016008993521800226834019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37344005995681200151222679 56016008993521800226834019)
                  ·
                    refine ⟨84024013490282700340251029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56016008993521800226834019 84024013490282700340251029)
                    ·
                      refine ⟨3938625632357001578449267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84024013490282700340251029 3938625632357001578449267)
                      ·
                        rfl

theorem cell23_7670446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_7670446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7670446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7670446 prefixEnd_7670446 := by exact prefixLift 7670446
  have htrace : WordTrace (prefixWord ++ tailWord_7670446) baseStart_7670446 baseEnd_7670446 := by
    simpa [prefixWord, tailWord_7670446, baseEnd_7670446] using wordTrace_append hprefix tailTrace_7670446
  have hstable : (prefixWord ++ tailWord_7670446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7670446).length < 2 ^ (prefixWord ++ tailWord_7670446).sum := by decide
  have hdescent : baseEnd_7670446 < baseStart_7670446 := by decide
  rcases family_descends (prefixWord ++ tailWord_7670446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7670453 : List Nat := [1, 3, 3, 3, 1, 1, 3, 2, 1, 2, 3]
def baseStart_7670453 : Nat := 118140960795 + 7670453 * 2 ^ 59
def prefixEnd_7670453 : Nat := 4983230072969 + 3 ^ 40 * 7670453 * 2
def baseEnd_7670453 : Nat := 3938629226721583051061735

theorem tailTrace_7670453 : CollatzResearch.WordTrace tailWord_7670453 prefixEnd_7670453 3938629226721583051061735 := by
  unfold tailWord_7670453
  simp only [CollatzResearch.WordTrace]
  refine ⟨279764404480266264922360013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186509602986844176614906675 279764404480266264922360013)
  ·
    refine ⟨104911651680099849345885005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 279764404480266264922360013 104911651680099849345885005)
    ·
      refine ⟨39341869380037443504706877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104911651680099849345885005 39341869380037443504706877)
      ·
        refine ⟨14753201017514041314265079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39341869380037443504706877 14753201017514041314265079)
        ·
          refine ⟨22129801526271061971397619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14753201017514041314265079 22129801526271061971397619)
          ·
            refine ⟨33194702289406592957096429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22129801526271061971397619 33194702289406592957096429)
            ·
              refine ⟨12448013358527472358911161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33194702289406592957096429 12448013358527472358911161)
              ·
                refine ⟨9336010018895604269183371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12448013358527472358911161 9336010018895604269183371)
                ·
                  refine ⟨14004015028343406403775057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9336010018895604269183371 14004015028343406403775057)
                  ·
                    refine ⟨10503011271257554802831293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14004015028343406403775057 10503011271257554802831293)
                    ·
                      refine ⟨3938629226721583051061735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10503011271257554802831293 3938629226721583051061735)
                      ·
                        rfl

theorem cell23_7670453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_7670453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7670453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7670453 prefixEnd_7670453 := by exact prefixLift 7670453
  have htrace : WordTrace (prefixWord ++ tailWord_7670453) baseStart_7670453 baseEnd_7670453 := by
    simpa [prefixWord, tailWord_7670453, baseEnd_7670453] using wordTrace_append hprefix tailTrace_7670453
  have hstable : (prefixWord ++ tailWord_7670453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7670453).length < 2 ^ (prefixWord ++ tailWord_7670453).sum := by decide
  have hdescent : baseEnd_7670453 < baseStart_7670453 := by decide
  rcases family_descends (prefixWord ++ tailWord_7670453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7670499 : List Nat := [1, 1, 1, 7, 1, 1, 1, 1, 1, 8]
def baseStart_7670499 : Nat := 118140960795 + 7670499 * 2 ^ 59
def prefixEnd_7670499 : Nat := 4983230072969 + 3 ^ 40 * 7670499 * 2
def baseEnd_7670499 : Nat := 1312884282277229957028841

theorem tailTrace_7670499 : CollatzResearch.WordTrace tailWord_7670499 prefixEnd_7670499 1312884282277229957028841 := by
  unfold tailWord_7670499
  simp only [CollatzResearch.WordTrace]
  refine ⟨279766082238099614778534551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186510721492066409852356367 279766082238099614778534551)
  ·
    refine ⟨419649123357149422167801827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279766082238099614778534551 419649123357149422167801827)
    ·
      refine ⟨629473685035724133251702741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419649123357149422167801827 629473685035724133251702741)
      ·
        refine ⟨14753289493024784373086783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 629473685035724133251702741 14753289493024784373086783)
        ·
          refine ⟨22129934239537176559630175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14753289493024784373086783 22129934239537176559630175)
          ·
            refine ⟨33194901359305764839445263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22129934239537176559630175 33194901359305764839445263)
            ·
              refine ⟨49792352038958647259167895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33194901359305764839445263 49792352038958647259167895)
              ·
                refine ⟨74688528058437970888751843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49792352038958647259167895 74688528058437970888751843)
                ·
                  refine ⟨112032792087656956333127765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74688528058437970888751843 112032792087656956333127765)
                  ·
                    refine ⟨1312884282277229957028841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 112032792087656956333127765 1312884282277229957028841)
                    ·
                      rfl

theorem cell23_7670499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 8].length) (baseStart_7670499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7670499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7670499 prefixEnd_7670499 := by exact prefixLift 7670499
  have htrace : WordTrace (prefixWord ++ tailWord_7670499) baseStart_7670499 baseEnd_7670499 := by
    simpa [prefixWord, tailWord_7670499, baseEnd_7670499] using wordTrace_append hprefix tailTrace_7670499
  have hstable : (prefixWord ++ tailWord_7670499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7670499).length < 2 ^ (prefixWord ++ tailWord_7670499).sum := by decide
  have hdescent : baseEnd_7670499 < baseStart_7670499 := by decide
  rcases family_descends (prefixWord ++ tailWord_7670499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7670556 : List Nat := [2, 2, 3, 1, 1, 3, 2, 1, 2, 3, 3]
def baseStart_7670556 : Nat := 118140960795 + 7670556 * 2 ^ 59
def prefixEnd_7670556 : Nat := 4983230072969 + 3 ^ 40 * 7670556 * 2
def baseEnd_7670556 : Nat := 3938682115228996148073761

theorem tailTrace_7670556 : CollatzResearch.WordTrace tailWord_7670556 prefixEnd_7670556 3938682115228996148073761 := by
  unfold tailWord_7670556
  simp only [CollatzResearch.WordTrace]
  refine ⟨139884080599446556756679761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186512107465928742342239681 139884080599446556756679761)
  ·
    refine ⟨104913060449584917567509821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139884080599446556756679761 104913060449584917567509821)
    ·
      refine ⟨39342397668594344087816183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104913060449584917567509821 39342397668594344087816183)
      ·
        refine ⟨59013596502891516131724275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39342397668594344087816183 59013596502891516131724275)
        ·
          refine ⟨88520394754337274197586413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59013596502891516131724275 88520394754337274197586413)
          ·
            refine ⟨33195148032876477824094905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88520394754337274197586413 33195148032876477824094905)
            ·
              refine ⟨24896361024657358368071179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33195148032876477824094905 24896361024657358368071179)
              ·
                refine ⟨37344541536986037552106769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24896361024657358368071179 37344541536986037552106769)
                ·
                  refine ⟨28008406152739528164080077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37344541536986037552106769 28008406152739528164080077)
                  ·
                    refine ⟨10503152307277323061530029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28008406152739528164080077 10503152307277323061530029)
                    ·
                      refine ⟨3938682115228996148073761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10503152307277323061530029 3938682115228996148073761)
                      ·
                        rfl

theorem cell23_7670556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 1, 2, 3, 3].length) (baseStart_7670556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7670556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7670556 prefixEnd_7670556 := by exact prefixLift 7670556
  have htrace : WordTrace (prefixWord ++ tailWord_7670556) baseStart_7670556 baseEnd_7670556 := by
    simpa [prefixWord, tailWord_7670556, baseEnd_7670556] using wordTrace_append hprefix tailTrace_7670556
  have hstable : (prefixWord ++ tailWord_7670556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7670556).length < 2 ^ (prefixWord ++ tailWord_7670556).sum := by decide
  have hdescent : baseEnd_7670556 < baseStart_7670556 := by decide
  rcases family_descends (prefixWord ++ tailWord_7670556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7670557 : List Nat := [1, 4, 2, 4, 1, 2, 1, 1, 1, 4, 2]
def baseStart_7670557 : Nat := 118140960795 + 7670557 * 2 ^ 59
def prefixEnd_7670557 : Nat := 4983230072969 + 3 ^ 40 * 7670557 * 2
def baseEnd_7670557 : Nat := 3938682628709650644161257

theorem tailTrace_7670557 : CollatzResearch.WordTrace tailWord_7670557 prefixEnd_7670557 3938682628709650644161257 := by
  unfold tailWord_7670557
  simp only [CollatzResearch.WordTrace]
  refine ⟨279768197671889490684145925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186512131781259660456097283 279768197671889490684145925)
  ·
    refine ⟨52456537063479279503277361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 279768197671889490684145925 52456537063479279503277361)
    ·
      refine ⟨39342402797609459627458021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52456537063479279503277361 39342402797609459627458021)
      ·
        refine ⟨7376700524551773680148379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39342402797609459627458021 7376700524551773680148379)
        ·
          refine ⟨11065050786827660520222569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7376700524551773680148379 11065050786827660520222569)
          ·
            refine ⟨8298788090120745390166927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11065050786827660520222569 8298788090120745390166927)
            ·
              refine ⟨12448182135181118085250391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8298788090120745390166927 12448182135181118085250391)
              ·
                refine ⟨18672273202771677127875587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12448182135181118085250391 18672273202771677127875587)
                ·
                  refine ⟨28008409804157515691813381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18672273202771677127875587 28008409804157515691813381)
                  ·
                    refine ⟨5251576838279534192215009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28008409804157515691813381 5251576838279534192215009)
                    ·
                      refine ⟨3938682628709650644161257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5251576838279534192215009 3938682628709650644161257)
                      ·
                        rfl

theorem cell23_7670557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_7670557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7670557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7670557 prefixEnd_7670557 := by exact prefixLift 7670557
  have htrace : WordTrace (prefixWord ++ tailWord_7670557) baseStart_7670557 baseEnd_7670557 := by
    simpa [prefixWord, tailWord_7670557, baseEnd_7670557] using wordTrace_append hprefix tailTrace_7670557
  have hstable : (prefixWord ++ tailWord_7670557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7670557).length < 2 ^ (prefixWord ++ tailWord_7670557).sum := by decide
  have hdescent : baseEnd_7670557 < baseStart_7670557 := by decide
  rcases family_descends (prefixWord ++ tailWord_7670557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7670559 : List Nat := [1, 1, 2, 4, 2, 2, 1, 2, 1, 7]
def baseStart_7670559 : Nat := 118140960795 + 7670559 * 2 ^ 59
def prefixEnd_7670559 : Nat := 4983230072969 + 3 ^ 40 * 7670559 * 2
def baseEnd_7670559 : Nat := 1312894551890319878778749

theorem tailTrace_7670559 : CollatzResearch.WordTrace tailWord_7670559 prefixEnd_7670559 1312894551890319878778749 := by
  unfold tailWord_7670559
  simp only [CollatzResearch.WordTrace]
  refine ⟨279768270617882245025718731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186512180411921496683812487 279768270617882245025718731)
  ·
    refine ⟨419652405926823367538578097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279768270617882245025718731 419652405926823367538578097)
    ·
      refine ⟨314739304445117525653933573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 419652405926823367538578097 314739304445117525653933573)
      ·
        refine ⟨59013619583459536060112545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 314739304445117525653933573 59013619583459536060112545)
        ·
          refine ⟨44260214687594652045084409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59013619583459536060112545 44260214687594652045084409)
          ·
            refine ⟨33195161015695989033813307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44260214687594652045084409 33195161015695989033813307)
            ·
              refine ⟨49792741523543983550719961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33195161015695989033813307 49792741523543983550719961)
              ·
                refine ⟨37344556142657987663039971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49792741523543983550719961 37344556142657987663039971)
                ·
                  refine ⟨56016834213986981494559957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37344556142657987663039971 56016834213986981494559957)
                  ·
                    refine ⟨1312894551890319878778749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56016834213986981494559957 1312894551890319878778749)
                    ·
                      rfl

theorem cell23_7670559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 2, 1, 7].length) (baseStart_7670559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7670559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7670559 prefixEnd_7670559 := by exact prefixLift 7670559
  have htrace : WordTrace (prefixWord ++ tailWord_7670559) baseStart_7670559 baseEnd_7670559 := by
    simpa [prefixWord, tailWord_7670559, baseEnd_7670559] using wordTrace_append hprefix tailTrace_7670559
  have hstable : (prefixWord ++ tailWord_7670559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7670559).length < 2 ^ (prefixWord ++ tailWord_7670559).sum := by decide
  have hdescent : baseEnd_7670559 < baseStart_7670559 := by decide
  rcases family_descends (prefixWord ++ tailWord_7670559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7670676 : List Nat := [2, 4, 2, 1, 1, 1, 1, 1, 2, 1, 7]
def baseStart_7670676 : Nat := 118140960795 + 7670676 * 2 ^ 59
def prefixEnd_7670676 : Nat := 4983230072969 + 3 ^ 40 * 7670676 * 2
def baseEnd_7670676 : Nat := 3938743732907535678573209

theorem tailTrace_7670676 : CollatzResearch.WordTrace tailWord_7670676 prefixEnd_7670676 3938743732907535678573209 := by
  unfold tailWord_7670676
  simp only [CollatzResearch.WordTrace]
  refine ⟨139886268979229187003863941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186515025305638916005151921 139886268979229187003863941)
  ·
    refine ⟨26228675433605472563224489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139886268979229187003863941 26228675433605472563224489)
    ·
      refine ⟨19671506575204104422418367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26228675433605472563224489 19671506575204104422418367)
      ·
        refine ⟨29507259862806156633627551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19671506575204104422418367 29507259862806156633627551)
        ·
          refine ⟨44260889794209234950441327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29507259862806156633627551 44260889794209234950441327)
          ·
            refine ⟨66391334691313852425661991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44260889794209234950441327 66391334691313852425661991)
            ·
              refine ⟨99587002036970778638492987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66391334691313852425661991 99587002036970778638492987)
              ·
                refine ⟨149380503055456167957739481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99587002036970778638492987 149380503055456167957739481)
                ·
                  refine ⟨112035377291592125968304611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 149380503055456167957739481 112035377291592125968304611)
                  ·
                    refine ⟨168053065937388188952456917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 112035377291592125968304611 168053065937388188952456917)
                    ·
                      refine ⟨3938743732907535678573209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 168053065937388188952456917 3938743732907535678573209)
                      ·
                        rfl

theorem cell23_7670676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_7670676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7670676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7670676 prefixEnd_7670676 := by exact prefixLift 7670676
  have htrace : WordTrace (prefixWord ++ tailWord_7670676) baseStart_7670676 baseEnd_7670676 := by
    simpa [prefixWord, tailWord_7670676, baseEnd_7670676] using wordTrace_append hprefix tailTrace_7670676
  have hstable : (prefixWord ++ tailWord_7670676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7670676).length < 2 ^ (prefixWord ++ tailWord_7670676).sum := by decide
  have hdescent : baseEnd_7670676 < baseStart_7670676 := by decide
  rcases family_descends (prefixWord ++ tailWord_7670676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7670690 : List Nat := [3, 3, 1, 2, 2, 2, 1, 1, 1, 5, 2]
def baseStart_7670690 : Nat := 118140960795 + 7670690 * 2 ^ 59
def prefixEnd_7670690 : Nat := 4983230072969 + 3 ^ 40 * 7670690 * 2
def baseEnd_7670690 : Nat := 3938750921636698623798145

theorem tailTrace_7670690 : CollatzResearch.WordTrace tailWord_7670690 prefixEnd_7670690 3938750921636698623798145 := by
  unfold tailWord_7670690
  simp only [CollatzResearch.WordTrace]
  refine ⟨69943262145101913599684381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186515365720271769599158349 69943262145101913599684381)
  ·
    refine ⟨26228723304413217599881643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69943262145101913599684381 26228723304413217599881643)
    ·
      refine ⟨39343084956619826399822465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26228723304413217599881643 39343084956619826399822465)
      ·
        refine ⟨29507313717464869799866849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39343084956619826399822465 29507313717464869799866849)
        ·
          refine ⟨22130485288098652349900137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29507313717464869799866849 22130485288098652349900137)
          ·
            refine ⟨16597863966073989262425103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22130485288098652349900137 16597863966073989262425103)
            ·
              refine ⟨24896795949110983893637655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16597863966073989262425103 24896795949110983893637655)
              ·
                refine ⟨37345193923666475840456483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24896795949110983893637655 37345193923666475840456483)
                ·
                  refine ⟨56017790885499713760684725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37345193923666475840456483 56017790885499713760684725)
                  ·
                    refine ⟨5251667895515598165064193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56017790885499713760684725 5251667895515598165064193)
                    ·
                      refine ⟨3938750921636698623798145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5251667895515598165064193 3938750921636698623798145)
                      ·
                        rfl

theorem cell23_7670690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 1, 1, 5, 2].length) (baseStart_7670690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7670690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7670690 prefixEnd_7670690 := by exact prefixLift 7670690
  have htrace : WordTrace (prefixWord ++ tailWord_7670690) baseStart_7670690 baseEnd_7670690 := by
    simpa [prefixWord, tailWord_7670690, baseEnd_7670690] using wordTrace_append hprefix tailTrace_7670690
  have hstable : (prefixWord ++ tailWord_7670690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7670690).length < 2 ^ (prefixWord ++ tailWord_7670690).sum := by decide
  have hdescent : baseEnd_7670690 < baseStart_7670690 := by decide
  rcases family_descends (prefixWord ++ tailWord_7670690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7670713 : List Nat := [1, 2, 1, 4, 2, 3, 1, 1, 4, 4]
def baseStart_7670713 : Nat := 118140960795 + 7670713 * 2 ^ 59
def prefixEnd_7670713 : Nat := 4983230072969 + 3 ^ 40 * 7670713 * 2
def baseEnd_7670713 : Nat := 1312920910563917344603513

theorem tailTrace_7670713 : CollatzResearch.WordTrace tailWord_7670713 prefixEnd_7670713 1312920910563917344603513 := by
  unfold tailWord_7670713
  simp only [CollatzResearch.WordTrace]
  refine ⟨279773887459324329326824793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186515924972882886217883195 279773887459324329326824793)
  ·
    refine ⟨209830415594493246995118595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279773887459324329326824793 209830415594493246995118595)
    ·
      refine ⟨314745623391739870492677893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209830415594493246995118595 314745623391739870492677893)
      ·
        refine ⟨59014804385951225717377105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 314745623391739870492677893 59014804385951225717377105)
        ·
          refine ⟨44261103289463419288032829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59014804385951225717377105 44261103289463419288032829)
          ·
            refine ⟨16597913733548782233012311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44261103289463419288032829 16597913733548782233012311)
            ·
              refine ⟨24896870600323173349518467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16597913733548782233012311 24896870600323173349518467)
              ·
                refine ⟨37345305900484760024277701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24896870600323173349518467 37345305900484760024277701)
                ·
                  refine ⟨7002244856340892504552069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37345305900484760024277701 7002244856340892504552069)
                  ·
                    refine ⟨1312920910563917344603513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7002244856340892504552069 1312920910563917344603513)
                    ·
                      rfl

theorem cell23_7670713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 1, 4, 4].length) (baseStart_7670713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7670713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7670713 prefixEnd_7670713 := by exact prefixLift 7670713
  have htrace : WordTrace (prefixWord ++ tailWord_7670713) baseStart_7670713 baseEnd_7670713 := by
    simpa [prefixWord, tailWord_7670713, baseEnd_7670713] using wordTrace_append hprefix tailTrace_7670713
  have hstable : (prefixWord ++ tailWord_7670713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7670713).length < 2 ^ (prefixWord ++ tailWord_7670713).sum := by decide
  have hdescent : baseEnd_7670713 < baseStart_7670713 := by decide
  rcases family_descends (prefixWord ++ tailWord_7670713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7670720 : List Nat := [2, 1, 1, 2, 3, 3, 1, 3, 3, 2, 2]
def baseStart_7670720 : Nat := 118140960795 + 7670720 * 2 ^ 59
def prefixEnd_7670720 : Nat := 4983230072969 + 3 ^ 40 * 7670720 * 2
def baseEnd_7670720 : Nat := 3938766326056333506423007

theorem tailTrace_7670720 : CollatzResearch.WordTrace tailWord_7670720 prefixEnd_7670720 3938766326056333506423007 := by
  unfold tailWord_7670720
  simp only [CollatzResearch.WordTrace]
  refine ⟨139887071385149484761164807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186516095180199313014886409 139887071385149484761164807)
  ·
    refine ⟨209830607077724227141747211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139887071385149484761164807 209830607077724227141747211)
    ·
      refine ⟨314745910616586340712620817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209830607077724227141747211 314745910616586340712620817)
      ·
        refine ⟨236059432962439755534465613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 314745910616586340712620817 236059432962439755534465613)
        ·
          refine ⟨88522287360914908325424605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 236059432962439755534465613 88522287360914908325424605)
          ·
            refine ⟨33195857760343090622034227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88522287360914908325424605 33195857760343090622034227)
            ·
              refine ⟨49793786640514635933051341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33195857760343090622034227 49793786640514635933051341)
              ·
                refine ⟨18672669990192988474894253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49793786640514635933051341 18672669990192988474894253)
                ·
                  refine ⟨7002251246322370678085345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18672669990192988474894253 7002251246322370678085345)
                  ·
                    refine ⟨5251688434741778008564009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7002251246322370678085345 5251688434741778008564009)
                    ·
                      refine ⟨3938766326056333506423007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5251688434741778008564009 3938766326056333506423007)
                      ·
                        rfl

theorem cell23_7670720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 3, 3, 2, 2].length) (baseStart_7670720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7670720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7670720 prefixEnd_7670720 := by exact prefixLift 7670720
  have htrace : WordTrace (prefixWord ++ tailWord_7670720) baseStart_7670720 baseEnd_7670720 := by
    simpa [prefixWord, tailWord_7670720, baseEnd_7670720] using wordTrace_append hprefix tailTrace_7670720
  have hstable : (prefixWord ++ tailWord_7670720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7670720).length < 2 ^ (prefixWord ++ tailWord_7670720).sum := by decide
  have hdescent : baseEnd_7670720 < baseStart_7670720 := by decide
  rcases family_descends (prefixWord ++ tailWord_7670720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7670740 : List Nat := [2, 4, 1, 2, 1, 2, 1, 4, 1, 2, 3]
def baseStart_7670740 : Nat := 118140960795 + 7670740 * 2 ^ 59
def prefixEnd_7670740 : Nat := 4983230072969 + 3 ^ 40 * 7670740 * 2
def baseEnd_7670740 : Nat := 3938776595669423428172915

theorem tailTrace_7670740 : CollatzResearch.WordTrace tailWord_7670740 prefixEnd_7670740 3938776595669423428172915 := by
  unfold tailWord_7670740
  simp only [CollatzResearch.WordTrace]
  refine ⟨139887436115113256469028837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186516581486817675292038449 139887436115113256469028837)
  ·
    refine ⟨26228894271583735587942907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139887436115113256469028837 26228894271583735587942907)
    ·
      refine ⟨39343341407375603381914361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26228894271583735587942907 39343341407375603381914361)
      ·
        refine ⟨29507506055531702536435771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39343341407375603381914361 29507506055531702536435771)
        ·
          refine ⟨44261259083297553804653657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29507506055531702536435771 44261259083297553804653657)
          ·
            refine ⟨33195944312473165353490243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44261259083297553804653657 33195944312473165353490243)
            ·
              refine ⟨49793916468709748030235365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33195944312473165353490243 49793916468709748030235365)
              ·
                refine ⟨9336359337883077755669131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49793916468709748030235365 9336359337883077755669131)
                ·
                  refine ⟨14004539006824616633503697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9336359337883077755669131 14004539006824616633503697)
                  ·
                    refine ⟨10503404255118462475127773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14004539006824616633503697 10503404255118462475127773)
                    ·
                      refine ⟨3938776595669423428172915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10503404255118462475127773 3938776595669423428172915)
                      ·
                        rfl

theorem cell23_7670740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_7670740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7670740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7670740 prefixEnd_7670740 := by exact prefixLift 7670740
  have htrace : WordTrace (prefixWord ++ tailWord_7670740) baseStart_7670740 baseEnd_7670740 := by
    simpa [prefixWord, tailWord_7670740, baseEnd_7670740] using wordTrace_append hprefix tailTrace_7670740
  have hstable : (prefixWord ++ tailWord_7670740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7670740).length < 2 ^ (prefixWord ++ tailWord_7670740).sum := by decide
  have hdescent : baseEnd_7670740 < baseStart_7670740 := by decide
  rcases family_descends (prefixWord ++ tailWord_7670740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7670763 : List Nat := [1, 1, 1, 1, 2, 3, 1, 1, 7, 3, 2]
def baseStart_7670763 : Nat := 118140960795 + 7670763 * 2 ^ 59
def prefixEnd_7670763 : Nat := 4983230072969 + 3 ^ 40 * 7670763 * 2
def baseEnd_7670763 : Nat := 3938788405724476838185309

theorem tailTrace_7670763 : CollatzResearch.WordTrace tailWord_7670763 prefixEnd_7670763 3938788405724476838185309 := by
  unfold tailWord_7670763
  simp only [CollatzResearch.WordTrace]
  refine ⟨279775711109143187866144943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186517140739428791910763295 279775711109143187866144943)
  ·
    refine ⟨419663566663714781799217415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279775711109143187866144943 419663566663714781799217415)
    ·
      refine ⟨629495349995572172698826123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419663566663714781799217415 629495349995572172698826123)
      ·
        refine ⟨944243024993358259048239185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 629495349995572172698826123 944243024993358259048239185)
        ·
          refine ⟨708182268745018694286179389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 944243024993358259048239185 708182268745018694286179389)
          ·
            refine ⟨265568350779382010357317271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 708182268745018694286179389 265568350779382010357317271)
            ·
              refine ⟨398352526169073015535975907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265568350779382010357317271 398352526169073015535975907)
              ·
                refine ⟨597528789253609523303963861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 398352526169073015535975907 597528789253609523303963861)
                ·
                  refine ⟨14004580998131473202436653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 597528789253609523303963861 14004580998131473202436653)
                  ·
                    refine ⟨5251717874299302450913745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14004580998131473202436653 5251717874299302450913745)
                    ·
                      refine ⟨3938788405724476838185309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5251717874299302450913745 3938788405724476838185309)
                      ·
                        rfl

theorem cell23_7670763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 7, 3, 2].length) (baseStart_7670763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7670763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7670763 prefixEnd_7670763 := by exact prefixLift 7670763
  have htrace : WordTrace (prefixWord ++ tailWord_7670763) baseStart_7670763 baseEnd_7670763 := by
    simpa [prefixWord, tailWord_7670763, baseEnd_7670763] using wordTrace_append hprefix tailTrace_7670763
  have hstable : (prefixWord ++ tailWord_7670763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7670763).length < 2 ^ (prefixWord ++ tailWord_7670763).sum := by decide
  have hdescent : baseEnd_7670763 < baseStart_7670763 := by decide
  rcases family_descends (prefixWord ++ tailWord_7670763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7670776 : List Nat := [2, 1, 2, 1, 1, 3, 1, 3, 2, 3, 4]
def baseStart_7670776 : Nat := 118140960795 + 7670776 * 2 ^ 59
def prefixEnd_7670776 : Nat := 4983230072969 + 3 ^ 40 * 7670776 * 2
def baseEnd_7670776 : Nat := 3938795080972985287322749

theorem tailTrace_7670776 : CollatzResearch.WordTrace tailWord_7670776 prefixEnd_7670776 3938795080972985287322749 := by
  unfold tailWord_7670776
  simp only [CollatzResearch.WordTrace]
  refine ⟨139888092629048045543184091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186517456838730727390912121 139888092629048045543184091)
  ·
    refine ⟨209832138943572068314776137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139888092629048045543184091 209832138943572068314776137)
    ·
      refine ⟨157374104207679051236082103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209832138943572068314776137 157374104207679051236082103)
      ·
        refine ⟨236061156311518576854123155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157374104207679051236082103 236061156311518576854123155)
        ·
          refine ⟨354091734467277865281184733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236061156311518576854123155 354091734467277865281184733)
          ·
            refine ⟨132784400425229199480444275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 354091734467277865281184733 132784400425229199480444275)
            ·
              refine ⟨199176600637843799220666413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132784400425229199480444275 199176600637843799220666413)
              ·
                refine ⟨74691225239191424707749905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 199176600637843799220666413 74691225239191424707749905)
                ·
                  refine ⟨56018418929393568530812429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74691225239191424707749905 56018418929393568530812429)
                  ·
                    refine ⟨21006907098522588199054661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56018418929393568530812429 21006907098522588199054661)
                    ·
                      refine ⟨3938795080972985287322749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21006907098522588199054661 3938795080972985287322749)
                      ·
                        rfl

theorem cell23_7670776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 2, 3, 4].length) (baseStart_7670776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7670776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7670776 prefixEnd_7670776 := by exact prefixLift 7670776
  have htrace : WordTrace (prefixWord ++ tailWord_7670776) baseStart_7670776 baseEnd_7670776 := by
    simpa [prefixWord, tailWord_7670776, baseEnd_7670776] using wordTrace_append hprefix tailTrace_7670776
  have hstable : (prefixWord ++ tailWord_7670776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7670776).length < 2 ^ (prefixWord ++ tailWord_7670776).sum := by decide
  have hdescent : baseEnd_7670776 < baseStart_7670776 := by decide
  rcases family_descends (prefixWord ++ tailWord_7670776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7670793 : List Nat := [1, 2, 1, 1, 3, 1, 1, 2, 5, 4, 2]
def baseStart_7670793 : Nat := 118140960795 + 7670793 * 2 ^ 59
def prefixEnd_7670793 : Nat := 4983230072969 + 3 ^ 40 * 7670793 * 2
def baseEnd_7670793 : Nat := 3938803810144111720810171

theorem tailTrace_7670793 : CollatzResearch.WordTrace tailWord_7670793 prefixEnd_7670793 3938803810144111720810171 := by
  unfold tailWord_7670793
  simp only [CollatzResearch.WordTrace]
  refine ⟨279776805299034502989737033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186517870199356335326491355 279776805299034502989737033)
  ·
    refine ⟨209832603974275877242302775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279776805299034502989737033 209832603974275877242302775)
    ·
      refine ⟨314748905961413815863454163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209832603974275877242302775 314748905961413815863454163)
      ·
        refine ⟨472123358942120723795181245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314748905961413815863454163 472123358942120723795181245)
        ·
          refine ⟨177046259603295271423192967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 472123358942120723795181245 177046259603295271423192967)
          ·
            refine ⟨265569389404942907134789451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177046259603295271423192967 265569389404942907134789451)
            ·
              refine ⟨398354084107414360702184177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265569389404942907134789451 398354084107414360702184177)
              ·
                refine ⟨298765563080560770526638133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 398354084107414360702184177 298765563080560770526638133)
                ·
                  refine ⟨28009271538802572236872325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 298765563080560770526638133 28009271538802572236872325)
                  ·
                    refine ⟨5251738413525482294413561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28009271538802572236872325 5251738413525482294413561)
                    ·
                      refine ⟨3938803810144111720810171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5251738413525482294413561 3938803810144111720810171)
                      ·
                        rfl

theorem cell23_7670793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 5, 4, 2].length) (baseStart_7670793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7670793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7670793 prefixEnd_7670793 := by exact prefixLift 7670793
  have htrace : WordTrace (prefixWord ++ tailWord_7670793) baseStart_7670793 baseEnd_7670793 := by
    simpa [prefixWord, tailWord_7670793, baseEnd_7670793] using wordTrace_append hprefix tailTrace_7670793
  have hstable : (prefixWord ++ tailWord_7670793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7670793).length < 2 ^ (prefixWord ++ tailWord_7670793).sum := by decide
  have hdescent : baseEnd_7670793 < baseStart_7670793 := by decide
  rcases family_descends (prefixWord ++ tailWord_7670793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7670810 : List Nat := [3, 1, 1, 3, 1, 2, 3, 2, 1, 4, 2]
def baseStart_7670810 : Nat := 118140960795 + 7670810 * 2 ^ 59
def prefixEnd_7670810 : Nat := 4983230072969 + 3 ^ 40 * 7670810 * 2
def baseEnd_7670810 : Nat := 3938812539315238154297593

theorem tailTrace_7670810 : CollatzResearch.WordTrace tailWord_7670810 prefixEnd_7670810 3938812539315238154297593 := by
  unfold tailWord_7670810
  simp only [CollatzResearch.WordTrace]
  refine ⟨69944356334993228723276471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186518283559981943262070589 69944356334993228723276471)
  ·
    refine ⟨104916534502489843084914707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69944356334993228723276471 104916534502489843084914707)
    ·
      refine ⟨157374801753734764627372061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104916534502489843084914707 157374801753734764627372061)
      ·
        refine ⟨59015550657650536735264523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157374801753734764627372061 59015550657650536735264523)
        ·
          refine ⟨88523325986475805102896785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59015550657650536735264523 88523325986475805102896785)
          ·
            refine ⟨66392494489856853827172589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88523325986475805102896785 66392494489856853827172589)
            ·
              refine ⟨24897185433696320185189721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66392494489856853827172589 24897185433696320185189721)
              ·
                refine ⟨18672889075272240138892291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24897185433696320185189721 18672889075272240138892291)
                ·
                  refine ⟨28009333612908360208338437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18672889075272240138892291 28009333612908360208338437)
                  ·
                    refine ⟨5251750052420317539063457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28009333612908360208338437 5251750052420317539063457)
                    ·
                      refine ⟨3938812539315238154297593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5251750052420317539063457 3938812539315238154297593)
                      ·
                        rfl

theorem cell23_7670810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 2, 1, 4, 2].length) (baseStart_7670810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7670810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7670810 prefixEnd_7670810 := by exact prefixLift 7670810
  have htrace : WordTrace (prefixWord ++ tailWord_7670810) baseStart_7670810 baseEnd_7670810 := by
    simpa [prefixWord, tailWord_7670810, baseEnd_7670810] using wordTrace_append hprefix tailTrace_7670810
  have hstable : (prefixWord ++ tailWord_7670810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7670810).length < 2 ^ (prefixWord ++ tailWord_7670810).sum := by decide
  have hdescent : baseEnd_7670810 < baseStart_7670810 := by decide
  rcases family_descends (prefixWord ++ tailWord_7670810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7670827 : List Nat := [1, 1, 1, 1, 2, 1, 8, 2, 2, 2, 2]
def baseStart_7670827 : Nat := 118140960795 + 7670827 * 2 ^ 59
def prefixEnd_7670827 : Nat := 4983230072969 + 3 ^ 40 * 7670827 * 2
def baseEnd_7670827 : Nat := 3938821268486364587785015

theorem tailTrace_7670827 : CollatzResearch.WordTrace tailWord_7670827 prefixEnd_7670827 3938821268486364587785015 := by
  unfold tailWord_7670827
  simp only [CollatzResearch.WordTrace]
  refine ⟨279778045380911326796474735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186518696920607551197649823 279778045380911326796474735)
  ·
    refine ⟨419667068071366990194712103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279778045380911326796474735 419667068071366990194712103)
    ·
      refine ⟨629500602107050485292068155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419667068071366990194712103 629500602107050485292068155)
      ·
        refine ⟨944250903160575727938102233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 629500602107050485292068155 944250903160575727938102233)
        ·
          refine ⟨708188177370431795953576675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 944250903160575727938102233 708188177370431795953576675)
          ·
            refine ⟨1062282266055647693930365013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 708188177370431795953576675 1062282266055647693930365013)
            ·
              refine ⟨12448620305339621413246465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1062282266055647693930365013 12448620305339621413246465)
              ·
                refine ⟨9336465229004716059934849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12448620305339621413246465 9336465229004716059934849)
                ·
                  refine ⟨7002348921753537044951137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9336465229004716059934849 7002348921753537044951137)
                  ·
                    refine ⟨5251761691315152783713353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7002348921753537044951137 5251761691315152783713353)
                    ·
                      refine ⟨3938821268486364587785015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5251761691315152783713353 3938821268486364587785015)
                      ·
                        rfl

theorem cell23_7670827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 2, 2, 2, 2].length) (baseStart_7670827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7670827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7670827 prefixEnd_7670827 := by exact prefixLift 7670827
  have htrace : WordTrace (prefixWord ++ tailWord_7670827) baseStart_7670827 baseEnd_7670827 := by
    simpa [prefixWord, tailWord_7670827, baseEnd_7670827] using wordTrace_append hprefix tailTrace_7670827
  have hstable : (prefixWord ++ tailWord_7670827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7670827).length < 2 ^ (prefixWord ++ tailWord_7670827).sum := by decide
  have hdescent : baseEnd_7670827 < baseStart_7670827 := by decide
  rcases family_descends (prefixWord ++ tailWord_7670827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7670878 : List Nat := [4, 4, 1, 1, 1, 1, 3, 2, 2, 2, 2]
def baseStart_7670878 : Nat := 118140960795 + 7670878 * 2 ^ 59
def prefixEnd_7670878 : Nat := 4983230072969 + 3 ^ 40 * 7670878 * 2
def baseEnd_7670878 : Nat := 3938847455999743888247281

theorem tailTrace_7670878 : CollatzResearch.WordTrace tailWord_7670878 prefixEnd_7670878 3938847455999743888247281 := by
  unfold tailWord_7670878
  simp only [CollatzResearch.WordTrace]
  refine ⟨34972488187965820313322661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186519937002484375004387525 34972488187965820313322661)
  ·
    refine ⟨6557341535243591308747999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34972488187965820313322661 6557341535243591308747999)
    ·
      refine ⟨9836012302865386963121999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6557341535243591308747999 9836012302865386963121999)
      ·
        refine ⟨14754018454298080444682999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9836012302865386963121999 14754018454298080444682999)
        ·
          refine ⟨22131027681447120667024499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14754018454298080444682999 22131027681447120667024499)
          ·
            refine ⟨33196541522170681000536749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22131027681447120667024499 33196541522170681000536749)
            ·
              refine ⟨12448703070814005375201281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33196541522170681000536749 12448703070814005375201281)
              ·
                refine ⟨9336527303110504031400961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12448703070814005375201281 9336527303110504031400961)
                ·
                  refine ⟨7002395477332878023550721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9336527303110504031400961 7002395477332878023550721)
                  ·
                    refine ⟨5251796607999658517663041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7002395477332878023550721 5251796607999658517663041)
                    ·
                      refine ⟨3938847455999743888247281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5251796607999658517663041 3938847455999743888247281)
                      ·
                        rfl

theorem cell23_7670878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_7670878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7670878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7670878 prefixEnd_7670878 := by exact prefixLift 7670878
  have htrace : WordTrace (prefixWord ++ tailWord_7670878) baseStart_7670878 baseEnd_7670878 := by
    simpa [prefixWord, tailWord_7670878, baseEnd_7670878] using wordTrace_append hprefix tailTrace_7670878
  have hstable : (prefixWord ++ tailWord_7670878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7670878).length < 2 ^ (prefixWord ++ tailWord_7670878).sum := by decide
  have hdescent : baseEnd_7670878 < baseStart_7670878 := by decide
  rcases family_descends (prefixWord ++ tailWord_7670878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7670883 : List Nat := [1, 1, 1, 5, 1, 1, 1, 3, 4, 1, 4]
def baseStart_7670883 : Nat := 118140960795 + 7670883 * 2 ^ 59
def prefixEnd_7670883 : Nat := 4983230072969 + 3 ^ 40 * 7670883 * 2
def baseEnd_7670883 : Nat := 3938850023403016368684757

theorem tailTrace_7670883 : CollatzResearch.WordTrace tailWord_7670883 prefixEnd_7670883 3938850023403016368684757 := by
  unfold tailWord_7670883
  simp only [CollatzResearch.WordTrace]
  refine ⟨279780087868708448360513303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186520058579138965573675535 279780087868708448360513303)
  ·
    refine ⟨419670131803062672540769955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279780087868708448360513303 419670131803062672540769955)
    ·
      refine ⟨629505197704594008811154933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419670131803062672540769955 629505197704594008811154933)
      ·
        refine ⟨59016112284805688326045775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 629505197704594008811154933 59016112284805688326045775)
        ·
          refine ⟨88524168427208532489068663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59016112284805688326045775 88524168427208532489068663)
          ·
            refine ⟨132786252640812798733602995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88524168427208532489068663 132786252640812798733602995)
            ·
              refine ⟨199179378961219198100404493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132786252640812798733602995 199179378961219198100404493)
              ·
                refine ⟨74692267110457199287651685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 199179378961219198100404493 74692267110457199287651685)
                ·
                  refine ⟨14004800083210724866434691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74692267110457199287651685 14004800083210724866434691)
                  ·
                    refine ⟨21007200124816087299652037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14004800083210724866434691 21007200124816087299652037)
                    ·
                      refine ⟨3938850023403016368684757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21007200124816087299652037 3938850023403016368684757)
                      ·
                        rfl

theorem cell23_7670883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_7670883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7670883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7670883 prefixEnd_7670883 := by exact prefixLift 7670883
  have htrace : WordTrace (prefixWord ++ tailWord_7670883) baseStart_7670883 baseEnd_7670883 := by
    simpa [prefixWord, tailWord_7670883, baseEnd_7670883] using wordTrace_append hprefix tailTrace_7670883
  have hstable : (prefixWord ++ tailWord_7670883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7670883).length < 2 ^ (prefixWord ++ tailWord_7670883).sum := by decide
  have hdescent : baseEnd_7670883 < baseStart_7670883 := by decide
  rcases family_descends (prefixWord ++ tailWord_7670883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7670903 : List Nat := [1, 1, 3, 1, 1, 4, 1, 1, 3, 4, 3]
def baseStart_7670903 : Nat := 118140960795 + 7670903 * 2 ^ 59
def prefixEnd_7670903 : Nat := 4983230072969 + 3 ^ 40 * 7670903 * 2
def baseEnd_7670903 : Nat := 3938860293016106290434665

theorem tailTrace_7670903 : CollatzResearch.WordTrace tailWord_7670903 prefixEnd_7670903 3938860293016106290434665 := by
  unfold tailWord_7670903
  simp only [CollatzResearch.WordTrace]
  refine ⟨279780817328635991776241363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186520544885757327850827575 279780817328635991776241363)
  ·
    refine ⟨419671225992953987664362045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279780817328635991776241363 419671225992953987664362045)
    ·
      refine ⟨157376709747357745374135767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 419671225992953987664362045 157376709747357745374135767)
      ·
        refine ⟨236065064621036618061203651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157376709747357745374135767 236065064621036618061203651)
        ·
          refine ⟨354097596931554927091805477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236065064621036618061203651 354097596931554927091805477)
          ·
            refine ⟨66393299424666548829713527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 354097596931554927091805477 66393299424666548829713527)
            ·
              refine ⟨99589949136999823244570291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66393299424666548829713527 99589949136999823244570291)
              ·
                refine ⟨149384923705499734866855437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99589949136999823244570291 149384923705499734866855437)
                ·
                  refine ⟨56019346389562400575070789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 149384923705499734866855437 56019346389562400575070789)
                  ·
                    refine ⟨10503627448042950107825773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56019346389562400575070789 10503627448042950107825773)
                    ·
                      refine ⟨3938860293016106290434665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10503627448042950107825773 3938860293016106290434665)
                      ·
                        rfl

theorem cell23_7670903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 3, 4, 3].length) (baseStart_7670903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7670903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7670903 prefixEnd_7670903 := by exact prefixLift 7670903
  have htrace : WordTrace (prefixWord ++ tailWord_7670903) baseStart_7670903 baseEnd_7670903 := by
    simpa [prefixWord, tailWord_7670903, baseEnd_7670903] using wordTrace_append hprefix tailTrace_7670903
  have hstable : (prefixWord ++ tailWord_7670903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7670903).length < 2 ^ (prefixWord ++ tailWord_7670903).sum := by decide
  have hdescent : baseEnd_7670903 < baseStart_7670903 := by decide
  rcases family_descends (prefixWord ++ tailWord_7670903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7670944 : List Nat := [2, 1, 1, 4, 2, 1, 5, 2, 1, 4]
def baseStart_7670944 : Nat := 118140960795 + 7670944 * 2 ^ 59
def prefixEnd_7670944 : Nat := 4983230072969 + 3 ^ 40 * 7670944 * 2
def baseEnd_7670944 : Nat := 1312960448574313543340659

theorem tailTrace_7670944 : CollatzResearch.WordTrace tailWord_7670944 prefixEnd_7670944 1312960448574313543340659 := by
  unfold tailWord_7670944
  simp only [CollatzResearch.WordTrace]
  refine ⟨139891156360743727889241943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186521541814324970518989257 139891156360743727889241943)
  ·
    refine ⟨209836734541115591833862915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139891156360743727889241943 209836734541115591833862915)
    ·
      refine ⟨314755101811673387750794373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209836734541115591833862915 314755101811673387750794373)
      ·
        refine ⟨59016581589688760203273945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 314755101811673387750794373 59016581589688760203273945)
        ·
          refine ⟨44262436192266570152455459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59016581589688760203273945 44262436192266570152455459)
          ·
            refine ⟨66393654288399855228683189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44262436192266570152455459 66393654288399855228683189)
            ·
              refine ⟨6224405089537486427689049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66393654288399855228683189 6224405089537486427689049)
              ·
                refine ⟨4668303817153114820766787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6224405089537486427689049 4668303817153114820766787)
                ·
                  refine ⟨7002455725729672231150181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4668303817153114820766787 7002455725729672231150181)
                  ·
                    refine ⟨1312960448574313543340659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7002455725729672231150181 1312960448574313543340659)
                    ·
                      rfl

theorem cell23_7670944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 5, 2, 1, 4].length) (baseStart_7670944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7670944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7670944 prefixEnd_7670944 := by exact prefixLift 7670944
  have htrace : WordTrace (prefixWord ++ tailWord_7670944) baseStart_7670944 baseEnd_7670944 := by
    simpa [prefixWord, tailWord_7670944, baseEnd_7670944] using wordTrace_append hprefix tailTrace_7670944
  have hstable : (prefixWord ++ tailWord_7670944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7670944).length < 2 ^ (prefixWord ++ tailWord_7670944).sum := by decide
  have hdescent : baseEnd_7670944 < baseStart_7670944 := by decide
  rcases family_descends (prefixWord ++ tailWord_7670944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7670957 : List Nat := [1, 5, 2, 1, 3, 1, 1, 3, 6]
def baseStart_7670957 : Nat := 118140960795 + 7670957 * 2 ^ 59
def prefixEnd_7670957 : Nat := 4983230072969 + 3 ^ 40 * 7670957 * 2
def baseEnd_7670957 : Nat := 437654224552383231017713

theorem tailTrace_7670957 : CollatzResearch.WordTrace tailWord_7670957 prefixEnd_7670957 437654224552383231017713 := by
  unfold tailWord_7670957
  simp only [CollatzResearch.WordTrace]
  refine ⟨279782786870440358998707125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186521857913626905999138083 279782786870440358998707125)
  ·
    refine ⟨26229636269103783656128793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 279782786870440358998707125 26229636269103783656128793)
    ·
      refine ⟨19672227201827837742096595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26229636269103783656128793 19672227201827837742096595)
      ·
        refine ⟨29508340802741756613144893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19672227201827837742096595 29508340802741756613144893)
        ·
          refine ⟨11065627801028158729929335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29508340802741756613144893 11065627801028158729929335)
          ·
            refine ⟨16598441701542238094894003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11065627801028158729929335 16598441701542238094894003)
            ·
              refine ⟨24897662552313357142341005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16598441701542238094894003 24897662552313357142341005)
              ·
                refine ⟨9336623457117508928377877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24897662552313357142341005 9336623457117508928377877)
                ·
                  refine ⟨437654224552383231017713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9336623457117508928377877 437654224552383231017713)
                  ·
                    rfl

theorem cell23_7670957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 3, 6].length) (baseStart_7670957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7670957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7670957 prefixEnd_7670957 := by exact prefixLift 7670957
  have htrace : WordTrace (prefixWord ++ tailWord_7670957) baseStart_7670957 baseEnd_7670957 := by
    simpa [prefixWord, tailWord_7670957, baseEnd_7670957] using wordTrace_append hprefix tailTrace_7670957
  have hstable : (prefixWord ++ tailWord_7670957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7670957).length < 2 ^ (prefixWord ++ tailWord_7670957).sum := by decide
  have hdescent : baseEnd_7670957 < baseStart_7670957 := by decide
  rcases family_descends (prefixWord ++ tailWord_7670957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7671020 : List Nat := [2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 4]
def baseStart_7671020 : Nat := 118140960795 + 7671020 * 2 ^ 59
def prefixEnd_7671020 : Nat := 4983230072969 + 3 ^ 40 * 7671020 * 2
def baseEnd_7671020 : Nat := 3938920370252682332671627

theorem tailTrace_7671020 : CollatzResearch.WordTrace tailWord_7671020 prefixEnd_7671020 3938920370252682332671627 := by
  unfold tailWord_7671020
  simp only [CollatzResearch.WordTrace]
  refine ⟨139892542334606060379125257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186523389779474747172167009 139892542334606060379125257)
  ·
    refine ⟨104919406750954545284343943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139892542334606060379125257 104919406750954545284343943)
    ·
      refine ⟨157379110126431817926515915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104919406750954545284343943 157379110126431817926515915)
      ·
        refine ⟨236068665189647726889773873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157379110126431817926515915 236068665189647726889773873)
        ·
          refine ⟨177051498892235795167330405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236068665189647726889773873 177051498892235795167330405)
          ·
            refine ⟨33197156042294211593874451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 177051498892235795167330405 33197156042294211593874451)
            ·
              refine ⟨49795734063441317390811677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33197156042294211593874451 49795734063441317390811677)
              ·
                refine ⟨18673400273790494021554379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49795734063441317390811677 18673400273790494021554379)
                ·
                  refine ⟨28010100410685741032331569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18673400273790494021554379 28010100410685741032331569)
                  ·
                    refine ⟨21007575308014305774248677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28010100410685741032331569 21007575308014305774248677)
                    ·
                      refine ⟨3938920370252682332671627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21007575308014305774248677 3938920370252682332671627)
                      ·
                        rfl

theorem cell23_7671020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 4].length) (baseStart_7671020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7671020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7671020 prefixEnd_7671020 := by exact prefixLift 7671020
  have htrace : WordTrace (prefixWord ++ tailWord_7671020) baseStart_7671020 baseEnd_7671020 := by
    simpa [prefixWord, tailWord_7671020, baseEnd_7671020] using wordTrace_append hprefix tailTrace_7671020
  have hstable : (prefixWord ++ tailWord_7671020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7671020).length < 2 ^ (prefixWord ++ tailWord_7671020).sum := by decide
  have hdescent : baseEnd_7671020 < baseStart_7671020 := by decide
  rcases family_descends (prefixWord ++ tailWord_7671020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7671028 : List Nat := [2, 6, 1, 2, 1, 1, 1, 1, 1, 5, 2]
def baseStart_7671028 : Nat := 118140960795 + 7671028 * 2 ^ 59
def prefixEnd_7671028 : Nat := 4983230072969 + 3 ^ 40 * 7671028 * 2
def baseEnd_7671028 : Nat := 3938924478097918301371591

theorem tailTrace_7671028 : CollatzResearch.WordTrace tailWord_7671028 prefixEnd_7671028 3938924478097918301371591 := by
  unfold tailWord_7671028
  simp only [CollatzResearch.WordTrace]
  refine ⟨139892688226591569062270869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186523584302122092083027825 139892688226591569062270869)
  ·
    refine ⟨6557469760621479799793947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 139892688226591569062270869 6557469760621479799793947)
    ·
      refine ⟨9836204640932219699690921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6557469760621479799793947 9836204640932219699690921)
      ·
        refine ⟨7377153480699164774768191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9836204640932219699690921 7377153480699164774768191)
        ·
          refine ⟨11065730221048747162152287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7377153480699164774768191 11065730221048747162152287)
          ·
            refine ⟨16598595331573120743228431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11065730221048747162152287 16598595331573120743228431)
            ·
              refine ⟨24897892997359681114842647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16598595331573120743228431 24897892997359681114842647)
              ·
                refine ⟨37346839496039521672263971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24897892997359681114842647 37346839496039521672263971)
                ·
                  refine ⟨56020259244059282508395957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37346839496039521672263971 56020259244059282508395957)
                  ·
                    refine ⟨5251899304130557735162121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56020259244059282508395957 5251899304130557735162121)
                    ·
                      refine ⟨3938924478097918301371591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5251899304130557735162121 3938924478097918301371591)
                      ·
                        rfl

theorem cell23_7671028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_7671028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7671028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7671028 prefixEnd_7671028 := by exact prefixLift 7671028
  have htrace : WordTrace (prefixWord ++ tailWord_7671028) baseStart_7671028 baseEnd_7671028 := by
    simpa [prefixWord, tailWord_7671028, baseEnd_7671028] using wordTrace_append hprefix tailTrace_7671028
  have hstable : (prefixWord ++ tailWord_7671028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7671028).length < 2 ^ (prefixWord ++ tailWord_7671028).sum := by decide
  have hdescent : baseEnd_7671028 < baseStart_7671028 := by decide
  rcases family_descends (prefixWord ++ tailWord_7671028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7671041 : List Nat := [1, 2, 4, 1, 1, 3, 1, 5, 1, 2, 2]
def baseStart_7671041 : Nat := 118140960795 + 7671041 * 2 ^ 59
def prefixEnd_7671041 : Nat := 4983230072969 + 3 ^ 40 * 7671041 * 2
def baseEnd_7671041 : Nat := 3938931153346426750509031

theorem tailTrace_7671041 : CollatzResearch.WordTrace tailWord_7671041 prefixEnd_7671041 3938931153346426750509031 := by
  unfold tailWord_7671041
  simp only [CollatzResearch.WordTrace]
  refine ⟨279785850602136041344764977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186523900401424027563176651 279785850602136041344764977)
  ·
    refine ⟨209839387951602031008573733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279785850602136041344764977 209839387951602031008573733)
    ·
      refine ⟨39344885240925380814107575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 209839387951602031008573733 39344885240925380814107575)
      ·
        refine ⟨59017327861388071221161363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39344885240925380814107575 59017327861388071221161363)
        ·
          refine ⟨88525991792082106831742045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59017327861388071221161363 88525991792082106831742045)
          ·
            refine ⟨33197246922030790061903267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88525991792082106831742045 33197246922030790061903267)
            ·
              refine ⟨49795870383046185092854901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33197246922030790061903267 49795870383046185092854901)
              ·
                refine ⟨4668362848410579852455147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49795870383046185092854901 4668362848410579852455147)
                ·
                  refine ⟨7002544272615869778682721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4668362848410579852455147 7002544272615869778682721)
                  ·
                    refine ⟨5251908204461902334012041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7002544272615869778682721 5251908204461902334012041)
                    ·
                      refine ⟨3938931153346426750509031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5251908204461902334012041 3938931153346426750509031)
                      ·
                        rfl

theorem cell23_7671041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 5, 1, 2, 2].length) (baseStart_7671041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7671041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7671041 prefixEnd_7671041 := by exact prefixLift 7671041
  have htrace : WordTrace (prefixWord ++ tailWord_7671041) baseStart_7671041 baseEnd_7671041 := by
    simpa [prefixWord, tailWord_7671041, baseEnd_7671041] using wordTrace_append hprefix tailTrace_7671041
  have hstable : (prefixWord ++ tailWord_7671041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7671041).length < 2 ^ (prefixWord ++ tailWord_7671041).sum := by decide
  have hdescent : baseEnd_7671041 < baseStart_7671041 := by decide
  rcases family_descends (prefixWord ++ tailWord_7671041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7671044 : List Nat := [2, 3, 2, 2, 2, 2, 1, 3, 1, 2, 3]
def baseStart_7671044 : Nat := 118140960795 + 7671044 * 2 ^ 59
def prefixEnd_7671044 : Nat := 4983230072969 + 3 ^ 40 * 7671044 * 2
def baseEnd_7671044 : Nat := 3938932693788390238771517

theorem tailTrace_7671044 : CollatzResearch.WordTrace tailWord_7671044 prefixEnd_7671044 3938932693788390238771517 := by
  unfold tailWord_7671044
  simp only [CollatzResearch.WordTrace]
  refine ⟨139892980010562586428562093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186523973347416781904749457 139892980010562586428562093)
  ·
    refine ⟨52459867503960969910710785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139892980010562586428562093 52459867503960969910710785)
    ·
      refine ⟨39344900627970727433033089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52459867503960969910710785 39344900627970727433033089)
      ·
        refine ⟨29508675470978045574774817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39344900627970727433033089 29508675470978045574774817)
        ·
          refine ⟨22131506603233534181081113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29508675470978045574774817 22131506603233534181081113)
          ·
            refine ⟨16598629952425150635810835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22131506603233534181081113 16598629952425150635810835)
            ·
              refine ⟨24897944928637725953716253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16598629952425150635810835 24897944928637725953716253)
              ·
                refine ⟨9336729348239147232643595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24897944928637725953716253 9336729348239147232643595)
                ·
                  refine ⟨14005094022358720848965393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9336729348239147232643595 14005094022358720848965393)
                  ·
                    refine ⟨10503820516769040636724045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14005094022358720848965393 10503820516769040636724045)
                    ·
                      refine ⟨3938932693788390238771517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10503820516769040636724045 3938932693788390238771517)
                      ·
                        rfl

theorem cell23_7671044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_7671044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7671044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7671044 prefixEnd_7671044 := by exact prefixLift 7671044
  have htrace : WordTrace (prefixWord ++ tailWord_7671044) baseStart_7671044 baseEnd_7671044 := by
    simpa [prefixWord, tailWord_7671044, baseEnd_7671044] using wordTrace_append hprefix tailTrace_7671044
  have hstable : (prefixWord ++ tailWord_7671044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7671044).length < 2 ^ (prefixWord ++ tailWord_7671044).sum := by decide
  have hdescent : baseEnd_7671044 < baseStart_7671044 := by decide
  rcases family_descends (prefixWord ++ tailWord_7671044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7671057 : List Nat := [1, 2, 2, 1, 1, 4, 3, 1, 4, 1, 3]
def baseStart_7671057 : Nat := 118140960795 + 7671057 * 2 ^ 59
def prefixEnd_7671057 : Nat := 4983230072969 + 3 ^ 40 * 7671057 * 2
def baseEnd_7671057 : Nat := 3938939369036898687908957

theorem tailTrace_7671057 : CollatzResearch.WordTrace tailWord_7671057 prefixEnd_7671057 3938939369036898687908957 := by
  unfold tailWord_7671057
  simp only [CollatzResearch.WordTrace]
  refine ⟨279786434170078076077347425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186524289446718717384898283 279786434170078076077347425)
  ·
    refine ⟨209839825627558557058010569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279786434170078076077347425 209839825627558557058010569)
    ·
      refine ⟨157379869220668917793507927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209839825627558557058010569 157379869220668917793507927)
      ·
        refine ⟨236069803831003376690261891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157379869220668917793507927 236069803831003376690261891)
        ·
          refine ⟨354104705746505065035392837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236069803831003376690261891 354104705746505065035392837)
          ·
            refine ⟨66394632327469699694136157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 354104705746505065035392837 66394632327469699694136157)
            ·
              refine ⟨24897987122801137385301059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66394632327469699694136157 24897987122801137385301059)
              ·
                refine ⟨37346980684201706077951589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24897987122801137385301059 37346980684201706077951589)
                ·
                  refine ⟨7002558878287819889615923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37346980684201706077951589 7002558878287819889615923)
                  ·
                    refine ⟨10503838317431729834423885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7002558878287819889615923 10503838317431729834423885)
                    ·
                      refine ⟨3938939369036898687908957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10503838317431729834423885 3938939369036898687908957)
                      ·
                        rfl

theorem cell23_7671057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 1, 4, 1, 3].length) (baseStart_7671057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7671057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7671057 prefixEnd_7671057 := by exact prefixLift 7671057
  have htrace : WordTrace (prefixWord ++ tailWord_7671057) baseStart_7671057 baseEnd_7671057 := by
    simpa [prefixWord, tailWord_7671057, baseEnd_7671057] using wordTrace_append hprefix tailTrace_7671057
  have hstable : (prefixWord ++ tailWord_7671057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7671057).length < 2 ^ (prefixWord ++ tailWord_7671057).sum := by decide
  have hdescent : baseEnd_7671057 < baseStart_7671057 := by decide
  rcases family_descends (prefixWord ++ tailWord_7671057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7671083 : List Nat := [1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 9]
def baseStart_7671083 : Nat := 118140960795 + 7671083 * 2 ^ 59
def prefixEnd_7671083 : Nat := 4983230072969 + 3 ^ 40 * 7671083 * 2
def baseEnd_7671083 : Nat := 3938952719533915586183837

theorem tailTrace_7671083 : CollatzResearch.WordTrace tailWord_7671083 prefixEnd_7671083 3938952719533915586183837 := by
  unfold tailWord_7671083
  simp only [CollatzResearch.WordTrace]
  refine ⟨279787382467983882517793903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186524921645322588345195935 279787382467983882517793903)
  ·
    refine ⟨419681073701975823776690855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279787382467983882517793903 419681073701975823776690855)
    ·
      refine ⟨629521610552963735665036283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419681073701975823776690855 629521610552963735665036283)
      ·
        refine ⟨944282415829445603497554425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 629521610552963735665036283 944282415829445603497554425)
        ·
          refine ⟨708211811872084202623165819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 944282415829445603497554425 708211811872084202623165819)
          ·
            refine ⟨1062317717808126303934748729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 708211811872084202623165819 1062317717808126303934748729)
            ·
              refine ⟨796738288356094727951061547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1062317717808126303934748729 796738288356094727951061547)
              ·
                refine ⟨1195107432534142091926592321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 796738288356094727951061547 1195107432534142091926592321)
                ·
                  refine ⟨896330574400606568944944241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1195107432534142091926592321 896330574400606568944944241)
                  ·
                    refine ⟨672247930800454926708708181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 896330574400606568944944241 672247930800454926708708181)
                    ·
                      refine ⟨3938952719533915586183837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 672247930800454926708708181 3938952719533915586183837)
                      ·
                        rfl

theorem cell23_7671083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 9].length) (baseStart_7671083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7671083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7671083 prefixEnd_7671083 := by exact prefixLift 7671083
  have htrace : WordTrace (prefixWord ++ tailWord_7671083) baseStart_7671083 baseEnd_7671083 := by
    simpa [prefixWord, tailWord_7671083, baseEnd_7671083] using wordTrace_append hprefix tailTrace_7671083
  have hstable : (prefixWord ++ tailWord_7671083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7671083).length < 2 ^ (prefixWord ++ tailWord_7671083).sum := by decide
  have hdescent : baseEnd_7671083 < baseStart_7671083 := by decide
  rcases family_descends (prefixWord ++ tailWord_7671083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7671100 : List Nat := [2, 2, 2, 2, 1, 3, 1, 1, 1, 3, 5]
def baseStart_7671100 : Nat := 118140960795 + 7671100 * 2 ^ 59
def prefixEnd_7671100 : Nat := 4983230072969 + 3 ^ 40 * 7671100 * 2
def baseEnd_7671100 : Nat := 3938961448705042019671259

theorem tailTrace_7671100 : CollatzResearch.WordTrace tailWord_7671100 prefixEnd_7671100 3938961448705042019671259 := by
  unfold tailWord_7671100
  simp only [CollatzResearch.WordTrace]
  refine ⟨139894001254461147210581377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186525335005948196280775169 139894001254461147210581377)
  ·
    refine ⟨104920500940845860407936033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139894001254461147210581377 104920500940845860407936033)
    ·
      refine ⟨78690375705634395305952025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104920500940845860407936033 78690375705634395305952025)
      ·
        refine ⟨59017781779225796479464019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78690375705634395305952025 59017781779225796479464019)
        ·
          refine ⟨88526672668838694719196029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59017781779225796479464019 88526672668838694719196029)
          ·
            refine ⟨33197502250814510519698511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88526672668838694719196029 33197502250814510519698511)
            ·
              refine ⟨49796253376221765779547767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33197502250814510519698511 49796253376221765779547767)
              ·
                refine ⟨74694380064332648669321651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49796253376221765779547767 74694380064332648669321651)
                ·
                  refine ⟨112041570096498973003982477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74694380064332648669321651 112041570096498973003982477)
                  ·
                    refine ⟨42015588786187114876493429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 112041570096498973003982477 42015588786187114876493429)
                    ·
                      refine ⟨3938961448705042019671259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42015588786187114876493429 3938961448705042019671259)
                      ·
                        rfl

theorem cell23_7671100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_7671100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7671100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7671100 prefixEnd_7671100 := by exact prefixLift 7671100
  have htrace : WordTrace (prefixWord ++ tailWord_7671100) baseStart_7671100 baseEnd_7671100 := by
    simpa [prefixWord, tailWord_7671100, baseEnd_7671100] using wordTrace_append hprefix tailTrace_7671100
  have hstable : (prefixWord ++ tailWord_7671100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7671100).length < 2 ^ (prefixWord ++ tailWord_7671100).sum := by decide
  have hdescent : baseEnd_7671100 < baseStart_7671100 := by decide
  rcases family_descends (prefixWord ++ tailWord_7671100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7671171 : List Nat := [1, 1, 1, 3, 5, 3, 2, 2, 5]
def baseStart_7671171 : Nat := 118140960795 + 7671171 * 2 ^ 59
def prefixEnd_7671171 : Nat := 4983230072969 + 3 ^ 40 * 7671171 * 2
def baseEnd_7671171 : Nat := 437666433981279026875937

theorem tailTrace_7671171 : CollatzResearch.WordTrace tailWord_7671171 prefixEnd_7671171 437666433981279026875937 := by
  unfold tailWord_7671171
  simp only [CollatzResearch.WordTrace]
  refine ⟨279790592091665073546997367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186527061394443382364664911 279790592091665073546997367)
  ·
    refine ⟨419685888137497610320496051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279790592091665073546997367 419685888137497610320496051)
    ·
      refine ⟨629528832206246415480744077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419685888137497610320496051 629528832206246415480744077)
      ·
        refine ⟨236073312077342405805279029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 629528832206246415480744077 236073312077342405805279029)
        ·
          refine ⟨22131873007250850544244909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 236073312077342405805279029 22131873007250850544244909)
          ·
            refine ⟨8299452377719068954091841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22131873007250850544244909 8299452377719068954091841)
            ·
              refine ⟨6224589283289301715568881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8299452377719068954091841 6224589283289301715568881)
              ·
                refine ⟨4668441962466976286676661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6224589283289301715568881 4668441962466976286676661)
                ·
                  refine ⟨437666433981279026875937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4668441962466976286676661 437666433981279026875937)
                  ·
                    rfl

theorem cell23_7671171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 2, 2, 5].length) (baseStart_7671171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7671171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7671171 prefixEnd_7671171 := by exact prefixLift 7671171
  have htrace : WordTrace (prefixWord ++ tailWord_7671171) baseStart_7671171 baseEnd_7671171 := by
    simpa [prefixWord, tailWord_7671171, baseEnd_7671171] using wordTrace_append hprefix tailTrace_7671171
  have hstable : (prefixWord ++ tailWord_7671171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7671171).length < 2 ^ (prefixWord ++ tailWord_7671171).sum := by decide
  have hdescent : baseEnd_7671171 < baseStart_7671171 := by decide
  rcases family_descends (prefixWord ++ tailWord_7671171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7671281 : List Nat := [1, 2, 2, 2, 3, 3, 1, 2, 2, 3, 2]
def baseStart_7671281 : Nat := 118140960795 + 7671281 * 2 ^ 59
def prefixEnd_7671281 : Nat := 4983230072969 + 3 ^ 40 * 7671281 * 2
def baseEnd_7671281 : Nat := 3939054388703505811507927

theorem tailTrace_7671281 : CollatzResearch.WordTrace tailWord_7671281 prefixEnd_7671281 3939054388703505811507927 := by
  unfold tailWord_7671281
  simp only [CollatzResearch.WordTrace]
  refine ⟨279794604121266562333501697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186529736080844374889001131 279794604121266562333501697)
  ·
    refine ⟨209845953090949921750126273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279794604121266562333501697 209845953090949921750126273)
    ·
      refine ⟨157384464818212441312594705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209845953090949921750126273 157384464818212441312594705)
      ·
        refine ⟨118038348613659330984446029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157384464818212441312594705 118038348613659330984446029)
        ·
          refine ⟨44264380730122249119167261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118038348613659330984446029 44264380730122249119167261)
          ·
            refine ⟨16599142773795843419687723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44264380730122249119167261 16599142773795843419687723)
            ·
              refine ⟨24898714160693765129531585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16599142773795843419687723 24898714160693765129531585)
              ·
                refine ⟨18674035620520323847148689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24898714160693765129531585 18674035620520323847148689)
                ·
                  refine ⟨14005526715390242885361517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18674035620520323847148689 14005526715390242885361517)
                  ·
                    refine ⟨5252072518271341082010569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14005526715390242885361517 5252072518271341082010569)
                    ·
                      refine ⟨3939054388703505811507927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5252072518271341082010569 3939054388703505811507927)
                      ·
                        rfl

theorem cell23_7671281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 2, 2, 3, 2].length) (baseStart_7671281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7671281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7671281 prefixEnd_7671281 := by exact prefixLift 7671281
  have htrace : WordTrace (prefixWord ++ tailWord_7671281) baseStart_7671281 baseEnd_7671281 := by
    simpa [prefixWord, tailWord_7671281, baseEnd_7671281] using wordTrace_append hprefix tailTrace_7671281
  have hstable : (prefixWord ++ tailWord_7671281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7671281).length < 2 ^ (prefixWord ++ tailWord_7671281).sum := by decide
  have hdescent : baseEnd_7671281 < baseStart_7671281 := by decide
  rcases family_descends (prefixWord ++ tailWord_7671281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7671308 : List Nat := [2, 2, 1, 2, 6, 1, 1, 2, 1, 5]
def baseStart_7671308 : Nat := 118140960795 + 7671308 * 2 ^ 59
def prefixEnd_7671308 : Nat := 4983230072969 + 3 ^ 40 * 7671308 * 2
def baseEnd_7671308 : Nat := 1313022750893725735290101

theorem tailTrace_7671308 : CollatzResearch.WordTrace tailWord_7671308 prefixEnd_7671308 1313022750893725735290101 := by
  unfold tailWord_7671308
  simp only [CollatzResearch.WordTrace]
  refine ⟨139897794446084372972367289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186530392594779163963156385 139897794446084372972367289)
  ·
    refine ⟨104923345834563279729275467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139897794446084372972367289 104923345834563279729275467)
    ·
      refine ⟨157385018751844919593913201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104923345834563279729275467 157385018751844919593913201)
      ·
        refine ⟨118038764063883689695434901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157385018751844919593913201 118038764063883689695434901)
        ·
          refine ⟨5533067065494547954473511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 118038764063883689695434901 5533067065494547954473511)
          ·
            refine ⟨8299600598241821931710267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5533067065494547954473511 8299600598241821931710267)
            ·
              refine ⟨12449400897362732897565401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8299600598241821931710267 12449400897362732897565401)
              ·
                refine ⟨9337050673022049673174051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12449400897362732897565401 9337050673022049673174051)
                ·
                  refine ⟨14005576009533074509761077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9337050673022049673174051 14005576009533074509761077)
                  ·
                    refine ⟨1313022750893725735290101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14005576009533074509761077 1313022750893725735290101)
                    ·
                      rfl

theorem cell23_7671308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 2, 1, 5].length) (baseStart_7671308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7671308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7671308 prefixEnd_7671308 := by exact prefixLift 7671308
  have htrace : WordTrace (prefixWord ++ tailWord_7671308) baseStart_7671308 baseEnd_7671308 := by
    simpa [prefixWord, tailWord_7671308, baseEnd_7671308] using wordTrace_append hprefix tailTrace_7671308
  have hstable : (prefixWord ++ tailWord_7671308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7671308).length < 2 ^ (prefixWord ++ tailWord_7671308).sum := by decide
  have hdescent : baseEnd_7671308 < baseStart_7671308 := by decide
  rcases family_descends (prefixWord ++ tailWord_7671308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7671317 : List Nat := [1, 3, 2, 1, 3, 2, 2, 9]
def baseStart_7671317 : Nat := 118140960795 + 7671317 * 2 ^ 59
def prefixEnd_7671317 : Nat := 4983230072969 + 3 ^ 40 * 7671317 * 2
def baseEnd_7671317 : Nat := 145891587926187691505843

theorem tailTrace_7671317 : CollatzResearch.WordTrace tailWord_7671317 prefixEnd_7671317 145891587926187691505843 := by
  unfold tailWord_7671317
  simp only [CollatzResearch.WordTrace]
  refine ⟨279795917149136140481812205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186530611432757426987874803 279795917149136140481812205)
  ·
    refine ⟨104923468930926052680679577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 279795917149136140481812205 104923468930926052680679577)
    ·
      refine ⟨78692601698194539510509683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104923468930926052680679577 78692601698194539510509683)
      ·
        refine ⟨118038902547291809265764525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78692601698194539510509683 118038902547291809265764525)
        ·
          refine ⟨44264588455234428474661697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118038902547291809265764525 44264588455234428474661697)
          ·
            refine ⟨33198441341425821355996273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44264588455234428474661697 33198441341425821355996273)
            ·
              refine ⟨24898831006069366016997205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33198441341425821355996273 24898831006069366016997205)
              ·
                refine ⟨145891587926187691505843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24898831006069366016997205 145891587926187691505843)
                ·
                  rfl

theorem cell23_7671317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 9].length) (baseStart_7671317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7671317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7671317 prefixEnd_7671317 := by exact prefixLift 7671317
  have htrace : WordTrace (prefixWord ++ tailWord_7671317) baseStart_7671317 baseEnd_7671317 := by
    simpa [prefixWord, tailWord_7671317, baseEnd_7671317] using wordTrace_append hprefix tailTrace_7671317
  have hstable : (prefixWord ++ tailWord_7671317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7671317).length < 2 ^ (prefixWord ++ tailWord_7671317).sum := by decide
  have hdescent : baseEnd_7671317 < baseStart_7671317 := by decide
  rcases family_descends (prefixWord ++ tailWord_7671317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7671324 : List Nat := [2, 2, 3, 1, 2, 1, 3, 2, 1, 2, 4]
def baseStart_7671324 : Nat := 118140960795 + 7671324 * 2 ^ 59
def prefixEnd_7671324 : Nat := 4983230072969 + 3 ^ 40 * 7671324 * 2
def baseEnd_7671324 : Nat := 3939076468371649143270229

theorem tailTrace_7671324 : CollatzResearch.WordTrace tailWord_7671324 prefixEnd_7671324 3939076468371649143270229 := by
  unfold tailWord_7671324
  simp only [CollatzResearch.WordTrace]
  refine ⟨139898086230055390338658513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186530781640073853784878017 139898086230055390338658513)
  ·
    refine ⟨104923564672541542753993885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139898086230055390338658513 104923564672541542753993885)
    ·
      refine ⟨39346336752203078532747707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104923564672541542753993885 39346336752203078532747707)
      ·
        refine ⟨59019505128304617799121561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39346336752203078532747707 59019505128304617799121561)
        ·
          refine ⟨44264628846228463349341171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59019505128304617799121561 44264628846228463349341171)
          ·
            refine ⟨66396943269342695024011757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44264628846228463349341171 66396943269342695024011757)
            ·
              refine ⟨24898853726003510634004409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66396943269342695024011757 24898853726003510634004409)
              ·
                refine ⟨18674140294502632975503307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24898853726003510634004409 18674140294502632975503307)
                ·
                  refine ⟨28011210441753949463254961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18674140294502632975503307 28011210441753949463254961)
                  ·
                    refine ⟨21008407831315462097441221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28011210441753949463254961 21008407831315462097441221)
                    ·
                      refine ⟨3939076468371649143270229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21008407831315462097441221 3939076468371649143270229)
                      ·
                        rfl

theorem cell23_7671324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_7671324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7671324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7671324 prefixEnd_7671324 := by exact prefixLift 7671324
  have htrace : WordTrace (prefixWord ++ tailWord_7671324) baseStart_7671324 baseEnd_7671324 := by
    simpa [prefixWord, tailWord_7671324, baseEnd_7671324] using wordTrace_append hprefix tailTrace_7671324
  have hstable : (prefixWord ++ tailWord_7671324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7671324).length < 2 ^ (prefixWord ++ tailWord_7671324).sum := by decide
  have hdescent : baseEnd_7671324 < baseStart_7671324 := by decide
  rcases family_descends (prefixWord ++ tailWord_7671324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7671328 : List Nat := [2, 1, 1, 6, 1, 2, 3, 1, 1, 1, 4]
def baseStart_7671328 : Nat := 118140960795 + 7671328 * 2 ^ 59
def prefixEnd_7671328 : Nat := 4983230072969 + 3 ^ 40 * 7671328 * 2
def baseEnd_7671328 : Nat := 3939078522294267127620211

theorem tailTrace_7671328 : CollatzResearch.WordTrace tailWord_7671328 prefixEnd_7671328 3939078522294267127620211 := by
  unfold tailWord_7671328
  simp only [CollatzResearch.WordTrace]
  refine ⟨139898159176048144680231319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186530878901397526240308425 139898159176048144680231319)
  ·
    refine ⟨209847238764072217020346979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139898159176048144680231319 209847238764072217020346979)
    ·
      refine ⟨314770858146108325530520469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209847238764072217020346979 314770858146108325530520469)
      ·
        refine ⟨14754883975598827759243147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 314770858146108325530520469 14754883975598827759243147)
        ·
          refine ⟨22132325963398241638864721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14754883975598827759243147 22132325963398241638864721)
          ·
            refine ⟨16599244472548681229148541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22132325963398241638864721 16599244472548681229148541)
            ·
              refine ⟨6224716677205755460930703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16599244472548681229148541 6224716677205755460930703)
              ·
                refine ⟨9337075015808633191396055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6224716677205755460930703 9337075015808633191396055)
                ·
                  refine ⟨14005612523712949787094083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9337075015808633191396055 14005612523712949787094083)
                  ·
                    refine ⟨21008418785569424680641125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14005612523712949787094083 21008418785569424680641125)
                    ·
                      refine ⟨3939078522294267127620211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21008418785569424680641125 3939078522294267127620211)
                      ·
                        rfl

theorem cell23_7671328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_7671328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7671328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7671328 prefixEnd_7671328 := by exact prefixLift 7671328
  have htrace : WordTrace (prefixWord ++ tailWord_7671328) baseStart_7671328 baseEnd_7671328 := by
    simpa [prefixWord, tailWord_7671328, baseEnd_7671328] using wordTrace_append hprefix tailTrace_7671328
  have hstable : (prefixWord ++ tailWord_7671328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7671328).length < 2 ^ (prefixWord ++ tailWord_7671328).sum := by decide
  have hdescent : baseEnd_7671328 < baseStart_7671328 := by decide
  rcases family_descends (prefixWord ++ tailWord_7671328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7671331 : List Nat := [1, 1, 1, 4, 5, 2, 1, 1, 1, 1, 5]
def baseStart_7671331 : Nat := 118140960795 + 7671331 * 2 ^ 59
def prefixEnd_7671331 : Nat := 4983230072969 + 3 ^ 40 * 7671331 * 2
def baseEnd_7671331 : Nat := 3939080062736230615882697

theorem tailTrace_7671331 : CollatzResearch.WordTrace tailWord_7671331 prefixEnd_7671331 3939080062736230615882697 := by
  unfold tailWord_7671331
  simp only [CollatzResearch.WordTrace]
  refine ⟨279796427771085420872821847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186530951847390280581881231 279796427771085420872821847)
  ·
    refine ⟨419694641656628131309232771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279796427771085420872821847 419694641656628131309232771)
    ·
      refine ⟨629541962484942196963849157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419694641656628131309232771 629541962484942196963849157)
      ·
        refine ⟨118039117965926661930721717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 629541962484942196963849157 118039117965926661930721717)
        ·
          refine ⟨11066167309305624556005161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 118039117965926661930721717 11066167309305624556005161)
          ·
            refine ⟨8299625481979218417003871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11066167309305624556005161 8299625481979218417003871)
            ·
              refine ⟨12449438222968827625505807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8299625481979218417003871 12449438222968827625505807)
              ·
                refine ⟨18674157334453241438258711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12449438222968827625505807 18674157334453241438258711)
                ·
                  refine ⟨28011236001679862157388067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18674157334453241438258711 28011236001679862157388067)
                  ·
                    refine ⟨42016854002519793236082101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28011236001679862157388067 42016854002519793236082101)
                    ·
                      refine ⟨3939080062736230615882697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42016854002519793236082101 3939080062736230615882697)
                      ·
                        rfl

theorem cell23_7671331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 1, 1, 1, 5].length) (baseStart_7671331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7671331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7671331 prefixEnd_7671331 := by exact prefixLift 7671331
  have htrace : WordTrace (prefixWord ++ tailWord_7671331) baseStart_7671331 baseEnd_7671331 := by
    simpa [prefixWord, tailWord_7671331, baseEnd_7671331] using wordTrace_append hprefix tailTrace_7671331
  have hstable : (prefixWord ++ tailWord_7671331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7671331).length < 2 ^ (prefixWord ++ tailWord_7671331).sum := by decide
  have hdescent : baseEnd_7671331 < baseStart_7671331 := by decide
  rcases family_descends (prefixWord ++ tailWord_7671331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7671347 : List Nat := [1, 1, 1, 2, 4, 3, 1, 1, 2, 7]
def baseStart_7671347 : Nat := 118140960795 + 7671347 * 2 ^ 59
def prefixEnd_7671347 : Nat := 4983230072969 + 3 ^ 40 * 7671347 * 2
def baseEnd_7671347 : Nat := 1313029426142234184427541

theorem tailTrace_7671347 : CollatzResearch.WordTrace tailWord_7671347 prefixEnd_7671347 1313029426142234184427541 := by
  unfold tailWord_7671347
  simp only [CollatzResearch.WordTrace]
  refine ⟨279797011339027455605404295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186531340892684970403602863 279797011339027455605404295)
  ·
    refine ⟨419695517008541183408106443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279797011339027455605404295 419695517008541183408106443)
    ·
      refine ⟨629543275512811775112159665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419695517008541183408106443 629543275512811775112159665)
      ·
        refine ⟨472157456634608831334119749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 629543275512811775112159665 472157456634608831334119749)
        ·
          refine ⟨88529523118989155875147453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 472157456634608831334119749 88529523118989155875147453)
          ·
            refine ⟨33198571169620933453180295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88529523118989155875147453 33198571169620933453180295)
            ·
              refine ⟨49797856754431400179770443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33198571169620933453180295 49797856754431400179770443)
              ·
                refine ⟨74696785131647100269655665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49797856754431400179770443 74696785131647100269655665)
                ·
                  refine ⟨56022588848735325202241749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74696785131647100269655665 56022588848735325202241749)
                  ·
                    refine ⟨1313029426142234184427541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56022588848735325202241749 1313029426142234184427541)
                    ·
                      rfl

theorem cell23_7671347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 2, 7].length) (baseStart_7671347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7671347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7671347 prefixEnd_7671347 := by exact prefixLift 7671347
  have htrace : WordTrace (prefixWord ++ tailWord_7671347) baseStart_7671347 baseEnd_7671347 := by
    simpa [prefixWord, tailWord_7671347, baseEnd_7671347] using wordTrace_append hprefix tailTrace_7671347
  have hstable : (prefixWord ++ tailWord_7671347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7671347).length < 2 ^ (prefixWord ++ tailWord_7671347).sum := by decide
  have hdescent : baseEnd_7671347 < baseStart_7671347 := by decide
  rcases family_descends (prefixWord ++ tailWord_7671347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7671361 : List Nat := [1, 2, 5, 1, 1, 1, 4, 1, 1, 3, 3]
def baseStart_7671361 : Nat := 118140960795 + 7671361 * 2 ^ 59
def prefixEnd_7671361 : Nat := 4983230072969 + 3 ^ 40 * 7671361 * 2
def baseEnd_7671361 : Nat := 3939095467155865498507559

theorem tailTrace_7671361 : CollatzResearch.WordTrace tailWord_7671361 prefixEnd_7671361 3939095467155865498507559 := by
  unfold tailWord_7671361
  simp only [CollatzResearch.WordTrace]
  refine ⟨279797521960976735996413937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186531681307317823997609291 279797521960976735996413937)
  ·
    refine ⟨209848141470732551997310453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279797521960976735996413937 209848141470732551997310453)
    ·
      refine ⟨19673263262881176749747855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 209848141470732551997310453 19673263262881176749747855)
      ·
        refine ⟨29509894894321765124621783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19673263262881176749747855 29509894894321765124621783)
        ·
          refine ⟨44264842341482647686932675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29509894894321765124621783 44264842341482647686932675)
          ·
            refine ⟨66397263512223971530399013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44264842341482647686932675 66397263512223971530399013)
            ·
              refine ⟨12449486908541994661949815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66397263512223971530399013 12449486908541994661949815)
              ·
                refine ⟨18674230362812991992924723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12449486908541994661949815 18674230362812991992924723)
                ·
                  refine ⟨28011345544219487989387085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18674230362812991992924723 28011345544219487989387085)
                  ·
                    refine ⟨10504254579082307996020157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28011345544219487989387085 10504254579082307996020157)
                    ·
                      refine ⟨3939095467155865498507559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10504254579082307996020157 3939095467155865498507559)
                      ·
                        rfl

theorem cell23_7671361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_7671361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7671361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7671361 prefixEnd_7671361 := by exact prefixLift 7671361
  have htrace : WordTrace (prefixWord ++ tailWord_7671361) baseStart_7671361 baseEnd_7671361 := by
    simpa [prefixWord, tailWord_7671361, baseEnd_7671361] using wordTrace_append hprefix tailTrace_7671361
  have hstable : (prefixWord ++ tailWord_7671361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7671361).length < 2 ^ (prefixWord ++ tailWord_7671361).sum := by decide
  have hdescent : baseEnd_7671361 < baseStart_7671361 := by decide
  rcases family_descends (prefixWord ++ tailWord_7671361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7671371 : List Nat := [1, 1, 1, 1, 3, 1, 3, 6, 1, 3, 2]
def baseStart_7671371 : Nat := 118140960795 + 7671371 * 2 ^ 59
def prefixEnd_7671371 : Nat := 4983230072969 + 3 ^ 40 * 7671371 * 2
def baseEnd_7671371 : Nat := 3939100601962410459382513

theorem tailTrace_7671371 : CollatzResearch.WordTrace tailWord_7671371 prefixEnd_7671371 3939100601962410459382513 := by
  unfold tailWord_7671371
  simp only [CollatzResearch.WordTrace]
  refine ⟨279797886690940507704277967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186531924460627005136185311 279797886690940507704277967)
  ·
    refine ⟨419696830036410761556416951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279797886690940507704277967 419696830036410761556416951)
    ·
      refine ⟨629545245054616142334625427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419696830036410761556416951 629545245054616142334625427)
      ·
        refine ⟨944317867581924213501938141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 629545245054616142334625427 944317867581924213501938141)
        ·
          refine ⟨354119200343221580063226803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 944317867581924213501938141 354119200343221580063226803)
          ·
            refine ⟨531178800514832370094840205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 354119200343221580063226803 531178800514832370094840205)
            ·
              refine ⟨199192050193062138785565077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 531178800514832370094840205 199192050193062138785565077)
              ·
                refine ⟨9337127352799787755573363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 199192050193062138785565077 9337127352799787755573363)
                ·
                  refine ⟨14005691029199681633360045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9337127352799787755573363 14005691029199681633360045)
                  ·
                    refine ⟨5252134135949880612510017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14005691029199681633360045 5252134135949880612510017)
                    ·
                      refine ⟨3939100601962410459382513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5252134135949880612510017 3939100601962410459382513)
                      ·
                        rfl

theorem cell23_7671371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 6, 1, 3, 2].length) (baseStart_7671371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7671371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7671371 prefixEnd_7671371 := by exact prefixLift 7671371
  have htrace : WordTrace (prefixWord ++ tailWord_7671371) baseStart_7671371 baseEnd_7671371 := by
    simpa [prefixWord, tailWord_7671371, baseEnd_7671371] using wordTrace_append hprefix tailTrace_7671371
  have hstable : (prefixWord ++ tailWord_7671371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7671371).length < 2 ^ (prefixWord ++ tailWord_7671371).sum := by decide
  have hdescent : baseEnd_7671371 < baseStart_7671371 := by decide
  rcases family_descends (prefixWord ++ tailWord_7671371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7671377 : List Nat := [1, 2, 2, 1, 3, 2, 1, 2, 1, 8]
def baseStart_7671377 : Nat := 118140960795 + 7671377 * 2 ^ 59
def prefixEnd_7671377 : Nat := 4983230072969 + 3 ^ 40 * 7671377 * 2
def baseEnd_7671377 : Nat := 1313034560948779145302495

theorem tailTrace_7671377 : CollatzResearch.WordTrace tailWord_7671377 prefixEnd_7671377 1313034560948779145302495 := by
  unfold tailWord_7671377
  simp only [CollatzResearch.WordTrace]
  refine ⟨279798105528918770728996385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186532070352612513819330923 279798105528918770728996385)
  ·
    refine ⟨209848579146689078046747289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279798105528918770728996385 209848579146689078046747289)
    ·
      refine ⟨157386434360016808535060467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209848579146689078046747289 157386434360016808535060467)
      ·
        refine ⟨236079651540025212802590701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157386434360016808535060467 236079651540025212802590701)
        ·
          refine ⟨88529869327509454800971513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 236079651540025212802590701 88529869327509454800971513)
          ·
            refine ⟨66397401995632091100728635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88529869327509454800971513 66397401995632091100728635)
            ·
              refine ⟨99596102993448136651092953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66397401995632091100728635 99596102993448136651092953)
              ·
                refine ⟨74697077245086102488319715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99596102993448136651092953 74697077245086102488319715)
                ·
                  refine ⟨112045615867629153732479573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74697077245086102488319715 112045615867629153732479573)
                  ·
                    refine ⟨1313034560948779145302495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 112045615867629153732479573 1313034560948779145302495)
                    ·
                      rfl

theorem cell23_7671377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 8].length) (baseStart_7671377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7671377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7671377 prefixEnd_7671377 := by exact prefixLift 7671377
  have htrace : WordTrace (prefixWord ++ tailWord_7671377) baseStart_7671377 baseEnd_7671377 := by
    simpa [prefixWord, tailWord_7671377, baseEnd_7671377] using wordTrace_append hprefix tailTrace_7671377
  have hstable : (prefixWord ++ tailWord_7671377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7671377).length < 2 ^ (prefixWord ++ tailWord_7671377).sum := by decide
  have hdescent : baseEnd_7671377 < baseStart_7671377 := by decide
  rcases family_descends (prefixWord ++ tailWord_7671377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7671382 : List Nat := [5, 2, 2, 2, 1, 1, 1, 3, 1, 2, 3]
def baseStart_7671382 : Nat := 118140960795 + 7671382 * 2 ^ 59
def prefixEnd_7671382 : Nat := 4983230072969 + 3 ^ 40 * 7671382 * 2
def baseEnd_7671382 : Nat := 3939106250249609916344963

theorem tailTrace_7671382 : CollatzResearch.WordTrace tailWord_7671382 prefixEnd_7671382 3939106250249609916344963 := by
  unfold tailWord_7671382
  simp only [CollatzResearch.WordTrace]
  refine ⟨17487392993368791036433025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 186532191929267104388618933 17487392993368791036433025)
  ·
    refine ⟨13115544745026593277324769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17487392993368791036433025 13115544745026593277324769)
    ·
      refine ⟨9836658558769944957993577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13115544745026593277324769 9836658558769944957993577)
      ·
        refine ⟨7377493919077458718495183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9836658558769944957993577 7377493919077458718495183)
        ·
          refine ⟨11066240878616188077742775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7377493919077458718495183 11066240878616188077742775)
          ·
            refine ⟨16599361317924282116614163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11066240878616188077742775 16599361317924282116614163)
            ·
              refine ⟨24899041976886423174921245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16599361317924282116614163 24899041976886423174921245)
              ·
                refine ⟨9337140741332408690595467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24899041976886423174921245 9337140741332408690595467)
                ·
                  refine ⟨14005711111998613035893201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9337140741332408690595467 14005711111998613035893201)
                  ·
                    refine ⟨10504283333998959776919901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14005711111998613035893201 10504283333998959776919901)
                    ·
                      refine ⟨3939106250249609916344963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10504283333998959776919901 3939106250249609916344963)
                      ·
                        rfl

theorem cell23_7671382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_7671382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7671382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7671382 prefixEnd_7671382 := by exact prefixLift 7671382
  have htrace : WordTrace (prefixWord ++ tailWord_7671382) baseStart_7671382 baseEnd_7671382 := by
    simpa [prefixWord, tailWord_7671382, baseEnd_7671382] using wordTrace_append hprefix tailTrace_7671382
  have hstable : (prefixWord ++ tailWord_7671382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7671382).length < 2 ^ (prefixWord ++ tailWord_7671382).sum := by decide
  have hdescent : baseEnd_7671382 < baseStart_7671382 := by decide
  rcases family_descends (prefixWord ++ tailWord_7671382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7671474 : List Nat := [3, 2, 1, 1, 1, 2, 2, 1, 3, 3, 4]
def baseStart_7671474 : Nat := 118140960795 + 7671474 * 2 ^ 59
def prefixEnd_7671474 : Nat := 4983230072969 + 3 ^ 40 * 7671474 * 2
def baseEnd_7671474 : Nat := 3939153490469823556394539

theorem tailTrace_7671474 : CollatzResearch.WordTrace tailWord_7671474 prefixEnd_7671474 3939153490469823556394539 := by
  unfold tailWord_7671474
  simp only [CollatzResearch.WordTrace]
  refine ⟨69950410852391839073819369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186534428939711570863518317 69950410852391839073819369)
  ·
    refine ⟨52462808139293879305364527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69950410852391839073819369 52462808139293879305364527)
    ·
      refine ⟨78694212208940818958046791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52462808139293879305364527 78694212208940818958046791)
      ·
        refine ⟨118041318313411228437070187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78694212208940818958046791 118041318313411228437070187)
        ·
          refine ⟨177061977470116842655605281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118041318313411228437070187 177061977470116842655605281)
          ·
            refine ⟨132796483102587631991703961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177061977470116842655605281 132796483102587631991703961)
            ·
              refine ⟨99597362326940723993777971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132796483102587631991703961 99597362326940723993777971)
              ·
                refine ⟨149396043490411085990666957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99597362326940723993777971 149396043490411085990666957)
                ·
                  refine ⟨56023516308904157246500109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 149396043490411085990666957 56023516308904157246500109)
                  ·
                    refine ⟨21008818615839058967437541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56023516308904157246500109 21008818615839058967437541)
                    ·
                      refine ⟨3939153490469823556394539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21008818615839058967437541 3939153490469823556394539)
                      ·
                        rfl

theorem cell23_7671474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 3, 3, 4].length) (baseStart_7671474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7671474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7671474 prefixEnd_7671474 := by exact prefixLift 7671474
  have htrace : WordTrace (prefixWord ++ tailWord_7671474) baseStart_7671474 baseEnd_7671474 := by
    simpa [prefixWord, tailWord_7671474, baseEnd_7671474] using wordTrace_append hprefix tailTrace_7671474
  have hstable : (prefixWord ++ tailWord_7671474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7671474).length < 2 ^ (prefixWord ++ tailWord_7671474).sum := by decide
  have hdescent : baseEnd_7671474 < baseStart_7671474 := by decide
  rcases family_descends (prefixWord ++ tailWord_7671474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7671508 : List Nat := [2, 4, 1, 3, 1, 1, 2, 2, 2, 1, 4]
def baseStart_7671508 : Nat := 118140960795 + 7671508 * 2 ^ 59
def prefixEnd_7671508 : Nat := 4983230072969 + 3 ^ 40 * 7671508 * 2
def baseEnd_7671508 : Nat := 3939170948812076423369383

theorem tailTrace_7671508 : CollatzResearch.WordTrace tailWord_7671508 prefixEnd_7671508 3939170948812076423369383 := by
  unfold tailWord_7671508
  simp only [CollatzResearch.WordTrace]
  refine ⟨139901441745722090051007589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186535255660962786734676785 139901441745722090051007589)
  ·
    refine ⟨26231520327322891884563923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139901441745722090051007589 26231520327322891884563923)
    ·
      refine ⟨39347280490984337826845885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26231520327322891884563923 39347280490984337826845885)
      ·
        refine ⟨14755230184119126685067207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39347280490984337826845885 14755230184119126685067207)
        ·
          refine ⟨22132845276178690027600811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14755230184119126685067207 22132845276178690027600811)
          ·
            refine ⟨33199267914268035041401217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22132845276178690027600811 33199267914268035041401217)
            ·
              refine ⟨24899450935701026281050913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33199267914268035041401217 24899450935701026281050913)
              ·
                refine ⟨18674588201775769710788185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24899450935701026281050913 18674588201775769710788185)
                ·
                  refine ⟨14005941151331827283091139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18674588201775769710788185 14005941151331827283091139)
                  ·
                    refine ⟨21008911726997740924636709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14005941151331827283091139 21008911726997740924636709)
                    ·
                      refine ⟨3939170948812076423369383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21008911726997740924636709 3939170948812076423369383)
                      ·
                        rfl

theorem cell23_7671508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_7671508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7671508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7671508 prefixEnd_7671508 := by exact prefixLift 7671508
  have htrace : WordTrace (prefixWord ++ tailWord_7671508) baseStart_7671508 baseEnd_7671508 := by
    simpa [prefixWord, tailWord_7671508, baseEnd_7671508] using wordTrace_append hprefix tailTrace_7671508
  have hstable : (prefixWord ++ tailWord_7671508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7671508).length < 2 ^ (prefixWord ++ tailWord_7671508).sum := by decide
  have hdescent : baseEnd_7671508 < baseStart_7671508 := by decide
  rcases family_descends (prefixWord ++ tailWord_7671508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7671511 : List Nat := [1, 1, 3, 2, 1, 3, 1, 4, 2, 2, 3]
def baseStart_7671511 : Nat := 118140960795 + 7671511 * 2 ^ 59
def prefixEnd_7671511 : Nat := 4983230072969 + 3 ^ 40 * 7671511 * 2
def baseEnd_7671511 : Nat := 3939172489254039911631869

theorem tailTrace_7671511 : CollatzResearch.WordTrace tailWord_7671511 prefixEnd_7671511 3939172489254039911631869 := by
  unfold tailWord_7671511
  simp only [CollatzResearch.WordTrace]
  refine ⟨279802992910433311614374387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186535328606955541076249591 279802992910433311614374387)
  ·
    refine ⟨419704489365649967421561581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279802992910433311614374387 419704489365649967421561581)
    ·
      refine ⟨157389183512118737783085593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 419704489365649967421561581 157389183512118737783085593)
      ·
        refine ⟨118041887634089053337314195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157389183512118737783085593 118041887634089053337314195)
        ·
          refine ⟨177062831451133580005971293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118041887634089053337314195 177062831451133580005971293)
          ·
            refine ⟨66398561794175092502239235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177062831451133580005971293 66398561794175092502239235)
            ·
              refine ⟨99597842691262638753358853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66398561794175092502239235 99597842691262638753358853)
              ·
                refine ⟨18674595504611744766254785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99597842691262638753358853 18674595504611744766254785)
                ·
                  refine ⟨14005946628458808574691089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18674595504611744766254785 14005946628458808574691089)
                  ·
                    refine ⟨10504459971344106431018317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14005946628458808574691089 10504459971344106431018317)
                    ·
                      refine ⟨3939172489254039911631869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10504459971344106431018317 3939172489254039911631869)
                      ·
                        rfl

theorem cell23_7671511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 4, 2, 2, 3].length) (baseStart_7671511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7671511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7671511 prefixEnd_7671511 := by exact prefixLift 7671511
  have htrace : WordTrace (prefixWord ++ tailWord_7671511) baseStart_7671511 baseEnd_7671511 := by
    simpa [prefixWord, tailWord_7671511, baseEnd_7671511] using wordTrace_append hprefix tailTrace_7671511
  have hstable : (prefixWord ++ tailWord_7671511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7671511).length < 2 ^ (prefixWord ++ tailWord_7671511).sum := by decide
  have hdescent : baseEnd_7671511 < baseStart_7671511 := by decide
  rcases family_descends (prefixWord ++ tailWord_7671511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7671575 : List Nat := [1, 1, 3, 4, 2, 2, 2, 1, 3, 1, 3]
def baseStart_7671575 : Nat := 118140960795 + 7671575 * 2 ^ 59
def prefixEnd_7671575 : Nat := 4983230072969 + 3 ^ 40 * 7671575 * 2
def baseEnd_7671575 : Nat := 3939205352015927661231575

theorem tailTrace_7671575 : CollatzResearch.WordTrace tailWord_7671575 prefixEnd_7671575 3939205352015927661231575 := by
  unfold tailWord_7671575
  simp only [CollatzResearch.WordTrace]
  refine ⟨279805327182201450544704179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186536884788134300363136119 279805327182201450544704179)
  ·
    refine ⟨419707990773302175817056269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279805327182201450544704179 419707990773302175817056269)
    ·
      refine ⟨157390496539988315931396101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 419707990773302175817056269 157390496539988315931396101)
      ·
        refine ⟨29510718101247809237136769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157390496539988315931396101 29510718101247809237136769)
        ·
          refine ⟨22133038575935856927852577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29510718101247809237136769 22133038575935856927852577)
          ·
            refine ⟨16599778931951892695889433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22133038575935856927852577 16599778931951892695889433)
            ·
              refine ⟨12449834198963919521917075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16599778931951892695889433 12449834198963919521917075)
              ·
                refine ⟨18674751298445879282875613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12449834198963919521917075 18674751298445879282875613)
                ·
                  refine ⟨7003031736917204731078355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18674751298445879282875613 7003031736917204731078355)
                  ·
                    refine ⟨10504547605375807096617533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7003031736917204731078355 10504547605375807096617533)
                    ·
                      refine ⟨3939205352015927661231575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10504547605375807096617533 3939205352015927661231575)
                      ·
                        rfl

theorem cell23_7671575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_7671575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7671575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7671575 prefixEnd_7671575 := by exact prefixLift 7671575
  have htrace : WordTrace (prefixWord ++ tailWord_7671575) baseStart_7671575 baseEnd_7671575 := by
    simpa [prefixWord, tailWord_7671575, baseEnd_7671575] using wordTrace_append hprefix tailTrace_7671575
  have hstable : (prefixWord ++ tailWord_7671575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7671575).length < 2 ^ (prefixWord ++ tailWord_7671575).sum := by decide
  have hdescent : baseEnd_7671575 < baseStart_7671575 := by decide
  rcases family_descends (prefixWord ++ tailWord_7671575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7671652 : List Nat := [2, 3, 1, 1, 5, 2, 1, 2, 1, 2, 3]
def baseStart_7671652 : Nat := 118140960795 + 7671652 * 2 ^ 59
def prefixEnd_7671652 : Nat := 4983230072969 + 3 ^ 40 * 7671652 * 2
def baseEnd_7671652 : Nat := 3939244890026323859968721

theorem tailTrace_7671652 : CollatzResearch.WordTrace tailWord_7671652 prefixEnd_7671652 3939244890026323859968721 := by
  unfold tailWord_7671652
  simp only [CollatzResearch.WordTrace]
  refine ⟨139904067801461246347628605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186538757068614995130171473 139904067801461246347628605)
  ·
    refine ⟨52464025425547967380360727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139904067801461246347628605 52464025425547967380360727)
    ·
      refine ⟨78696038138321951070541091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52464025425547967380360727 78696038138321951070541091)
      ·
        refine ⟨118044057207482926605811637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78696038138321951070541091 118044057207482926605811637)
        ·
          refine ⟨11066630363201524369294841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 118044057207482926605811637 11066630363201524369294841)
          ·
            refine ⟨8299972772401143276971131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11066630363201524369294841 8299972772401143276971131)
            ·
              refine ⟨12449959158601714915456697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8299972772401143276971131 12449959158601714915456697)
              ·
                refine ⟨9337469368951286186592523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12449959158601714915456697 9337469368951286186592523)
                ·
                  refine ⟨14006204053426929279888785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9337469368951286186592523 14006204053426929279888785)
                  ·
                    refine ⟨10504653040070196959916589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14006204053426929279888785 10504653040070196959916589)
                    ·
                      refine ⟨3939244890026323859968721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10504653040070196959916589 3939244890026323859968721)
                      ·
                        rfl

theorem cell23_7671652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 2, 1, 2, 3].length) (baseStart_7671652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7671652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7671652 prefixEnd_7671652 := by exact prefixLift 7671652
  have htrace : WordTrace (prefixWord ++ tailWord_7671652) baseStart_7671652 baseEnd_7671652 := by
    simpa [prefixWord, tailWord_7671652, baseEnd_7671652] using wordTrace_append hprefix tailTrace_7671652
  have hstable : (prefixWord ++ tailWord_7671652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7671652).length < 2 ^ (prefixWord ++ tailWord_7671652).sum := by decide
  have hdescent : baseEnd_7671652 < baseStart_7671652 := by decide
  rcases family_descends (prefixWord ++ tailWord_7671652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7671661 : List Nat := [1, 5, 1, 1, 1, 1, 2, 1, 1, 4, 5]
def baseStart_7671661 : Nat := 118140960795 + 7671661 * 2 ^ 59
def prefixEnd_7671661 : Nat := 4983230072969 + 3 ^ 40 * 7671661 * 2
def baseEnd_7671661 : Nat := 3939249511352214324756179

theorem tailTrace_7671661 : CollatzResearch.WordTrace tailWord_7671661 prefixEnd_7671661 3939249511352214324756179 := by
  unfold tailWord_7671661
  simp only [CollatzResearch.WordTrace]
  refine ⟨279808463859889887232334837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186538975906593258154889891 279808463859889887232334837)
  ·
    refine ⟨26232043486864676928031391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 279808463859889887232334837 26232043486864676928031391)
    ·
      refine ⟨39348065230297015392047087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26232043486864676928031391 39348065230297015392047087)
      ·
        refine ⟨59022097845445523088070631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39348065230297015392047087 59022097845445523088070631)
        ·
          refine ⟨88533146768168284632105947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59022097845445523088070631 88533146768168284632105947)
          ·
            refine ⟨132799720152252426948158921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88533146768168284632105947 132799720152252426948158921)
            ·
              refine ⟨99599790114189320211119191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132799720152252426948158921 99599790114189320211119191)
              ·
                refine ⟨149399685171283980316678787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99599790114189320211119191 149399685171283980316678787)
                ·
                  refine ⟨224099527756925970475018181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 149399685171283980316678787 224099527756925970475018181)
                  ·
                    refine ⟨42018661454423619464065909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 224099527756925970475018181 42018661454423619464065909)
                    ·
                      refine ⟨3939249511352214324756179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42018661454423619464065909 3939249511352214324756179)
                      ·
                        rfl

theorem cell23_7671661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_7671661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7671661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7671661 prefixEnd_7671661 := by exact prefixLift 7671661
  have htrace : WordTrace (prefixWord ++ tailWord_7671661) baseStart_7671661 baseEnd_7671661 := by
    simpa [prefixWord, tailWord_7671661, baseEnd_7671661] using wordTrace_append hprefix tailTrace_7671661
  have hstable : (prefixWord ++ tailWord_7671661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7671661).length < 2 ^ (prefixWord ++ tailWord_7671661).sum := by decide
  have hdescent : baseEnd_7671661 < baseStart_7671661 := by decide
  rcases family_descends (prefixWord ++ tailWord_7671661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7671698 : List Nat := [3, 2, 3, 2, 1, 1, 1, 1, 1, 8]
def baseStart_7671698 : Nat := 118140960795 + 7671698 * 2 ^ 59
def prefixEnd_7671698 : Nat := 4983230072969 + 3 ^ 40 * 7671698 * 2
def baseEnd_7671698 : Nat := 1313089503378810226664503

theorem tailTrace_7671698 : CollatzResearch.WordTrace tailWord_7671698 prefixEnd_7671698 1313089503378810226664503 := by
  unfold tailWord_7671698
  simp only [CollatzResearch.WordTrace]
  refine ⟨69952453340188960637857937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186539875573837228367621165 69952453340188960637857937)
  ·
    refine ⟨52464340005141720478393453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69952453340188960637857937 52464340005141720478393453)
    ·
      refine ⟨19674127501928145179397545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52464340005141720478393453 19674127501928145179397545)
      ·
        refine ⟨14755595626446108884548159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19674127501928145179397545 14755595626446108884548159)
        ·
          refine ⟨22133393439669163326822239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14755595626446108884548159 22133393439669163326822239)
          ·
            refine ⟨33200090159503744990233359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22133393439669163326822239 33200090159503744990233359)
            ·
              refine ⟨49800135239255617485350039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33200090159503744990233359 49800135239255617485350039)
              ·
                refine ⟨74700202858883426228025059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49800135239255617485350039 74700202858883426228025059)
                ·
                  refine ⟨112050304288325139342037589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74700202858883426228025059 112050304288325139342037589)
                  ·
                    refine ⟨1313089503378810226664503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 112050304288325139342037589 1313089503378810226664503)
                    ·
                      rfl

theorem cell23_7671698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_7671698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7671698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7671698 prefixEnd_7671698 := by exact prefixLift 7671698
  have htrace : WordTrace (prefixWord ++ tailWord_7671698) baseStart_7671698 baseEnd_7671698 := by
    simpa [prefixWord, tailWord_7671698, baseEnd_7671698] using wordTrace_append hprefix tailTrace_7671698
  have hstable : (prefixWord ++ tailWord_7671698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7671698).length < 2 ^ (prefixWord ++ tailWord_7671698).sum := by decide
  have hdescent : baseEnd_7671698 < baseStart_7671698 := by decide
  rcases family_descends (prefixWord ++ tailWord_7671698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7671751 : List Nat := [1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 7]
def baseStart_7671751 : Nat := 118140960795 + 7671751 * 2 ^ 59
def prefixEnd_7671751 : Nat := 4983230072969 + 3 ^ 40 * 7671751 * 2
def baseEnd_7671751 : Nat := 3939295724611118972630765

theorem tailTrace_7671751 : CollatzResearch.WordTrace tailWord_7671751 prefixEnd_7671751 3939295724611118972630765 := by
  unfold tailWord_7671751
  simp only [CollatzResearch.WordTrace]
  refine ⟨279811746429563832603111107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186541164286375888402074071 279811746429563832603111107)
  ·
    refine ⟨419717619644345748904666661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279811746429563832603111107 419717619644345748904666661)
    ·
      refine ⟨78697053683314827919624999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 419717619644345748904666661 78697053683314827919624999)
      ·
        refine ⟨118045580524972241879437499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78697053683314827919624999 118045580524972241879437499)
        ·
          refine ⟨177068370787458362819156249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118045580524972241879437499 177068370787458362819156249)
          ·
            refine ⟨132801278090593772114367187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177068370787458362819156249 132801278090593772114367187)
            ·
              refine ⟨199201917135890658171550781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132801278090593772114367187 199201917135890658171550781)
              ·
                refine ⟨74700718925958996814331543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 199201917135890658171550781 74700718925958996814331543)
                ·
                  refine ⟨112051078388938495221497315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74700718925958996814331543 112051078388938495221497315)
                  ·
                    refine ⟨168076617583407742832245973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 112051078388938495221497315 168076617583407742832245973)
                    ·
                      refine ⟨3939295724611118972630765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 168076617583407742832245973 3939295724611118972630765)
                      ·
                        rfl

theorem cell23_7671751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 7].length) (baseStart_7671751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7671751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7671751 prefixEnd_7671751 := by exact prefixLift 7671751
  have htrace : WordTrace (prefixWord ++ tailWord_7671751) baseStart_7671751 baseEnd_7671751 := by
    simpa [prefixWord, tailWord_7671751, baseEnd_7671751] using wordTrace_append hprefix tailTrace_7671751
  have hstable : (prefixWord ++ tailWord_7671751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7671751).length < 2 ^ (prefixWord ++ tailWord_7671751).sum := by decide
  have hdescent : baseEnd_7671751 < baseStart_7671751 := by decide
  rcases family_descends (prefixWord ++ tailWord_7671751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7671788 : List Nat := [2, 2, 1, 1, 2, 1, 1, 4, 5, 4]
def baseStart_7671788 : Nat := 118140960795 + 7671788 * 2 ^ 59
def prefixEnd_7671788 : Nat := 4983230072969 + 3 ^ 40 * 7671788 * 2
def baseEnd_7671788 : Nat := 1313104907798445109289365

theorem tailTrace_7671788 : CollatzResearch.WordTrace tailWord_7671788 prefixEnd_7671788 1313104907798445109289365 := by
  unfold tailWord_7671788
  simp only [CollatzResearch.WordTrace]
  refine ⟨139906547965214893961104009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186542063953619858614805345 139906547965214893961104009)
  ·
    refine ⟨104929910973911170470828007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139906547965214893961104009 104929910973911170470828007)
    ·
      refine ⟨157394866460866755706242011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104929910973911170470828007 157394866460866755706242011)
      ·
        refine ⟨236092299691300133559363017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157394866460866755706242011 236092299691300133559363017)
        ·
          refine ⟨177069224768475100169522263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236092299691300133559363017 177069224768475100169522263)
          ·
            refine ⟨265603837152712650254283395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177069224768475100169522263 265603837152712650254283395)
            ·
              refine ⟨398405755729068975381425093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265603837152712650254283395 398405755729068975381425093)
              ·
                refine ⟨74701079199200432884017205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 398405755729068975381425093 74701079199200432884017205)
                ·
                  refine ⟨7003226174925040582876613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74701079199200432884017205 7003226174925040582876613)
                  ·
                    refine ⟨1313104907798445109289365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7003226174925040582876613 1313104907798445109289365)
                    ·
                      rfl

theorem cell23_7671788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 4].length) (baseStart_7671788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7671788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7671788 prefixEnd_7671788 := by exact prefixLift 7671788
  have htrace : WordTrace (prefixWord ++ tailWord_7671788) baseStart_7671788 baseEnd_7671788 := by
    simpa [prefixWord, tailWord_7671788, baseEnd_7671788] using wordTrace_append hprefix tailTrace_7671788
  have hstable : (prefixWord ++ tailWord_7671788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7671788).length < 2 ^ (prefixWord ++ tailWord_7671788).sum := by decide
  have hdescent : baseEnd_7671788 < baseStart_7671788 := by decide
  rcases family_descends (prefixWord ++ tailWord_7671788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7671805 : List Nat := [1, 4, 1, 1, 1, 2, 5, 1, 3, 4]
def baseStart_7671805 : Nat := 118140960795 + 7671805 * 2 ^ 59
def prefixEnd_7671805 : Nat := 4983230072969 + 3 ^ 40 * 7671805 * 2
def baseEnd_7671805 : Nat := 1313107817522153920451839

theorem tailTrace_7671805 : CollatzResearch.WordTrace tailWord_7671805 prefixEnd_7671805 1313107817522153920451839 := by
  unfold tailWord_7671805
  simp only [CollatzResearch.WordTrace]
  refine ⟨279813715971368199825576869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186542477314245466550384579 279813715971368199825576869)
  ·
    refine ⟨52465071744631537467295663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 279813715971368199825576869 52465071744631537467295663)
    ·
      refine ⟨78697607616947306200943495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52465071744631537467295663 78697607616947306200943495)
      ·
        refine ⟨118046411425420959301415243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78697607616947306200943495 118046411425420959301415243)
        ·
          refine ⟨177069617138131438952122865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118046411425420959301415243 177069617138131438952122865)
          ·
            refine ⟨132802212853598579214092149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177069617138131438952122865 132802212853598579214092149)
            ·
              refine ⟨12450207455024866801321139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 132802212853598579214092149 12450207455024866801321139)
              ·
                refine ⟨18675311182537300201981709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12450207455024866801321139 18675311182537300201981709)
                ·
                  refine ⟨7003241693451487575743141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18675311182537300201981709 7003241693451487575743141)
                  ·
                    refine ⟨1313107817522153920451839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7003241693451487575743141 1313107817522153920451839)
                    ·
                      rfl

theorem cell23_7671805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 1, 3, 4].length) (baseStart_7671805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7671805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7671805 prefixEnd_7671805 := by exact prefixLift 7671805
  have htrace : WordTrace (prefixWord ++ tailWord_7671805) baseStart_7671805 baseEnd_7671805 := by
    simpa [prefixWord, tailWord_7671805, baseEnd_7671805] using wordTrace_append hprefix tailTrace_7671805
  have hstable : (prefixWord ++ tailWord_7671805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7671805).length < 2 ^ (prefixWord ++ tailWord_7671805).sum := by decide
  have hdescent : baseEnd_7671805 < baseStart_7671805 := by decide
  rcases family_descends (prefixWord ++ tailWord_7671805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7671855 : List Nat := [1, 1, 2, 1, 2, 1, 1, 5, 4, 3, 2]
def baseStart_7671855 : Nat := 118140960795 + 7671855 * 2 ^ 59
def prefixEnd_7671855 : Nat := 4983230072969 + 3 ^ 40 * 7671855 * 2
def baseEnd_7671855 : Nat := 3939349126599186565730287

theorem tailTrace_7671855 : CollatzResearch.WordTrace tailWord_7671855 prefixEnd_7671855 3939349126599186565730287 := by
  unfold tailWord_7671855
  simp only [CollatzResearch.WordTrace]
  refine ⟨279815539621187058364897019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186543693080791372243264679 279815539621187058364897019)
  ·
    refine ⟨419723309431780587547345529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279815539621187058364897019 419723309431780587547345529)
    ·
      refine ⟨314792482073835440660509147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 419723309431780587547345529 314792482073835440660509147)
      ·
        refine ⟨472188723110753160990763721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314792482073835440660509147 472188723110753160990763721)
        ·
          refine ⟨354141542333064870743072791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 472188723110753160990763721 354141542333064870743072791)
          ·
            refine ⟨531212313499597306114609187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 354141542333064870743072791 531212313499597306114609187)
            ·
              refine ⟨796818470249395959171913781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 531212313499597306114609187 796818470249395959171913781)
              ·
                refine ⟨74701731585880871172366917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 796818470249395959171913781 74701731585880871172366917)
                ·
                  refine ⟨14006574672352663344818797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74701731585880871172366917 14006574672352663344818797)
                  ·
                    refine ⟨5252465502132248754307049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14006574672352663344818797 5252465502132248754307049)
                    ·
                      refine ⟨3939349126599186565730287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5252465502132248754307049 3939349126599186565730287)
                      ·
                        rfl

theorem cell23_7671855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 4, 3, 2].length) (baseStart_7671855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7671855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7671855 prefixEnd_7671855 := by exact prefixLift 7671855
  have htrace : WordTrace (prefixWord ++ tailWord_7671855) baseStart_7671855 baseEnd_7671855 := by
    simpa [prefixWord, tailWord_7671855, baseEnd_7671855] using wordTrace_append hprefix tailTrace_7671855
  have hstable : (prefixWord ++ tailWord_7671855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7671855).length < 2 ^ (prefixWord ++ tailWord_7671855).sum := by decide
  have hdescent : baseEnd_7671855 < baseStart_7671855 := by decide
  rcases family_descends (prefixWord ++ tailWord_7671855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7671919 : List Nat := [1, 1, 2, 1, 3, 5, 2, 1, 3, 2, 2]
def baseStart_7671919 : Nat := 118140960795 + 7671919 * 2 ^ 59
def prefixEnd_7671919 : Nat := 4983230072969 + 3 ^ 40 * 7671919 * 2
def baseEnd_7671919 : Nat := 3939381989361074315329993

theorem tailTrace_7671919 : CollatzResearch.WordTrace tailWord_7671919 prefixEnd_7671919 3939381989361074315329993 := by
  unfold tailWord_7671919
  simp only [CollatzResearch.WordTrace]
  refine ⟨279817873892955197295226811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186545249261970131530151207 279817873892955197295226811)
  ·
    refine ⟨419726810839432795942840217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279817873892955197295226811 419726810839432795942840217)
    ·
      refine ⟨314795108129574596957130163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 419726810839432795942840217 314795108129574596957130163)
      ·
        refine ⟨472192662194361895435695245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314795108129574596957130163 472192662194361895435695245)
        ·
          refine ⟨177072248322885710788385717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 472192662194361895435695245 177072248322885710788385717)
          ·
            refine ⟨16600523280270535386411161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 177072248322885710788385717 16600523280270535386411161)
            ·
              refine ⟨12450392460202901539808371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16600523280270535386411161 12450392460202901539808371)
              ·
                refine ⟨18675588690304352309712557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12450392460202901539808371 18675588690304352309712557)
                ·
                  refine ⟨7003345758864132116142209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18675588690304352309712557 7003345758864132116142209)
                  ·
                    refine ⟨5252509319148099087106657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7003345758864132116142209 5252509319148099087106657)
                    ·
                      refine ⟨3939381989361074315329993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5252509319148099087106657 3939381989361074315329993)
                      ·
                        rfl

theorem cell23_7671919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 1, 3, 2, 2].length) (baseStart_7671919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7671919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7671919 prefixEnd_7671919 := by exact prefixLift 7671919
  have htrace : WordTrace (prefixWord ++ tailWord_7671919) baseStart_7671919 baseEnd_7671919 := by
    simpa [prefixWord, tailWord_7671919, baseEnd_7671919] using wordTrace_append hprefix tailTrace_7671919
  have hstable : (prefixWord ++ tailWord_7671919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7671919).length < 2 ^ (prefixWord ++ tailWord_7671919).sum := by decide
  have hdescent : baseEnd_7671919 < baseStart_7671919 := by decide
  rcases family_descends (prefixWord ++ tailWord_7671919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7671929 : List Nat := [1, 2, 1, 3, 4, 2, 3, 1, 2, 4]
def baseStart_7671929 : Nat := 118140960795 + 7671929 * 2 ^ 59
def prefixEnd_7671929 : Nat := 4983230072969 + 3 ^ 40 * 7671929 * 2
def baseEnd_7671929 : Nat := 1313129041389206425401649

theorem tailTrace_7671929 : CollatzResearch.WordTrace tailWord_7671929 prefixEnd_7671929 1313129041389206425401649 := by
  unfold tailWord_7671929
  simp only [CollatzResearch.WordTrace]
  refine ⟨279818238622918969003090841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186545492415279312668727227 279818238622918969003090841)
  ·
    refine ⟨209863678967189226752318131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279818238622918969003090841 209863678967189226752318131)
    ·
      refine ⟨314795518450783840128477197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209863678967189226752318131 314795518450783840128477197)
      ·
        refine ⟨118048319419043940048178949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 314795518450783840128477197 118048319419043940048178949)
        ·
          refine ⟨22134059891070738759033553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118048319419043940048178949 22134059891070738759033553)
          ·
            refine ⟨16600544918303054069275165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22134059891070738759033553 16600544918303054069275165)
            ·
              refine ⟨6225204344363645275978187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16600544918303054069275165 6225204344363645275978187)
              ·
                refine ⟨9337806516545467913967281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6225204344363645275978187 9337806516545467913967281)
                ·
                  refine ⟨7003354887409100935475461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9337806516545467913967281 7003354887409100935475461)
                  ·
                    refine ⟨1313129041389206425401649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7003354887409100935475461 1313129041389206425401649)
                    ·
                      rfl

theorem cell23_7671929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 3, 1, 2, 4].length) (baseStart_7671929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7671929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7671929 prefixEnd_7671929 := by exact prefixLift 7671929
  have htrace : WordTrace (prefixWord ++ tailWord_7671929) baseStart_7671929 baseEnd_7671929 := by
    simpa [prefixWord, tailWord_7671929, baseEnd_7671929] using wordTrace_append hprefix tailTrace_7671929
  have hstable : (prefixWord ++ tailWord_7671929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7671929).length < 2 ^ (prefixWord ++ tailWord_7671929).sum := by decide
  have hdescent : baseEnd_7671929 < baseStart_7671929 := by decide
  rcases family_descends (prefixWord ++ tailWord_7671929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7671932 : List Nat := [2, 2, 2, 1, 1, 6, 1, 1, 1, 2, 4]
def baseStart_7671932 : Nat := 118140960795 + 7671932 * 2 ^ 59
def prefixEnd_7671932 : Nat := 4983230072969 + 3 ^ 40 * 7671932 * 2
def baseEnd_7671932 : Nat := 3939388664609582764467433

theorem tailTrace_7671932 : CollatzResearch.WordTrace tailWord_7671932 prefixEnd_7671932 3939388664609582764467433 := by
  unfold tailWord_7671932
  simp only [CollatzResearch.WordTrace]
  refine ⟨139909174020954050257725025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186545565361272067010300033 139909174020954050257725025)
  ·
    refine ⟨104931880515715537693293769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139909174020954050257725025 104931880515715537693293769)
    ·
      refine ⟨78698910386786653269970327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104931880515715537693293769 78698910386786653269970327)
      ·
        refine ⟨118048365580179979904955491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78698910386786653269970327 118048365580179979904955491)
        ·
          refine ⟨177072548370269969857433237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118048365580179979904955491 177072548370269969857433237)
          ·
            refine ⟨8300275704856404837067183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 177072548370269969857433237 8300275704856404837067183)
            ·
              refine ⟨12450413557284607255600775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8300275704856404837067183 12450413557284607255600775)
              ·
                refine ⟨18675620335926910883401163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12450413557284607255600775 18675620335926910883401163)
                ·
                  refine ⟨28013430503890366325101745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18675620335926910883401163 28013430503890366325101745)
                  ·
                    refine ⟨21010072877917774743826309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28013430503890366325101745 21010072877917774743826309)
                    ·
                      refine ⟨3939388664609582764467433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21010072877917774743826309 3939388664609582764467433)
                      ·
                        rfl

theorem cell23_7671932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 1, 1, 2, 4].length) (baseStart_7671932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7671932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7671932 prefixEnd_7671932 := by exact prefixLift 7671932
  have htrace : WordTrace (prefixWord ++ tailWord_7671932) baseStart_7671932 baseEnd_7671932 := by
    simpa [prefixWord, tailWord_7671932, baseEnd_7671932] using wordTrace_append hprefix tailTrace_7671932
  have hstable : (prefixWord ++ tailWord_7671932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7671932).length < 2 ^ (prefixWord ++ tailWord_7671932).sum := by decide
  have hdescent : baseEnd_7671932 < baseStart_7671932 := by decide
  rcases family_descends (prefixWord ++ tailWord_7671932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7671970 : List Nat := [3, 3, 1, 3, 1, 2, 3, 2, 1, 2, 2]
def baseStart_7671970 : Nat := 118140960795 + 7671970 * 2 ^ 59
def prefixEnd_7671970 : Nat := 4983230072969 + 3 ^ 40 * 7671970 * 2
def baseEnd_7671970 : Nat := 3939408176874453615792259

theorem tailTrace_7671970 : CollatzResearch.WordTrace tailWord_7671970 prefixEnd_7671970 3939408176874453615792259 := by
  unfold tailWord_7671970
  simp only [CollatzResearch.WordTrace]
  refine ⟨69954933503942608251333341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186546489343846955336888909 69954933503942608251333341)
  ·
    refine ⟨26233100063978478094250003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69954933503942608251333341 26233100063978478094250003)
    ·
      refine ⟨39349650095967717141375005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26233100063978478094250003 39349650095967717141375005)
      ·
        refine ⟨14756118785987893928015627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39349650095967717141375005 14756118785987893928015627)
        ·
          refine ⟨22134178178981840892023441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14756118785987893928015627 22134178178981840892023441)
          ·
            refine ⟨16600633634236380669017581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22134178178981840892023441 16600633634236380669017581)
            ·
              refine ⟨6225237612838642750881593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16600633634236380669017581 6225237612838642750881593)
              ·
                refine ⟨4668928209628982063161195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6225237612838642750881593 4668928209628982063161195)
                ·
                  refine ⟨7003392314443473094741793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4668928209628982063161195 7003392314443473094741793)
                  ·
                    refine ⟨5252544235832604821056345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7003392314443473094741793 5252544235832604821056345)
                    ·
                      refine ⟨3939408176874453615792259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5252544235832604821056345 3939408176874453615792259)
                      ·
                        rfl

theorem cell23_7671970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_7671970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7671970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7671970 prefixEnd_7671970 := by exact prefixLift 7671970
  have htrace : WordTrace (prefixWord ++ tailWord_7671970) baseStart_7671970 baseEnd_7671970 := by
    simpa [prefixWord, tailWord_7671970, baseEnd_7671970] using wordTrace_append hprefix tailTrace_7671970
  have hstable : (prefixWord ++ tailWord_7671970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7671970).length < 2 ^ (prefixWord ++ tailWord_7671970).sum := by decide
  have hdescent : baseEnd_7671970 < baseStart_7671970 := by decide
  rcases family_descends (prefixWord ++ tailWord_7671970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7671992 : List Nat := [2, 1, 2, 1, 2, 1, 4, 3, 1, 4, 2]
def baseStart_7671992 : Nat := 118140960795 + 7671992 * 2 ^ 59
def prefixEnd_7671992 : Nat := 4983230072969 + 3 ^ 40 * 7671992 * 2
def baseEnd_7671992 : Nat := 3939419473448852529717157

theorem tailTrace_7671992 : CollatzResearch.WordTrace tailWord_7671992 prefixEnd_7671992 3939419473448852529717157 := by
  unfold tailWord_7671992
  simp only [CollatzResearch.WordTrace]
  refine ⟨139910268210845365381317115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186547024281127153841756153 139910268210845365381317115)
  ·
    refine ⟨209865402316268048071975673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139910268210845365381317115 209865402316268048071975673)
    ·
      refine ⟨157399051737201036053981755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209865402316268048071975673 157399051737201036053981755)
      ·
        refine ⟨236098577605801554080972633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157399051737201036053981755 236098577605801554080972633)
        ·
          refine ⟨177073933204351165560729475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236098577605801554080972633 177073933204351165560729475)
          ·
            refine ⟨265610899806526748341094213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177073933204351165560729475 265610899806526748341094213)
            ·
              refine ⟨49802043713723765313955165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 265610899806526748341094213 49802043713723765313955165)
              ·
                refine ⟨18675766392646411992733187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49802043713723765313955165 18675766392646411992733187)
                ·
                  refine ⟨28013649588969617989099781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18675766392646411992733187 28013649588969617989099781)
                  ·
                    refine ⟨5252559297931803372956209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28013649588969617989099781 5252559297931803372956209)
                    ·
                      refine ⟨3939419473448852529717157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5252559297931803372956209 3939419473448852529717157)
                      ·
                        rfl

theorem cell23_7671992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 3, 1, 4, 2].length) (baseStart_7671992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7671992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7671992 prefixEnd_7671992 := by exact prefixLift 7671992
  have htrace : WordTrace (prefixWord ++ tailWord_7671992) baseStart_7671992 baseEnd_7671992 := by
    simpa [prefixWord, tailWord_7671992, baseEnd_7671992] using wordTrace_append hprefix tailTrace_7671992
  have hstable : (prefixWord ++ tailWord_7671992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7671992).length < 2 ^ (prefixWord ++ tailWord_7671992).sum := by decide
  have hdescent : baseEnd_7671992 < baseStart_7671992 := by decide
  rcases family_descends (prefixWord ++ tailWord_7671992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7672032 : List Nat := [2, 1, 1, 3, 1, 3, 3, 4, 5]
def baseStart_7672032 : Nat := 118140960795 + 7672032 * 2 ^ 59
def prefixEnd_7672032 : Nat := 4983230072969 + 3 ^ 40 * 7672032 * 2
def baseEnd_7672032 : Nat := 437715556963892485912997

theorem tailTrace_7672032 : CollatzResearch.WordTrace tailWord_7672032 prefixEnd_7672032 437715556963892485912997 := by
  unfold tailWord_7672032
  simp only [CollatzResearch.WordTrace]
  refine ⟨139910997670772908797045175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186547996894363878396060233 139910997670772908797045175)
  ·
    refine ⟨209866496506159363195567763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139910997670772908797045175 209866496506159363195567763)
    ·
      refine ⟨314799744759239044793351645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209866496506159363195567763 314799744759239044793351645)
      ·
        refine ⟨118049904284714641797506867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 314799744759239044793351645 118049904284714641797506867)
        ·
          refine ⟨177074856427071962696260301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118049904284714641797506867 177074856427071962696260301)
          ·
            refine ⟨66403071160151986011097613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177074856427071962696260301 66403071160151986011097613)
            ·
              refine ⟨24901151685056994754161605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66403071160151986011097613 24901151685056994754161605)
              ·
                refine ⟨4668965940948186516405301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24901151685056994754161605 4668965940948186516405301)
                ·
                  refine ⟨437715556963892485912997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4668965940948186516405301 437715556963892485912997)
                  ·
                    rfl

theorem cell23_7672032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 4, 5].length) (baseStart_7672032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7672032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7672032 prefixEnd_7672032 := by exact prefixLift 7672032
  have htrace : WordTrace (prefixWord ++ tailWord_7672032) baseStart_7672032 baseEnd_7672032 := by
    simpa [prefixWord, tailWord_7672032, baseEnd_7672032] using wordTrace_append hprefix tailTrace_7672032
  have hstable : (prefixWord ++ tailWord_7672032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7672032).length < 2 ^ (prefixWord ++ tailWord_7672032).sum := by decide
  have hdescent : baseEnd_7672032 < baseStart_7672032 := by decide
  rcases family_descends (prefixWord ++ tailWord_7672032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7672042 : List Nat := [3, 1, 3, 1, 1, 2, 3, 1, 2, 3, 3]
def baseStart_7672042 : Nat := 118140960795 + 7672042 * 2 ^ 59
def prefixEnd_7672042 : Nat := 4983230072969 + 3 ^ 40 * 7672042 * 2
def baseEnd_7672042 : Nat := 3939445147481577334091927

theorem tailTrace_7672042 : CollatzResearch.WordTrace tailWord_7672042 prefixEnd_7672042 3939445147481577334091927 := by
  unfold tailWord_7672042
  simp only [CollatzResearch.WordTrace]
  refine ⟨69955590017877397325488595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186548240047673059534636253 69955590017877397325488595)
  ·
    refine ⟨104933385026816095988232893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69955590017877397325488595 104933385026816095988232893)
    ·
      refine ⟨39350019385056035995587335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104933385026816095988232893 39350019385056035995587335)
      ·
        refine ⟨59025029077584053993381003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39350019385056035995587335 59025029077584053993381003)
        ·
          refine ⟨88537543616376080990071505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59025029077584053993381003 88537543616376080990071505)
          ·
            refine ⟨66403157712282060742553629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88537543616376080990071505 66403157712282060742553629)
            ·
              refine ⟨24901184142105772778457611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66403157712282060742553629 24901184142105772778457611)
              ·
                refine ⟨37351776213158659167686417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24901184142105772778457611 37351776213158659167686417)
                ·
                  refine ⟨28013832159868994375764813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37351776213158659167686417 28013832159868994375764813)
                  ·
                    refine ⟨10505187059950872890911805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28013832159868994375764813 10505187059950872890911805)
                    ·
                      refine ⟨3939445147481577334091927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10505187059950872890911805 3939445147481577334091927)
                      ·
                        rfl

theorem cell23_7672042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 1, 2, 3, 3].length) (baseStart_7672042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7672042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7672042 prefixEnd_7672042 := by exact prefixLift 7672042
  have htrace : WordTrace (prefixWord ++ tailWord_7672042) baseStart_7672042 baseEnd_7672042 := by
    simpa [prefixWord, tailWord_7672042, baseEnd_7672042] using wordTrace_append hprefix tailTrace_7672042
  have hstable : (prefixWord ++ tailWord_7672042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7672042).length < 2 ^ (prefixWord ++ tailWord_7672042).sum := by decide
  have hdescent : baseEnd_7672042 < baseStart_7672042 := by decide
  rcases family_descends (prefixWord ++ tailWord_7672042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7672062 : List Nat := [4, 2, 2, 1, 1, 1, 3, 1, 1, 7]
def baseStart_7672062 : Nat := 118140960795 + 7672062 * 2 ^ 59
def prefixEnd_7672062 : Nat := 4983230072969 + 3 ^ 40 * 7672062 * 2
def baseEnd_7672062 : Nat := 1313151805698222418613945

theorem tailTrace_7672062 : CollatzResearch.WordTrace tailWord_7672062 prefixEnd_7672062 1313151805698222418613945 := by
  unfold tailWord_7672062
  simp only [CollatzResearch.WordTrace]
  refine ⟨34977886191429641589710305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186548726354291421811788293 34977886191429641589710305)
  ·
    refine ⟨26233414643572231192282729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34977886191429641589710305 26233414643572231192282729)
    ·
      refine ⟨19675060982679173394212047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26233414643572231192282729 19675060982679173394212047)
      ·
        refine ⟨29512591474018760091318071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19675060982679173394212047 29512591474018760091318071)
        ·
          refine ⟨44268887211028140136977107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29512591474018760091318071 44268887211028140136977107)
          ·
            refine ⟨66403330816542210205465661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44268887211028140136977107 66403330816542210205465661)
            ·
              refine ⟨24901249056203328827049623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66403330816542210205465661 24901249056203328827049623)
              ·
                refine ⟨37351873584304993240574435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24901249056203328827049623 37351873584304993240574435)
                ·
                  refine ⟨56027810376457489860861653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37351873584304993240574435 56027810376457489860861653)
                  ·
                    refine ⟨1313151805698222418613945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56027810376457489860861653 1313151805698222418613945)
                    ·
                      rfl

theorem cell23_7672062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_7672062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7672062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7672062 prefixEnd_7672062 := by exact prefixLift 7672062
  have htrace : WordTrace (prefixWord ++ tailWord_7672062) baseStart_7672062 baseEnd_7672062 := by
    simpa [prefixWord, tailWord_7672062, baseEnd_7672062] using wordTrace_append hprefix tailTrace_7672062
  have hstable : (prefixWord ++ tailWord_7672062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7672062).length < 2 ^ (prefixWord ++ tailWord_7672062).sum := by decide
  have hdescent : baseEnd_7672062 < baseStart_7672062 := by decide
  rcases family_descends (prefixWord ++ tailWord_7672062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7672066 : List Nat := [3, 4, 1, 1, 2, 2, 2, 3, 5]
def baseStart_7672066 : Nat := 118140960795 + 7672066 * 2 ^ 59
def prefixEnd_7672066 : Nat := 4983230072969 + 3 ^ 40 * 7672066 * 2
def baseEnd_7672066 : Nat := 437717496779698360021313

theorem tailTrace_7672066 : CollatzResearch.WordTrace tailWord_7672066 prefixEnd_7672066 437717496779698360021313 := by
  unfold tailWord_7672066
  simp only [CollatzResearch.WordTrace]
  refine ⟨69955808855855660350207013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186548823615615094267218701 69955808855855660350207013)
  ·
    refine ⟨13116714160472936315663815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69955808855855660350207013 13116714160472936315663815)
    ·
      refine ⟨19675071240709404473495723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13116714160472936315663815 19675071240709404473495723)
      ·
        refine ⟨29512606861064106710243585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19675071240709404473495723 29512606861064106710243585)
        ·
          refine ⟨22134455145798080032682689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29512606861064106710243585 22134455145798080032682689)
          ·
            refine ⟨16600841359348560024512017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22134455145798080032682689 16600841359348560024512017)
            ·
              refine ⟨12450631019511420018384013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16600841359348560024512017 12450631019511420018384013)
              ·
                refine ⟨4668986632316782506894005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12450631019511420018384013 4668986632316782506894005)
                ·
                  refine ⟨437717496779698360021313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4668986632316782506894005 437717496779698360021313)
                  ·
                    rfl

theorem cell23_7672066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 3, 5].length) (baseStart_7672066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7672066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7672066 prefixEnd_7672066 := by exact prefixLift 7672066
  have htrace : WordTrace (prefixWord ++ tailWord_7672066) baseStart_7672066 baseEnd_7672066 := by
    simpa [prefixWord, tailWord_7672066, baseEnd_7672066] using wordTrace_append hprefix tailTrace_7672066
  have hstable : (prefixWord ++ tailWord_7672066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7672066).length < 2 ^ (prefixWord ++ tailWord_7672066).sum := by decide
  have hdescent : baseEnd_7672066 < baseStart_7672066 := by decide
  rcases family_descends (prefixWord ++ tailWord_7672066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7672085 : List Nat := [1, 3, 2, 1, 2, 1, 2, 1, 2, 3, 5]
def baseStart_7672085 : Nat := 118140960795 + 7672085 * 2 ^ 59
def prefixEnd_7672085 : Nat := 4983230072969 + 3 ^ 40 * 7672085 * 2
def baseEnd_7672085 : Nat := 3939467227149720665854229

theorem tailTrace_7672085 : CollatzResearch.WordTrace tailWord_7672085 prefixEnd_7672085 3939467227149720665854229 := by
  unfold tailWord_7672085
  simp only [CollatzResearch.WordTrace]
  refine ⟨279823928410353807645769709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186549285606902538430513139 279823928410353807645769709)
  ·
    refine ⟨104933973153882677867163641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 279823928410353807645769709 104933973153882677867163641)
    ·
      refine ⟨78700479865412008400372731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104933973153882677867163641 78700479865412008400372731)
      ·
        refine ⟨118050719798118012600559097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78700479865412008400372731 118050719798118012600559097)
        ·
          refine ⟨88538039848588509450419323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118050719798118012600559097 88538039848588509450419323)
          ·
            refine ⟨132807059772882764175628985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88538039848588509450419323 132807059772882764175628985)
            ·
              refine ⟨99605294829662073131721739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132807059772882764175628985 99605294829662073131721739)
              ·
                refine ⟨149407942244493109697582609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99605294829662073131721739 149407942244493109697582609)
                ·
                  refine ⟨112055956683369832273186957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 149407942244493109697582609 112055956683369832273186957)
                  ·
                    refine ⟨42020983756263687102445109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 112055956683369832273186957 42020983756263687102445109)
                    ·
                      refine ⟨3939467227149720665854229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42020983756263687102445109 3939467227149720665854229)
                      ·
                        rfl

theorem cell23_7672085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 3, 5].length) (baseStart_7672085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7672085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7672085 prefixEnd_7672085 := by exact prefixLift 7672085
  have htrace : WordTrace (prefixWord ++ tailWord_7672085) baseStart_7672085 baseEnd_7672085 := by
    simpa [prefixWord, tailWord_7672085, baseEnd_7672085] using wordTrace_append hprefix tailTrace_7672085
  have hstable : (prefixWord ++ tailWord_7672085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7672085).length < 2 ^ (prefixWord ++ tailWord_7672085).sum := by decide
  have hdescent : baseEnd_7672085 < baseStart_7672085 := by decide
  rcases family_descends (prefixWord ++ tailWord_7672085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7672156 : List Nat := [2, 2, 4, 3, 1, 1, 1, 3, 6]
def baseStart_7672156 : Nat := 118140960795 + 7672156 * 2 ^ 59
def prefixEnd_7672156 : Nat := 4983230072969 + 3 ^ 40 * 7672156 * 2
def baseEnd_7672156 : Nat := 437722631586243320896267

theorem tailTrace_7672156 : CollatzResearch.WordTrace tailWord_7672156 prefixEnd_7672156 437722631586243320896267 := by
  unfold tailWord_7672156
  simp only [CollatzResearch.WordTrace]
  refine ⟨139913258996548293385802161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186551011995397724514402881 139913258996548293385802161)
  ·
    refine ⟨104934944247411220039351621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139913258996548293385802161 104934944247411220039351621)
    ·
      refine ⟨19675302046389603757378429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104934944247411220039351621 19675302046389603757378429)
      ·
        refine ⟨7378238267396101409016911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19675302046389603757378429 7378238267396101409016911)
        ·
          refine ⟨11067357401094152113525367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7378238267396101409016911 11067357401094152113525367)
          ·
            refine ⟨16601036101641228170288051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11067357401094152113525367 16601036101641228170288051)
            ·
              refine ⟨24901554152461842255432077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16601036101641228170288051 24901554152461842255432077)
              ·
                refine ⟨9338082807173190845787029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24901554152461842255432077 9338082807173190845787029)
                ·
                  refine ⟨437722631586243320896267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9338082807173190845787029 437722631586243320896267)
                  ·
                    rfl

theorem cell23_7672156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 3, 6].length) (baseStart_7672156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7672156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7672156 prefixEnd_7672156 := by exact prefixLift 7672156
  have htrace : WordTrace (prefixWord ++ tailWord_7672156) baseStart_7672156 baseEnd_7672156 := by
    simpa [prefixWord, tailWord_7672156, baseEnd_7672156] using wordTrace_append hprefix tailTrace_7672156
  have hstable : (prefixWord ++ tailWord_7672156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7672156).length < 2 ^ (prefixWord ++ tailWord_7672156).sum := by decide
  have hdescent : baseEnd_7672156 < baseStart_7672156 := by decide
  rcases family_descends (prefixWord ++ tailWord_7672156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7672176 : List Nat := [2, 1, 1, 1, 4, 4, 2, 1, 2, 3, 2]
def baseStart_7672176 : Nat := 118140960795 + 7672176 * 2 ^ 59
def prefixEnd_7672176 : Nat := 4983230072969 + 3 ^ 40 * 7672176 * 2
def baseEnd_7672176 : Nat := 3939513953889279809816311

theorem tailTrace_7672176 : CollatzResearch.WordTrace tailWord_7672176 prefixEnd_7672176 3939513953889279809816311 := by
  unfold tailWord_7672176
  simp only [CollatzResearch.WordTrace]
  refine ⟨139913623726512065093666191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186551498302016086791554921 139913623726512065093666191)
  ·
    refine ⟨209870435589768097640499287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139913623726512065093666191 209870435589768097640499287)
    ·
      refine ⟨314805653384652146460748931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209870435589768097640499287 314805653384652146460748931)
      ·
        refine ⟨472208480076978219691123397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314805653384652146460748931 472208480076978219691123397)
        ·
          refine ⟨88539090014433416192085637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 472208480076978219691123397 88539090014433416192085637)
          ·
            refine ⟨16601079377706265536016057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88539090014433416192085637 16601079377706265536016057)
            ·
              refine ⟨12450809533279699152012043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16601079377706265536016057 12450809533279699152012043)
              ·
                refine ⟨18676214299919548728018065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12450809533279699152012043 18676214299919548728018065)
                ·
                  refine ⟨14007160724939661546013549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18676214299919548728018065 14007160724939661546013549)
                  ·
                    refine ⟨5252685271852373079755081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14007160724939661546013549 5252685271852373079755081)
                    ·
                      refine ⟨3939513953889279809816311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5252685271852373079755081 3939513953889279809816311)
                      ·
                        rfl

theorem cell23_7672176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 1, 2, 3, 2].length) (baseStart_7672176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7672176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7672176 prefixEnd_7672176 := by exact prefixLift 7672176
  have htrace : WordTrace (prefixWord ++ tailWord_7672176) baseStart_7672176 baseEnd_7672176 := by
    simpa [prefixWord, tailWord_7672176, baseEnd_7672176] using wordTrace_append hprefix tailTrace_7672176
  have hstable : (prefixWord ++ tailWord_7672176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7672176).length < 2 ^ (prefixWord ++ tailWord_7672176).sum := by decide
  have hdescent : baseEnd_7672176 < baseStart_7672176 := by decide
  rcases family_descends (prefixWord ++ tailWord_7672176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7672194 : List Nat := [3, 4, 2, 1, 3, 1, 2, 2, 1, 4]
def baseStart_7672194 : Nat := 118140960795 + 7672194 * 2 ^ 59
def prefixEnd_7672194 : Nat := 4983230072969 + 3 ^ 40 * 7672194 * 2
def baseEnd_7672194 : Nat := 1313174398847020246463743

theorem tailTrace_7672194 : CollatzResearch.WordTrace tailWord_7672194 prefixEnd_7672194 1313174398847020246463743 := by
  unfold tailWord_7672194
  simp only [CollatzResearch.WordTrace]
  refine ⟨69956975991739729815371909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186551935977972612840991757 69956975991739729815371909)
  ·
    refine ⟨13116932998451199340382233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69956975991739729815371909 13116932998451199340382233)
    ·
      refine ⟨9837699748838399505286675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13116932998451199340382233 9837699748838399505286675)
      ·
        refine ⟨14756549623257599257930013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9837699748838399505286675 14756549623257599257930013)
        ·
          refine ⟨5533706108721599721723755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14756549623257599257930013 5533706108721599721723755)
          ·
            refine ⟨8300559163082399582585633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5533706108721599721723755 8300559163082399582585633)
            ·
              refine ⟨6225419372311799686939225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8300559163082399582585633 6225419372311799686939225)
              ·
                refine ⟨4669064529233849765204419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6225419372311799686939225 4669064529233849765204419)
                ·
                  refine ⟨7003596793850774647806629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4669064529233849765204419 7003596793850774647806629)
                  ·
                    refine ⟨1313174398847020246463743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7003596793850774647806629 1313174398847020246463743)
                    ·
                      rfl

theorem cell23_7672194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_7672194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7672194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7672194 prefixEnd_7672194 := by exact prefixLift 7672194
  have htrace : WordTrace (prefixWord ++ tailWord_7672194) baseStart_7672194 baseEnd_7672194 := by
    simpa [prefixWord, tailWord_7672194, baseEnd_7672194] using wordTrace_append hprefix tailTrace_7672194
  have hstable : (prefixWord ++ tailWord_7672194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7672194).length < 2 ^ (prefixWord ++ tailWord_7672194).sum := by decide
  have hdescent : baseEnd_7672194 < baseStart_7672194 := by decide
  rcases family_descends (prefixWord ++ tailWord_7672194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7672195 : List Nat := [1, 1, 1, 3, 17]
def baseStart_7672195 : Nat := 118140960795 + 7672195 * 2 ^ 59
def prefixEnd_7672195 : Nat := 4983230072969 + 3 ^ 40 * 7672195 * 2
def baseEnd_7672195 : Nat := 5404010576161474945787

theorem tailTrace_7672195 : CollatzResearch.WordTrace tailWord_7672195 prefixEnd_7672195 5404010576161474945787 := by
  unfold tailWord_7672195
  simp only [CollatzResearch.WordTrace]
  refine ⟨279827940439955296432274039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186551960293303530954849359 279827940439955296432274039)
  ·
    refine ⟨419741910659932944648411059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279827940439955296432274039 419741910659932944648411059)
    ·
      refine ⟨629612865989899416972616589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419741910659932944648411059 629612865989899416972616589)
      ·
        refine ⟨236104824746212281364731221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 629612865989899416972616589 236104824746212281364731221)
        ·
          refine ⟨5404010576161474945787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 17 236104824746212281364731221 5404010576161474945787)
          ·
            rfl

theorem cell23_7672195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 17].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 17].length) (baseStart_7672195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7672195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7672195 prefixEnd_7672195 := by exact prefixLift 7672195
  have htrace : WordTrace (prefixWord ++ tailWord_7672195) baseStart_7672195 baseEnd_7672195 := by
    simpa [prefixWord, tailWord_7672195, baseEnd_7672195] using wordTrace_append hprefix tailTrace_7672195
  have hstable : (prefixWord ++ tailWord_7672195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7672195).length < 2 ^ (prefixWord ++ tailWord_7672195).sum := by decide
  have hdescent : baseEnd_7672195 < baseStart_7672195 := by decide
  rcases family_descends (prefixWord ++ tailWord_7672195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7672216 : List Nat := [2, 1, 2, 5, 1, 1, 2, 3, 2, 4]
def baseStart_7672216 : Nat := 118140960795 + 7672216 * 2 ^ 59
def prefixEnd_7672216 : Nat := 4983230072969 + 3 ^ 40 * 7672216 * 2
def baseEnd_7672216 : Nat := 1313178164371819884438709

theorem tailTrace_7672216 : CollatzResearch.WordTrace tailWord_7672216 prefixEnd_7672216 1313178164371819884438709 := by
  unfold tailWord_7672216
  simp only [CollatzResearch.WordTrace]
  refine ⟨139914353186439608509394251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186552470915252811345859001 139914353186439608509394251)
  ·
    refine ⟨209871529779659412764091377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139914353186439608509394251 209871529779659412764091377)
    ·
      refine ⟨157403647334744559573068533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209871529779659412764091377 157403647334744559573068533)
      ·
        refine ⟨14756591937632302459975175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 157403647334744559573068533 14756591937632302459975175)
        ·
          refine ⟨22134887906448453689962763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14756591937632302459975175 22134887906448453689962763)
          ·
            refine ⟨33202331859672680534944145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22134887906448453689962763 33202331859672680534944145)
            ·
              refine ⟨24901748894754510401208109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33202331859672680534944145 24901748894754510401208109)
              ·
                refine ⟨9338155835532941400453041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24901748894754510401208109 9338155835532941400453041)
                ·
                  refine ⟨7003616876649706050339781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9338155835532941400453041 7003616876649706050339781)
                  ·
                    refine ⟨1313178164371819884438709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7003616876649706050339781 1313178164371819884438709)
                    ·
                      rfl

theorem cell23_7672216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 3, 2, 4].length) (baseStart_7672216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7672216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7672216 prefixEnd_7672216 := by exact prefixLift 7672216
  have htrace : WordTrace (prefixWord ++ tailWord_7672216) baseStart_7672216 baseEnd_7672216 := by
    simpa [prefixWord, tailWord_7672216, baseEnd_7672216] using wordTrace_append hprefix tailTrace_7672216
  have hstable : (prefixWord ++ tailWord_7672216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7672216).length < 2 ^ (prefixWord ++ tailWord_7672216).sum := by decide
  have hdescent : baseEnd_7672216 < baseStart_7672216 := by decide
  rcases family_descends (prefixWord ++ tailWord_7672216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7672226 : List Nat := [3, 3, 1, 2, 1, 1, 2, 4, 1, 2, 3]
def baseStart_7672226 : Nat := 118140960795 + 7672226 * 2 ^ 59
def prefixEnd_7672226 : Nat := 4983230072969 + 3 ^ 40 * 7672226 * 2
def baseEnd_7672226 : Nat := 3939539627922004614191081

theorem tailTrace_7672226 : CollatzResearch.WordTrace tailWord_7672226 prefixEnd_7672226 3939539627922004614191081 := by
  unfold tailWord_7672226
  simp only [CollatzResearch.WordTrace]
  refine ⟨69957267775710747181663133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186552714068561992484435021 69957267775710747181663133)
  ·
    refine ⟨26233975415891530193123675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69957267775710747181663133 26233975415891530193123675)
    ·
      refine ⟨39350963123837295289685513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26233975415891530193123675 39350963123837295289685513)
      ·
        refine ⟨29513222342877971467264135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39350963123837295289685513 29513222342877971467264135)
        ·
          refine ⟨44269833514316957200896203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29513222342877971467264135 44269833514316957200896203)
          ·
            refine ⟨66404750271475435801344305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44269833514316957200896203 66404750271475435801344305)
            ·
              refine ⟨49803562703606576851008229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66404750271475435801344305 49803562703606576851008229)
              ·
                refine ⟨9338168006926233159564043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49803562703606576851008229 9338168006926233159564043)
                ·
                  refine ⟨14007252010389349739346065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9338168006926233159564043 14007252010389349739346065)
                  ·
                    refine ⟨10505439007792012304509549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14007252010389349739346065 10505439007792012304509549)
                    ·
                      refine ⟨3939539627922004614191081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10505439007792012304509549 3939539627922004614191081)
                      ·
                        rfl

theorem cell23_7672226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_7672226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7672226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7672226 prefixEnd_7672226 := by exact prefixLift 7672226
  have htrace : WordTrace (prefixWord ++ tailWord_7672226) baseStart_7672226 baseEnd_7672226 := by
    simpa [prefixWord, tailWord_7672226, baseEnd_7672226] using wordTrace_append hprefix tailTrace_7672226
  have hstable : (prefixWord ++ tailWord_7672226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7672226).length < 2 ^ (prefixWord ++ tailWord_7672226).sum := by decide
  have hdescent : baseEnd_7672226 < baseStart_7672226 := by decide
  rcases family_descends (prefixWord ++ tailWord_7672226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7672234 : List Nat := [3, 1, 6, 1, 1, 1, 2, 3, 1, 1, 3]
def baseStart_7672234 : Nat := 118140960795 + 7672234 * 2 ^ 59
def prefixEnd_7672234 : Nat := 4983230072969 + 3 ^ 40 * 7672234 * 2
def baseEnd_7672234 : Nat := 3939543735767240582891045

theorem tailTrace_7672234 : CollatzResearch.WordTrace tailWord_7672234 prefixEnd_7672234 3939543735767240582891045 := by
  unfold tailWord_7672234
  simp only [CollatzResearch.WordTrace]
  refine ⟨69957340721703501523235939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186552908591209337395295837 69957340721703501523235939)
  ·
    refine ⟨104936011082555252284853909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69957340721703501523235939 104936011082555252284853909)
    ·
      refine ⟨4918875519494777450852527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 104936011082555252284853909 4918875519494777450852527)
      ·
        refine ⟨7378313279242166176278791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4918875519494777450852527 7378313279242166176278791)
        ·
          refine ⟨11067469918863249264418187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7378313279242166176278791 11067469918863249264418187)
          ·
            refine ⟨16601204878294873896627281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11067469918863249264418187 16601204878294873896627281)
            ·
              refine ⟨12450903658721155422470461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16601204878294873896627281 12450903658721155422470461)
              ·
                refine ⟨4669088872020433283426423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12450903658721155422470461 4669088872020433283426423)
                ·
                  refine ⟨7003633308030649925139635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4669088872020433283426423 7003633308030649925139635)
                  ·
                    refine ⟨10505449962045974887709453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7003633308030649925139635 10505449962045974887709453)
                    ·
                      refine ⟨3939543735767240582891045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10505449962045974887709453 3939543735767240582891045)
                      ·
                        rfl

theorem cell23_7672234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_7672234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7672234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7672234 prefixEnd_7672234 := by exact prefixLift 7672234
  have htrace : WordTrace (prefixWord ++ tailWord_7672234) baseStart_7672234 baseEnd_7672234 := by
    simpa [prefixWord, tailWord_7672234, baseEnd_7672234] using wordTrace_append hprefix tailTrace_7672234
  have hstable : (prefixWord ++ tailWord_7672234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7672234).length < 2 ^ (prefixWord ++ tailWord_7672234).sum := by decide
  have hdescent : baseEnd_7672234 < baseStart_7672234 := by decide
  rcases family_descends (prefixWord ++ tailWord_7672234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7672312 : List Nat := [2, 1, 2, 1, 1, 4, 1, 1, 1, 2, 7]
def baseStart_7672312 : Nat := 118140960795 + 7672312 * 2 ^ 59
def prefixEnd_7672312 : Nat := 4983230072969 + 3 ^ 40 * 7672312 * 2
def baseEnd_7672312 : Nat := 3939583787258291277715685

theorem tailTrace_7672312 : CollatzResearch.WordTrace tailWord_7672312 prefixEnd_7672312 3939583787258291277715685 := by
  unfold tailWord_7672312
  simp only [CollatzResearch.WordTrace]
  refine ⟨139916103890265712707141595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186554805187020950276188793 139916103890265712707141595)
  ·
    refine ⟨209874155835398569060712393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139916103890265712707141595 209874155835398569060712393)
    ·
      refine ⟨157405616876548926795534295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209874155835398569060712393 157405616876548926795534295)
      ·
        refine ⟨236108425314823390193301443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157405616876548926795534295 236108425314823390193301443)
        ·
          refine ⟨354162637972235085289952165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236108425314823390193301443 354162637972235085289952165)
          ·
            refine ⟨66405494619794078491866031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 354162637972235085289952165 66405494619794078491866031)
            ·
              refine ⟨99608241929691117737799047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66405494619794078491866031 99608241929691117737799047)
              ·
                refine ⟨149412362894536676606698571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99608241929691117737799047 149412362894536676606698571)
                ·
                  refine ⟨224118544341805014910047857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 149412362894536676606698571 224118544341805014910047857)
                  ·
                    refine ⟨168088908256353761182535893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 224118544341805014910047857 168088908256353761182535893)
                    ·
                      refine ⟨3939583787258291277715685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 168088908256353761182535893 3939583787258291277715685)
                      ·
                        rfl

theorem cell23_7672312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 1, 2, 7].length) (baseStart_7672312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7672312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7672312 prefixEnd_7672312 := by exact prefixLift 7672312
  have htrace : WordTrace (prefixWord ++ tailWord_7672312) baseStart_7672312 baseEnd_7672312 := by
    simpa [prefixWord, tailWord_7672312, baseEnd_7672312] using wordTrace_append hprefix tailTrace_7672312
  have hstable : (prefixWord ++ tailWord_7672312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7672312).length < 2 ^ (prefixWord ++ tailWord_7672312).sum := by decide
  have hdescent : baseEnd_7672312 < baseStart_7672312 := by decide
  rcases family_descends (prefixWord ++ tailWord_7672312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7672333 : List Nat := [1, 7, 1, 1, 1, 1, 1, 2, 2, 1, 5]
def baseStart_7672333 : Nat := 118140960795 + 7672333 * 2 ^ 59
def prefixEnd_7672333 : Nat := 4983230072969 + 3 ^ 40 * 7672333 * 2
def baseEnd_7672333 : Nat := 3939594570352035695553089

theorem tailTrace_7672333 : CollatzResearch.WordTrace tailWord_7672333 prefixEnd_7672333 3939594570352035695553089 := by
  unfold tailWord_7672333
  simp only [CollatzResearch.WordTrace]
  refine ⟨279832973713455346000797653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186555315808970230667198435 279832973713455346000797653)
  ·
    refine ⟨6558585321409109671893695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 279832973713455346000797653 6558585321409109671893695)
    ·
      refine ⟨9837877982113664507840543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6558585321409109671893695 9837877982113664507840543)
      ·
        refine ⟨14756816973170496761760815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9837877982113664507840543 14756816973170496761760815)
        ·
          refine ⟨22135225459755745142641223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14756816973170496761760815 22135225459755745142641223)
          ·
            refine ⟨33202838189633617713961835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22135225459755745142641223 33202838189633617713961835)
            ·
              refine ⟨49804257284450426570942753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33202838189633617713961835 49804257284450426570942753)
              ·
                refine ⟨37353192963337819928207065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49804257284450426570942753 37353192963337819928207065)
                ·
                  refine ⟨28014894722503364946155299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37353192963337819928207065 28014894722503364946155299)
                  ·
                    refine ⟨42022342083755047419232949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28014894722503364946155299 42022342083755047419232949)
                    ·
                      refine ⟨3939594570352035695553089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42022342083755047419232949 3939594570352035695553089)
                      ·
                        rfl

theorem cell23_7672333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_7672333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7672333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7672333 prefixEnd_7672333 := by exact prefixLift 7672333
  have htrace : WordTrace (prefixWord ++ tailWord_7672333) baseStart_7672333 baseEnd_7672333 := by
    simpa [prefixWord, tailWord_7672333, baseEnd_7672333] using wordTrace_append hprefix tailTrace_7672333
  have hstable : (prefixWord ++ tailWord_7672333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7672333).length < 2 ^ (prefixWord ++ tailWord_7672333).sum := by decide
  have hdescent : baseEnd_7672333 < baseStart_7672333 := by decide
  rcases family_descends (prefixWord ++ tailWord_7672333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7672396 : List Nat := [2, 2, 1, 3, 1, 2, 3, 2, 3, 4]
def baseStart_7672396 : Nat := 118140960795 + 7672396 * 2 ^ 59
def prefixEnd_7672396 : Nat := 4983230072969 + 3 ^ 40 * 7672396 * 2
def baseEnd_7672396 : Nat := 1313208973211089649688433

theorem tailTrace_7672396 : CollatzResearch.WordTrace tailWord_7672396 prefixEnd_7672396 1313208973211089649688433 := by
  unfold tailWord_7672396
  simp only [CollatzResearch.WordTrace]
  refine ⟨139917635756113553880170521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186556847674818071840227361 139917635756113553880170521)
  ·
    refine ⟨104938226817085165410127891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139917635756113553880170521 104938226817085165410127891)
    ·
      refine ⟨157407340225627748115191837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104938226817085165410127891 157407340225627748115191837)
      ·
        refine ⟨59027752584610405543196939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157407340225627748115191837 59027752584610405543196939)
        ·
          refine ⟨88541628876915608314795409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59027752584610405543196939 88541628876915608314795409)
          ·
            refine ⟨66406221657686706236096557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88541628876915608314795409 66406221657686706236096557)
            ·
              refine ⟨24902333121632514838536209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66406221657686706236096557 24902333121632514838536209)
              ·
                refine ⟨18676749841224386128902157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24902333121632514838536209 18676749841224386128902157)
                ·
                  refine ⟨7003781190459144798338309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18676749841224386128902157 7003781190459144798338309)
                  ·
                    refine ⟨1313208973211089649688433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7003781190459144798338309 1313208973211089649688433)
                    ·
                      rfl

theorem cell23_7672396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 2, 3, 4].length) (baseStart_7672396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7672396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7672396 prefixEnd_7672396 := by exact prefixLift 7672396
  have htrace : WordTrace (prefixWord ++ tailWord_7672396) baseStart_7672396 baseEnd_7672396 := by
    simpa [prefixWord, tailWord_7672396, baseEnd_7672396] using wordTrace_append hprefix tailTrace_7672396
  have hstable : (prefixWord ++ tailWord_7672396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7672396).length < 2 ^ (prefixWord ++ tailWord_7672396).sum := by decide
  have hdescent : baseEnd_7672396 < baseStart_7672396 := by decide
  rcases family_descends (prefixWord ++ tailWord_7672396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7672430 : List Nat := [4, 1, 2, 2, 2, 1, 2, 4, 1, 4]
def baseStart_7672430 : Nat := 118140960795 + 7672430 * 2 ^ 59
def prefixEnd_7672430 : Nat := 4983230072969 + 3 ^ 40 * 7672430 * 2
def baseEnd_7672430 : Nat := 1313214792658507272013381

theorem tailTrace_7672430 : CollatzResearch.WordTrace tailWord_7672430 prefixEnd_7672430 1313214792658507272013381 := by
  unfold tailWord_7672430
  simp only [CollatzResearch.WordTrace]
  refine ⟨34979563949262991445884843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186557674396069287711385829 34979563949262991445884843)
  ·
    refine ⟨52469345923894487168827265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34979563949262991445884843 52469345923894487168827265)
    ·
      refine ⟨39352009442920865376620449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52469345923894487168827265 39352009442920865376620449)
      ·
        refine ⟨29514007082190649032465337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39352009442920865376620449 29514007082190649032465337)
        ·
          refine ⟨22135505311642986774349003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29514007082190649032465337 22135505311642986774349003)
          ·
            refine ⟨33203257967464480161523505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22135505311642986774349003 33203257967464480161523505)
            ·
              refine ⟨24902443475598360121142629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33203257967464480161523505 24902443475598360121142629)
              ·
                refine ⟨4669208151674692522714243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24902443475598360121142629 4669208151674692522714243)
                ·
                  refine ⟨7003812227512038784071365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4669208151674692522714243 7003812227512038784071365)
                  ·
                    refine ⟨1313214792658507272013381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7003812227512038784071365 1313214792658507272013381)
                    ·
                      rfl

theorem cell23_7672430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 4, 1, 4].length) (baseStart_7672430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7672430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7672430 prefixEnd_7672430 := by exact prefixLift 7672430
  have htrace : WordTrace (prefixWord ++ tailWord_7672430) baseStart_7672430 baseEnd_7672430 := by
    simpa [prefixWord, tailWord_7672430, baseEnd_7672430] using wordTrace_append hprefix tailTrace_7672430
  have hstable : (prefixWord ++ tailWord_7672430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7672430).length < 2 ^ (prefixWord ++ tailWord_7672430).sum := by decide
  have hdescent : baseEnd_7672430 < baseStart_7672430 := by decide
  rcases family_descends (prefixWord ++ tailWord_7672430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7672439 : List Nat := [1, 1, 3, 1, 1, 3, 2, 1, 5, 5]
def baseStart_7672439 : Nat := 118140960795 + 7672439 * 2 ^ 59
def prefixEnd_7672439 : Nat := 4983230072969 + 3 ^ 40 * 7672439 * 2
def baseEnd_7672439 : Nat := 1313216333100470760275867

theorem tailTrace_7672439 : CollatzResearch.WordTrace tailWord_7672439 prefixEnd_7672439 1313216333100470760275867 := by
  unfold tailWord_7672439
  simp only [CollatzResearch.WordTrace]
  refine ⟨279836839851071326104156371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186557893234047550736104247 279836839851071326104156371)
  ·
    refine ⟨419755259776606989156234557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279836839851071326104156371 419755259776606989156234557)
    ·
      refine ⟨157408222416227620933587959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 419755259776606989156234557 157408222416227620933587959)
      ·
        refine ⟨236112333624341431400381939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157408222416227620933587959 236112333624341431400381939)
        ·
          refine ⟨354168500436512147100572909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236112333624341431400381939 354168500436512147100572909)
          ·
            refine ⟨132813187663692055162714841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 354168500436512147100572909 132813187663692055162714841)
            ·
              refine ⟨99609890747769041372036131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132813187663692055162714841 99609890747769041372036131)
              ·
                refine ⟨149414836121653562058054197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99609890747769041372036131 149414836121653562058054197)
                ·
                  refine ⟨14007640886405021442942581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 149414836121653562058054197 14007640886405021442942581)
                  ·
                    refine ⟨1313216333100470760275867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14007640886405021442942581 1313216333100470760275867)
                    ·
                      rfl

theorem cell23_7672439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 5, 5].length) (baseStart_7672439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7672439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7672439 prefixEnd_7672439 := by exact prefixLift 7672439
  have htrace : WordTrace (prefixWord ++ tailWord_7672439) baseStart_7672439 baseEnd_7672439 := by
    simpa [prefixWord, tailWord_7672439, baseEnd_7672439] using wordTrace_append hprefix tailTrace_7672439
  have hstable : (prefixWord ++ tailWord_7672439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7672439).length < 2 ^ (prefixWord ++ tailWord_7672439).sum := by decide
  have hdescent : baseEnd_7672439 < baseStart_7672439 := by decide
  rcases family_descends (prefixWord ++ tailWord_7672439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7672453 : List Nat := [1, 3, 1, 1, 4, 2, 2, 2, 3, 1, 3]
def baseStart_7672453 : Nat := 118140960795 + 7672453 * 2 ^ 59
def prefixEnd_7672453 : Nat := 4983230072969 + 3 ^ 40 * 7672453 * 2
def baseEnd_7672453 : Nat := 3939656188030575226052537

theorem tailTrace_7672453 : CollatzResearch.WordTrace tailWord_7672453 prefixEnd_7672453 3939656188030575226052537 := by
  unfold tailWord_7672453
  simp only [CollatzResearch.WordTrace]
  refine ⟨279837350473020606495166013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186558233648680404330110675 279837350473020606495166013)
  ·
    refine ⟨104939006427382727435687255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 279837350473020606495166013 104939006427382727435687255)
    ·
      refine ⟨157408509641074091153530883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104939006427382727435687255 157408509641074091153530883)
      ·
        refine ⟨236112764461611136730296325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157408509641074091153530883 236112764461611136730296325)
        ·
          refine ⟨44271143336552088136930561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 236112764461611136730296325 44271143336552088136930561)
          ·
            refine ⟨33203357502414066102697921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44271143336552088136930561 33203357502414066102697921)
            ·
              refine ⟨24902518126810549577023441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33203357502414066102697921 24902518126810549577023441)
              ·
                refine ⟨18676888595107912182767581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24902518126810549577023441 18676888595107912182767581)
                ·
                  refine ⟨7003833223165467068537843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18676888595107912182767581 7003833223165467068537843)
                  ·
                    refine ⟨10505749834748200602806765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7003833223165467068537843 10505749834748200602806765)
                    ·
                      refine ⟨3939656188030575226052537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10505749834748200602806765 3939656188030575226052537)
                      ·
                        rfl

theorem cell23_7672453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 2, 3, 1, 3].length) (baseStart_7672453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7672453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7672453 prefixEnd_7672453 := by exact prefixLift 7672453
  have htrace : WordTrace (prefixWord ++ tailWord_7672453) baseStart_7672453 baseEnd_7672453 := by
    simpa [prefixWord, tailWord_7672453, baseEnd_7672453] using wordTrace_append hprefix tailTrace_7672453
  have hstable : (prefixWord ++ tailWord_7672453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7672453).length < 2 ^ (prefixWord ++ tailWord_7672453).sum := by decide
  have hdescent : baseEnd_7672453 < baseStart_7672453 := by decide
  rcases family_descends (prefixWord ++ tailWord_7672453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7672480 : List Nat := [2, 1, 1, 4, 4, 1, 1, 2, 2, 3, 2]
def baseStart_7672480 : Nat := 118140960795 + 7672480 * 2 ^ 59
def prefixEnd_7672480 : Nat := 4983230072969 + 3 ^ 40 * 7672480 * 2
def baseEnd_7672480 : Nat := 3939670052008246620414913

theorem tailTrace_7672480 : CollatzResearch.WordTrace tailWord_7672480 prefixEnd_7672480 3939670052008246620414913 := by
  unfold tailWord_7672480
  simp only [CollatzResearch.WordTrace]
  refine ⟨139919167621961395053199447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186558890162615193404265929 139919167621961395053199447)
  ·
    refine ⟨209878751432942092579799171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139919167621961395053199447 209878751432942092579799171)
    ·
      refine ⟨314818127149413138869698757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209878751432942092579799171 314818127149413138869698757)
      ·
        refine ⟨59028398840514963538068517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 314818127149413138869698757 59028398840514963538068517)
        ·
          refine ⟨11067824782596555663387847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59028398840514963538068517 11067824782596555663387847)
          ·
            refine ⟨16601737173894833495081771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11067824782596555663387847 16601737173894833495081771)
            ·
              refine ⟨24902605760842250242622657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16601737173894833495081771 24902605760842250242622657)
              ·
                refine ⟨18676954320631687681966993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24902605760842250242622657 18676954320631687681966993)
                ·
                  refine ⟨14007715740473765761475245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18676954320631687681966993 14007715740473765761475245)
                  ·
                    refine ⟨5252893402677662160553217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14007715740473765761475245 5252893402677662160553217)
                    ·
                      refine ⟨3939670052008246620414913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5252893402677662160553217 3939670052008246620414913)
                      ·
                        rfl

theorem cell23_7672480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 2, 2, 3, 2].length) (baseStart_7672480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7672480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7672480 prefixEnd_7672480 := by exact prefixLift 7672480
  have htrace : WordTrace (prefixWord ++ tailWord_7672480) baseStart_7672480 baseEnd_7672480 := by
    simpa [prefixWord, tailWord_7672480, baseEnd_7672480] using wordTrace_append hprefix tailTrace_7672480
  have hstable : (prefixWord ++ tailWord_7672480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7672480).length < 2 ^ (prefixWord ++ tailWord_7672480).sum := by decide
  have hdescent : baseEnd_7672480 < baseStart_7672480 := by decide
  rcases family_descends (prefixWord ++ tailWord_7672480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7672489 : List Nat := [1, 2, 1, 1, 1, 1, 2, 6, 1, 1, 6]
def baseStart_7672489 : Nat := 118140960795 + 7672489 * 2 ^ 59
def prefixEnd_7672489 : Nat := 4983230072969 + 3 ^ 40 * 7672489 * 2
def baseEnd_7672489 : Nat := 3939674673334137085202371

theorem tailTrace_7672489 : CollatzResearch.WordTrace tailWord_7672489 prefixEnd_7672489 3939674673334137085202371 := by
  unfold tailWord_7672489
  simp only [CollatzResearch.WordTrace]
  refine ⟨279838663500890184643476521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186559109000593456428984347 279838663500890184643476521)
  ·
    refine ⟨209878997625667638482607391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279838663500890184643476521 209878997625667638482607391)
    ·
      refine ⟨314818496438501457723911087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209878997625667638482607391 314818496438501457723911087)
      ·
        refine ⟨472227744657752186585866631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314818496438501457723911087 472227744657752186585866631)
        ·
          refine ⟨708341616986628279878799947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 472227744657752186585866631 708341616986628279878799947)
          ·
            refine ⟨1062512425479942419818199921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 708341616986628279878799947 1062512425479942419818199921)
            ·
              refine ⟨796884319109956814863649941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1062512425479942419818199921 796884319109956814863649941)
              ·
                refine ⟨37353952458279225696733591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 796884319109956814863649941 37353952458279225696733591)
                ·
                  refine ⟨56030928687418838545100387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37353952458279225696733591 56030928687418838545100387)
                  ·
                    refine ⟨84046393031128257817650581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56030928687418838545100387 84046393031128257817650581)
                    ·
                      refine ⟨3939674673334137085202371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84046393031128257817650581 3939674673334137085202371)
                      ·
                        rfl

theorem cell23_7672489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 6, 1, 1, 6].length) (baseStart_7672489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7672489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7672489 prefixEnd_7672489 := by exact prefixLift 7672489
  have htrace : WordTrace (prefixWord ++ tailWord_7672489) baseStart_7672489 baseEnd_7672489 := by
    simpa [prefixWord, tailWord_7672489, baseEnd_7672489] using wordTrace_append hprefix tailTrace_7672489
  have hstable : (prefixWord ++ tailWord_7672489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7672489).length < 2 ^ (prefixWord ++ tailWord_7672489).sum := by decide
  have hdescent : baseEnd_7672489 < baseStart_7672489 := by decide
  rcases family_descends (prefixWord ++ tailWord_7672489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7672496 : List Nat := [2, 1, 1, 1, 2, 1, 3, 4, 3, 2, 3]
def baseStart_7672496 : Nat := 118140960795 + 7672496 * 2 ^ 59
def prefixEnd_7672496 : Nat := 4983230072969 + 3 ^ 40 * 7672496 * 2
def baseEnd_7672496 : Nat := 3939678267698718557814839

theorem tailTrace_7672496 : CollatzResearch.WordTrace tailWord_7672496 prefixEnd_7672496 3939678267698718557814839 := by
  unfold tailWord_7672496
  simp only [CollatzResearch.WordTrace]
  refine ⟨139919459405932412419490671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186559279207909883225987561 139919459405932412419490671)
  ·
    refine ⟨209879189108898618629236007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139919459405932412419490671 209879189108898618629236007)
    ·
      refine ⟨314818783663347927943854011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209879189108898618629236007 314818783663347927943854011)
      ·
        refine ⟨472228175495021891915781017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314818783663347927943854011 472228175495021891915781017)
        ·
          refine ⟨354171131621266418936835763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 472228175495021891915781017 354171131621266418936835763)
          ·
            refine ⟨531256697431899628405253645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 354171131621266418936835763 531256697431899628405253645)
            ·
              refine ⟨199221261536962360651970117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 531256697431899628405253645 199221261536962360651970117)
              ·
                refine ⟨37353986538180442622244397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 199221261536962360651970117 37353986538180442622244397)
                ·
                  refine ⟨14007744951817665983341649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37353986538180442622244397 14007744951817665983341649)
                  ·
                    refine ⟨10505808713863249487506237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14007744951817665983341649 10505808713863249487506237)
                    ·
                      refine ⟨3939678267698718557814839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10505808713863249487506237 3939678267698718557814839)
                      ·
                        rfl

theorem cell23_7672496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 4, 3, 2, 3].length) (baseStart_7672496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7672496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7672496 prefixEnd_7672496 := by exact prefixLift 7672496
  have htrace : WordTrace (prefixWord ++ tailWord_7672496) baseStart_7672496 baseEnd_7672496 := by
    simpa [prefixWord, tailWord_7672496, baseEnd_7672496] using wordTrace_append hprefix tailTrace_7672496
  have hstable : (prefixWord ++ tailWord_7672496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7672496).length < 2 ^ (prefixWord ++ tailWord_7672496).sum := by decide
  have hdescent : baseEnd_7672496 < baseStart_7672496 := by decide
  rcases family_descends (prefixWord ++ tailWord_7672496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7672499 : List Nat := [1, 1, 1, 2, 3, 4, 1, 10]
def baseStart_7672499 : Nat := 118140960795 + 7672499 * 2 ^ 59
def prefixEnd_7672499 : Nat := 4983230072969 + 3 ^ 40 * 7672499 * 2
def baseEnd_7672499 : Nat := 145914066968173409113975

theorem tailTrace_7672499 : CollatzResearch.WordTrace tailWord_7672499 prefixEnd_7672499 145914066968173409113975 := by
  unfold tailWord_7672499
  simp only [CollatzResearch.WordTrace]
  refine ⟨279839028230853956351340551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186559352153902637567560367 279839028230853956351340551)
  ·
    refine ⟨419758542346280934527010827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279839028230853956351340551 419758542346280934527010827)
    ·
      refine ⟨629637813519421401790516241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419758542346280934527010827 629637813519421401790516241)
      ·
        refine ⟨472228360139566051342887181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 629637813519421401790516241 472228360139566051342887181)
        ·
          refine ⟨177085635052337269253582693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 472228360139566051342887181 177085635052337269253582693)
          ·
            refine ⟨33203556572313237985046755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 177085635052337269253582693 33203556572313237985046755)
            ·
              refine ⟨49805334858469856977570133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33203556572313237985046755 49805334858469856977570133)
              ·
                refine ⟨145914066968173409113975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 49805334858469856977570133 145914066968173409113975)
                ·
                  rfl

theorem cell23_7672499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 10].length) (baseStart_7672499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7672499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7672499 prefixEnd_7672499 := by exact prefixLift 7672499
  have htrace : WordTrace (prefixWord ++ tailWord_7672499) baseStart_7672499 baseEnd_7672499 := by
    simpa [prefixWord, tailWord_7672499, baseEnd_7672499] using wordTrace_append hprefix tailTrace_7672499
  have hstable : (prefixWord ++ tailWord_7672499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7672499).length < 2 ^ (prefixWord ++ tailWord_7672499).sum := by decide
  have hdescent : baseEnd_7672499 < baseStart_7672499 := by decide
  rcases family_descends (prefixWord ++ tailWord_7672499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7672506 : List Nat := [3, 1, 1, 1, 2, 3, 2, 3, 1, 2, 4]
def baseStart_7672506 : Nat := 118140960795 + 7672506 * 2 ^ 59
def prefixEnd_7672506 : Nat := 4983230072969 + 3 ^ 40 * 7672506 * 2
def baseEnd_7672506 : Nat := 3939683402505263518689793

theorem tailTrace_7672506 : CollatzResearch.WordTrace tailWord_7672506 prefixEnd_7672506 3939683402505263518689793 := by
  unfold tailWord_7672506
  simp only [CollatzResearch.WordTrace]
  refine ⟨69959820885457149136711343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186559522361219064364563581 69959820885457149136711343)
  ·
    refine ⟨104939731328185723705067015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69959820885457149136711343 104939731328185723705067015)
    ·
      refine ⟨157409596992278585557600523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104939731328185723705067015 157409596992278585557600523)
      ·
        refine ⟨236114395488417878336400785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157409596992278585557600523 236114395488417878336400785)
        ·
          refine ⟨177085796616313408752300589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236114395488417878336400785 177085796616313408752300589)
          ·
            refine ⟨66407173731117528282112721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177085796616313408752300589 66407173731117528282112721)
            ·
              refine ⟨49805380298338146211584541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66407173731117528282112721 49805380298338146211584541)
              ·
                refine ⟨18677017611876804829344203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49805380298338146211584541 18677017611876804829344203)
                ·
                  refine ⟨28015526417815207244016305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18677017611876804829344203 28015526417815207244016305)
                  ·
                    refine ⟨21011644813361405433012229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28015526417815207244016305 21011644813361405433012229)
                    ·
                      refine ⟨3939683402505263518689793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21011644813361405433012229 3939683402505263518689793)
                      ·
                        rfl

theorem cell23_7672506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 3, 1, 2, 4].length) (baseStart_7672506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7672506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7672506 prefixEnd_7672506 := by exact prefixLift 7672506
  have htrace : WordTrace (prefixWord ++ tailWord_7672506) baseStart_7672506 baseEnd_7672506 := by
    simpa [prefixWord, tailWord_7672506, baseEnd_7672506] using wordTrace_append hprefix tailTrace_7672506
  have hstable : (prefixWord ++ tailWord_7672506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7672506).length < 2 ^ (prefixWord ++ tailWord_7672506).sum := by decide
  have hdescent : baseEnd_7672506 < baseStart_7672506 := by decide
  rcases family_descends (prefixWord ++ tailWord_7672506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7672510 : List Nat := [4, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2]
def baseStart_7672510 : Nat := 118140960795 + 7672510 * 2 ^ 59
def prefixEnd_7672510 : Nat := 4983230072969 + 3 ^ 40 * 7672510 * 2
def baseEnd_7672510 : Nat := 3939685456427881503039775

theorem tailTrace_7672510 : CollatzResearch.WordTrace tailWord_7672510 prefixEnd_7672510 3939685456427881503039775 := by
  unfold tailWord_7672510
  simp only [CollatzResearch.WordTrace]
  refine ⟨34979928679226763153748873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186559619622542736819993989 34979928679226763153748873)
  ·
    refine ⟨26234946509420072365311655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34979928679226763153748873 26234946509420072365311655)
    ·
      refine ⟨39352419764130108547967483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26234946509420072365311655 39352419764130108547967483)
      ·
        refine ⟨59028629646195162821951225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39352419764130108547967483 59028629646195162821951225)
        ·
          refine ⟨44271472234646372116463419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59028629646195162821951225 44271472234646372116463419)
          ·
            refine ⟨66407208351969558174695129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44271472234646372116463419 66407208351969558174695129)
            ·
              refine ⟨49805406263977168631021347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66407208351969558174695129 49805406263977168631021347)
              ·
                refine ⟨74708109395965752946532021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49805406263977168631021347 74708109395965752946532021)
                ·
                  refine ⟨7003885255871789338737377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74708109395965752946532021 7003885255871789338737377)
                  ·
                    refine ⟨5252913941903842004053033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7003885255871789338737377 5252913941903842004053033)
                    ·
                      refine ⟨3939685456427881503039775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5252913941903842004053033 3939685456427881503039775)
                      ·
                        rfl

theorem cell23_7672510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2].length) (baseStart_7672510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7672510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7672510 prefixEnd_7672510 := by exact prefixLift 7672510
  have htrace : WordTrace (prefixWord ++ tailWord_7672510) baseStart_7672510 baseEnd_7672510 := by
    simpa [prefixWord, tailWord_7672510, baseEnd_7672510] using wordTrace_append hprefix tailTrace_7672510
  have hstable : (prefixWord ++ tailWord_7672510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7672510).length < 2 ^ (prefixWord ++ tailWord_7672510).sum := by decide
  have hdescent : baseEnd_7672510 < baseStart_7672510 := by decide
  rcases family_descends (prefixWord ++ tailWord_7672510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7672516 : List Nat := [2, 3, 3, 1, 1, 2, 2, 9]
def baseStart_7672516 : Nat := 118140960795 + 7672516 * 2 ^ 59
def prefixEnd_7672516 : Nat := 4983230072969 + 3 ^ 40 * 7672516 * 2
def baseEnd_7672516 : Nat := 145914390270807721465361

theorem tailTrace_7672516 : CollatzResearch.WordTrace tailWord_7672516 prefixEnd_7672516 145914390270807721465361 := by
  unfold tailWord_7672516
  simp only [CollatzResearch.WordTrace]
  refine ⟨139919824135896184127354701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186559765514528245503139601 139919824135896184127354701)
  ·
    refine ⟨52469934050961069047758013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139919824135896184127354701 52469934050961069047758013)
    ·
      refine ⟨19676225269110400892909255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52469934050961069047758013 19676225269110400892909255)
      ·
        refine ⟨29514337903665601339363883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19676225269110400892909255 29514337903665601339363883)
        ·
          refine ⟨44271506855498402009045825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29514337903665601339363883 44271506855498402009045825)
          ·
            refine ⟨33203630141623801506784369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44271506855498402009045825 33203630141623801506784369)
            ·
              refine ⟨24902722606217851130088277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33203630141623801506784369 24902722606217851130088277)
              ·
                refine ⟨145914390270807721465361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24902722606217851130088277 145914390270807721465361)
                ·
                  rfl

theorem cell23_7672516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 9].length) (baseStart_7672516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7672516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7672516 prefixEnd_7672516 := by exact prefixLift 7672516
  have htrace : WordTrace (prefixWord ++ tailWord_7672516) baseStart_7672516 baseEnd_7672516 := by
    simpa [prefixWord, tailWord_7672516, baseEnd_7672516] using wordTrace_append hprefix tailTrace_7672516
  have hstable : (prefixWord ++ tailWord_7672516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7672516).length < 2 ^ (prefixWord ++ tailWord_7672516).sum := by decide
  have hdescent : baseEnd_7672516 < baseStart_7672516 := by decide
  rcases family_descends (prefixWord ++ tailWord_7672516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7672530 : List Nat := [3, 2, 2, 2, 3, 2, 1, 1, 1, 1, 5]
def baseStart_7672530 : Nat := 118140960795 + 7672530 * 2 ^ 59
def prefixEnd_7672530 : Nat := 4983230072969 + 3 ^ 40 * 7672530 * 2
def baseEnd_7672530 : Nat := 3939695726040971424789683

theorem tailTrace_7672530 : CollatzResearch.WordTrace tailWord_7672530 prefixEnd_7672530 3939695726040971424789683 := by
  unfold tailWord_7672530
  simp only [CollatzResearch.WordTrace]
  refine ⟨69960039723435412161429761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186560105929161099097146029 69960039723435412161429761)
  ·
    refine ⟨52470029792576559121072321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69960039723435412161429761 52470029792576559121072321)
    ·
      refine ⟨39352522344432419340804241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52470029792576559121072321 39352522344432419340804241)
      ·
        refine ⟨29514391758324314505603181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39352522344432419340804241 29514391758324314505603181)
        ·
          refine ⟨11067896909371617939601193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29514391758324314505603181 11067896909371617939601193)
          ·
            refine ⟨8300922682028713454700895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11067896909371617939601193 8300922682028713454700895)
            ·
              refine ⟨12451384023043070182051343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8300922682028713454700895 12451384023043070182051343)
              ·
                refine ⟨18677076034564605273077015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12451384023043070182051343 18677076034564605273077015)
                ·
                  refine ⟨28015614051846907909615523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18677076034564605273077015 28015614051846907909615523)
                  ·
                    refine ⟨42023421077770361864423285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28015614051846907909615523 42023421077770361864423285)
                    ·
                      refine ⟨3939695726040971424789683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42023421077770361864423285 3939695726040971424789683)
                      ·
                        rfl

theorem cell23_7672530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_7672530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7672530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7672530 prefixEnd_7672530 := by exact prefixLift 7672530
  have htrace : WordTrace (prefixWord ++ tailWord_7672530) baseStart_7672530 baseEnd_7672530 := by
    simpa [prefixWord, tailWord_7672530, baseEnd_7672530] using wordTrace_append hprefix tailTrace_7672530
  have hstable : (prefixWord ++ tailWord_7672530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7672530).length < 2 ^ (prefixWord ++ tailWord_7672530).sum := by decide
  have hdescent : baseEnd_7672530 < baseStart_7672530 := by decide
  rcases family_descends (prefixWord ++ tailWord_7672530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7672533 : List Nat := [1, 3, 2, 5, 2, 10]
def baseStart_7672533 : Nat := 118140960795 + 7672533 * 2 ^ 59
def prefixEnd_7672533 : Nat := 4983230072969 + 3 ^ 40 * 7672533 * 2
def baseEnd_7672533 : Nat := 16212745952604670424083

theorem tailTrace_7672533 : CollatzResearch.WordTrace tailWord_7672533 prefixEnd_7672533 16212745952604670424083 := by
  unfold tailWord_7672533
  simp only [CollatzResearch.WordTrace]
  refine ⟨279840268312730780158078253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186560178875153853438718835 279840268312730780158078253)
  ·
    refine ⟨104940100617274042559279345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 279840268312730780158078253 104940100617274042559279345)
    ·
      refine ⟨78705075462955531919459509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104940100617274042559279345 78705075462955531919459509)
      ·
        refine ⟨7378600824652081117449329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78705075462955531919459509 7378600824652081117449329)
        ·
          refine ⟨5533950618489060838086997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7378600824652081117449329 5533950618489060838086997)
          ·
            refine ⟨16212745952604670424083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5533950618489060838086997 16212745952604670424083)
            ·
              rfl

theorem cell23_7672533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 10].length) (baseStart_7672533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7672533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7672533 prefixEnd_7672533 := by exact prefixLift 7672533
  have htrace : WordTrace (prefixWord ++ tailWord_7672533) baseStart_7672533 baseEnd_7672533 := by
    simpa [prefixWord, tailWord_7672533, baseEnd_7672533] using wordTrace_append hprefix tailTrace_7672533
  have hstable : (prefixWord ++ tailWord_7672533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7672533).length < 2 ^ (prefixWord ++ tailWord_7672533).sum := by decide
  have hdescent : baseEnd_7672533 < baseStart_7672533 := by decide
  rcases family_descends (prefixWord ++ tailWord_7672533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7672553 : List Nat := [1, 2, 1, 1, 1, 2, 5, 2, 3, 3, 2]
def baseStart_7672553 : Nat := 118140960795 + 7672553 * 2 ^ 59
def prefixEnd_7672553 : Nat := 4983230072969 + 3 ^ 40 * 7672553 * 2
def baseEnd_7672553 : Nat := 3939707536096024834802077

theorem tailTrace_7672553 : CollatzResearch.WordTrace tailWord_7672553 prefixEnd_7672553 3939707536096024834802077 := by
  unfold tailWord_7672553
  simp only [CollatzResearch.WordTrace]
  refine ⟨279840997772658323573806313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186560665181772215715870875 279840997772658323573806313)
  ·
    refine ⟨209880748329493742680354735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279840997772658323573806313 209880748329493742680354735)
    ·
      refine ⟨314821122494240614020532103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209880748329493742680354735 314821122494240614020532103)
      ·
        refine ⟨472231683741360921030798155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314821122494240614020532103 472231683741360921030798155)
        ·
          refine ⟨708347525612041381546197233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 472231683741360921030798155 708347525612041381546197233)
          ·
            refine ⟨531260644209031036159647925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 708347525612041381546197233 531260644209031036159647925)
            ·
              refine ⟨49805685394596659639966993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 531260644209031036159647925 49805685394596659639966993)
              ·
                refine ⟨37354264045947494729975245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49805685394596659639966993 37354264045947494729975245)
                ·
                  refine ⟨14007849017230310523740717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37354264045947494729975245 14007849017230310523740717)
                  ·
                    refine ⟨5252943381461366446402769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14007849017230310523740717 5252943381461366446402769)
                    ·
                      refine ⟨3939707536096024834802077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5252943381461366446402769 3939707536096024834802077)
                      ·
                        rfl

theorem cell23_7672553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 2, 3, 3, 2].length) (baseStart_7672553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7672553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7672553 prefixEnd_7672553 := by exact prefixLift 7672553
  have htrace : WordTrace (prefixWord ++ tailWord_7672553) baseStart_7672553 baseEnd_7672553 := by
    simpa [prefixWord, tailWord_7672553, baseEnd_7672553] using wordTrace_append hprefix tailTrace_7672553
  have hstable : (prefixWord ++ tailWord_7672553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7672553).length < 2 ^ (prefixWord ++ tailWord_7672553).sum := by decide
  have hdescent : baseEnd_7672553 < baseStart_7672553 := by decide
  rcases family_descends (prefixWord ++ tailWord_7672553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7672586 : List Nat := [3, 1, 2, 2, 1, 2, 2, 1, 1, 3, 5]
def baseStart_7672586 : Nat := 118140960795 + 7672586 * 2 ^ 59
def prefixEnd_7672586 : Nat := 4983230072969 + 3 ^ 40 * 7672586 * 2
def baseEnd_7672586 : Nat := 3939724480957623205689425

theorem tailTrace_7672586 : CollatzResearch.WordTrace tailWord_7672586 prefixEnd_7672586 3939724480957623205689425 := by
  unfold tailWord_7672586
  simp only [CollatzResearch.WordTrace]
  refine ⟨69960550345384692552439403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186561467587692513473171741 69960550345384692552439403)
  ·
    refine ⟨104940825518077038828659105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69960550345384692552439403 104940825518077038828659105)
    ·
      refine ⟨78705619138557779121494329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104940825518077038828659105 78705619138557779121494329)
      ·
        refine ⟨59029214353918334341120747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78705619138557779121494329 59029214353918334341120747)
        ·
          refine ⟨88543821530877501511681121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59029214353918334341120747 88543821530877501511681121)
          ·
            refine ⟨66407866148158126133760841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88543821530877501511681121 66407866148158126133760841)
            ·
              refine ⟨49805899611118594600320631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66407866148158126133760841 49805899611118594600320631)
              ·
                refine ⟨74708849416677891900480947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49805899611118594600320631 74708849416677891900480947)
                ·
                  refine ⟨112063274125016837850721421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74708849416677891900480947 112063274125016837850721421)
                  ·
                    refine ⟨42023727796881314194020533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 112063274125016837850721421 42023727796881314194020533)
                    ·
                      refine ⟨3939724480957623205689425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42023727796881314194020533 3939724480957623205689425)
                      ·
                        rfl

theorem cell23_7672586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_7672586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7672586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7672586 prefixEnd_7672586 := by exact prefixLift 7672586
  have htrace : WordTrace (prefixWord ++ tailWord_7672586) baseStart_7672586 baseEnd_7672586 := by
    simpa [prefixWord, tailWord_7672586, baseEnd_7672586] using wordTrace_append hprefix tailTrace_7672586
  have hstable : (prefixWord ++ tailWord_7672586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7672586).length < 2 ^ (prefixWord ++ tailWord_7672586).sum := by decide
  have hdescent : baseEnd_7672586 < baseStart_7672586 := by decide
  rcases family_descends (prefixWord ++ tailWord_7672586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7672621 : List Nat := [1, 5, 3, 2, 1, 1, 2, 2, 1, 3, 2]
def baseStart_7672621 : Nat := 118140960795 + 7672621 * 2 ^ 59
def prefixEnd_7672621 : Nat := 4983230072969 + 3 ^ 40 * 7672621 * 2
def baseEnd_7672621 : Nat := 3939742452780530568751765

theorem tailTrace_7672621 : CollatzResearch.WordTrace tailWord_7672621 prefixEnd_7672621 3939742452780530568751765 := by
  unfold tailWord_7672621
  simp only [CollatzResearch.WordTrace]
  refine ⟨279843477936411971187281717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186562318624274647458187811 279843477936411971187281717)
  ·
    refine ⟨26235326056538622298807661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 279843477936411971187281717 26235326056538622298807661)
    ·
      refine ⟨9838247271201983362052873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26235326056538622298807661 9838247271201983362052873)
      ·
        refine ⟨7378685453401487521539655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9838247271201983362052873 7378685453401487521539655)
        ·
          refine ⟨11068028180102231282309483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7378685453401487521539655 11068028180102231282309483)
          ·
            refine ⟨16602042270153346923464225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11068028180102231282309483 16602042270153346923464225)
            ·
              refine ⟨12451531702615010192598169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16602042270153346923464225 12451531702615010192598169)
              ·
                refine ⟨9338648776961257644448627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12451531702615010192598169 9338648776961257644448627)
                ·
                  refine ⟨14007973165441886466672941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9338648776961257644448627 14007973165441886466672941)
                  ·
                    refine ⟨5252989937040707425002353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14007973165441886466672941 5252989937040707425002353)
                    ·
                      refine ⟨3939742452780530568751765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5252989937040707425002353 3939742452780530568751765)
                      ·
                        rfl

theorem cell23_7672621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_7672621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7672621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7672621 prefixEnd_7672621 := by exact prefixLift 7672621
  have htrace : WordTrace (prefixWord ++ tailWord_7672621) baseStart_7672621 baseEnd_7672621 := by
    simpa [prefixWord, tailWord_7672621, baseEnd_7672621] using wordTrace_append hprefix tailTrace_7672621
  have hstable : (prefixWord ++ tailWord_7672621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7672621).length < 2 ^ (prefixWord ++ tailWord_7672621).sum := by decide
  have hdescent : baseEnd_7672621 < baseStart_7672621 := by decide
  rcases family_descends (prefixWord ++ tailWord_7672621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7672657 : List Nat := [1, 2, 2, 1, 6, 1, 3, 2, 5]
def baseStart_7672657 : Nat := 118140960795 + 7672657 * 2 ^ 59
def prefixEnd_7672657 : Nat := 4983230072969 + 3 ^ 40 * 7672657 * 2
def baseEnd_7672657 : Nat := 437751215342676936433511

theorem tailTrace_7672657 : CollatzResearch.WordTrace tailWord_7672657 prefixEnd_7672657 437751215342676936433511 := by
  unfold tailWord_7672657
  simp only [CollatzResearch.WordTrace]
  refine ⟨279844790964281549335592225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186563193976187699557061483 279844790964281549335592225)
  ·
    refine ⟨209883593223211162001694169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279844790964281549335592225 209883593223211162001694169)
    ·
      refine ⟨157412694917408371501270627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209883593223211162001694169 157412694917408371501270627)
      ·
        refine ⟨236119042376112557251905941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157412694917408371501270627 236119042376112557251905941)
        ·
          refine ⟨11068080111380276121183091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 236119042376112557251905941 11068080111380276121183091)
          ·
            refine ⟨16602120167070414181774637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11068080111380276121183091 16602120167070414181774637)
            ·
              refine ⟨6225795062651405318165489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16602120167070414181774637 6225795062651405318165489)
              ·
                refine ⟨4669346296988553988624117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6225795062651405318165489 4669346296988553988624117)
                ·
                  refine ⟨437751215342676936433511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4669346296988553988624117 437751215342676936433511)
                  ·
                    rfl

theorem cell23_7672657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 3, 2, 5].length) (baseStart_7672657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7672657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7672657 prefixEnd_7672657 := by exact prefixLift 7672657
  have htrace : WordTrace (prefixWord ++ tailWord_7672657) baseStart_7672657 baseEnd_7672657 := by
    simpa [prefixWord, tailWord_7672657, baseEnd_7672657] using wordTrace_append hprefix tailTrace_7672657
  have hstable : (prefixWord ++ tailWord_7672657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7672657).length < 2 ^ (prefixWord ++ tailWord_7672657).sum := by decide
  have hdescent : baseEnd_7672657 < baseStart_7672657 := by decide
  rcases family_descends (prefixWord ++ tailWord_7672657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7672663 : List Nat := [1, 1, 3, 2, 4, 2, 1, 1, 1, 2, 5]
def baseStart_7672663 : Nat := 118140960795 + 7672663 * 2 ^ 59
def prefixEnd_7672663 : Nat := 4983230072969 + 3 ^ 40 * 7672663 * 2
def baseEnd_7672663 : Nat := 3939764018968019404426571

theorem tailTrace_7672663 : CollatzResearch.WordTrace tailWord_7672663 prefixEnd_7672663 3939764018968019404426571 := by
  unfold tailWord_7672663
  simp only [CollatzResearch.WordTrace]
  refine ⟨279845009802259812360310643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186563339868173208240207095 279845009802259812360310643)
  ·
    refine ⟨419767514703389718540465965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279845009802259812360310643 419767514703389718540465965)
    ·
      refine ⟨157412818013771144452674737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 419767514703389718540465965 157412818013771144452674737)
      ·
        refine ⟨118059613510328358339506053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157412818013771144452674737 118059613510328358339506053)
        ·
          refine ⟨22136177533186567188657385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118059613510328358339506053 22136177533186567188657385)
          ·
            refine ⟨16602133149889925391493039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22136177533186567188657385 16602133149889925391493039)
            ·
              refine ⟨24903199724834888087239559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16602133149889925391493039 24903199724834888087239559)
              ·
                refine ⟨37354799587252332130859339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24903199724834888087239559 37354799587252332130859339)
                ·
                  refine ⟨56032199380878498196289009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37354799587252332130859339 56032199380878498196289009)
                  ·
                    refine ⟨42024149535658873647216757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56032199380878498196289009 42024149535658873647216757)
                    ·
                      refine ⟨3939764018968019404426571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42024149535658873647216757 3939764018968019404426571)
                      ·
                        rfl

theorem cell23_7672663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 1, 1, 2, 5].length) (baseStart_7672663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7672663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7672663 prefixEnd_7672663 := by exact prefixLift 7672663
  have htrace : WordTrace (prefixWord ++ tailWord_7672663) baseStart_7672663 baseEnd_7672663 := by
    simpa [prefixWord, tailWord_7672663, baseEnd_7672663] using wordTrace_append hprefix tailTrace_7672663
  have hstable : (prefixWord ++ tailWord_7672663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7672663).length < 2 ^ (prefixWord ++ tailWord_7672663).sum := by decide
  have hdescent : baseEnd_7672663 < baseStart_7672663 := by decide
  rcases family_descends (prefixWord ++ tailWord_7672663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7672683 : List Nat := [1, 1, 1, 1, 2, 2, 4, 4, 3, 4]
def baseStart_7672683 : Nat := 118140960795 + 7672683 * 2 ^ 59
def prefixEnd_7672683 : Nat := 4983230072969 + 3 ^ 40 * 7672683 * 2
def baseEnd_7672683 : Nat := 1313258096193703108725493

theorem tailTrace_7672683 : CollatzResearch.WordTrace tailWord_7672683 prefixEnd_7672683 1313258096193703108725493 := by
  unfold tailWord_7672683
  simp only [CollatzResearch.WordTrace]
  refine ⟨279845739262187355776038703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186563826174791570517359135 279845739262187355776038703)
  ·
    refine ⟨419768608893281033664058055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279845739262187355776038703 419768608893281033664058055)
    ·
      refine ⟨629652913339921550496087083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419768608893281033664058055 629652913339921550496087083)
      ·
        refine ⟨944479370009882325744130625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 629652913339921550496087083 944479370009882325744130625)
        ·
          refine ⟨708359527507411744308097969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 944479370009882325744130625 708359527507411744308097969)
          ·
            refine ⟨531269645630558808231073477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 708359527507411744308097969 531269645630558808231073477)
            ·
              refine ⟨99613058555729776543326277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 531269645630558808231073477 99613058555729776543326277)
              ·
                refine ⟨18677448479199333101873677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99613058555729776543326277 18677448479199333101873677)
                ·
                  refine ⟨7004043179699749913202629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18677448479199333101873677 7004043179699749913202629)
                  ·
                    refine ⟨1313258096193703108725493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7004043179699749913202629 1313258096193703108725493)
                    ·
                      rfl

theorem cell23_7672683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4, 3, 4].length) (baseStart_7672683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7672683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7672683 prefixEnd_7672683 := by exact prefixLift 7672683
  have htrace : WordTrace (prefixWord ++ tailWord_7672683) baseStart_7672683 baseEnd_7672683 := by
    simpa [prefixWord, tailWord_7672683, baseEnd_7672683] using wordTrace_append hprefix tailTrace_7672683
  have hstable : (prefixWord ++ tailWord_7672683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7672683).length < 2 ^ (prefixWord ++ tailWord_7672683).sum := by decide
  have hdescent : baseEnd_7672683 < baseStart_7672683 := by decide
  rcases family_descends (prefixWord ++ tailWord_7672683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7672696 : List Nat := [2, 1, 2, 1, 1, 1, 1, 6, 8]
def baseStart_7672696 : Nat := 118140960795 + 7672696 * 2 ^ 59
def prefixEnd_7672696 : Nat := 4983230072969 + 3 ^ 40 * 7672696 * 2
def baseEnd_7672696 : Nat := 437753440425513086145991

theorem tailTrace_7672696 : CollatzResearch.WordTrace tailWord_7672696 prefixEnd_7672696 437753440425513086145991 := by
  unfold tailWord_7672696
  simp only [CollatzResearch.WordTrace]
  refine ⟨139923106705570129498130971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186564142274093505997507961 139923106705570129498130971)
  ·
    refine ⟨209884660058355194247196457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139923106705570129498130971 209884660058355194247196457)
    ·
      refine ⟨157413495043766395685397343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209884660058355194247196457 157413495043766395685397343)
      ·
        refine ⟨236120242565649593528096015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157413495043766395685397343 236120242565649593528096015)
        ·
          refine ⟨354180363848474390292144023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236120242565649593528096015 354180363848474390292144023)
          ·
            refine ⟨531270545772711585438216035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 354180363848474390292144023 531270545772711585438216035)
            ·
              refine ⟨796905818659067378157324053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 531270545772711585438216035 796905818659067378157324053)
              ·
                refine ⟨37354960249643783351124565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 796905818659067378157324053 37354960249643783351124565)
                ·
                  refine ⟨437753440425513086145991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37354960249643783351124565 437753440425513086145991)
                  ·
                    rfl

theorem cell23_7672696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 6, 8].length) (baseStart_7672696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7672696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7672696 prefixEnd_7672696 := by exact prefixLift 7672696
  have htrace : WordTrace (prefixWord ++ tailWord_7672696) baseStart_7672696 baseEnd_7672696 := by
    simpa [prefixWord, tailWord_7672696, baseEnd_7672696] using wordTrace_append hprefix tailTrace_7672696
  have hstable : (prefixWord ++ tailWord_7672696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7672696).length < 2 ^ (prefixWord ++ tailWord_7672696).sum := by decide
  have hdescent : baseEnd_7672696 < baseStart_7672696 := by decide
  rcases family_descends (prefixWord ++ tailWord_7672696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7672713 : List Nat := [1, 2, 1, 1, 5, 2, 1, 4, 6]
def baseStart_7672713 : Nat := 118140960795 + 7672713 * 2 ^ 59
def prefixEnd_7672713 : Nat := 4983230072969 + 3 ^ 40 * 7672713 * 2
def baseEnd_7672713 : Nat := 437754410333416023200149

theorem tailTrace_7672713 : CollatzResearch.WordTrace tailWord_7672713 prefixEnd_7672713 437754410333416023200149 := by
  unfold tailWord_7672713
  simp only [CollatzResearch.WordTrace]
  refine ⟨279846833452078670899630793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186564555634719113933087195 279846833452078670899630793)
  ·
    refine ⟨209885125089059003174723095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279846833452078670899630793 209885125089059003174723095)
    ·
      refine ⟨314827687633588504762084643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209885125089059003174723095 314827687633588504762084643)
      ·
        refine ⟨472241531450382757143126965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314827687633588504762084643 472241531450382757143126965)
        ·
          refine ⟨44272643573473383482168153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 472241531450382757143126965 44272643573473383482168153)
          ·
            refine ⟨33204482680105037611626115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44272643573473383482168153 33204482680105037611626115)
            ·
              refine ⟨49806724020157556417439173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33204482680105037611626115 49806724020157556417439173)
              ·
                refine ⟨9338760753779541828269845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49806724020157556417439173 9338760753779541828269845)
                ·
                  refine ⟨437754410333416023200149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9338760753779541828269845 437754410333416023200149)
                  ·
                    rfl

theorem cell23_7672713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 4, 6].length) (baseStart_7672713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7672713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7672713 prefixEnd_7672713 := by exact prefixLift 7672713
  have htrace : WordTrace (prefixWord ++ tailWord_7672713) baseStart_7672713 baseEnd_7672713 := by
    simpa [prefixWord, tailWord_7672713, baseEnd_7672713] using wordTrace_append hprefix tailTrace_7672713
  have hstable : (prefixWord ++ tailWord_7672713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7672713).length < 2 ^ (prefixWord ++ tailWord_7672713).sum := by decide
  have hdescent : baseEnd_7672713 < baseStart_7672713 := by decide
  rcases family_descends (prefixWord ++ tailWord_7672713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7672760 : List Nat := [2, 1, 2, 1, 2, 5, 1, 3, 1, 5]
def baseStart_7672760 : Nat := 118140960795 + 7672760 * 2 ^ 59
def prefixEnd_7672760 : Nat := 4983230072969 + 3 ^ 40 * 7672760 * 2
def baseEnd_7672760 : Nat := 1313271275530501841637875

theorem tailTrace_7672760 : CollatzResearch.WordTrace tailWord_7672760 prefixEnd_7672760 1313271275530501841637875 := by
  unfold tailWord_7672760
  simp only [CollatzResearch.WordTrace]
  refine ⟨139924273841454198963295867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186565698455272265284394489 139924273841454198963295867)
  ·
    refine ⟨209886410762181298444943801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139924273841454198963295867 209886410762181298444943801)
    ·
      refine ⟨157414808071635973833707851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209886410762181298444943801 157414808071635973833707851)
      ·
        refine ⟨236122212107453960750561777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157414808071635973833707851 236122212107453960750561777)
        ·
          refine ⟨177091659080590470562921333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236122212107453960750561777 177091659080590470562921333)
          ·
            refine ⟨16602343038805356615273875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 177091659080590470562921333 16602343038805356615273875)
            ·
              refine ⟨24903514558208034922910813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16602343038805356615273875 24903514558208034922910813)
              ·
                refine ⟨9338817959328013096091555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24903514558208034922910813 9338817959328013096091555)
                ·
                  refine ⟨14008226938992019644137333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9338817959328013096091555 14008226938992019644137333)
                  ·
                    refine ⟨1313271275530501841637875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14008226938992019644137333 1313271275530501841637875)
                    ·
                      rfl

theorem cell23_7672760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 3, 1, 5].length) (baseStart_7672760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7672760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7672760 prefixEnd_7672760 := by exact prefixLift 7672760
  have htrace : WordTrace (prefixWord ++ tailWord_7672760) baseStart_7672760 baseEnd_7672760 := by
    simpa [prefixWord, tailWord_7672760, baseEnd_7672760] using wordTrace_append hprefix tailTrace_7672760
  have hstable : (prefixWord ++ tailWord_7672760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7672760).length < 2 ^ (prefixWord ++ tailWord_7672760).sum := by decide
  have hdescent : baseEnd_7672760 < baseStart_7672760 := by decide
  rcases family_descends (prefixWord ++ tailWord_7672760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7672783 : List Nat := [1, 1, 2, 1, 1, 6, 1, 1, 3, 1, 5]
def baseStart_7672783 : Nat := 118140960795 + 7672783 * 2 ^ 59
def prefixEnd_7672783 : Nat := 4983230072969 + 3 ^ 40 * 7672783 * 2
def baseEnd_7672783 : Nat := 3939825636646558934926019

theorem tailTrace_7672783 : CollatzResearch.WordTrace tailWord_7672783 prefixEnd_7672783 3939825636646558934926019 := by
  unfold tailWord_7672783
  simp only [CollatzResearch.WordTrace]
  refine ⟨279849386561825072854679003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186566257707883381903119335 279849386561825072854679003)
  ·
    refine ⟨419774079842737609282018505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279849386561825072854679003 419774079842737609282018505)
    ·
      refine ⟨314830559882053206961513879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 419774079842737609282018505 314830559882053206961513879)
      ·
        refine ⟨472245839823079810442270819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314830559882053206961513879 472245839823079810442270819)
        ·
          refine ⟨708368759734619715663406229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 472245839823079810442270819 708368759734619715663406229)
          ·
            refine ⟨33204785612560299171722167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 708368759734619715663406229 33204785612560299171722167)
            ·
              refine ⟨49807178418840448757583251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33204785612560299171722167 49807178418840448757583251)
              ·
                refine ⟨74710767628260673136374877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49807178418840448757583251 74710767628260673136374877)
                ·
                  refine ⟨28016537860597752426140579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74710767628260673136374877 28016537860597752426140579)
                  ·
                    refine ⟨42024806790896628639210869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28016537860597752426140579 42024806790896628639210869)
                    ·
                      refine ⟨3939825636646558934926019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42024806790896628639210869 3939825636646558934926019)
                      ·
                        rfl

theorem cell23_7672783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 3, 1, 5].length) (baseStart_7672783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7672783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7672783 prefixEnd_7672783 := by exact prefixLift 7672783
  have htrace : WordTrace (prefixWord ++ tailWord_7672783) baseStart_7672783 baseEnd_7672783 := by
    simpa [prefixWord, tailWord_7672783, baseEnd_7672783] using wordTrace_append hprefix tailTrace_7672783
  have hstable : (prefixWord ++ tailWord_7672783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7672783).length < 2 ^ (prefixWord ++ tailWord_7672783).sum := by decide
  have hdescent : baseEnd_7672783 < baseStart_7672783 := by decide
  rcases family_descends (prefixWord ++ tailWord_7672783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7672797 : List Nat := [1, 4, 3, 1, 2, 1, 1, 4, 1, 1, 4]
def baseStart_7672797 : Nat := 118140960795 + 7672797 * 2 ^ 59
def prefixEnd_7672797 : Nat := 4983230072969 + 3 ^ 40 * 7672797 * 2
def baseEnd_7672797 : Nat := 3939832825375721880150955

theorem tailTrace_7672797 : CollatzResearch.WordTrace tailWord_7672797 prefixEnd_7672797 3939832825375721880150955 := by
  unfold tailWord_7672797
  simp only [CollatzResearch.WordTrace]
  refine ⟨279849897183774353245688645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186566598122516235497125763 279849897183774353245688645)
  ·
    refine ⟨52471855721957691233566621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 279849897183774353245688645 52471855721957691233566621)
    ·
      refine ⟨19676945895734134212587483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52471855721957691233566621 19676945895734134212587483)
      ·
        refine ⟨29515418843601201318881225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19676945895734134212587483 29515418843601201318881225)
        ·
          refine ⟨22136564132700900989160919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29515418843601201318881225 22136564132700900989160919)
          ·
            refine ⟨33204846199051351483741379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22136564132700900989160919 33204846199051351483741379)
            ·
              refine ⟨49807269298577027225612069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33204846199051351483741379 49807269298577027225612069)
              ·
                refine ⟨9338862993483192604802263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49807269298577027225612069 9338862993483192604802263)
                ·
                  refine ⟨14008294490224788907203395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9338862993483192604802263 14008294490224788907203395)
                  ·
                    refine ⟨21012441735337183360805093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14008294490224788907203395 21012441735337183360805093)
                    ·
                      refine ⟨3939832825375721880150955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21012441735337183360805093 3939832825375721880150955)
                      ·
                        rfl

theorem cell23_7672797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_7672797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7672797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7672797 prefixEnd_7672797 := by exact prefixLift 7672797
  have htrace : WordTrace (prefixWord ++ tailWord_7672797) baseStart_7672797 baseEnd_7672797 := by
    simpa [prefixWord, tailWord_7672797, baseEnd_7672797] using wordTrace_append hprefix tailTrace_7672797
  have hstable : (prefixWord ++ tailWord_7672797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7672797).length < 2 ^ (prefixWord ++ tailWord_7672797).sum := by decide
  have hdescent : baseEnd_7672797 < baseStart_7672797 := by decide
  rcases family_descends (prefixWord ++ tailWord_7672797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7672803 : List Nat := [1, 1, 1, 6, 1, 1, 3, 9]
def baseStart_7672803 : Nat := 118140960795 + 7672803 * 2 ^ 59
def prefixEnd_7672803 : Nat := 4983230072969 + 3 ^ 40 * 7672803 * 2
def baseEnd_7672803 : Nat := 145919848379986994691701

theorem tailTrace_7672803 : CollatzResearch.WordTrace tailWord_7672803 prefixEnd_7672803 145919848379986994691701 := by
  unfold tailWord_7672803
  simp only [CollatzResearch.WordTrace]
  refine ⟨279850116021752616270407063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186566744014501744180271375 279850116021752616270407063)
  ·
    refine ⟨419775174032628924405610595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279850116021752616270407063 419775174032628924405610595)
    ·
      refine ⟨629662761048943386608415893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419775174032628924405610595 629662761048943386608415893)
      ·
        refine ⟨29515441924169221247269495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 629662761048943386608415893 29515441924169221247269495)
        ·
          refine ⟨44273162886253831870904243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29515441924169221247269495 44273162886253831870904243)
          ·
            refine ⟨66409744329380747806356365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44273162886253831870904243 66409744329380747806356365)
            ·
              refine ⟨24903654123517780427383637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66409744329380747806356365 24903654123517780427383637)
              ·
                refine ⟨145919848379986994691701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24903654123517780427383637 145919848379986994691701)
                ·
                  rfl

theorem cell23_7672803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 9].length) (baseStart_7672803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7672803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7672803 prefixEnd_7672803 := by exact prefixLift 7672803
  have htrace : WordTrace (prefixWord ++ tailWord_7672803) baseStart_7672803 baseEnd_7672803 := by
    simpa [prefixWord, tailWord_7672803, baseEnd_7672803] using wordTrace_append hprefix tailTrace_7672803
  have hstable : (prefixWord ++ tailWord_7672803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7672803).length < 2 ^ (prefixWord ++ tailWord_7672803).sum := by decide
  have hdescent : baseEnd_7672803 < baseStart_7672803 := by decide
  rcases family_descends (prefixWord ++ tailWord_7672803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7672817 : List Nat := [1, 2, 2, 2, 4, 1, 2, 3, 1, 2, 3]
def baseStart_7672817 : Nat := 118140960795 + 7672817 * 2 ^ 59
def prefixEnd_7672817 : Nat := 4983230072969 + 3 ^ 40 * 7672817 * 2
def baseEnd_7672817 : Nat := 3939843094988811801900863

theorem tailTrace_7672817 : CollatzResearch.WordTrace tailWord_7672817 prefixEnd_7672817 3939843094988811801900863 := by
  unfold tailWord_7672817
  simp only [CollatzResearch.WordTrace]
  refine ⟨279850626643701896661416705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186567084429134597774277803 279850626643701896661416705)
  ·
    refine ⟨209887969982776422496062529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279850626643701896661416705 209887969982776422496062529)
    ·
      refine ⟨157415977487082316872046897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209887969982776422496062529 157415977487082316872046897)
      ·
        refine ⟨118061983115311737654035173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157415977487082316872046897 118061983115311737654035173)
        ·
          refine ⟨22136621834120950810131595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118061983115311737654035173 22136621834120950810131595)
          ·
            refine ⟨33204932751181426215197393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22136621834120950810131595 33204932751181426215197393)
            ·
              refine ⟨24903699563386069661398045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33204932751181426215197393 24903699563386069661398045)
              ·
                refine ⟨9338887336269776123024267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24903699563386069661398045 9338887336269776123024267)
                ·
                  refine ⟨14008331004404664184536401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9338887336269776123024267 14008331004404664184536401)
                  ·
                    refine ⟨10506248253303498138402301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14008331004404664184536401 10506248253303498138402301)
                    ·
                      refine ⟨3939843094988811801900863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10506248253303498138402301 3939843094988811801900863)
                      ·
                        rfl

theorem cell23_7672817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 3, 1, 2, 3].length) (baseStart_7672817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7672817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7672817 prefixEnd_7672817 := by exact prefixLift 7672817
  have htrace : WordTrace (prefixWord ++ tailWord_7672817) baseStart_7672817 baseEnd_7672817 := by
    simpa [prefixWord, tailWord_7672817, baseEnd_7672817] using wordTrace_append hprefix tailTrace_7672817
  have hstable : (prefixWord ++ tailWord_7672817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7672817).length < 2 ^ (prefixWord ++ tailWord_7672817).sum := by decide
  have hdescent : baseEnd_7672817 < baseStart_7672817 := by decide
  rcases family_descends (prefixWord ++ tailWord_7672817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7672864 : List Nat := [2, 1, 1, 7, 1, 1, 1, 2, 1, 3, 3]
def baseStart_7672864 : Nat := 118140960795 + 7672864 * 2 ^ 59
def prefixEnd_7672864 : Nat := 4983230072969 + 3 ^ 40 * 7672864 * 2
def baseEnd_7672864 : Nat := 3939867228579573118013147

theorem tailTrace_7672864 : CollatzResearch.WordTrace tailWord_7672864 prefixEnd_7672864 3939867228579573118013147 := by
  unfold tailWord_7672864
  simp only [CollatzResearch.WordTrace]
  refine ⟨139926170437265811844188823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186568227249687749125585097 139926170437265811844188823)
  ·
    refine ⟨209889255655898717766283235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139926170437265811844188823 209889255655898717766283235)
    ·
      refine ⟨314833883483848076649424853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209889255655898717766283235 314833883483848076649424853)
      ·
        refine ⟨7378919144152689296470895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 314833883483848076649424853 7378919144152689296470895)
        ·
          refine ⟨11068378716229033944706343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7378919144152689296470895 11068378716229033944706343)
          ·
            refine ⟨16602568074343550917059515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11068378716229033944706343 16602568074343550917059515)
            ·
              refine ⟨24903852111515326375589273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16602568074343550917059515 24903852111515326375589273)
              ·
                refine ⟨18677889083636494781691955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24903852111515326375589273 18677889083636494781691955)
                ·
                  refine ⟨28016833625454742172537933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18677889083636494781691955 28016833625454742172537933)
                  ·
                    refine ⟨10506312609545528314701725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28016833625454742172537933 10506312609545528314701725)
                    ·
                      refine ⟨3939867228579573118013147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10506312609545528314701725 3939867228579573118013147)
                      ·
                        rfl

theorem cell23_7672864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_7672864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7672864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7672864 prefixEnd_7672864 := by exact prefixLift 7672864
  have htrace : WordTrace (prefixWord ++ tailWord_7672864) baseStart_7672864 baseEnd_7672864 := by
    simpa [prefixWord, tailWord_7672864, baseEnd_7672864] using wordTrace_append hprefix tailTrace_7672864
  have hstable : (prefixWord ++ tailWord_7672864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7672864).length < 2 ^ (prefixWord ++ tailWord_7672864).sum := by decide
  have hdescent : baseEnd_7672864 < baseStart_7672864 := by decide
  rcases family_descends (prefixWord ++ tailWord_7672864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7672883 : List Nat := [1, 1, 1, 2, 4, 1, 1, 1, 2, 3, 6]
def baseStart_7672883 : Nat := 118140960795 + 7672883 * 2 ^ 59
def prefixEnd_7672883 : Nat := 4983230072969 + 3 ^ 40 * 7672883 * 2
def baseEnd_7672883 : Nat := 3939876984712008543675559

theorem tailTrace_7672883 : CollatzResearch.WordTrace tailWord_7672883 prefixEnd_7672883 3939876984712008543675559 := by
  unfold tailWord_7672883
  simp only [CollatzResearch.WordTrace]
  refine ⟨279853033861462789933319303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186568689240975193288879535 279853033861462789933319303)
  ·
    refine ⟨419779550792194184899978955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279853033861462789933319303 419779550792194184899978955)
    ·
      refine ⟨629669326188291277349968433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419779550792194184899978955 629669326188291277349968433)
      ·
        refine ⟨472251994641218458012476325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 629669326188291277349968433 472251994641218458012476325)
        ·
          refine ⟨88547248995228460877339311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 472251994641218458012476325 88547248995228460877339311)
          ·
            refine ⟨132820873492842691316008967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88547248995228460877339311 132820873492842691316008967)
            ·
              refine ⟨199231310239264036974013451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132820873492842691316008967 199231310239264036974013451)
              ·
                refine ⟨298846965358896055461020177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199231310239264036974013451 298846965358896055461020177)
                ·
                  refine ⟨224135224019172041595765133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 298846965358896055461020177 224135224019172041595765133)
                  ·
                    refine ⟨84050709007189515598411925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 224135224019172041595765133 84050709007189515598411925)
                    ·
                      refine ⟨3939876984712008543675559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84050709007189515598411925 3939876984712008543675559)
                      ·
                        rfl

theorem cell23_7672883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 3, 6].length) (baseStart_7672883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7672883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7672883 prefixEnd_7672883 := by exact prefixLift 7672883
  have htrace : WordTrace (prefixWord ++ tailWord_7672883) baseStart_7672883 baseEnd_7672883 := by
    simpa [prefixWord, tailWord_7672883, baseEnd_7672883] using wordTrace_append hprefix tailTrace_7672883
  have hstable : (prefixWord ++ tailWord_7672883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7672883).length < 2 ^ (prefixWord ++ tailWord_7672883).sum := by decide
  have hdescent : baseEnd_7672883 < baseStart_7672883 := by decide
  rcases family_descends (prefixWord ++ tailWord_7672883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7672890 : List Nat := [3, 1, 1, 1, 3, 1, 3, 1, 2, 4, 3]
def baseStart_7672890 : Nat := 118140960795 + 7672890 * 2 ^ 59
def prefixEnd_7672890 : Nat := 4983230072969 + 3 ^ 40 * 7672890 * 2
def baseEnd_7672890 : Nat := 3939880579076590016288027

theorem tailTrace_7672890 : CollatzResearch.WordTrace tailWord_7672890 prefixEnd_7672890 3939880579076590016288027 := by
  unfold tailWord_7672890
  simp only [CollatzResearch.WordTrace]
  refine ⟨69963322293109357532206031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186568859448291620085882749 69963322293109357532206031)
  ·
    refine ⟨104944983439664036298309047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69963322293109357532206031 104944983439664036298309047)
    ·
      refine ⟨157417475159496054447463571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104944983439664036298309047 157417475159496054447463571)
      ·
        refine ⟨236126212739244081671195357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157417475159496054447463571 236126212739244081671195357)
        ·
          refine ⟨88547329777216530626698259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 236126212739244081671195357 88547329777216530626698259)
          ·
            refine ⟨132820994665824795940047389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88547329777216530626698259 132820994665824795940047389)
            ·
              refine ⟨49807872999684298477517771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132820994665824795940047389 49807872999684298477517771)
              ·
                refine ⟨74711809499526447716276657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49807872999684298477517771 74711809499526447716276657)
                ·
                  refine ⟨56033857124644835787207493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74711809499526447716276657 56033857124644835787207493)
                  ·
                    refine ⟨10506348210870906710101405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56033857124644835787207493 10506348210870906710101405)
                    ·
                      refine ⟨3939880579076590016288027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10506348210870906710101405 3939880579076590016288027)
                      ·
                        rfl

theorem cell23_7672890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 2, 4, 3].length) (baseStart_7672890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7672890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7672890 prefixEnd_7672890 := by exact prefixLift 7672890
  have htrace : WordTrace (prefixWord ++ tailWord_7672890) baseStart_7672890 baseEnd_7672890 := by
    simpa [prefixWord, tailWord_7672890, baseEnd_7672890] using wordTrace_append hprefix tailTrace_7672890
  have hstable : (prefixWord ++ tailWord_7672890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7672890).length < 2 ^ (prefixWord ++ tailWord_7672890).sum := by decide
  have hdescent : baseEnd_7672890 < baseStart_7672890 := by decide
  rcases family_descends (prefixWord ++ tailWord_7672890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7672897 : List Nat := [1, 2, 5, 1, 3, 1, 1, 1, 2, 6]
def baseStart_7672897 : Nat := 118140960795 + 7672897 * 2 ^ 59
def prefixEnd_7672897 : Nat := 4983230072969 + 3 ^ 40 * 7672897 * 2
def baseEnd_7672897 : Nat := 1313294724480390496300165

theorem tailTrace_7672897 : CollatzResearch.WordTrace tailWord_7672897 prefixEnd_7672897 1313294724480390496300165 := by
  unfold tailWord_7672897
  simp only [CollatzResearch.WordTrace]
  refine ⟨279853544483412070324328945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186569029655608046882885963 279853544483412070324328945)
  ·
    refine ⟨209890158362559052743246709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279853544483412070324328945 209890158362559052743246709)
    ·
      refine ⟨19677202346489911194679379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 209890158362559052743246709 19677202346489911194679379)
      ·
        refine ⟨29515803519734866792019069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19677202346489911194679379 29515803519734866792019069)
        ·
          refine ⟨11068426319900575047007151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29515803519734866792019069 11068426319900575047007151)
          ·
            refine ⟨16602639479850862570510727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11068426319900575047007151 16602639479850862570510727)
            ·
              refine ⟨24903959219776293855766091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16602639479850862570510727 24903959219776293855766091)
              ·
                refine ⟨37355938829664440783649137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24903959219776293855766091 37355938829664440783649137)
                ·
                  refine ⟨28016954122248330587736853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37355938829664440783649137 28016954122248330587736853)
                  ·
                    refine ⟨1313294724480390496300165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28016954122248330587736853 1313294724480390496300165)
                    ·
                      rfl

theorem cell23_7672897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_7672897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7672897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7672897 prefixEnd_7672897 := by exact prefixLift 7672897
  have htrace : WordTrace (prefixWord ++ tailWord_7672897) baseStart_7672897 baseEnd_7672897 := by
    simpa [prefixWord, tailWord_7672897, baseEnd_7672897] using wordTrace_append hprefix tailTrace_7672897
  have hstable : (prefixWord ++ tailWord_7672897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7672897).length < 2 ^ (prefixWord ++ tailWord_7672897).sum := by decide
  have hdescent : baseEnd_7672897 < baseStart_7672897 := by decide
  rcases family_descends (prefixWord ++ tailWord_7672897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7672904 : List Nat := [2, 1, 3, 1, 1, 1, 3, 5, 2, 2, 2]
def baseStart_7672904 : Nat := 118140960795 + 7672904 * 2 ^ 59
def prefixEnd_7672904 : Nat := 4983230072969 + 3 ^ 40 * 7672904 * 2
def baseEnd_7672904 : Nat := 3939887767805752961512963

theorem tailTrace_7672904 : CollatzResearch.WordTrace tailWord_7672904 prefixEnd_7672904 3939887767805752961512963 := by
  unfold tailWord_7672904
  simp only [CollatzResearch.WordTrace]
  refine ⟨139926899897193355259916883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186569199862924473679889177 139926899897193355259916883)
  ·
    refine ⟨209890349845790032889875325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139926899897193355259916883 209890349845790032889875325)
    ·
      refine ⟨78708881192171262333703247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209890349845790032889875325 78708881192171262333703247)
      ·
        refine ⟨118063321788256893500554871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78708881192171262333703247 118063321788256893500554871)
        ·
          refine ⟨177094982682385340250832307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118063321788256893500554871 177094982682385340250832307)
          ·
            refine ⟨265642474023578010376248461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177094982682385340250832307 265642474023578010376248461)
            ·
              refine ⟨99615927758841753891093173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 265642474023578010376248461 99615927758841753891093173)
              ·
                refine ⟨9338993227391414427289985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 99615927758841753891093173 9338993227391414427289985)
                ·
                  refine ⟨7004244920543560820467489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9338993227391414427289985 7004244920543560820467489)
                  ·
                    refine ⟨5253183690407670615350617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7004244920543560820467489 5253183690407670615350617)
                    ·
                      refine ⟨3939887767805752961512963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5253183690407670615350617 3939887767805752961512963)
                      ·
                        rfl

theorem cell23_7672904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 5, 2, 2, 2].length) (baseStart_7672904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7672904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7672904 prefixEnd_7672904 := by exact prefixLift 7672904
  have htrace : WordTrace (prefixWord ++ tailWord_7672904) baseStart_7672904 baseEnd_7672904 := by
    simpa [prefixWord, tailWord_7672904, baseEnd_7672904] using wordTrace_append hprefix tailTrace_7672904
  have hstable : (prefixWord ++ tailWord_7672904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7672904).length < 2 ^ (prefixWord ++ tailWord_7672904).sum := by decide
  have hdescent : baseEnd_7672904 < baseStart_7672904 := by decide
  rcases family_descends (prefixWord ++ tailWord_7672904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7672910 : List Nat := [4, 1, 1, 1, 1, 3, 3, 2, 7]
def baseStart_7672910 : Nat := 118140960795 + 7672910 * 2 ^ 59
def prefixEnd_7672910 : Nat := 4983230072969 + 3 ^ 40 * 7672910 * 2
def baseEnd_7672910 : Nat := 437765649854408882004215

theorem tailTrace_7672910 : CollatzResearch.WordTrace tailWord_7672910 prefixEnd_7672910 437765649854408882004215 := by
  unfold tailWord_7672910
  simp only [CollatzResearch.WordTrace]
  refine ⟨34981752329045621693069023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186569345754909982363034789 34981752329045621693069023)
  ·
    refine ⟨52472628493568432539603535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34981752329045621693069023 52472628493568432539603535)
    ·
      refine ⟨78708942740352648809405303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52472628493568432539603535 78708942740352648809405303)
      ·
        refine ⟨118063414110528973214107955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78708942740352648809405303 118063414110528973214107955)
        ·
          refine ⟨177095121165793459821161933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118063414110528973214107955 177095121165793459821161933)
          ·
            refine ⟨66410670437172547432935725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177095121165793459821161933 66410670437172547432935725)
            ·
              refine ⟨24904001413939705287350897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66410670437172547432935725 24904001413939705287350897)
              ·
                refine ⟨18678001060454778965513173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24904001413939705287350897 18678001060454778965513173)
                ·
                  refine ⟨437765649854408882004215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18678001060454778965513173 437765649854408882004215)
                  ·
                    rfl

theorem cell23_7672910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 2, 7].length) (baseStart_7672910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7672910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7672910 prefixEnd_7672910 := by exact prefixLift 7672910
  have htrace : WordTrace (prefixWord ++ tailWord_7672910) baseStart_7672910 baseEnd_7672910 := by
    simpa [prefixWord, tailWord_7672910, baseEnd_7672910] using wordTrace_append hprefix tailTrace_7672910
  have hstable : (prefixWord ++ tailWord_7672910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7672910).length < 2 ^ (prefixWord ++ tailWord_7672910).sum := by decide
  have hdescent : baseEnd_7672910 < baseStart_7672910 := by decide
  rcases family_descends (prefixWord ++ tailWord_7672910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7672920 : List Nat := [2, 1, 2, 2, 1, 3, 1, 2, 1, 5, 3]
def baseStart_7672920 : Nat := 118140960795 + 7672920 * 2 ^ 59
def prefixEnd_7672920 : Nat := 4983230072969 + 3 ^ 40 * 7672920 * 2
def baseEnd_7672920 : Nat := 3939895983496224898912889

theorem tailTrace_7672920 : CollatzResearch.WordTrace tailWord_7672920 prefixEnd_7672920 3939895983496224898912889 := by
  unfold tailWord_7672920
  simp only [CollatzResearch.WordTrace]
  refine ⟨139927191681164372626208107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186569588908219163501610809 139927191681164372626208107)
  ·
    refine ⟨209890787521746558939312161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139927191681164372626208107 209890787521746558939312161)
    ·
      refine ⟨157418090641309919204484121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209890787521746558939312161 157418090641309919204484121)
      ·
        refine ⟨118063567980982439403363091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157418090641309919204484121 118063567980982439403363091)
        ·
          refine ⟨177095351971473659105044637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118063567980982439403363091 177095351971473659105044637)
          ·
            refine ⟨66410756989302622164391739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177095351971473659105044637 66410756989302622164391739)
            ·
              refine ⟨99616135483953933246587609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66410756989302622164391739 99616135483953933246587609)
              ·
                refine ⟨74712101612965449934940707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99616135483953933246587609 74712101612965449934940707)
                ·
                  refine ⟨112068152419448174902411061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74712101612965449934940707 112068152419448174902411061)
                  ·
                    refine ⟨10506389289323266397101037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 112068152419448174902411061 10506389289323266397101037)
                    ·
                      refine ⟨3939895983496224898912889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10506389289323266397101037 3939895983496224898912889)
                      ·
                        rfl

theorem cell23_7672920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 1, 5, 3].length) (baseStart_7672920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7672920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7672920 prefixEnd_7672920 := by exact prefixLift 7672920
  have htrace : WordTrace (prefixWord ++ tailWord_7672920) baseStart_7672920 baseEnd_7672920 := by
    simpa [prefixWord, tailWord_7672920, baseEnd_7672920] using wordTrace_append hprefix tailTrace_7672920
  have hstable : (prefixWord ++ tailWord_7672920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7672920).length < 2 ^ (prefixWord ++ tailWord_7672920).sum := by decide
  have hdescent : baseEnd_7672920 < baseStart_7672920 := by decide
  rcases family_descends (prefixWord ++ tailWord_7672920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7672925 : List Nat := [1, 4, 4, 1, 2, 2, 2, 1, 1, 3, 2]
def baseStart_7672925 : Nat := 118140960795 + 7672925 * 2 ^ 59
def prefixEnd_7672925 : Nat := 4983230072969 + 3 ^ 40 * 7672925 * 2
def baseEnd_7672925 : Nat := 3939898550899497379350367

theorem tailTrace_7672925 : CollatzResearch.WordTrace tailWord_7672925 prefixEnd_7672925 3939898550899497379350367 := by
  unfold tailWord_7672925
  simp only [CollatzResearch.WordTrace]
  refine ⟨279854565727310631106348229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186569710484873754070898819 279854565727310631106348229)
  ·
    refine ⟨52472731073870743332440293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 279854565727310631106348229 52472731073870743332440293)
    ·
      refine ⟨9838637076350764374832555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52472731073870743332440293 9838637076350764374832555)
      ·
        refine ⟨14757955614526146562248833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9838637076350764374832555 14757955614526146562248833)
        ·
          refine ⟨11068466710894609921686625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14757955614526146562248833 11068466710894609921686625)
          ·
            refine ⟨8301350033170957441264969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11068466710894609921686625 8301350033170957441264969)
            ·
              refine ⟨6226012524878218080948727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8301350033170957441264969 6226012524878218080948727)
              ·
                refine ⟨9339018787317327121423091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6226012524878218080948727 9339018787317327121423091)
                ·
                  refine ⟨14008528180975990682134637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9339018787317327121423091 14008528180975990682134637)
                  ·
                    refine ⟨5253198067865996505800489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14008528180975990682134637 5253198067865996505800489)
                    ·
                      refine ⟨3939898550899497379350367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5253198067865996505800489 3939898550899497379350367)
                      ·
                        rfl

theorem cell23_7672925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_7672925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7672925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7672925 prefixEnd_7672925 := by exact prefixLift 7672925
  have htrace : WordTrace (prefixWord ++ tailWord_7672925) baseStart_7672925 baseEnd_7672925 := by
    simpa [prefixWord, tailWord_7672925, baseEnd_7672925] using wordTrace_append hprefix tailTrace_7672925
  have hstable : (prefixWord ++ tailWord_7672925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7672925).length < 2 ^ (prefixWord ++ tailWord_7672925).sum := by decide
  have hdescent : baseEnd_7672925 < baseStart_7672925 := by decide
  rcases family_descends (prefixWord ++ tailWord_7672925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7672927 : List Nat := [1, 1, 2, 3, 1, 1, 6, 3, 5]
def baseStart_7672927 : Nat := 118140960795 + 7672927 * 2 ^ 59
def prefixEnd_7672927 : Nat := 4983230072969 + 3 ^ 40 * 7672927 * 2
def baseEnd_7672927 : Nat := 437766619762311819058373

theorem tailTrace_7672927 : CollatzResearch.WordTrace tailWord_7672927 prefixEnd_7672927 437766619762311819058373 := by
  unfold tailWord_7672927
  simp only [CollatzResearch.WordTrace]
  refine ⟨279854638673303385447921035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186569759115535590298614023 279854638673303385447921035)
  ·
    refine ⟨419781958009955078171881553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279854638673303385447921035 419781958009955078171881553)
    ·
      refine ⟨314836468507466308628911165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 419781958009955078171881553 314836468507466308628911165)
      ·
        refine ⟨118063675690299865735841687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 314836468507466308628911165 118063675690299865735841687)
        ·
          refine ⟨177095513535449798603762531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118063675690299865735841687 177095513535449798603762531)
          ·
            refine ⟨265643270303174697905643797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177095513535449798603762531 265643270303174697905643797)
            ·
              refine ⟨12452028295461313964327053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 265643270303174697905643797 12452028295461313964327053)
              ·
                refine ⟨4669510610797992736622645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12452028295461313964327053 4669510610797992736622645)
                ·
                  refine ⟨437766619762311819058373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4669510610797992736622645 437766619762311819058373)
                  ·
                    rfl

theorem cell23_7672927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 3, 5].length) (baseStart_7672927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7672927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7672927 prefixEnd_7672927 := by exact prefixLift 7672927
  have htrace : WordTrace (prefixWord ++ tailWord_7672927) baseStart_7672927 baseEnd_7672927 := by
    simpa [prefixWord, tailWord_7672927, baseEnd_7672927] using wordTrace_append hprefix tailTrace_7672927
  have hstable : (prefixWord ++ tailWord_7672927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7672927).length < 2 ^ (prefixWord ++ tailWord_7672927).sum := by decide
  have hdescent : baseEnd_7672927 < baseStart_7672927 := by decide
  rcases family_descends (prefixWord ++ tailWord_7672927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7672938 : List Nat := [3, 1, 3, 2, 2, 3, 1, 2, 2, 2, 2]
def baseStart_7672938 : Nat := 118140960795 + 7672938 * 2 ^ 59
def prefixEnd_7672938 : Nat := 4983230072969 + 3 ^ 40 * 7672938 * 2
def baseEnd_7672938 : Nat := 3939905226148005828487807

theorem tailTrace_7672938 : CollatzResearch.WordTrace tailWord_7672938 prefixEnd_7672938 3939905226148005828487807 := by
  unfold tailWord_7672938
  simp only [CollatzResearch.WordTrace]
  refine ⟨69963759969065883581642867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186570026584175689551047645 69963759969065883581642867)
  ·
    refine ⟨104945639953598825372464301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69963759969065883581642867 104945639953598825372464301)
    ·
      refine ⟨39354614982599559514674113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104945639953598825372464301 39354614982599559514674113)
      ·
        refine ⟨29515961236949669636005585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39354614982599559514674113 29515961236949669636005585)
        ·
          refine ⟨22136970927712252227004189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29515961236949669636005585 22136970927712252227004189)
          ·
            refine ⟨8301364097892094585126571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22136970927712252227004189 8301364097892094585126571)
            ·
              refine ⟨12452046146838141877689857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8301364097892094585126571 12452046146838141877689857)
              ·
                refine ⟨9339034610128606408267393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12452046146838141877689857 9339034610128606408267393)
                ·
                  refine ⟨7004275957596454806200545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9339034610128606408267393 7004275957596454806200545)
                  ·
                    refine ⟨5253206968197341104650409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7004275957596454806200545 5253206968197341104650409)
                    ·
                      refine ⟨3939905226148005828487807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5253206968197341104650409 3939905226148005828487807)
                      ·
                        rfl

theorem cell23_7672938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 2, 2, 2, 2].length) (baseStart_7672938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7672938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7672938 prefixEnd_7672938 := by exact prefixLift 7672938
  have htrace : WordTrace (prefixWord ++ tailWord_7672938) baseStart_7672938 baseEnd_7672938 := by
    simpa [prefixWord, tailWord_7672938, baseEnd_7672938] using wordTrace_append hprefix tailTrace_7672938
  have hstable : (prefixWord ++ tailWord_7672938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7672938).length < 2 ^ (prefixWord ++ tailWord_7672938).sum := by decide
  have hdescent : baseEnd_7672938 < baseStart_7672938 := by decide
  rcases family_descends (prefixWord ++ tailWord_7672938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7672940 : List Nat := [2, 2, 1, 1, 3, 2, 2, 1, 4, 5]
def baseStart_7672940 : Nat := 118140960795 + 7672940 * 2 ^ 59
def prefixEnd_7672940 : Nat := 4983230072969 + 3 ^ 40 * 7672940 * 2
def baseEnd_7672940 : Nat := 1313302084369771606887599

theorem tailTrace_7672940 : CollatzResearch.WordTrace tailWord_7672940 prefixEnd_7672940 1313302084369771606887599 := by
  unfold tailWord_7672940
  simp only [CollatzResearch.WordTrace]
  refine ⟨139927556411128144334072137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186570075214837525778762849 139927556411128144334072137)
  ·
    refine ⟨104945667308346108250554103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139927556411128144334072137 104945667308346108250554103)
    ·
      refine ⟨157418500962519162375831155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104945667308346108250554103 157418500962519162375831155)
      ·
        refine ⟨236127751443778743563746733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157418500962519162375831155 236127751443778743563746733)
        ·
          refine ⟨88547906791417028836405025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 236127751443778743563746733 88547906791417028836405025)
          ·
            refine ⟨66410930093562771627303769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88547906791417028836405025 66410930093562771627303769)
            ·
              refine ⟨49808197570172078720477827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66410930093562771627303769 49808197570172078720477827)
              ·
                refine ⟨74712296355258118080716741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49808197570172078720477827 74712296355258118080716741)
                ·
                  refine ⟨14008555566610897140134389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74712296355258118080716741 14008555566610897140134389)
                  ·
                    refine ⟨1313302084369771606887599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14008555566610897140134389 1313302084369771606887599)
                    ·
                      rfl

theorem cell23_7672940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 5].length) (baseStart_7672940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7672940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7672940 prefixEnd_7672940 := by exact prefixLift 7672940
  have htrace : WordTrace (prefixWord ++ tailWord_7672940) baseStart_7672940 baseEnd_7672940 := by
    simpa [prefixWord, tailWord_7672940, baseEnd_7672940] using wordTrace_append hprefix tailTrace_7672940
  have hstable : (prefixWord ++ tailWord_7672940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7672940).length < 2 ^ (prefixWord ++ tailWord_7672940).sum := by decide
  have hdescent : baseEnd_7672940 < baseStart_7672940 := by decide
  rcases family_descends (prefixWord ++ tailWord_7672940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7672960 : List Nat := [2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 4]
def baseStart_7672960 : Nat := 118140960795 + 7672960 * 2 ^ 59
def prefixEnd_7672960 : Nat := 4983230072969 + 3 ^ 40 * 7672960 * 2
def baseEnd_7672960 : Nat := 3939916522722404742412705

theorem tailTrace_7672960 : CollatzResearch.WordTrace tailWord_7672960 prefixEnd_7672960 3939916522722404742412705 := by
  unfold tailWord_7672960
  simp only [CollatzResearch.WordTrace]
  refine ⟨139927921141091916041936167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186570561521455888055914889 139927921141091916041936167)
  ·
    refine ⟨209891881711637874062904251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139927921141091916041936167 209891881711637874062904251)
    ·
      refine ⟨314837822567456811094356377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209891881711637874062904251 314837822567456811094356377)
      ·
        refine ⟨236128366925592608320767283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 314837822567456811094356377 236128366925592608320767283)
        ·
          refine ⟨354192550388388912481150925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236128366925592608320767283 354192550388388912481150925)
          ·
            refine ⟨132822206395645842180431597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 354192550388388912481150925 132822206395645842180431597)
            ·
              refine ⟨49808327398367190817661849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132822206395645842180431597 49808327398367190817661849)
              ·
                refine ⟨37356245548775393113246387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49808327398367190817661849 37356245548775393113246387)
                ·
                  refine ⟨56034368323163089669869581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37356245548775393113246387 56034368323163089669869581)
                  ·
                    refine ⟨21012888121186158626201093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56034368323163089669869581 21012888121186158626201093)
                    ·
                      refine ⟨3939916522722404742412705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21012888121186158626201093 3939916522722404742412705)
                      ·
                        rfl

theorem cell23_7672960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 4].length) (baseStart_7672960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7672960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7672960 prefixEnd_7672960 := by exact prefixLift 7672960
  have htrace : WordTrace (prefixWord ++ tailWord_7672960) baseStart_7672960 baseEnd_7672960 := by
    simpa [prefixWord, tailWord_7672960, baseEnd_7672960] using wordTrace_append hprefix tailTrace_7672960
  have hstable : (prefixWord ++ tailWord_7672960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7672960).length < 2 ^ (prefixWord ++ tailWord_7672960).sum := by decide
  have hdescent : baseEnd_7672960 < baseStart_7672960 := by decide
  rcases family_descends (prefixWord ++ tailWord_7672960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7672970 : List Nat := [3, 1, 2, 3, 1, 1, 1, 1, 2, 8]
def baseStart_7672970 : Nat := 118140960795 + 7672970 * 2 ^ 59
def prefixEnd_7672970 : Nat := 4983230072969 + 3 ^ 40 * 7672970 * 2
def baseEnd_7672970 : Nat := 1313307219176316567762553

theorem tailTrace_7672970 : CollatzResearch.WordTrace tailWord_7672970 prefixEnd_7672970 1313307219176316567762553 := by
  unfold tailWord_7672970
  simp only [CollatzResearch.WordTrace]
  refine ⟨69964051753036900947934091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186570804674765069194490909 69964051753036900947934091)
  ·
    refine ⟨104946077629555351421901137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69964051753036900947934091 104946077629555351421901137)
    ·
      refine ⟨78709558222166513566425853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104946077629555351421901137 78709558222166513566425853)
      ·
        refine ⟨29516084333312442587409695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78709558222166513566425853 29516084333312442587409695)
        ·
          refine ⟨44274126499968663881114543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29516084333312442587409695 44274126499968663881114543)
          ·
            refine ⟨66411189749952995821671815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44274126499968663881114543 66411189749952995821671815)
            ·
              refine ⟨99616784624929493732507723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66411189749952995821671815 99616784624929493732507723)
              ·
                refine ⟨149425176937394240598761585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99616784624929493732507723 149425176937394240598761585)
                ·
                  refine ⟨112068882703045680449071189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 149425176937394240598761585 112068882703045680449071189)
                  ·
                    refine ⟨1313307219176316567762553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 112068882703045680449071189 1313307219176316567762553)
                    ·
                      rfl

theorem cell23_7672970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 2, 8].length) (baseStart_7672970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7672970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7672970 prefixEnd_7672970 := by exact prefixLift 7672970
  have htrace : WordTrace (prefixWord ++ tailWord_7672970) baseStart_7672970 baseEnd_7672970 := by
    simpa [prefixWord, tailWord_7672970, baseEnd_7672970] using wordTrace_append hprefix tailTrace_7672970
  have hstable : (prefixWord ++ tailWord_7672970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7672970).length < 2 ^ (prefixWord ++ tailWord_7672970).sum := by decide
  have hdescent : baseEnd_7672970 < baseStart_7672970 := by decide
  rcases family_descends (prefixWord ++ tailWord_7672970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7672997 : List Nat := [1, 3, 1, 2, 1, 4, 1, 1, 4, 2, 3]
def baseStart_7672997 : Nat := 118140960795 + 7672997 * 2 ^ 59
def prefixEnd_7672997 : Nat := 4983230072969 + 3 ^ 40 * 7672997 * 2
def baseEnd_7672997 : Nat := 3939935521506621097650035

theorem tailTrace_7672997 : CollatzResearch.WordTrace tailWord_7672997 prefixEnd_7672997 3939935521506621097650035 := by
  unfold tailWord_7672997
  simp only [CollatzResearch.WordTrace]
  refine ⟨279857191783049787402969245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186571461188699858268646163 279857191783049787402969245)
  ·
    refine ⟨104946446918643670276113467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 279857191783049787402969245 104946446918643670276113467)
    ·
      refine ⟨157419670377965505414170201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104946446918643670276113467 157419670377965505414170201)
      ·
        refine ⟨118064752783474129060627651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157419670377965505414170201 118064752783474129060627651)
        ·
          refine ⟨177097129175211193590941477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118064752783474129060627651 177097129175211193590941477)
          ·
            refine ⟨33205711720352098798301527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 177097129175211193590941477 33205711720352098798301527)
            ·
              refine ⟨49808567580528148197452291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33205711720352098798301527 49808567580528148197452291)
              ·
                refine ⟨74712851370792222296178437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49808567580528148197452291 74712851370792222296178437)
                ·
                  refine ⟨14008659632023541680533457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74712851370792222296178437 14008659632023541680533457)
                  ·
                    refine ⟨10506494724017656260400093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14008659632023541680533457 10506494724017656260400093)
                    ·
                      refine ⟨3939935521506621097650035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10506494724017656260400093 3939935521506621097650035)
                      ·
                        rfl

theorem cell23_7672997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 4, 2, 3].length) (baseStart_7672997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7672997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7672997 prefixEnd_7672997 := by exact prefixLift 7672997
  have htrace : WordTrace (prefixWord ++ tailWord_7672997) baseStart_7672997 baseEnd_7672997 := by
    simpa [prefixWord, tailWord_7672997, baseEnd_7672997] using wordTrace_append hprefix tailTrace_7672997
  have hstable : (prefixWord ++ tailWord_7672997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7672997).length < 2 ^ (prefixWord ++ tailWord_7672997).sum := by decide
  have hdescent : baseEnd_7672997 < baseStart_7672997 := by decide
  rcases family_descends (prefixWord ++ tailWord_7672997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7673017 : List Nat := [1, 2, 1, 4, 1, 4, 1, 3, 6]
def baseStart_7673017 : Nat := 118140960795 + 7673017 * 2 ^ 59
def prefixEnd_7673017 : Nat := 4983230072969 + 3 ^ 40 * 7673017 * 2
def baseEnd_7673017 : Nat := 437771754568856779933327

theorem tailTrace_7673017 : CollatzResearch.WordTrace tailWord_7673017 prefixEnd_7673017 437771754568856779933327 := by
  unfold tailWord_7673017
  simp only [CollatzResearch.WordTrace]
  refine ⟨279857921242977330818697305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186571947495318220545798203 279857921242977330818697305)
  ·
    refine ⟨209893440932232998114022979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279857921242977330818697305 209893440932232998114022979)
    ·
      refine ⟨314840161398349497171034469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209893440932232998114022979 314840161398349497171034469)
      ·
        refine ⟨59032530262190530719568963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 314840161398349497171034469 59032530262190530719568963)
        ·
          refine ⟨88548795393285796079353445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59032530262190530719568963 88548795393285796079353445)
          ·
            refine ⟨16602899136241086764878771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88548795393285796079353445 16602899136241086764878771)
            ·
              refine ⟨24904348704361630147318157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16602899136241086764878771 24904348704361630147318157)
              ·
                refine ⟨9339130764135611305244309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24904348704361630147318157 9339130764135611305244309)
                ·
                  refine ⟨437771754568856779933327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9339130764135611305244309 437771754568856779933327)
                  ·
                    rfl

theorem cell23_7673017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 3, 6].length) (baseStart_7673017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7673017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7673017 prefixEnd_7673017 := by exact prefixLift 7673017
  have htrace : WordTrace (prefixWord ++ tailWord_7673017) baseStart_7673017 baseEnd_7673017 := by
    simpa [prefixWord, tailWord_7673017, baseEnd_7673017] using wordTrace_append hprefix tailTrace_7673017
  have hstable : (prefixWord ++ tailWord_7673017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7673017).length < 2 ^ (prefixWord ++ tailWord_7673017).sum := by decide
  have hdescent : baseEnd_7673017 < baseStart_7673017 := by decide
  rcases family_descends (prefixWord ++ tailWord_7673017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7673047 : List Nat := [1, 1, 3, 2, 1, 2, 2, 5, 1, 5]
def baseStart_7673047 : Nat := 118140960795 + 7673047 * 2 ^ 59
def prefixEnd_7673047 : Nat := 4983230072969 + 3 ^ 40 * 7673047 * 2
def baseEnd_7673047 : Nat := 1313320398513115300674935

theorem tailTrace_7673047 : CollatzResearch.WordTrace tailWord_7673047 prefixEnd_7673047 1313320398513115300674935 := by
  unfold tailWord_7673047
  simp only [CollatzResearch.WordTrace]
  refine ⟨279859015432868645942289395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186572676955245763961526263 279859015432868645942289395)
  ·
    refine ⟨419788523149302968913434093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279859015432868645942289395 419788523149302968913434093)
    ·
      refine ⟨157420696180988613342537785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 419788523149302968913434093 157420696180988613342537785)
      ·
        refine ⟨118065522135741460006903339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157420696180988613342537785 118065522135741460006903339)
        ·
          refine ⟨177098283203612190010355009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118065522135741460006903339 177098283203612190010355009)
          ·
            refine ⟨132823712402709142507766257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177098283203612190010355009 132823712402709142507766257)
            ·
              refine ⟨99617784302031856880824693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132823712402709142507766257 99617784302031856880824693)
              ·
                refine ⟨9339167278315486582577315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 99617784302031856880824693 9339167278315486582577315)
                ·
                  refine ⟨14008750917473229873865973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9339167278315486582577315 14008750917473229873865973)
                  ·
                    refine ⟨1313320398513115300674935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14008750917473229873865973 1313320398513115300674935)
                    ·
                      rfl

theorem cell23_7673047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 5, 1, 5].length) (baseStart_7673047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7673047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7673047 prefixEnd_7673047 := by exact prefixLift 7673047
  have htrace : WordTrace (prefixWord ++ tailWord_7673047) baseStart_7673047 baseEnd_7673047 := by
    simpa [prefixWord, tailWord_7673047, baseEnd_7673047] using wordTrace_append hprefix tailTrace_7673047
  have hstable : (prefixWord ++ tailWord_7673047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7673047).length < 2 ^ (prefixWord ++ tailWord_7673047).sum := by decide
  have hdescent : baseEnd_7673047 < baseStart_7673047 := by decide
  rcases family_descends (prefixWord ++ tailWord_7673047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7673067 : List Nat := [1, 1, 1, 1, 2, 6, 1, 2, 3, 1, 4]
def baseStart_7673067 : Nat := 118140960795 + 7673067 * 2 ^ 59
def prefixEnd_7673067 : Nat := 4983230072969 + 3 ^ 40 * 7673067 * 2
def baseEnd_7673067 : Nat := 3939971465152435823774713

theorem tailTrace_7673067 : CollatzResearch.WordTrace tailWord_7673067 prefixEnd_7673067 3939971465152435823774713 := by
  unfold tailWord_7673067
  simp only [CollatzResearch.WordTrace]
  refine ⟨279859744892796189358017455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186573163261864126238678303 279859744892796189358017455)
  ·
    refine ⟨419789617339194284037026183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279859744892796189358017455 419789617339194284037026183)
    ·
      refine ⟨629684426008791426055539275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419789617339194284037026183 629684426008791426055539275)
      ·
        refine ⟨944526639013187139083308913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 629684426008791426055539275 944526639013187139083308913)
        ·
          refine ⟨708394979259890354312481685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 944526639013187139083308913 708394979259890354312481685)
          ·
            refine ⟨33206014652807360358397579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 708394979259890354312481685 33206014652807360358397579)
            ·
              refine ⟨49809021979211040537596369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33206014652807360358397579 49809021979211040537596369)
              ·
                refine ⟨37356766484408280403197277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49809021979211040537596369 37356766484408280403197277)
                ·
                  refine ⟨14008787431653105151198979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37356766484408280403197277 14008787431653105151198979)
                  ·
                    refine ⟨21013181147479657726798469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14008787431653105151198979 21013181147479657726798469)
                    ·
                      refine ⟨3939971465152435823774713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21013181147479657726798469 3939971465152435823774713)
                      ·
                        rfl

theorem cell23_7673067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 2, 3, 1, 4].length) (baseStart_7673067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7673067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7673067 prefixEnd_7673067 := by exact prefixLift 7673067
  have htrace : WordTrace (prefixWord ++ tailWord_7673067) baseStart_7673067 baseEnd_7673067 := by
    simpa [prefixWord, tailWord_7673067, baseEnd_7673067] using wordTrace_append hprefix tailTrace_7673067
  have hstable : (prefixWord ++ tailWord_7673067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7673067).length < 2 ^ (prefixWord ++ tailWord_7673067).sum := by decide
  have hdescent : baseEnd_7673067 < baseStart_7673067 := by decide
  rcases family_descends (prefixWord ++ tailWord_7673067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7673097 : List Nat := [1, 2, 1, 1, 3, 3, 1, 4, 1, 2, 4]
def baseStart_7673097 : Nat := 118140960795 + 7673097 * 2 ^ 59
def prefixEnd_7673097 : Nat := 4983230072969 + 3 ^ 40 * 7673097 * 2
def baseEnd_7673097 : Nat := 3939986869572070706399575

theorem tailTrace_7673097 : CollatzResearch.WordTrace tailWord_7673097 prefixEnd_7673097 3939986869572070706399575 := by
  unfold tailWord_7673097
  simp only [CollatzResearch.WordTrace]
  refine ⟨279860839082687504481609545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186573892721791669654406363 279860839082687504481609545)
  ·
    refine ⟨209895629312015628361207159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279860839082687504481609545 209895629312015628361207159)
    ·
      refine ⟨314843443968023442541810739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209895629312015628361207159 314843443968023442541810739)
      ·
        refine ⟨472265165952035163812716109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314843443968023442541810739 472265165952035163812716109)
        ·
          refine ⟨177099437232013186429768541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 472265165952035163812716109 177099437232013186429768541)
          ·
            refine ⟨66412288962004944911163203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177099437232013186429768541 66412288962004944911163203)
            ·
              refine ⟨99618433443007417366744805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66412288962004944911163203 99618433443007417366744805)
              ·
                refine ⟨18678456270563890756264651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99618433443007417366744805 18678456270563890756264651)
                ·
                  refine ⟨28017684405845836134396977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18678456270563890756264651 28017684405845836134396977)
                  ·
                    refine ⟨21013263304384377100797733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28017684405845836134396977 21013263304384377100797733)
                    ·
                      refine ⟨3939986869572070706399575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21013263304384377100797733 3939986869572070706399575)
                      ·
                        rfl

theorem cell23_7673097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 4, 1, 2, 4].length) (baseStart_7673097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7673097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7673097 prefixEnd_7673097 := by exact prefixLift 7673097
  have htrace : WordTrace (prefixWord ++ tailWord_7673097) baseStart_7673097 baseEnd_7673097 := by
    simpa [prefixWord, tailWord_7673097, baseEnd_7673097] using wordTrace_append hprefix tailTrace_7673097
  have hstable : (prefixWord ++ tailWord_7673097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7673097).length < 2 ^ (prefixWord ++ tailWord_7673097).sum := by decide
  have hdescent : baseEnd_7673097 < baseStart_7673097 := by decide
  rcases family_descends (prefixWord ++ tailWord_7673097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7673128 : List Nat := [2, 1, 5, 1, 2, 2, 3, 1, 2, 4]
def baseStart_7673128 : Nat := 118140960795 + 7673128 * 2 ^ 59
def prefixEnd_7673128 : Nat := 4983230072969 + 3 ^ 40 * 7673128 * 2
def baseEnd_7673128 : Nat := 1313334262490786695037311

theorem tailTrace_7673128 : CollatzResearch.WordTrace tailWord_7673128 prefixEnd_7673128 1313334262490786695037311 := by
  unfold tailWord_7673128
  simp only [CollatzResearch.WordTrace]
  refine ⟨139930984872787598387994019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186574646497050131183992025 139930984872787598387994019)
  ·
    refine ⟨209896477309181397581991029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139930984872787598387994019 209896477309181397581991029)
    ·
      refine ⟨19677794747735756023311659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 209896477309181397581991029 19677794747735756023311659)
      ·
        refine ⟨29516692121603634034967489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19677794747735756023311659 29516692121603634034967489)
        ·
          refine ⟨22137519091202725526225617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29516692121603634034967489 22137519091202725526225617)
          ·
            refine ⟨16603139318402044144669213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22137519091202725526225617 16603139318402044144669213)
            ·
              refine ⟨6226177244400766554250955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16603139318402044144669213 6226177244400766554250955)
              ·
                refine ⟨9339265866601149831376433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6226177244400766554250955 9339265866601149831376433)
                ·
                  refine ⟨7004449399950862373532325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9339265866601149831376433 7004449399950862373532325)
                  ·
                    refine ⟨1313334262490786695037311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7004449399950862373532325 1313334262490786695037311)
                    ·
                      rfl

theorem cell23_7673128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_7673128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7673128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7673128 prefixEnd_7673128 := by exact prefixLift 7673128
  have htrace : WordTrace (prefixWord ++ tailWord_7673128) baseStart_7673128 baseEnd_7673128 := by
    simpa [prefixWord, tailWord_7673128, baseEnd_7673128] using wordTrace_append hprefix tailTrace_7673128
  have hstable : (prefixWord ++ tailWord_7673128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7673128).length < 2 ^ (prefixWord ++ tailWord_7673128).sum := by decide
  have hdescent : baseEnd_7673128 < baseStart_7673128 := by decide
  rcases family_descends (prefixWord ++ tailWord_7673128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7673158 : List Nat := [6, 1, 1, 3, 1, 2, 9]
def baseStart_7673158 : Nat := 118140960795 + 7673158 * 2 ^ 59
def prefixEnd_7673158 : Nat := 4983230072969 + 3 ^ 40 * 7673158 * 2
def baseEnd_7673158 : Nat := 48642199899901172441195

theorem tailTrace_7673158 : CollatzResearch.WordTrace tailWord_7673158 prefixEnd_7673158 48642199899901172441195 := by
  unfold tailWord_7673158
  simp only [CollatzResearch.WordTrace]
  refine ⟨8745720747983328496861879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 186575375956977674599720085 8745720747983328496861879)
  ·
    refine ⟨13118581121974992745292819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8745720747983328496861879 13118581121974992745292819)
    ·
      refine ⟨19677871682962489117939229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13118581121974992745292819 19677871682962489117939229)
      ·
        refine ⟨7379201881110933419227211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19677871682962489117939229 7379201881110933419227211)
        ·
          refine ⟨11068802821666400128840817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7379201881110933419227211 11068802821666400128840817)
          ·
            refine ⟨8301602116249800096630613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11068802821666400128840817 8301602116249800096630613)
            ·
              refine ⟨48642199899901172441195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8301602116249800096630613 48642199899901172441195)
              ·
                rfl

theorem cell23_7673158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 9].length) (baseStart_7673158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7673158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7673158 prefixEnd_7673158 := by exact prefixLift 7673158
  have htrace : WordTrace (prefixWord ++ tailWord_7673158) baseStart_7673158 baseEnd_7673158 := by
    simpa [prefixWord, tailWord_7673158, baseEnd_7673158] using wordTrace_append hprefix tailTrace_7673158
  have hstable : (prefixWord ++ tailWord_7673158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7673158).length < 2 ^ (prefixWord ++ tailWord_7673158).sum := by decide
  have hdescent : baseEnd_7673158 < baseStart_7673158 := by decide
  rcases family_descends (prefixWord ++ tailWord_7673158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7673161 : List Nat := [1, 2, 1, 1, 2, 3, 4, 3, 1, 3, 2]
def baseStart_7673161 : Nat := 118140960795 + 7673161 * 2 ^ 59
def prefixEnd_7673161 : Nat := 4983230072969 + 3 ^ 40 * 7673161 * 2
def baseEnd_7673161 : Nat := 3940019732333958455999281

theorem tailTrace_7673161 : CollatzResearch.WordTrace tailWord_7673161 prefixEnd_7673161 3940019732333958455999281 := by
  unfold tailWord_7673161
  simp only [CollatzResearch.WordTrace]
  refine ⟨279863173354455643411939337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186575448902970428941292891 279863173354455643411939337)
  ·
    refine ⟨209897380015841732558954503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279863173354455643411939337 209897380015841732558954503)
    ·
      refine ⟨314846070023762598838431755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209897380015841732558954503 314846070023762598838431755)
      ·
        refine ⟨472269105035643898257647633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314846070023762598838431755 472269105035643898257647633)
        ·
          refine ⟨354201828776732923693235725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 472269105035643898257647633 354201828776732923693235725)
          ·
            refine ⟨132825685791274846384963397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 354201828776732923693235725 132825685791274846384963397)
            ·
              refine ⟨24904816085864033697180637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 132825685791274846384963397 24904816085864033697180637)
              ·
                refine ⟨9339306032199012636442739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24904816085864033697180637 9339306032199012636442739)
                ·
                  refine ⟨14008959048298518954664109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9339306032199012636442739 14008959048298518954664109)
                  ·
                    refine ⟨5253359643111944607999041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14008959048298518954664109 5253359643111944607999041)
                    ·
                      refine ⟨3940019732333958455999281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5253359643111944607999041 3940019732333958455999281)
                      ·
                        rfl

theorem cell23_7673161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 3, 1, 3, 2].length) (baseStart_7673161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7673161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7673161 prefixEnd_7673161 := by exact prefixLift 7673161
  have htrace : WordTrace (prefixWord ++ tailWord_7673161) baseStart_7673161 baseEnd_7673161 := by
    simpa [prefixWord, tailWord_7673161, baseEnd_7673161] using wordTrace_append hprefix tailTrace_7673161
  have hstable : (prefixWord ++ tailWord_7673161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7673161).length < 2 ^ (prefixWord ++ tailWord_7673161).sum := by decide
  have hdescent : baseEnd_7673161 < baseStart_7673161 := by decide
  rcases family_descends (prefixWord ++ tailWord_7673161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7673225 : List Nat := [1, 2, 1, 1, 7, 1, 2, 2, 2, 2, 2]
def baseStart_7673225 : Nat := 118140960795 + 7673225 * 2 ^ 59
def prefixEnd_7673225 : Nat := 4983230072969 + 3 ^ 40 * 7673225 * 2
def baseEnd_7673225 : Nat := 3940052595095846205598987

theorem tailTrace_7673225 : CollatzResearch.WordTrace tailWord_7673225 prefixEnd_7673225 3940052595095846205598987 := by
  unfold tailWord_7673225
  simp only [CollatzResearch.WordTrace]
  refine ⟨279865507626223782342269129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186577005084149188228179419 279865507626223782342269129)
  ·
    refine ⟨209899130719667836756701847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279865507626223782342269129 209899130719667836756701847)
    ·
      refine ⟨314848696079501755135052771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209899130719667836756701847 314848696079501755135052771)
      ·
        refine ⟨472273044119252632702579157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314848696079501755135052771 472273044119252632702579157)
        ·
          refine ⟨11068899471544983578966699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 472273044119252632702579157 11068899471544983578966699)
          ·
            refine ⟨16603349207317475368450049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11068899471544983578966699 16603349207317475368450049)
            ·
              refine ⟨12452511905488106526337537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16603349207317475368450049 12452511905488106526337537)
              ·
                refine ⟨9339383929116079894753153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12452511905488106526337537 9339383929116079894753153)
                ·
                  refine ⟨7004537946837059921064865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9339383929116079894753153 7004537946837059921064865)
                  ·
                    refine ⟨5253403460127794940798649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7004537946837059921064865 5253403460127794940798649)
                    ·
                      refine ⟨3940052595095846205598987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5253403460127794940798649 3940052595095846205598987)
                      ·
                        rfl

theorem cell23_7673225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 2, 2, 2, 2].length) (baseStart_7673225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7673225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7673225 prefixEnd_7673225 := by exact prefixLift 7673225
  have htrace : WordTrace (prefixWord ++ tailWord_7673225) baseStart_7673225 baseEnd_7673225 := by
    simpa [prefixWord, tailWord_7673225, baseEnd_7673225] using wordTrace_append hprefix tailTrace_7673225
  have hstable : (prefixWord ++ tailWord_7673225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7673225).length < 2 ^ (prefixWord ++ tailWord_7673225).sum := by decide
  have hdescent : baseEnd_7673225 < baseStart_7673225 := by decide
  rcases family_descends (prefixWord ++ tailWord_7673225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7673261 : List Nat := [1, 5, 2, 2, 1, 2, 1, 1, 1, 7]
def baseStart_7673261 : Nat := 118140960795 + 7673261 * 2 ^ 59
def prefixEnd_7673261 : Nat := 4983230072969 + 3 ^ 40 * 7673261 * 2
def baseEnd_7673261 : Nat := 1313357026799802688249607

theorem tailTrace_7673261 : CollatzResearch.WordTrace tailWord_7673261 prefixEnd_7673261 1313357026799802688249607 := by
  unfold tailWord_7673261
  simp only [CollatzResearch.WordTrace]
  refine ⟨279866820654093360490579637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186577880436062240327053091 279866820654093360490579637)
  ·
    refine ⟨26237514436321252545991841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 279866820654093360490579637 26237514436321252545991841)
    ·
      refine ⟨19678135827240939409493881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26237514436321252545991841 19678135827240939409493881)
      ·
        refine ⟨14758601870430704557120411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19678135827240939409493881 14758601870430704557120411)
        ·
          refine ⟨22137902805646056835680617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14758601870430704557120411 22137902805646056835680617)
          ·
            refine ⟨16603427104234542626760463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22137902805646056835680617 16603427104234542626760463)
            ·
              refine ⟨24905140656351813940140695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16603427104234542626760463 24905140656351813940140695)
              ·
                refine ⟨37357710984527720910211043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24905140656351813940140695 37357710984527720910211043)
                ·
                  refine ⟨56036566476791581365316565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37357710984527720910211043 56036566476791581365316565)
                  ·
                    refine ⟨1313357026799802688249607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56036566476791581365316565 1313357026799802688249607)
                    ·
                      rfl

theorem cell23_7673261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_7673261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7673261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7673261 prefixEnd_7673261 := by exact prefixLift 7673261
  have htrace : WordTrace (prefixWord ++ tailWord_7673261) baseStart_7673261 baseEnd_7673261 := by
    simpa [prefixWord, tailWord_7673261, baseEnd_7673261] using wordTrace_append hprefix tailTrace_7673261
  have hstable : (prefixWord ++ tailWord_7673261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7673261).length < 2 ^ (prefixWord ++ tailWord_7673261).sum := by decide
  have hdescent : baseEnd_7673261 < baseStart_7673261 := by decide
  rcases family_descends (prefixWord ++ tailWord_7673261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7673264 : List Nat := [2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 4]
def baseStart_7673264 : Nat := 118140960795 + 7673264 * 2 ^ 59
def prefixEnd_7673264 : Nat := 4983230072969 + 3 ^ 40 * 7673264 * 2
def baseEnd_7673264 : Nat := 3940072620841371553011307

theorem tailTrace_7673264 : CollatzResearch.WordTrace tailWord_7673264 prefixEnd_7673264 3940072620841371553011307 := by
  unfold tailWord_7673264
  simp only [CollatzResearch.WordTrace]
  refine ⟨139933465036541246001469423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186577953382054994668625897 139933465036541246001469423)
  ·
    refine ⟨209900197554811869002204135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139933465036541246001469423 209900197554811869002204135)
    ·
      refine ⟨314850296332217803503306203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209900197554811869002204135 314850296332217803503306203)
      ·
        refine ⟨472275444498326705254959305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314850296332217803503306203 472275444498326705254959305)
        ·
          refine ⟨354206583373745028941219479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 472275444498326705254959305 354206583373745028941219479)
          ·
            refine ⟨531309875060617543411829219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 354206583373745028941219479 531309875060617543411829219)
            ·
              refine ⟨796964812590926315117743829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 531309875060617543411829219 796964812590926315117743829)
              ·
                refine ⟨18678862795099835510572121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 796964812590926315117743829 18678862795099835510572121)
                ·
                  refine ⟨14009147096324876632929091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18678862795099835510572121 14009147096324876632929091)
                  ·
                    refine ⟨21013720644487314949393637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14009147096324876632929091 21013720644487314949393637)
                    ·
                      refine ⟨3940072620841371553011307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21013720644487314949393637 3940072620841371553011307)
                      ·
                        rfl

theorem cell23_7673264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 4].length) (baseStart_7673264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7673264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7673264 prefixEnd_7673264 := by exact prefixLift 7673264
  have htrace : WordTrace (prefixWord ++ tailWord_7673264) baseStart_7673264 baseEnd_7673264 := by
    simpa [prefixWord, tailWord_7673264, baseEnd_7673264] using wordTrace_append hprefix tailTrace_7673264
  have hstable : (prefixWord ++ tailWord_7673264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7673264).length < 2 ^ (prefixWord ++ tailWord_7673264).sum := by decide
  have hdescent : baseEnd_7673264 < baseStart_7673264 := by decide
  rcases family_descends (prefixWord ++ tailWord_7673264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7673282 : List Nat := [3, 5, 2, 1, 1, 1, 2, 1, 7]
def baseStart_7673282 : Nat := 118140960795 + 7673282 * 2 ^ 59
def prefixEnd_7673282 : Nat := 4983230072969 + 3 ^ 40 * 7673282 * 2
def baseEnd_7673282 : Nat := 437786873721461386954025

theorem tailTrace_7673282 : CollatzResearch.WordTrace tailWord_7673282 prefixEnd_7673282 437786873721461386954025 := by
  unfold tailWord_7673282
  simp only [CollatzResearch.WordTrace]
  refine ⟨69966896646754320269273525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186578391058011520718062733 69966896646754320269273525)
  ·
    refine ⟨6559396560633217525244393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69966896646754320269273525 6559396560633217525244393)
    ·
      refine ⟨4919547420474913143933295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6559396560633217525244393 4919547420474913143933295)
      ·
        refine ⟨7379321130712369715899943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4919547420474913143933295 7379321130712369715899943)
        ·
          refine ⟨11068981696068554573849915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7379321130712369715899943 11068981696068554573849915)
          ·
            refine ⟨16603472544102831860774873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11068981696068554573849915 16603472544102831860774873)
            ·
              refine ⟨12452604408077123895581155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16603472544102831860774873 12452604408077123895581155)
              ·
                refine ⟨18678906612115685843371733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12452604408077123895581155 18678906612115685843371733)
                ·
                  refine ⟨437786873721461386954025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18678906612115685843371733 437786873721461386954025)
                  ·
                    rfl

theorem cell23_7673282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_7673282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7673282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7673282 prefixEnd_7673282 := by exact prefixLift 7673282
  have htrace : WordTrace (prefixWord ++ tailWord_7673282) baseStart_7673282 baseEnd_7673282 := by
    simpa [prefixWord, tailWord_7673282, baseEnd_7673282] using wordTrace_append hprefix tailTrace_7673282
  have hstable : (prefixWord ++ tailWord_7673282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7673282).length < 2 ^ (prefixWord ++ tailWord_7673282).sum := by decide
  have hdescent : baseEnd_7673282 < baseStart_7673282 := by decide
  rcases family_descends (prefixWord ++ tailWord_7673282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7673304 : List Nat := [2, 1, 2, 2, 2, 1, 2, 5, 6]
def baseStart_7673304 : Nat := 118140960795 + 7673304 * 2 ^ 59
def prefixEnd_7673304 : Nat := 4983230072969 + 3 ^ 40 * 7673304 * 2
def baseEnd_7673304 : Nat := 437788128896394599612347

theorem tailTrace_7673304 : CollatzResearch.WordTrace tailWord_7673304 prefixEnd_7673304 437788128896394599612347 := by
  unfold tailWord_7673304
  simp only [CollatzResearch.WordTrace]
  refine ⟨139934194496468789417197483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186578925995291719222929977 139934194496468789417197483)
  ·
    refine ⟨209901291744703184125796225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139934194496468789417197483 209901291744703184125796225)
    ·
      refine ⟨157425968808527388094347169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209901291744703184125796225 157425968808527388094347169)
      ·
        refine ⟨118069476606395541070760377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157425968808527388094347169 118069476606395541070760377)
        ·
          refine ⟨88552107454796655803070283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118069476606395541070760377 88552107454796655803070283)
          ·
            refine ⟨132828161182194983704605425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88552107454796655803070283 132828161182194983704605425)
            ·
              refine ⟨99621120886646237778454069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132828161182194983704605425 99621120886646237778454069)
              ·
                refine ⟨9339480083123084791730069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 99621120886646237778454069 9339480083123084791730069)
                ·
                  refine ⟨437788128896394599612347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9339480083123084791730069 437788128896394599612347)
                  ·
                    rfl

theorem cell23_7673304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 5, 6].length) (baseStart_7673304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7673304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7673304 prefixEnd_7673304 := by exact prefixLift 7673304
  have htrace : WordTrace (prefixWord ++ tailWord_7673304) baseStart_7673304 baseEnd_7673304 := by
    simpa [prefixWord, tailWord_7673304, baseEnd_7673304] using wordTrace_append hprefix tailTrace_7673304
  have hstable : (prefixWord ++ tailWord_7673304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7673304).length < 2 ^ (prefixWord ++ tailWord_7673304).sum := by decide
  have hdescent : baseEnd_7673304 < baseStart_7673304 := by decide
  rcases family_descends (prefixWord ++ tailWord_7673304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7673342 : List Nat := [4, 2, 2, 3, 1, 2, 1, 1, 3, 4]
def baseStart_7673342 : Nat := 118140960795 + 7673342 * 2 ^ 59
def prefixEnd_7673342 : Nat := 4983230072969 + 3 ^ 40 * 7673342 * 2
def baseEnd_7673342 : Nat := 1313370890777474082611983

theorem tailTrace_7673342 : CollatzResearch.WordTrace tailWord_7673342 prefixEnd_7673342 1313370890777474082611983 := by
  unfold tailWord_7673342
  simp only [CollatzResearch.WordTrace]
  refine ⟨34983721870849988915534785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186579849977866607549518853 34983721870849988915534785)
  ·
    refine ⟨26237791403137491686651089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34983721870849988915534785 26237791403137491686651089)
    ·
      refine ⟨19678343552353118764988317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26237791403137491686651089 19678343552353118764988317)
      ·
        refine ⟨7379378832132419536870619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19678343552353118764988317 7379378832132419536870619)
        ·
          refine ⟨11069068248198629305305929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7379378832132419536870619 11069068248198629305305929)
          ·
            refine ⟨8301801186148971978979447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11069068248198629305305929 8301801186148971978979447)
            ·
              refine ⟨12452701779223457968469171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8301801186148971978979447 12452701779223457968469171)
              ·
                refine ⟨18679052668835186952703757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12452701779223457968469171 18679052668835186952703757)
                ·
                  refine ⟨7004644750813195107263909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18679052668835186952703757 7004644750813195107263909)
                  ·
                    refine ⟨1313370890777474082611983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7004644750813195107263909 1313370890777474082611983)
                    ·
                      rfl

theorem cell23_7673342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_7673342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7673342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7673342 prefixEnd_7673342 := by exact prefixLift 7673342
  have htrace : WordTrace (prefixWord ++ tailWord_7673342) baseStart_7673342 baseEnd_7673342 := by
    simpa [prefixWord, tailWord_7673342, baseEnd_7673342] using wordTrace_append hprefix tailTrace_7673342
  have hstable : (prefixWord ++ tailWord_7673342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7673342).length < 2 ^ (prefixWord ++ tailWord_7673342).sum := by decide
  have hdescent : baseEnd_7673342 < baseStart_7673342 := by decide
  rcases family_descends (prefixWord ++ tailWord_7673342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7673355 : List Nat := [1, 1, 1, 1, 9, 1, 2, 1, 6]
def baseStart_7673355 : Nat := 118140960795 + 7673355 * 2 ^ 59
def prefixEnd_7673355 : Nat := 4983230072969 + 3 ^ 40 * 7673355 * 2
def baseEnd_7673355 : Nat := 437791038620103410774821

theorem tailTrace_7673355 : CollatzResearch.WordTrace tailWord_7673355 prefixEnd_7673355 437791038620103410774821 := by
  unfold tailWord_7673355
  simp only [CollatzResearch.WordTrace]
  refine ⟨279870249115752814544501519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186580166077168543029667679 279870249115752814544501519)
  ·
    refine ⟨419805373673629221816752279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279870249115752814544501519 419805373673629221816752279)
    ·
      refine ⟨629708060510443832725128419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419805373673629221816752279 629708060510443832725128419)
      ·
        refine ⟨944562090765665749087692629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 629708060510443832725128419 944562090765665749087692629)
        ·
          refine ⟨5534543500580072748560699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 944562090765665749087692629 5534543500580072748560699)
          ·
            refine ⟨8301815250870109122841049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5534543500580072748560699 8301815250870109122841049)
            ·
              refine ⟨6226361438152581842130787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8301815250870109122841049 6226361438152581842130787)
              ·
                refine ⟨9339542157228872763196181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6226361438152581842130787 9339542157228872763196181)
                ·
                  refine ⟨437791038620103410774821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9339542157228872763196181 437791038620103410774821)
                  ·
                    rfl

theorem cell23_7673355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 2, 1, 6].length) (baseStart_7673355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7673355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7673355 prefixEnd_7673355 := by exact prefixLift 7673355
  have htrace : WordTrace (prefixWord ++ tailWord_7673355) baseStart_7673355 baseEnd_7673355 := by
    simpa [prefixWord, tailWord_7673355, baseEnd_7673355] using wordTrace_append hprefix tailTrace_7673355
  have hstable : (prefixWord ++ tailWord_7673355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7673355).length < 2 ^ (prefixWord ++ tailWord_7673355).sum := by decide
  have hdescent : baseEnd_7673355 < baseStart_7673355 := by decide
  rcases family_descends (prefixWord ++ tailWord_7673355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7673424 : List Nat := [2, 1, 1, 1, 1, 3, 3, 2, 2, 7]
def baseStart_7673424 : Nat := 118140960795 + 7673424 * 2 ^ 59
def prefixEnd_7673424 : Nat := 4983230072969 + 3 ^ 40 * 7673424 * 2
def baseEnd_7673424 : Nat := 1313384925915363642336857

theorem tailTrace_7673424 : CollatzResearch.WordTrace tailWord_7673424 prefixEnd_7673424 1313384925915363642336857 := by
  unfold tailWord_7673424
  simp only [CollatzResearch.WordTrace]
  refine ⟨139936382876251419664381663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186581843835001892885842217 139936382876251419664381663)
  ·
    refine ⟨209904574314377129496572495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139936382876251419664381663 209904574314377129496572495)
    ·
      refine ⟨314856861471565694244858743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209904574314377129496572495 314856861471565694244858743)
      ·
        refine ⟨472285292207348541367288115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314856861471565694244858743 472285292207348541367288115)
        ·
          refine ⟨708427938311022812050932173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 472285292207348541367288115 708427938311022812050932173)
          ·
            refine ⟨265660476866633554519099565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 708427938311022812050932173 265660476866633554519099565)
            ·
              refine ⟨99622678824987582944662337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 265660476866633554519099565 99622678824987582944662337)
              ·
                refine ⟨74717009118740687208496753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99622678824987582944662337 74717009118740687208496753)
                ·
                  refine ⟨56037756839055515406372565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74717009118740687208496753 56037756839055515406372565)
                  ·
                    refine ⟨1313384925915363642336857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56037756839055515406372565 1313384925915363642336857)
                    ·
                      rfl

theorem cell23_7673424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 2, 7].length) (baseStart_7673424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7673424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7673424 prefixEnd_7673424 := by exact prefixLift 7673424
  have htrace : WordTrace (prefixWord ++ tailWord_7673424) baseStart_7673424 baseEnd_7673424 := by
    simpa [prefixWord, tailWord_7673424, baseEnd_7673424] using wordTrace_append hprefix tailTrace_7673424
  have hstable : (prefixWord ++ tailWord_7673424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7673424).length < 2 ^ (prefixWord ++ tailWord_7673424).sum := by decide
  have hdescent : baseEnd_7673424 < baseStart_7673424 := by decide
  rcases family_descends (prefixWord ++ tailWord_7673424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7673481 : List Nat := [1, 2, 1, 1, 4, 1, 2, 2, 2, 4, 3]
def baseStart_7673481 : Nat := 118140960795 + 7673481 * 2 ^ 59
def prefixEnd_7673481 : Nat := 4983230072969 + 3 ^ 40 * 7673481 * 2
def baseEnd_7673481 : Nat := 3940184046143397203997809

theorem tailTrace_7673481 : CollatzResearch.WordTrace tailWord_7673481 prefixEnd_7673481 3940184046143397203997809 := by
  unfold tailWord_7673481
  simp only [CollatzResearch.WordTrace]
  refine ⟨279874844713296338063588297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186583229808864225375725531 279874844713296338063588297)
  ·
    refine ⟨209906133534972253547691223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279874844713296338063588297 209906133534972253547691223)
    ·
      refine ⟨314859200302458380321536835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209906133534972253547691223 314859200302458380321536835)
      ·
        refine ⟨472288800453687570482305253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314859200302458380321536835 472288800453687570482305253)
        ·
          refine ⟨88554150085066419465432235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 472288800453687570482305253 88554150085066419465432235)
          ·
            refine ⟨132831225127599629198148353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88554150085066419465432235 132831225127599629198148353)
            ·
              refine ⟨99623418845699721898611265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132831225127599629198148353 99623418845699721898611265)
              ·
                refine ⟨74717564134274791423958449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99623418845699721898611265 74717564134274791423958449)
                ·
                  refine ⟨56038173100706093567968837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74717564134274791423958449 56038173100706093567968837)
                  ·
                    refine ⟨10507157456382392543994157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56038173100706093567968837 10507157456382392543994157)
                    ·
                      refine ⟨3940184046143397203997809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10507157456382392543994157 3940184046143397203997809)
                      ·
                        rfl

theorem cell23_7673481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 2, 4, 3].length) (baseStart_7673481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7673481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7673481 prefixEnd_7673481 := by exact prefixLift 7673481
  have htrace : WordTrace (prefixWord ++ tailWord_7673481) baseStart_7673481 baseEnd_7673481 := by
    simpa [prefixWord, tailWord_7673481, baseEnd_7673481] using wordTrace_append hprefix tailTrace_7673481
  have hstable : (prefixWord ++ tailWord_7673481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7673481).length < 2 ^ (prefixWord ++ tailWord_7673481).sum := by decide
  have hdescent : baseEnd_7673481 < baseStart_7673481 := by decide
  rcases family_descends (prefixWord ++ tailWord_7673481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7673482 : List Nat := [3, 1, 2, 3, 2, 2, 2, 2, 1, 3, 2]
def baseStart_7673482 : Nat := 118140960795 + 7673482 * 2 ^ 59
def prefixEnd_7673482 : Nat := 4983230072969 + 3 ^ 40 * 7673482 * 2
def baseEnd_7673482 : Nat := 3940184559624051700085305

theorem tailTrace_7673482 : CollatzResearch.WordTrace tailWord_7673482 prefixEnd_7673482 3940184559624051700085305 := by
  unfold tailWord_7673482
  simp only [CollatzResearch.WordTrace]
  refine ⟨69968720296573178808593675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186583254124195143489583133 69968720296573178808593675)
  ·
    refine ⟨104953080444859768212890513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69968720296573178808593675 104953080444859768212890513)
    ·
      refine ⟨78714810333644826159667885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104953080444859768212890513 78714810333644826159667885)
      ·
        refine ⟨29518053875116809809875457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78714810333644826159667885 29518053875116809809875457)
        ·
          refine ⟨22138540406337607357406593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29518053875116809809875457 22138540406337607357406593)
          ·
            refine ⟨16603905304753205518054945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22138540406337607357406593 16603905304753205518054945)
            ·
              refine ⟨12452928978564904138541209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16603905304753205518054945 12452928978564904138541209)
              ·
                refine ⟨9339696733923678103905907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12452928978564904138541209 9339696733923678103905907)
                ·
                  refine ⟨14009545100885517155858861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9339696733923678103905907 14009545100885517155858861)
                  ·
                    refine ⟨5253579412832068933447073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14009545100885517155858861 5253579412832068933447073)
                    ·
                      refine ⟨3940184559624051700085305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5253579412832068933447073 3940184559624051700085305)
                      ·
                        rfl

theorem cell23_7673482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 2, 1, 3, 2].length) (baseStart_7673482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7673482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7673482 prefixEnd_7673482 := by exact prefixLift 7673482
  have htrace : WordTrace (prefixWord ++ tailWord_7673482) baseStart_7673482 baseEnd_7673482 := by
    simpa [prefixWord, tailWord_7673482, baseEnd_7673482] using wordTrace_append hprefix tailTrace_7673482
  have hstable : (prefixWord ++ tailWord_7673482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7673482).length < 2 ^ (prefixWord ++ tailWord_7673482).sum := by decide
  have hdescent : baseEnd_7673482 < baseStart_7673482 := by decide
  rcases family_descends (prefixWord ++ tailWord_7673482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7673495 : List Nat := [1, 1, 3, 3, 2, 2, 1, 2, 4, 2, 2]
def baseStart_7673495 : Nat := 118140960795 + 7673495 * 2 ^ 59
def prefixEnd_7673495 : Nat := 4983230072969 + 3 ^ 40 * 7673495 * 2
def baseEnd_7673495 : Nat := 3940191234872560149222745

theorem tailTrace_7673495 : CollatzResearch.WordTrace tailWord_7673495 prefixEnd_7673495 3940191234872560149222745 := by
  unfold tailWord_7673495
  simp only [CollatzResearch.WordTrace]
  refine ⟨279875355335245618454597939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186583570223497078969731959 279875355335245618454597939)
  ·
    refine ⟨419813033002868427681896909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279875355335245618454597939 419813033002868427681896909)
    ·
      refine ⟨157429887376075660380711341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 419813033002868427681896909 157429887376075660380711341)
      ·
        refine ⟨59036207766028372642766753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157429887376075660380711341 59036207766028372642766753)
        ·
          refine ⟨44277155824521279482075065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59036207766028372642766753 44277155824521279482075065)
          ·
            refine ⟨33207866868390959611556299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44277155824521279482075065 33207866868390959611556299)
            ·
              refine ⟨49811800302586439417334449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33207866868390959611556299 49811800302586439417334449)
              ·
                refine ⟨37358850226939829563000837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49811800302586439417334449 37358850226939829563000837)
                ·
                  refine ⟨7004784417551218043062657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37358850226939829563000837 7004784417551218043062657)
                  ·
                    refine ⟨5253588313163413532296993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7004784417551218043062657 5253588313163413532296993)
                    ·
                      refine ⟨3940191234872560149222745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5253588313163413532296993 3940191234872560149222745)
                      ·
                        rfl

theorem cell23_7673495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 2, 4, 2, 2].length) (baseStart_7673495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7673495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7673495 prefixEnd_7673495 := by exact prefixLift 7673495
  have htrace : WordTrace (prefixWord ++ tailWord_7673495) baseStart_7673495 baseEnd_7673495 := by
    simpa [prefixWord, tailWord_7673495, baseEnd_7673495] using wordTrace_append hprefix tailTrace_7673495
  have hstable : (prefixWord ++ tailWord_7673495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7673495).length < 2 ^ (prefixWord ++ tailWord_7673495).sum := by decide
  have hdescent : baseEnd_7673495 < baseStart_7673495 := by decide
  rcases family_descends (prefixWord ++ tailWord_7673495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7673551 : List Nat := [1, 1, 2, 1, 1, 3, 1, 5, 1, 3, 4]
def baseStart_7673551 : Nat := 118140960795 + 7673551 * 2 ^ 59
def prefixEnd_7673551 : Nat := 4983230072969 + 3 ^ 40 * 7673551 * 2
def baseEnd_7673551 : Nat := 3940219989789211930122487

theorem tailTrace_7673551 : CollatzResearch.WordTrace tailWord_7673551 prefixEnd_7673551 3940219989789211930122487 := by
  unfold tailWord_7673551
  simp only [CollatzResearch.WordTrace]
  refine ⟨279877397823042740018636507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186584931882028493345757671 279877397823042740018636507)
  ·
    refine ⟨419816096734564110027954761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279877397823042740018636507 419816096734564110027954761)
    ·
      refine ⟨314862072550923082520966071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 419816096734564110027954761 314862072550923082520966071)
      ·
        refine ⟨472293108826384623781449107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314862072550923082520966071 472293108826384623781449107)
        ·
          refine ⟨708439663239576935672173661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 472293108826384623781449107 708439663239576935672173661)
          ·
            refine ⟨265664873714841350877065123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 708439663239576935672173661 265664873714841350877065123)
            ·
              refine ⟨398497310572262026315597685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265664873714841350877065123 398497310572262026315597685)
              ·
                refine ⟨37359122866149564967087283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 398497310572262026315597685 37359122866149564967087283)
                ·
                  refine ⟨56038684299224347450630925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37359122866149564967087283 56038684299224347450630925)
                  ·
                    refine ⟨21014506612209130293986597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56038684299224347450630925 21014506612209130293986597)
                    ·
                      refine ⟨3940219989789211930122487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21014506612209130293986597 3940219989789211930122487)
                      ·
                        rfl

theorem cell23_7673551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 5, 1, 3, 4].length) (baseStart_7673551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7673551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7673551 prefixEnd_7673551 := by exact prefixLift 7673551
  have htrace : WordTrace (prefixWord ++ tailWord_7673551) baseStart_7673551 baseEnd_7673551 := by
    simpa [prefixWord, tailWord_7673551, baseEnd_7673551] using wordTrace_append hprefix tailTrace_7673551
  have hstable : (prefixWord ++ tailWord_7673551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7673551).length < 2 ^ (prefixWord ++ tailWord_7673551).sum := by decide
  have hdescent : baseEnd_7673551 < baseStart_7673551 := by decide
  rcases family_descends (prefixWord ++ tailWord_7673551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7673568 : List Nat := [2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 4]
def baseStart_7673568 : Nat := 118140960795 + 7673568 * 2 ^ 59
def prefixEnd_7673568 : Nat := 4983230072969 + 3 ^ 40 * 7673568 * 2
def baseEnd_7673568 : Nat := 3940228718960338363609909

theorem tailTrace_7673568 : CollatzResearch.WordTrace tailWord_7673568 prefixEnd_7673568 3940228718960338363609909 := by
  unfold tailWord_7673568
  simp only [CollatzResearch.WordTrace]
  refine ⟨139939008931990575961002679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186585345242654101281336905 139939008931990575961002679)
  ·
    refine ⟨209908513397985863941504019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139939008931990575961002679 209908513397985863941504019)
    ·
      refine ⟨314862770096978795912256029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209908513397985863941504019 314862770096978795912256029)
      ·
        refine ⟨118073538786367048467096011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 314862770096978795912256029 118073538786367048467096011)
        ·
          refine ⟨177110308179550572700644017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118073538786367048467096011 177110308179550572700644017)
          ·
            refine ⟨132832731134662929525483013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177110308179550572700644017 132832731134662929525483013)
            ·
              refine ⟨24906137087749299286028065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 132832731134662929525483013 24906137087749299286028065)
              ·
                refine ⟨18679602815811974464521049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24906137087749299286028065 18679602815811974464521049)
                ·
                  refine ⟨14009702111858980848390787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18679602815811974464521049 14009702111858980848390787)
                  ·
                    refine ⟨21014553167788471272586181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14009702111858980848390787 21014553167788471272586181)
                    ·
                      refine ⟨3940228718960338363609909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21014553167788471272586181 3940228718960338363609909)
                      ·
                        rfl

theorem cell23_7673568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 4].length) (baseStart_7673568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7673568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7673568 prefixEnd_7673568 := by exact prefixLift 7673568
  have htrace : WordTrace (prefixWord ++ tailWord_7673568) baseStart_7673568 baseEnd_7673568 := by
    simpa [prefixWord, tailWord_7673568, baseEnd_7673568] using wordTrace_append hprefix tailTrace_7673568
  have hstable : (prefixWord ++ tailWord_7673568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7673568).length < 2 ^ (prefixWord ++ tailWord_7673568).sum := by decide
  have hdescent : baseEnd_7673568 < baseStart_7673568 := by decide
  rcases family_descends (prefixWord ++ tailWord_7673568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7673569 : List Nat := [1, 2, 3, 1, 6, 1, 2, 2, 5]
def baseStart_7673569 : Nat := 118140960795 + 7673569 * 2 ^ 59
def prefixEnd_7673569 : Nat := 4983230072969 + 3 ^ 40 * 7673569 * 2
def baseEnd_7673569 : Nat := 437803248048999206633045

theorem tailTrace_7673569 : CollatzResearch.WordTrace tailWord_7673569 prefixEnd_7673569 437803248048999206633045 := by
  unfold tailWord_7673569
  simp only [CollatzResearch.WordTrace]
  refine ⟨279878054336977529092791761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186585369557985019395194507 279878054336977529092791761)
  ·
    refine ⟨209908540752733146819593821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279878054336977529092791761 209908540752733146819593821)
    ·
      refine ⟨78715702782274930057347683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209908540752733146819593821 78715702782274930057347683)
      ·
        refine ⟨118073554173412395086021525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78715702782274930057347683 118073554173412395086021525)
        ·
          refine ⟨5534697851878706019657259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 118073554173412395086021525 5534697851878706019657259)
          ·
            refine ⟨8302046777818059029485889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5534697851878706019657259 8302046777818059029485889)
            ·
              refine ⟨6226535083363544272114417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8302046777818059029485889 6226535083363544272114417)
              ·
                refine ⟨4669901312522658204085813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6226535083363544272114417 4669901312522658204085813)
                ·
                  refine ⟨437803248048999206633045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4669901312522658204085813 437803248048999206633045)
                  ·
                    rfl

theorem cell23_7673569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 2, 2, 5].length) (baseStart_7673569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7673569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7673569 prefixEnd_7673569 := by exact prefixLift 7673569
  have htrace : WordTrace (prefixWord ++ tailWord_7673569) baseStart_7673569 baseEnd_7673569 := by
    simpa [prefixWord, tailWord_7673569, baseEnd_7673569] using wordTrace_append hprefix tailTrace_7673569
  have hstable : (prefixWord ++ tailWord_7673569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7673569).length < 2 ^ (prefixWord ++ tailWord_7673569).sum := by decide
  have hdescent : baseEnd_7673569 < baseStart_7673569 := by decide
  rcases family_descends (prefixWord ++ tailWord_7673569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7673585 : List Nat := [1, 2, 2, 2, 2, 4, 1, 1, 2, 4, 2]
def baseStart_7673585 : Nat := 118140960795 + 7673585 * 2 ^ 59
def prefixEnd_7673585 : Nat := 4983230072969 + 3 ^ 40 * 7673585 * 2
def baseEnd_7673585 : Nat := 3940237448131464797097331

theorem tailTrace_7673585 : CollatzResearch.WordTrace tailWord_7673585 prefixEnd_7673585 3940237448131464797097331 := by
  unfold tailWord_7673585
  simp only [CollatzResearch.WordTrace]
  refine ⟨279878637904919563825374209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186585758603279709216916139 279878637904919563825374209)
  ·
    refine ⟨209908978428689672869030657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279878637904919563825374209 209908978428689672869030657)
    ·
      refine ⟨157431733821517254651772993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209908978428689672869030657 157431733821517254651772993)
      ·
        refine ⟨118073800366137940988829745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157431733821517254651772993 118073800366137940988829745)
        ·
          refine ⟨88555350274603455741622309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118073800366137940988829745 88555350274603455741622309)
          ·
            refine ⟨16604128176488147951554183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88555350274603455741622309 16604128176488147951554183)
            ·
              refine ⟨24906192264732221927331275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16604128176488147951554183 24906192264732221927331275)
              ·
                refine ⟨37359288397098332890996913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24906192264732221927331275 37359288397098332890996913)
                ·
                  refine ⟨28019466297823749668247685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37359288397098332890996913 28019466297823749668247685)
                  ·
                    refine ⟨5253649930841953062796441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28019466297823749668247685 5253649930841953062796441)
                    ·
                      refine ⟨3940237448131464797097331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5253649930841953062796441 3940237448131464797097331)
                      ·
                        rfl

theorem cell23_7673585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 1, 2, 4, 2].length) (baseStart_7673585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7673585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7673585 prefixEnd_7673585 := by exact prefixLift 7673585
  have htrace : WordTrace (prefixWord ++ tailWord_7673585) baseStart_7673585 baseEnd_7673585 := by
    simpa [prefixWord, tailWord_7673585, baseEnd_7673585] using wordTrace_append hprefix tailTrace_7673585
  have hstable : (prefixWord ++ tailWord_7673585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7673585).length < 2 ^ (prefixWord ++ tailWord_7673585).sum := by decide
  have hdescent : baseEnd_7673585 < baseStart_7673585 := by decide
  rcases family_descends (prefixWord ++ tailWord_7673585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7673635 : List Nat := [1, 1, 1, 4, 2, 1, 3, 3, 3, 1, 3]
def baseStart_7673635 : Nat := 118140960795 + 7673635 * 2 ^ 59
def prefixEnd_7673635 : Nat := 4983230072969 + 3 ^ 40 * 7673635 * 2
def baseEnd_7673635 : Nat := 3940263122164189601472101

theorem tailTrace_7673635 : CollatzResearch.WordTrace tailWord_7673635 prefixEnd_7673635 3940263122164189601472101 := by
  unfold tailWord_7673635
  simp only [CollatzResearch.WordTrace]
  refine ⟨279880461554738422364694359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186586974369825614909796239 279880461554738422364694359)
  ·
    refine ⟨419820692332107633547041539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279880461554738422364694359 419820692332107633547041539)
    ·
      refine ⟨629731038498161450320562309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419820692332107633547041539 629731038498161450320562309)
      ·
        refine ⟨118074569718405271935105433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 629731038498161450320562309 118074569718405271935105433)
        ·
          refine ⟨88555927288803953951329075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118074569718405271935105433 88555927288803953951329075)
          ·
            refine ⟨132833890933205930926993613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88555927288803953951329075 132833890933205930926993613)
            ·
              refine ⟨49812709099952224097622605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132833890933205930926993613 49812709099952224097622605)
              ·
                refine ⟨18679765912482084036608477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49812709099952224097622605 18679765912482084036608477)
                ·
                  refine ⟨7004912217180781513728179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18679765912482084036608477 7004912217180781513728179)
                  ·
                    refine ⟨10507368325771172270592269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7004912217180781513728179 10507368325771172270592269)
                    ·
                      refine ⟨3940263122164189601472101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10507368325771172270592269 3940263122164189601472101)
                      ·
                        rfl

theorem cell23_7673635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 3, 3, 1, 3].length) (baseStart_7673635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7673635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7673635 prefixEnd_7673635 := by exact prefixLift 7673635
  have htrace : WordTrace (prefixWord ++ tailWord_7673635) baseStart_7673635 baseEnd_7673635 := by
    simpa [prefixWord, tailWord_7673635, baseEnd_7673635] using wordTrace_append hprefix tailTrace_7673635
  have hstable : (prefixWord ++ tailWord_7673635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7673635).length < 2 ^ (prefixWord ++ tailWord_7673635).sum := by decide
  have hdescent : baseEnd_7673635 < baseStart_7673635 := by decide
  rcases family_descends (prefixWord ++ tailWord_7673635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7673662 : List Nat := [4, 2, 1, 2, 2, 1, 2, 1, 1, 5, 2]
def baseStart_7673662 : Nat := 118140960795 + 7673662 * 2 ^ 59
def prefixEnd_7673662 : Nat := 4983230072969 + 3 ^ 40 * 7673662 * 2
def baseEnd_7673662 : Nat := 3940276986141860995834477

theorem tailTrace_7673662 : CollatzResearch.WordTrace tailWord_7673662 prefixEnd_7673662 3940276986141860995834477 := by
  unfold tailWord_7673662
  simp only [CollatzResearch.WordTrace]
  refine ⟨34985180790705075746990905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186587630883760403983951493 34985180790705075746990905)
  ·
    refine ⟨26238885593028806810243179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34985180790705075746990905 26238885593028806810243179)
    ·
      refine ⟨39358328389543210215364769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26238885593028806810243179 39358328389543210215364769)
      ·
        refine ⟨29518746292157407661523577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39358328389543210215364769 29518746292157407661523577)
        ·
          refine ⟨22139059719118055746142683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29518746292157407661523577 22139059719118055746142683)
          ·
            refine ⟨33208589578677083619214025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22139059719118055746142683 33208589578677083619214025)
            ·
              refine ⟨24906442184007812714410519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33208589578677083619214025 24906442184007812714410519)
              ·
                refine ⟨37359663276011719071615779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24906442184007812714410519 37359663276011719071615779)
                ·
                  refine ⟨56039494914017578607423669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37359663276011719071615779 56039494914017578607423669)
                  ·
                    refine ⟨5253702648189147994445969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56039494914017578607423669 5253702648189147994445969)
                    ·
                      refine ⟨3940276986141860995834477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5253702648189147994445969 3940276986141860995834477)
                      ·
                        rfl

theorem cell23_7673662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 1, 1, 5, 2].length) (baseStart_7673662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7673662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7673662 prefixEnd_7673662 := by exact prefixLift 7673662
  have htrace : WordTrace (prefixWord ++ tailWord_7673662) baseStart_7673662 baseEnd_7673662 := by
    simpa [prefixWord, tailWord_7673662, baseEnd_7673662] using wordTrace_append hprefix tailTrace_7673662
  have hstable : (prefixWord ++ tailWord_7673662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7673662).length < 2 ^ (prefixWord ++ tailWord_7673662).sum := by decide
  have hdescent : baseEnd_7673662 < baseStart_7673662 := by decide
  rcases family_descends (prefixWord ++ tailWord_7673662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7673685 : List Nat := [1, 3, 2, 2, 2, 2, 2, 1, 4, 4]
def baseStart_7673685 : Nat := 118140960795 + 7673685 * 2 ^ 59
def prefixEnd_7673685 : Nat := 4983230072969 + 3 ^ 40 * 7673685 * 2
def baseEnd_7673685 : Nat := 1313429598732304801948957

theorem tailTrace_7673685 : CollatzResearch.WordTrace tailWord_7673685 prefixEnd_7673685 1313429598732304801948957 := by
  unfold tailWord_7673685
  simp only [CollatzResearch.WordTrace]
  refine ⟨279882285204557280904014509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186588190136371520602676339 279882285204557280904014509)
  ·
    refine ⟨104955856951708980339005441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 279882285204557280904014509 104955856951708980339005441)
    ·
      refine ⟨78716892713781735254254081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104955856951708980339005441 78716892713781735254254081)
      ·
        refine ⟨59037669535336301440690561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78716892713781735254254081 59037669535336301440690561)
        ·
          refine ⟨44278252151502226080517921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59037669535336301440690561 44278252151502226080517921)
          ·
            refine ⟨33208689113626669560388441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44278252151502226080517921 33208689113626669560388441)
            ·
              refine ⟨24906516835220002170291331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33208689113626669560388441 24906516835220002170291331)
              ·
                refine ⟨37359775252830003255436997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24906516835220002170291331 37359775252830003255436997)
                ·
                  refine ⟨7004957859905625610394437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37359775252830003255436997 7004957859905625610394437)
                  ·
                    refine ⟨1313429598732304801948957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7004957859905625610394437 1313429598732304801948957)
                    ·
                      rfl

theorem cell23_7673685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 1, 4, 4].length) (baseStart_7673685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7673685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7673685 prefixEnd_7673685 := by exact prefixLift 7673685
  have htrace : WordTrace (prefixWord ++ tailWord_7673685) baseStart_7673685 baseEnd_7673685 := by
    simpa [prefixWord, tailWord_7673685, baseEnd_7673685] using wordTrace_append hprefix tailTrace_7673685
  have hstable : (prefixWord ++ tailWord_7673685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7673685).length < 2 ^ (prefixWord ++ tailWord_7673685).sum := by decide
  have hdescent : baseEnd_7673685 < baseStart_7673685 := by decide
  rcases family_descends (prefixWord ++ tailWord_7673685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7673706 : List Nat := [3, 1, 3, 4, 2, 1, 1, 2, 1, 5]
def baseStart_7673706 : Nat := 118140960795 + 7673706 * 2 ^ 59
def prefixEnd_7673706 : Nat := 4983230072969 + 3 ^ 40 * 7673706 * 2
def baseEnd_7673706 : Nat := 1313433193096886274561425

theorem tailTrace_7673706 : CollatzResearch.WordTrace tailWord_7673706 prefixEnd_7673706 1313433193096886274561425 := by
  unfold tailWord_7673706
  simp only [CollatzResearch.WordTrace]
  refine ⟨69970762784370300372632243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186588700758320800993685981 69970762784370300372632243)
  ·
    refine ⟨104956144176555450558948365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69970762784370300372632243 104956144176555450558948365)
    ·
      refine ⟨39358554066208293959605637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104956144176555450558948365 39358554066208293959605637)
      ·
        refine ⟨7379728887414055117426057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39358554066208293959605637 7379728887414055117426057)
        ·
          refine ⟨5534796665560541338069543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7379728887414055117426057 5534796665560541338069543)
          ·
            refine ⟨8302194998340812007104315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5534796665560541338069543 8302194998340812007104315)
            ·
              refine ⟨12453292497511218010656473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8302194998340812007104315 12453292497511218010656473)
              ·
                refine ⟨9339969373133413507992355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12453292497511218010656473 9339969373133413507992355)
                ·
                  refine ⟨14009954059700120261988533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9339969373133413507992355 14009954059700120261988533)
                  ·
                    refine ⟨1313433193096886274561425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14009954059700120261988533 1313433193096886274561425)
                    ·
                      rfl

theorem cell23_7673706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 2, 1, 5].length) (baseStart_7673706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7673706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7673706 prefixEnd_7673706 := by exact prefixLift 7673706
  have htrace : WordTrace (prefixWord ++ tailWord_7673706) baseStart_7673706 baseEnd_7673706 := by
    simpa [prefixWord, tailWord_7673706, baseEnd_7673706] using wordTrace_append hprefix tailTrace_7673706
  have hstable : (prefixWord ++ tailWord_7673706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7673706).length < 2 ^ (prefixWord ++ tailWord_7673706).sum := by decide
  have hdescent : baseEnd_7673706 < baseStart_7673706 := by decide
  rcases family_descends (prefixWord ++ tailWord_7673706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7673726 : List Nat := [4, 2, 3, 1, 1, 2, 3, 1, 1, 1, 4]
def baseStart_7673726 : Nat := 118140960795 + 7673726 * 2 ^ 59
def prefixEnd_7673726 : Nat := 4983230072969 + 3 ^ 40 * 7673726 * 2
def baseEnd_7673726 : Nat := 3940309848903748745434183

theorem tailTrace_7673726 : CollatzResearch.WordTrace tailWord_7673726 prefixEnd_7673726 3940309848903748745434183 := by
  unfold tailWord_7673726
  simp only [CollatzResearch.WordTrace]
  refine ⟨34985472574676093113282129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186589187064939163270838021 34985472574676093113282129)
  ·
    refine ⟨26239104431007069834961597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34985472574676093113282129 26239104431007069834961597)
    ·
      refine ⟨9839664161627651188110599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26239104431007069834961597 9839664161627651188110599)
      ·
        refine ⟨14759496242441476782165899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9839664161627651188110599 14759496242441476782165899)
        ·
          refine ⟨22139244363662215173248849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14759496242441476782165899 22139244363662215173248849)
          ·
            refine ⟨16604433272746661379936637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22139244363662215173248849 16604433272746661379936637)
            ·
              refine ⟨6226662477279998017476239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16604433272746661379936637 6226662477279998017476239)
              ·
                refine ⟨9339993715919997026214359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6226662477279998017476239 9339993715919997026214359)
                ·
                  refine ⟨14009990573879995539321539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9339993715919997026214359 14009990573879995539321539)
                  ·
                    refine ⟨21014985860819993308982309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14009990573879995539321539 21014985860819993308982309)
                    ·
                      refine ⟨3940309848903748745434183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21014985860819993308982309 3940309848903748745434183)
                      ·
                        rfl

theorem cell23_7673726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_7673726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7673726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7673726 prefixEnd_7673726 := by exact prefixLift 7673726
  have htrace : WordTrace (prefixWord ++ tailWord_7673726) baseStart_7673726 baseEnd_7673726 := by
    simpa [prefixWord, tailWord_7673726, baseEnd_7673726] using wordTrace_append hprefix tailTrace_7673726
  have hstable : (prefixWord ++ tailWord_7673726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7673726).length < 2 ^ (prefixWord ++ tailWord_7673726).sum := by decide
  have hdescent : baseEnd_7673726 < baseStart_7673726 := by decide
  rcases family_descends (prefixWord ++ tailWord_7673726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7673729 : List Nat := [1, 2, 4, 4, 1, 2, 1, 1, 1, 1, 5]
def baseStart_7673729 : Nat := 118140960795 + 7673729 * 2 ^ 59
def prefixEnd_7673729 : Nat := 4983230072969 + 3 ^ 40 * 7673729 * 2
def baseEnd_7673729 : Nat := 3940311389345712233696669

theorem tailTrace_7673729 : CollatzResearch.WordTrace tailWord_7673729 prefixEnd_7673729 3940311389345712233696669 := by
  unfold tailWord_7673729
  simp only [CollatzResearch.WordTrace]
  refine ⟨279883890016397876418616241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186589260010931917612410827 279883890016397876418616241)
  ·
    refine ⟨209912917512298407313962181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279883890016397876418616241 209912917512298407313962181)
    ·
      refine ⟨39358672033555951371367909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 209912917512298407313962181 39358672033555951371367909)
      ·
        refine ⟨7379751006291740882131483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39358672033555951371367909 7379751006291740882131483)
        ·
          refine ⟨11069626509437611323197225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7379751006291740882131483 11069626509437611323197225)
          ·
            refine ⟨8302219882078208492397919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11069626509437611323197225 8302219882078208492397919)
            ·
              refine ⟨12453329823117312738596879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8302219882078208492397919 12453329823117312738596879)
              ·
                refine ⟨18679994734675969107895319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12453329823117312738596879 18679994734675969107895319)
                ·
                  refine ⟨28019992102013953661842979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18679994734675969107895319 28019992102013953661842979)
                  ·
                    refine ⟨42029988153020930492764469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28019992102013953661842979 42029988153020930492764469)
                    ·
                      refine ⟨3940311389345712233696669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42029988153020930492764469 3940311389345712233696669)
                      ·
                        rfl

theorem cell23_7673729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_7673729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7673729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7673729 prefixEnd_7673729 := by exact prefixLift 7673729
  have htrace : WordTrace (prefixWord ++ tailWord_7673729) baseStart_7673729 baseEnd_7673729 := by
    simpa [prefixWord, tailWord_7673729, baseEnd_7673729] using wordTrace_append hprefix tailTrace_7673729
  have hstable : (prefixWord ++ tailWord_7673729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7673729).length < 2 ^ (prefixWord ++ tailWord_7673729).sum := by decide
  have hdescent : baseEnd_7673729 < baseStart_7673729 := by decide
  rcases family_descends (prefixWord ++ tailWord_7673729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7673780 : List Nat := [2, 5, 2, 1, 3, 1, 2, 1, 1, 2, 3]
def baseStart_7673780 : Nat := 118140960795 + 7673780 * 2 ^ 59
def prefixEnd_7673780 : Nat := 4983230072969 + 3 ^ 40 * 7673780 * 2
def baseEnd_7673780 : Nat := 3940337576859091534158935

theorem tailTrace_7673780 : CollatzResearch.WordTrace tailWord_7673780 prefixEnd_7673780 3940337576859091534158935 := by
  unfold tailWord_7673780
  simp only [CollatzResearch.WordTrace]
  refine ⟨139942875069606556064361397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186590500092808741419148529 139942875069606556064361397)
  ·
    refine ⟨13119644537775614631033881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 139942875069606556064361397 13119644537775614631033881)
    ·
      refine ⟨9839733403331710973275411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13119644537775614631033881 9839733403331710973275411)
      ·
        refine ⟨14759600104997566459913117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9839733403331710973275411 14759600104997566459913117)
        ·
          refine ⟨5534850039374087422467419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14759600104997566459913117 5534850039374087422467419)
          ·
            refine ⟨8302275059061131133701129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5534850039374087422467419 8302275059061131133701129)
            ·
              refine ⟨6226706294295848350275847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8302275059061131133701129 6226706294295848350275847)
              ·
                refine ⟨9340059441443772525413771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6226706294295848350275847 9340059441443772525413771)
                ·
                  refine ⟨14010089162165658788120657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9340059441443772525413771 14010089162165658788120657)
                  ·
                    refine ⟨10507566871624244091090493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14010089162165658788120657 10507566871624244091090493)
                    ·
                      refine ⟨3940337576859091534158935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10507566871624244091090493 3940337576859091534158935)
                      ·
                        rfl

theorem cell23_7673780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_7673780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7673780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7673780 prefixEnd_7673780 := by exact prefixLift 7673780
  have htrace : WordTrace (prefixWord ++ tailWord_7673780) baseStart_7673780 baseEnd_7673780 := by
    simpa [prefixWord, tailWord_7673780, baseEnd_7673780] using wordTrace_append hprefix tailTrace_7673780
  have hstable : (prefixWord ++ tailWord_7673780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7673780).length < 2 ^ (prefixWord ++ tailWord_7673780).sum := by decide
  have hdescent : baseEnd_7673780 < baseStart_7673780 := by decide
  rcases family_descends (prefixWord ++ tailWord_7673780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7673815 : List Nat := [1, 1, 3, 2, 1, 1, 3, 3, 2, 3, 3]
def baseStart_7673815 : Nat := 118140960795 + 7673815 * 2 ^ 59
def prefixEnd_7673815 : Nat := 4983230072969 + 3 ^ 40 * 7673815 * 2
def baseEnd_7673815 : Nat := 3940355548681998897221273

theorem tailTrace_7673815 : CollatzResearch.WordTrace tailWord_7673815 prefixEnd_7673815 3940355548681998897221273 := by
  unfold tailWord_7673815
  simp only [CollatzResearch.WordTrace]
  refine ⟨279887026694086313106246899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186591351129390875404164599 279887026694086313106246899)
  ·
    refine ⟨419830540041129469659370349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279887026694086313106246899 419830540041129469659370349)
    ·
      refine ⟨157436452515423551122263881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 419830540041129469659370349 157436452515423551122263881)
      ·
        refine ⟨118077339386567663341697911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157436452515423551122263881 118077339386567663341697911)
        ·
          refine ⟨177116009079851495012546867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118077339386567663341697911 177116009079851495012546867)
          ·
            refine ⟨265674013619777242518820301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177116009079851495012546867 265674013619777242518820301)
            ·
              refine ⟨99627755107416465944557613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 265674013619777242518820301 99627755107416465944557613)
              ·
                refine ⟨37360408165281174729209105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99627755107416465944557613 37360408165281174729209105)
                ·
                  refine ⟨28020306123960881046906829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37360408165281174729209105 28020306123960881046906829)
                  ·
                    refine ⟨10507614796485330392590061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28020306123960881046906829 10507614796485330392590061)
                    ·
                      refine ⟨3940355548681998897221273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10507614796485330392590061 3940355548681998897221273)
                      ·
                        rfl

theorem cell23_7673815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 3, 2, 3, 3].length) (baseStart_7673815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7673815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7673815 prefixEnd_7673815 := by exact prefixLift 7673815
  have htrace : WordTrace (prefixWord ++ tailWord_7673815) baseStart_7673815 baseEnd_7673815 := by
    simpa [prefixWord, tailWord_7673815, baseEnd_7673815] using wordTrace_append hprefix tailTrace_7673815
  have hstable : (prefixWord ++ tailWord_7673815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7673815).length < 2 ^ (prefixWord ++ tailWord_7673815).sum := by decide
  have hdescent : baseEnd_7673815 < baseStart_7673815 := by decide
  rcases family_descends (prefixWord ++ tailWord_7673815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7673816 : List Nat := [2, 1, 2, 2, 2, 2, 5, 1, 2, 2, 2]
def baseStart_7673816 : Nat := 118140960795 + 7673816 * 2 ^ 59
def prefixEnd_7673816 : Nat := 4983230072969 + 3 ^ 40 * 7673816 * 2
def baseEnd_7673816 : Nat := 3940356062162653393308769

theorem tailTrace_7673816 : CollatzResearch.WordTrace tailWord_7673816 prefixEnd_7673816 3940356062162653393308769 := by
  unfold tailWord_7673816
  simp only [CollatzResearch.WordTrace]
  refine ⟨139943531583541345138516651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186591375444721793518022201 139943531583541345138516651)
  ·
    refine ⟨209915297375312017707774977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139943531583541345138516651 209915297375312017707774977)
    ·
      refine ⟨157436473031484013280831233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209915297375312017707774977 157436473031484013280831233)
      ·
        refine ⟨118077354773613009960623425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157436473031484013280831233 118077354773613009960623425)
        ·
          refine ⟨88558016080209757470467569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118077354773613009960623425 88558016080209757470467569)
          ·
            refine ⟨66418512060157318102850677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88558016080209757470467569 66418512060157318102850677)
            ·
              refine ⟨6226735505639748572142251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66418512060157318102850677 6226735505639748572142251)
              ·
                refine ⟨9340103258459622858213377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6226735505639748572142251 9340103258459622858213377)
                ·
                  refine ⟨7005077443844717143660033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9340103258459622858213377 7005077443844717143660033)
                  ·
                    refine ⟨5253808082883537857745025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7005077443844717143660033 5253808082883537857745025)
                    ·
                      refine ⟨3940356062162653393308769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5253808082883537857745025 3940356062162653393308769)
                      ·
                        rfl

theorem cell23_7673816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 5, 1, 2, 2, 2].length) (baseStart_7673816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7673816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7673816 prefixEnd_7673816 := by exact prefixLift 7673816
  have htrace : WordTrace (prefixWord ++ tailWord_7673816) baseStart_7673816 baseEnd_7673816 := by
    simpa [prefixWord, tailWord_7673816, baseEnd_7673816] using wordTrace_append hprefix tailTrace_7673816
  have hstable : (prefixWord ++ tailWord_7673816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7673816).length < 2 ^ (prefixWord ++ tailWord_7673816).sum := by decide
  have hdescent : baseEnd_7673816 < baseStart_7673816 := by decide
  rcases family_descends (prefixWord ++ tailWord_7673816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7673820 : List Nat := [2, 2, 6, 1, 1, 1, 2, 2, 1, 3, 2]
def baseStart_7673820 : Nat := 118140960795 + 7673820 * 2 ^ 59
def prefixEnd_7673820 : Nat := 4983230072969 + 3 ^ 40 * 7673820 * 2
def baseEnd_7673820 : Nat := 3940358116085271377658751

theorem tailTrace_7673820 : CollatzResearch.WordTrace tailWord_7673820 prefixEnd_7673820 3940358116085271377658751 := by
  unfold tailWord_7673820
  simp only [CollatzResearch.WordTrace]
  refine ⟨139943604529534099480089457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186591472706045465973452609 139943604529534099480089457)
  ·
    refine ⟨104957703397150574610067093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139943604529534099480089457 104957703397150574610067093)
    ·
      refine ⟨4919892346741433184846895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 104957703397150574610067093 4919892346741433184846895)
      ·
        refine ⟨7379838520112149777270343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4919892346741433184846895 7379838520112149777270343)
        ·
          refine ⟨11069757780168224665905515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7379838520112149777270343 11069757780168224665905515)
          ·
            refine ⟨16604636670252336998858273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11069757780168224665905515 16604636670252336998858273)
            ·
              refine ⟨12453477502689252749143705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16604636670252336998858273 12453477502689252749143705)
              ·
                refine ⟨9340108127016939561857779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12453477502689252749143705 9340108127016939561857779)
                ·
                  refine ⟨14010162190525409342786669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9340108127016939561857779 14010162190525409342786669)
                  ·
                    refine ⟨5253810821447028503545001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14010162190525409342786669 5253810821447028503545001)
                    ·
                      refine ⟨3940358116085271377658751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5253810821447028503545001 3940358116085271377658751)
                      ·
                        rfl

theorem cell23_7673820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_7673820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7673820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7673820 prefixEnd_7673820 := by exact prefixLift 7673820
  have htrace : WordTrace (prefixWord ++ tailWord_7673820) baseStart_7673820 baseEnd_7673820 := by
    simpa [prefixWord, tailWord_7673820, baseEnd_7673820] using wordTrace_append hprefix tailTrace_7673820
  have hstable : (prefixWord ++ tailWord_7673820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7673820).length < 2 ^ (prefixWord ++ tailWord_7673820).sum := by decide
  have hdescent : baseEnd_7673820 < baseStart_7673820 := by decide
  rcases family_descends (prefixWord ++ tailWord_7673820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7673875 : List Nat := [1, 1, 1, 2, 1, 4, 2, 1, 3, 4, 3]
def baseStart_7673875 : Nat := 118140960795 + 7673875 * 2 ^ 59
def prefixEnd_7673875 : Nat := 4983230072969 + 3 ^ 40 * 7673875 * 2
def baseEnd_7673875 : Nat := 3940386357521268662470997

theorem tailTrace_7673875 : CollatzResearch.WordTrace tailWord_7673875 prefixEnd_7673875 3940386357521268662470997 := by
  unfold tailWord_7673875
  simp only [CollatzResearch.WordTrace]
  refine ⟨279889215073868943353431079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186592810049245962235620719 279889215073868943353431079)
  ·
    refine ⟨419833822610803415030146619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279889215073868943353431079 419833822610803415030146619)
    ·
      refine ⟨629750733916205122545219929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419833822610803415030146619 629750733916205122545219929)
      ·
        refine ⟨472313050437153841908914947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 629750733916205122545219929 472313050437153841908914947)
        ·
          refine ⟨708469575655730762863372421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 472313050437153841908914947 708469575655730762863372421)
          ·
            refine ⟨132838045435449518036882329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 708469575655730762863372421 132838045435449518036882329)
            ·
              refine ⟨99628534076587138527661747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132838045435449518036882329 99628534076587138527661747)
              ·
                refine ⟨149442801114880707791492621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99628534076587138527661747 149442801114880707791492621)
                ·
                  refine ⟨56041050418080265421809733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 149442801114880707791492621 56041050418080265421809733)
                  ·
                    refine ⟨10507696953390049766589325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56041050418080265421809733 10507696953390049766589325)
                    ·
                      refine ⟨3940386357521268662470997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10507696953390049766589325 3940386357521268662470997)
                      ·
                        rfl

theorem cell23_7673875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 3, 4, 3].length) (baseStart_7673875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7673875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7673875 prefixEnd_7673875 := by exact prefixLift 7673875
  have htrace : WordTrace (prefixWord ++ tailWord_7673875) baseStart_7673875 baseEnd_7673875 := by
    simpa [prefixWord, tailWord_7673875, baseEnd_7673875] using wordTrace_append hprefix tailTrace_7673875
  have hstable : (prefixWord ++ tailWord_7673875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7673875).length < 2 ^ (prefixWord ++ tailWord_7673875).sum := by decide
  have hdescent : baseEnd_7673875 < baseStart_7673875 := by decide
  rcases family_descends (prefixWord ++ tailWord_7673875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7673889 : List Nat := [1, 2, 3, 2, 4, 1, 2, 1, 2, 1, 4]
def baseStart_7673889 : Nat := 118140960795 + 7673889 * 2 ^ 59
def prefixEnd_7673889 : Nat := 4983230072969 + 3 ^ 40 * 7673889 * 2
def baseEnd_7673889 : Nat := 3940393546250431607695933

theorem tailTrace_7673889 : CollatzResearch.WordTrace tailWord_7673889 prefixEnd_7673889 3940393546250431607695933 := by
  unfold tailWord_7673889
  simp only [CollatzResearch.WordTrace]
  refine ⟨279889725695818223744440721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186593150463878815829627147 279889725695818223744440721)
  ·
    refine ⟨209917294271863667808330541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279889725695818223744440721 209917294271863667808330541)
    ·
      refine ⟨78718985351948875428123953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209917294271863667808330541 78718985351948875428123953)
      ·
        refine ⟨59039239013961656571092965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78718985351948875428123953 59039239013961656571092965)
        ·
          refine ⟨11069857315117810607079931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59039239013961656571092965 11069857315117810607079931)
          ·
            refine ⟨16604785972676715910619897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11069857315117810607079931 16604785972676715910619897)
            ·
              refine ⟨12453589479507536932964923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16604785972676715910619897 12453589479507536932964923)
              ·
                refine ⟨18680384219261305399447385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12453589479507536932964923 18680384219261305399447385)
                ·
                  refine ⟨14010288164445979049585539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18680384219261305399447385 14010288164445979049585539)
                  ·
                    refine ⟨21015432246668968574378309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14010288164445979049585539 21015432246668968574378309)
                    ·
                      refine ⟨3940393546250431607695933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21015432246668968574378309 3940393546250431607695933)
                      ·
                        rfl

theorem cell23_7673889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 1, 2, 1, 4].length) (baseStart_7673889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7673889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7673889 prefixEnd_7673889 := by exact prefixLift 7673889
  have htrace : WordTrace (prefixWord ++ tailWord_7673889) baseStart_7673889 baseEnd_7673889 := by
    simpa [prefixWord, tailWord_7673889, baseEnd_7673889] using wordTrace_append hprefix tailTrace_7673889
  have hstable : (prefixWord ++ tailWord_7673889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7673889).length < 2 ^ (prefixWord ++ tailWord_7673889).sum := by decide
  have hdescent : baseEnd_7673889 < baseStart_7673889 := by decide
  rcases family_descends (prefixWord ++ tailWord_7673889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7673956 : List Nat := [2, 3, 1, 1, 2, 1, 3, 5, 1, 1, 3]
def baseStart_7673956 : Nat := 118140960795 + 7673956 * 2 ^ 59
def prefixEnd_7673956 : Nat := 4983230072969 + 3 ^ 40 * 7673956 * 2
def baseEnd_7673956 : Nat := 3940427949454282845558125

theorem tailTrace_7673956 : CollatzResearch.WordTrace tailWord_7673956 prefixEnd_7673956 3940427949454282845558125 := by
  unfold tailWord_7673956
  simp only [CollatzResearch.WordTrace]
  refine ⟨139946084693287747093564861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186594779591050329458086481 139946084693287747093564861)
  ·
    refine ⟨52479781759982905160086823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139946084693287747093564861 52479781759982905160086823)
    ·
      refine ⟨78719672639974357740130235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52479781759982905160086823 78719672639974357740130235)
      ·
        refine ⟨118079508959961536610195353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78719672639974357740130235 118079508959961536610195353)
        ·
          refine ⟨88559631719971152457646515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118079508959961536610195353 88559631719971152457646515)
          ·
            refine ⟨132839447579956728686469773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88559631719971152457646515 132839447579956728686469773)
            ·
              refine ⟨49814792842483773257426165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132839447579956728686469773 49814792842483773257426165)
              ·
                refine ⟨4670136828982853742883703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49814792842483773257426165 4670136828982853742883703)
                ·
                  refine ⟨7005205243474280614325555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4670136828982853742883703 7005205243474280614325555)
                  ·
                    refine ⟨10507807865211420921488333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7005205243474280614325555 10507807865211420921488333)
                    ·
                      refine ⟨3940427949454282845558125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10507807865211420921488333 3940427949454282845558125)
                      ·
                        rfl

theorem cell23_7673956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 5, 1, 1, 3].length) (baseStart_7673956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7673956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7673956 prefixEnd_7673956 := by exact prefixLift 7673956
  have htrace : WordTrace (prefixWord ++ tailWord_7673956) baseStart_7673956 baseEnd_7673956 := by
    simpa [prefixWord, tailWord_7673956, baseEnd_7673956] using wordTrace_append hprefix tailTrace_7673956
  have hstable : (prefixWord ++ tailWord_7673956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7673956).length < 2 ^ (prefixWord ++ tailWord_7673956).sum := by decide
  have hdescent : baseEnd_7673956 < baseStart_7673956 := by decide
  rcases family_descends (prefixWord ++ tailWord_7673956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7673989 : List Nat := [1, 3, 1, 1, 5, 3, 1, 1, 1, 6]
def baseStart_7673989 : Nat := 118140960795 + 7673989 * 2 ^ 59
def prefixEnd_7673989 : Nat := 4983230072969 + 3 ^ 40 * 7673989 * 2
def baseEnd_7673989 : Nat := 1313481631438627072148491

theorem tailTrace_7673989 : CollatzResearch.WordTrace tailWord_7673989 prefixEnd_7673989 1313481631438627072148491 := by
  unfold tailWord_7673989
  simp only [CollatzResearch.WordTrace]
  refine ⟨279893372995455940823081021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186595581996970627215387347 279893372995455940823081021)
  ·
    refine ⟨104960014873295977808655383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 279893372995455940823081021 104960014873295977808655383)
    ·
      refine ⟨157440022309943966712983075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104960014873295977808655383 157440022309943966712983075)
      ·
        refine ⟨236160033464915950069474613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157440022309943966712983075 236160033464915950069474613)
        ·
          refine ⟨22140003137335870319013245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 236160033464915950069474613 22140003137335870319013245)
          ·
            refine ⟨8302501176500951369629967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22140003137335870319013245 8302501176500951369629967)
            ·
              refine ⟨12453751764751427054444951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8302501176500951369629967 12453751764751427054444951)
              ·
                refine ⟨18680627647127140581667427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12453751764751427054444951 18680627647127140581667427)
                ·
                  refine ⟨28020941470690710872501141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18680627647127140581667427 28020941470690710872501141)
                  ·
                    refine ⟨1313481631438627072148491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28020941470690710872501141 1313481631438627072148491)
                    ·
                      rfl

theorem cell23_7673989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 1, 1, 6].length) (baseStart_7673989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7673989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7673989 prefixEnd_7673989 := by exact prefixLift 7673989
  have htrace : WordTrace (prefixWord ++ tailWord_7673989) baseStart_7673989 baseEnd_7673989 := by
    simpa [prefixWord, tailWord_7673989, baseEnd_7673989] using wordTrace_append hprefix tailTrace_7673989
  have hstable : (prefixWord ++ tailWord_7673989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7673989).length < 2 ^ (prefixWord ++ tailWord_7673989).sum := by decide
  have hdescent : baseEnd_7673989 < baseStart_7673989 := by decide
  rcases family_descends (prefixWord ++ tailWord_7673989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7674002 : List Nat := [3, 2, 3, 1, 1, 1, 3, 9]
def baseStart_7674002 : Nat := 118140960795 + 7674002 * 2 ^ 59
def prefixEnd_7674002 : Nat := 4983230072969 + 3 ^ 40 * 7674002 * 2
def baseEnd_7674002 : Nat := 145942650724607024651219

theorem tailTrace_7674002 : CollatzResearch.WordTrace tailWord_7674002 prefixEnd_7674002 145942650724607024651219 := by
  unfold tailWord_7674002
  simp only [CollatzResearch.WordTrace]
  refine ⟨69973461786102211010826065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186595898096272562695536173 69973461786102211010826065)
  ·
    refine ⟨52480096339576658258119549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69973461786102211010826065 52480096339576658258119549)
    ·
      refine ⟨19680036127341246846794831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52480096339576658258119549 19680036127341246846794831)
      ·
        refine ⟨29520054191011870270192247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19680036127341246846794831 29520054191011870270192247)
        ·
          refine ⟨44280081286517805405288371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29520054191011870270192247 44280081286517805405288371)
          ·
            refine ⟨66420121929776708107932557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44280081286517805405288371 66420121929776708107932557)
            ·
              refine ⟨24907545723666265540474709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66420121929776708107932557 24907545723666265540474709)
              ·
                refine ⟨145942650724607024651219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24907545723666265540474709 145942650724607024651219)
                ·
                  rfl

theorem cell23_7674002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 9].length) (baseStart_7674002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7674002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7674002 prefixEnd_7674002 := by exact prefixLift 7674002
  have htrace : WordTrace (prefixWord ++ tailWord_7674002) baseStart_7674002 baseEnd_7674002 := by
    simpa [prefixWord, tailWord_7674002, baseEnd_7674002] using wordTrace_append hprefix tailTrace_7674002
  have hstable : (prefixWord ++ tailWord_7674002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7674002).length < 2 ^ (prefixWord ++ tailWord_7674002).sum := by decide
  have hdescent : baseEnd_7674002 < baseStart_7674002 := by decide
  rcases family_descends (prefixWord ++ tailWord_7674002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7674025 : List Nat := [1, 2, 1, 1, 1, 1, 2, 1, 1, 5, 7]
def baseStart_7674025 : Nat := 118140960795 + 7674025 * 2 ^ 59
def prefixEnd_7674025 : Nat := 4983230072969 + 3 ^ 40 * 7674025 * 2
def baseEnd_7674025 : Nat := 3940463379619443075595307

theorem tailTrace_7674025 : CollatzResearch.WordTrace tailWord_7674025 prefixEnd_7674025 3940463379619443075595307 := by
  unfold tailWord_7674025
  simp only [CollatzResearch.WordTrace]
  refine ⟨279894686023325518971391529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186596457348883679314261019 279894686023325518971391529)
  ·
    refine ⟨209921014517494139228543647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279894686023325518971391529 209921014517494139228543647)
    ·
      refine ⟨314881521776241208842815471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209921014517494139228543647 314881521776241208842815471)
      ·
        refine ⟨472322282664361813264223207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314881521776241208842815471 472322282664361813264223207)
        ·
          refine ⟨708483423996542719896334811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 472322282664361813264223207 708483423996542719896334811)
          ·
            refine ⟨1062725135994814079844502217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 708483423996542719896334811 1062725135994814079844502217)
            ·
              refine ⟨797043851996110559883376663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1062725135994814079844502217 797043851996110559883376663)
              ·
                refine ⟨1195565777994165839825064995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 797043851996110559883376663 1195565777994165839825064995)
                ·
                  refine ⟨1793348666991248759737597493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1195565777994165839825064995 1793348666991248759737597493)
                  ·
                    refine ⟨168126437530429571225399765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1793348666991248759737597493 168126437530429571225399765)
                    ·
                      refine ⟨3940463379619443075595307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 168126437530429571225399765 3940463379619443075595307)
                      ·
                        rfl

theorem cell23_7674025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 5, 7].length) (baseStart_7674025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7674025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7674025 prefixEnd_7674025 := by exact prefixLift 7674025
  have htrace : WordTrace (prefixWord ++ tailWord_7674025) baseStart_7674025 baseEnd_7674025 := by
    simpa [prefixWord, tailWord_7674025, baseEnd_7674025] using wordTrace_append hprefix tailTrace_7674025
  have hstable : (prefixWord ++ tailWord_7674025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7674025).length < 2 ^ (prefixWord ++ tailWord_7674025).sum := by decide
  have hdescent : baseEnd_7674025 < baseStart_7674025 := by decide
  rcases family_descends (prefixWord ++ tailWord_7674025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7674050 : List Nat := [3, 5, 1, 1, 1, 1, 3, 2, 1, 2, 3]
def baseStart_7674050 : Nat := 118140960795 + 7674050 * 2 ^ 59
def prefixEnd_7674050 : Nat := 4983230072969 + 3 ^ 40 * 7674050 * 2
def baseEnd_7674050 : Nat := 3940476216635805477782693

theorem tailTrace_7674050 : CollatzResearch.WordTrace tailWord_7674050 prefixEnd_7674050 3940476216635805477782693 := by
  unfold tailWord_7674050
  simp only [CollatzResearch.WordTrace]
  refine ⟨69973899462058737060262901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186597065232156632160701069 69973899462058737060262901)
  ·
    refine ⟨6560053074568006599399647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69973899462058737060262901 6560053074568006599399647)
    ·
      refine ⟨9840079611852009899099471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6560053074568006599399647 9840079611852009899099471)
      ·
        refine ⟨14760119417778014848649207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9840079611852009899099471 14760119417778014848649207)
        ·
          refine ⟨22140179126667022272973811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14760119417778014848649207 22140179126667022272973811)
          ·
            refine ⟨33210268690000533409460717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22140179126667022272973811 33210268690000533409460717)
            ·
              refine ⟨12453850758750200028547769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33210268690000533409460717 12453850758750200028547769)
              ·
                refine ⟨9340388069062650021410827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12453850758750200028547769 9340388069062650021410827)
                ·
                  refine ⟨14010582103593975032116241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9340388069062650021410827 14010582103593975032116241)
                  ·
                    refine ⟨10507936577695481274087181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14010582103593975032116241 10507936577695481274087181)
                    ·
                      refine ⟨3940476216635805477782693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10507936577695481274087181 3940476216635805477782693)
                      ·
                        rfl

theorem cell23_7674050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_7674050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7674050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7674050 prefixEnd_7674050 := by exact prefixLift 7674050
  have htrace : WordTrace (prefixWord ++ tailWord_7674050) baseStart_7674050 baseEnd_7674050 := by
    simpa [prefixWord, tailWord_7674050, baseEnd_7674050] using wordTrace_append hprefix tailTrace_7674050
  have hstable : (prefixWord ++ tailWord_7674050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7674050).length < 2 ^ (prefixWord ++ tailWord_7674050).sum := by decide
  have hdescent : baseEnd_7674050 < baseStart_7674050 := by decide
  rcases family_descends (prefixWord ++ tailWord_7674050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7674092 : List Nat := [2, 2, 1, 1, 2, 3, 2, 3, 7]
def baseStart_7674092 : Nat := 118140960795 + 7674092 * 2 ^ 59
def prefixEnd_7674092 : Nat := 4983230072969 + 3 ^ 40 * 7674092 * 2
def baseEnd_7674092 : Nat := 437833086980366034828611

theorem tailTrace_7674092 : CollatzResearch.WordTrace tailWord_7674092 prefixEnd_7674092 437833086980366034828611 := by
  unfold tailWord_7674092
  simp only [CollatzResearch.WordTrace]
  refine ⟨139948564857041394707040265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186598086476055192942720353 139948564857041394707040265)
  ·
    refine ⟨104961423642781046030280199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139948564857041394707040265 104961423642781046030280199)
    ·
      refine ⟨157442135464171569045420299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104961423642781046030280199 157442135464171569045420299)
      ·
        refine ⟨236163203196257353568130449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157442135464171569045420299 236163203196257353568130449)
        ·
          refine ⟨177122402397193015176097837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236163203196257353568130449 177122402397193015176097837)
          ·
            refine ⟨66420900898947380691036689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177122402397193015176097837 66420900898947380691036689)
            ·
              refine ⟨49815675674210535518277517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66420900898947380691036689 49815675674210535518277517)
              ·
                refine ⟨18680878377828950819354069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49815675674210535518277517 18680878377828950819354069)
                ·
                  refine ⟨437833086980366034828611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18680878377828950819354069 437833086980366034828611)
                  ·
                    rfl

theorem cell23_7674092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 7].length) (baseStart_7674092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7674092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7674092 prefixEnd_7674092 := by exact prefixLift 7674092
  have htrace : WordTrace (prefixWord ++ tailWord_7674092) baseStart_7674092 baseEnd_7674092 := by
    simpa [prefixWord, tailWord_7674092, baseEnd_7674092] using wordTrace_append hprefix tailTrace_7674092
  have hstable : (prefixWord ++ tailWord_7674092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7674092).length < 2 ^ (prefixWord ++ tailWord_7674092).sum := by decide
  have hdescent : baseEnd_7674092 < baseStart_7674092 := by decide
  rcases family_descends (prefixWord ++ tailWord_7674092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7674126 : List Nat := [4, 1, 1, 2, 1, 2, 4, 3, 5]
def baseStart_7674126 : Nat := 118140960795 + 7674126 * 2 ^ 59
def prefixEnd_7674126 : Nat := 4983230072969 + 3 ^ 40 * 7674126 * 2
def baseEnd_7674126 : Nat := 437835026796171908936927

theorem tailTrace_7674126 : CollatzResearch.WordTrace tailWord_7674126 prefixEnd_7674126 437835026796171908936927 := by
  unfold tailWord_7674126
  simp only [CollatzResearch.WordTrace]
  refine ⟨34987296224494951652602279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186598913197306408813878821 34987296224494951652602279)
  ·
    refine ⟨52480944336742427478903419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34987296224494951652602279 52480944336742427478903419)
    ·
      refine ⟨78721416505113641218355129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52480944336742427478903419 78721416505113641218355129)
      ·
        refine ⟨59041062378835230913766347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78721416505113641218355129 59041062378835230913766347)
        ·
          refine ⟨88561593568252846370649521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59041062378835230913766347 88561593568252846370649521)
          ·
            refine ⟨66421195176189634777987141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88561593568252846370649521 66421195176189634777987141)
            ·
              refine ⟨12453974095535556520872589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66421195176189634777987141 12453974095535556520872589)
              ·
                refine ⟨4670240285825833695327221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12453974095535556520872589 4670240285825833695327221)
                ·
                  refine ⟨437835026796171908936927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4670240285825833695327221 437835026796171908936927)
                  ·
                    rfl

theorem cell23_7674126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 3, 5].length) (baseStart_7674126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7674126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7674126 prefixEnd_7674126 := by exact prefixLift 7674126
  have htrace : WordTrace (prefixWord ++ tailWord_7674126) baseStart_7674126 baseEnd_7674126 := by
    simpa [prefixWord, tailWord_7674126, baseEnd_7674126] using wordTrace_append hprefix tailTrace_7674126
  have hstable : (prefixWord ++ tailWord_7674126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7674126).length < 2 ^ (prefixWord ++ tailWord_7674126).sum := by decide
  have hdescent : baseEnd_7674126 < baseStart_7674126 := by decide
  rcases family_descends (prefixWord ++ tailWord_7674126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7674179 : List Nat := [1, 1, 1, 3, 1, 3, 4, 1, 1, 4, 3]
def baseStart_7674179 : Nat := 118140960795 + 7674179 * 2 ^ 59
def prefixEnd_7674179 : Nat := 4983230072969 + 3 ^ 40 * 7674179 * 2
def baseEnd_7674179 : Nat := 3940542455640235473069599

theorem tailTrace_7674179 : CollatzResearch.WordTrace tailWord_7674179 prefixEnd_7674179 3940542455640235473069599 := by
  unfold tailWord_7674179
  simp only [CollatzResearch.WordTrace]
  refine ⟨279900302864767603272497591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186600201909845068848331727 279900302864767603272497591)
  ·
    refine ⟨419850454297151404908746387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279900302864767603272497591 419850454297151404908746387)
    ·
      refine ⟨629775681445727107363119581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419850454297151404908746387 629775681445727107363119581)
      ·
        refine ⟨236165880542147665261169843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 629775681445727107363119581 236165880542147665261169843)
        ·
          refine ⟨354248820813221497891754765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236165880542147665261169843 354248820813221497891754765)
          ·
            refine ⟨132843307804958061709408037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 354248820813221497891754765 132843307804958061709408037)
            ·
              refine ⟨24908120213429636570514007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 132843307804958061709408037 24908120213429636570514007)
              ·
                refine ⟨37362180320144454855771011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24908120213429636570514007 37362180320144454855771011)
                ·
                  refine ⟨56043270480216682283656517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37362180320144454855771011 56043270480216682283656517)
                  ·
                    refine ⟨10508113215040627928185597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56043270480216682283656517 10508113215040627928185597)
                    ·
                      refine ⟨3940542455640235473069599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10508113215040627928185597 3940542455640235473069599)
                      ·
                        rfl

theorem cell23_7674179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 1, 1, 4, 3].length) (baseStart_7674179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7674179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7674179 prefixEnd_7674179 := by exact prefixLift 7674179
  have htrace : WordTrace (prefixWord ++ tailWord_7674179) baseStart_7674179 baseEnd_7674179 := by
    simpa [prefixWord, tailWord_7674179, baseEnd_7674179] using wordTrace_append hprefix tailTrace_7674179
  have hstable : (prefixWord ++ tailWord_7674179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7674179).length < 2 ^ (prefixWord ++ tailWord_7674179).sum := by decide
  have hdescent : baseEnd_7674179 < baseStart_7674179 := by decide
  rcases family_descends (prefixWord ++ tailWord_7674179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7674196 : List Nat := [2, 4, 1, 1, 2, 2, 1, 1, 4, 2, 3]
def baseStart_7674196 : Nat := 118140960795 + 7674196 * 2 ^ 59
def prefixEnd_7674196 : Nat := 4983230072969 + 3 ^ 40 * 7674196 * 2
def baseEnd_7674196 : Nat := 3940551184811361906557021

theorem tailTrace_7674196 : CollatzResearch.WordTrace tailWord_7674196 prefixEnd_7674196 3940551184811361906557021 := by
  unfold tailWord_7674196
  simp only [CollatzResearch.WordTrace]
  refine ⟨139950461452853007587933221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186600615270470676783910961 139950461452853007587933221)
  ·
    refine ⟨26240711522409938922737479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139950461452853007587933221 26240711522409938922737479)
    ·
      refine ⟨39361067283614908384106219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26240711522409938922737479 39361067283614908384106219)
      ·
        refine ⟨59041600925422362576159329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39361067283614908384106219 59041600925422362576159329)
        ·
          refine ⟨44281200694066771932119497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59041600925422362576159329 44281200694066771932119497)
          ·
            refine ⟨33210900520550078949089623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44281200694066771932119497 33210900520550078949089623)
            ·
              refine ⟨49816350780825118423634435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33210900520550078949089623 49816350780825118423634435)
              ·
                refine ⟨74724526171237677635451653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49816350780825118423634435 74724526171237677635451653)
                ·
                  refine ⟨14010848657107064556647185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74724526171237677635451653 14010848657107064556647185)
                  ·
                    refine ⟨10508136492830298417485389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14010848657107064556647185 10508136492830298417485389)
                    ·
                      refine ⟨3940551184811361906557021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10508136492830298417485389 3940551184811361906557021)
                      ·
                        rfl

theorem cell23_7674196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 4, 2, 3].length) (baseStart_7674196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7674196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7674196 prefixEnd_7674196 := by exact prefixLift 7674196
  have htrace : WordTrace (prefixWord ++ tailWord_7674196) baseStart_7674196 baseEnd_7674196 := by
    simpa [prefixWord, tailWord_7674196, baseEnd_7674196] using wordTrace_append hprefix tailTrace_7674196
  have hstable : (prefixWord ++ tailWord_7674196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7674196).length < 2 ^ (prefixWord ++ tailWord_7674196).sum := by decide
  have hdescent : baseEnd_7674196 < baseStart_7674196 := by decide
  rcases family_descends (prefixWord ++ tailWord_7674196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7674199 : List Nat := [1, 1, 3, 2, 3, 1, 2, 4, 6]
def baseStart_7674199 : Nat := 118140960795 + 7674199 * 2 ^ 59
def prefixEnd_7674199 : Nat := 4983230072969 + 3 ^ 40 * 7674199 * 2
def baseEnd_7674199 : Nat := 437839191694813932757723

theorem tailTrace_7674199 : CollatzResearch.WordTrace tailWord_7674199 prefixEnd_7674199 437839191694813932757723 := by
  unfold tailWord_7674199
  simp only [CollatzResearch.WordTrace]
  refine ⟨279901032324695146688225651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186600688216463431125483767 279901032324695146688225651)
  ·
    refine ⟨419851548487042720032338477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279901032324695146688225651 419851548487042720032338477)
    ·
      refine ⟨157444330682641020012126929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 419851548487042720032338477 157444330682641020012126929)
      ·
        refine ⟨118083248011980765009095197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157444330682641020012126929 118083248011980765009095197)
        ·
          refine ⟨44281218004492786878410699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118083248011980765009095197 44281218004492786878410699)
          ·
            refine ⟨66421827006739180317616049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44281218004492786878410699 66421827006739180317616049)
            ·
              refine ⟨49816370255054385238212037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66421827006739180317616049 49816370255054385238212037)
              ·
                refine ⟨9340569422822697232164757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49816370255054385238212037 9340569422822697232164757)
                ·
                  refine ⟨437839191694813932757723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9340569422822697232164757 437839191694813932757723)
                  ·
                    rfl

theorem cell23_7674199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 4, 6].length) (baseStart_7674199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7674199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7674199 prefixEnd_7674199 := by exact prefixLift 7674199
  have htrace : WordTrace (prefixWord ++ tailWord_7674199) baseStart_7674199 baseEnd_7674199 := by
    simpa [prefixWord, tailWord_7674199, baseEnd_7674199] using wordTrace_append hprefix tailTrace_7674199
  have hstable : (prefixWord ++ tailWord_7674199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7674199).length < 2 ^ (prefixWord ++ tailWord_7674199).sum := by decide
  have hdescent : baseEnd_7674199 < baseStart_7674199 := by decide
  rcases family_descends (prefixWord ++ tailWord_7674199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7674216 : List Nat := [2, 1, 4, 2, 2, 2, 1, 3, 6]
def baseStart_7674216 : Nat := 118140960795 + 7674216 * 2 ^ 59
def prefixEnd_7674216 : Nat := 4983230072969 + 3 ^ 40 * 7674216 * 2
def baseEnd_7674216 : Nat := 437840161602716869811881

theorem tailTrace_7674216 : CollatzResearch.WordTrace tailWord_7674216 prefixEnd_7674216 437840161602716869811881 := by
  unfold tailWord_7674216
  simp only [CollatzResearch.WordTrace]
  refine ⟨139950826182816779295797251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186601101577089039061063001 139950826182816779295797251)
  ·
    refine ⟨209926239274225168943695877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139950826182816779295797251 209926239274225168943695877)
    ·
      refine ⟨39361169863917219176942977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 209926239274225168943695877 39361169863917219176942977)
      ·
        refine ⟨29520877397937914382707233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39361169863917219176942977 29520877397937914382707233)
        ·
          refine ⟨22140658048453435787030425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29520877397937914382707233 22140658048453435787030425)
          ·
            refine ⟨16605493536340076840272819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22140658048453435787030425 16605493536340076840272819)
            ·
              refine ⟨24908240304510115260409229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16605493536340076840272819 24908240304510115260409229)
              ·
                refine ⟨9340590114191293222653461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24908240304510115260409229 9340590114191293222653461)
                ·
                  refine ⟨437840161602716869811881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9340590114191293222653461 437840161602716869811881)
                  ·
                    rfl

theorem cell23_7674216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 3, 6].length) (baseStart_7674216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7674216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7674216 prefixEnd_7674216 := by exact prefixLift 7674216
  have htrace : WordTrace (prefixWord ++ tailWord_7674216) baseStart_7674216 baseEnd_7674216 := by
    simpa [prefixWord, tailWord_7674216, baseEnd_7674216] using wordTrace_append hprefix tailTrace_7674216
  have hstable : (prefixWord ++ tailWord_7674216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7674216).length < 2 ^ (prefixWord ++ tailWord_7674216).sum := by decide
  have hdescent : baseEnd_7674216 < baseStart_7674216 := by decide
  rcases family_descends (prefixWord ++ tailWord_7674216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7674266 : List Nat := [3, 1, 1, 4, 1, 2, 1, 2, 3, 1, 4]
def baseStart_7674266 : Nat := 118140960795 + 7674266 * 2 ^ 59
def prefixEnd_7674266 : Nat := 4983230072969 + 3 ^ 40 * 7674266 * 2
def baseEnd_7674266 : Nat := 3940587128457176632681699

theorem tailTrace_7674266 : CollatzResearch.WordTrace tailWord_7674266 prefixEnd_7674266 3940587128457176632681699 := by
  unfold tailWord_7674266
  simp only [CollatzResearch.WordTrace]
  refine ⟨69975869003863104282728663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186602317343634944753943101 69975869003863104282728663)
  ·
    refine ⟨104963803505794656424092995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69975869003863104282728663 104963803505794656424092995)
    ·
      refine ⟨157445705258691984636139493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104963803505794656424092995 157445705258691984636139493)
      ·
        refine ⟨29521069736004747119276155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157445705258691984636139493 29521069736004747119276155)
        ·
          refine ⟨44281604604007120678914233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29521069736004747119276155 44281604604007120678914233)
          ·
            refine ⟨33211203453005340509185675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44281604604007120678914233 33211203453005340509185675)
            ·
              refine ⟨49816805179508010763778513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33211203453005340509185675 49816805179508010763778513)
              ·
                refine ⟨37362603884631008072833885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49816805179508010763778513 37362603884631008072833885)
                ·
                  refine ⟨14010976456736628027312707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37362603884631008072833885 14010976456736628027312707)
                  ·
                    refine ⟨21016464685104942040969061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14010976456736628027312707 21016464685104942040969061)
                    ·
                      refine ⟨3940587128457176632681699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21016464685104942040969061 3940587128457176632681699)
                      ·
                        rfl

theorem cell23_7674266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_7674266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7674266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7674266 prefixEnd_7674266 := by exact prefixLift 7674266
  have htrace : WordTrace (prefixWord ++ tailWord_7674266) baseStart_7674266 baseEnd_7674266 := by
    simpa [prefixWord, tailWord_7674266, baseEnd_7674266] using wordTrace_append hprefix tailTrace_7674266
  have hstable : (prefixWord ++ tailWord_7674266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7674266).length < 2 ^ (prefixWord ++ tailWord_7674266).sum := by decide
  have hdescent : baseEnd_7674266 < baseStart_7674266 := by decide
  rcases family_descends (prefixWord ++ tailWord_7674266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7674300 : List Nat := [2, 2, 2, 4, 1, 1, 4, 1, 1, 1, 4]
def baseStart_7674300 : Nat := 118140960795 + 7674300 * 2 ^ 59
def prefixEnd_7674300 : Nat := 4983230072969 + 3 ^ 40 * 7674300 * 2
def baseEnd_7674300 : Nat := 3940604586799429499656543

theorem tailTrace_7674300 : CollatzResearch.WordTrace tailWord_7674300 prefixEnd_7674300 3940604586799429499656543 := by
  unfold tailWord_7674300
  simp only [CollatzResearch.WordTrace]
  refine ⟨139952358048664620468826177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186603144064886160625101569 139952358048664620468826177)
  ·
    refine ⟨104964268536498465351619633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139952358048664620468826177 104964268536498465351619633)
    ·
      refine ⟨78723201402373849013714725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104964268536498465351619633 78723201402373849013714725)
      ·
        refine ⟨14760600262945096690071511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78723201402373849013714725 14760600262945096690071511)
        ·
          refine ⟨22140900394417645035107267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14760600262945096690071511 22140900394417645035107267)
          ·
            refine ⟨33211350591626467552660901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22140900394417645035107267 33211350591626467552660901)
            ·
              refine ⟨6227128235929962666123919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33211350591626467552660901 6227128235929962666123919)
              ·
                refine ⟨9340692353894943999185879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6227128235929962666123919 9340692353894943999185879)
                ·
                  refine ⟨14011038530842415998778819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9340692353894943999185879 14011038530842415998778819)
                  ·
                    refine ⟨21016557796263623998168229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14011038530842415998778819 21016557796263623998168229)
                    ·
                      refine ⟨3940604586799429499656543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21016557796263623998168229 3940604586799429499656543)
                      ·
                        rfl

theorem cell23_7674300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_7674300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7674300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7674300 prefixEnd_7674300 := by exact prefixLift 7674300
  have htrace : WordTrace (prefixWord ++ tailWord_7674300) baseStart_7674300 baseEnd_7674300 := by
    simpa [prefixWord, tailWord_7674300, baseEnd_7674300] using wordTrace_append hprefix tailTrace_7674300
  have hstable : (prefixWord ++ tailWord_7674300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7674300).length < 2 ^ (prefixWord ++ tailWord_7674300).sum := by decide
  have hdescent : baseEnd_7674300 < baseStart_7674300 := by decide
  rcases family_descends (prefixWord ++ tailWord_7674300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7674346 : List Nat := [3, 1, 3, 1, 3, 1, 1, 1, 2, 2, 5]
def baseStart_7674346 : Nat := 118140960795 + 7674346 * 2 ^ 59
def prefixEnd_7674346 : Nat := 4983230072969 + 3 ^ 40 * 7674346 * 2
def baseEnd_7674346 : Nat := 3940628206909536319681331

theorem tailTrace_7674346 : CollatzResearch.WordTrace tailWord_7674346 prefixEnd_7674346 3940628206909536319681331 := by
  unfold tailWord_7674346
  simp only [CollatzResearch.WordTrace]
  refine ⟨69976598463790647698456723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186604262570108393862551261 69976598463790647698456723)
  ·
    refine ⟨104964897695685971547685085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69976598463790647698456723 104964897695685971547685085)
    ·
      refine ⟨39361836635882239330381907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104964897695685971547685085 39361836635882239330381907)
      ·
        refine ⟨59042754953823358995572861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39361836635882239330381907 59042754953823358995572861)
        ·
          refine ⟨22141033107683759623339823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59042754953823358995572861 22141033107683759623339823)
          ·
            refine ⟨33211549661525639435009735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22141033107683759623339823 33211549661525639435009735)
            ·
              refine ⟨49817324492288459152514603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33211549661525639435009735 49817324492288459152514603)
              ·
                refine ⟨74725986738432688728771905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49817324492288459152514603 74725986738432688728771905)
                ·
                  refine ⟨56044490053824516546578929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74725986738432688728771905 56044490053824516546578929)
                  ·
                    refine ⟨42033367540368387409934197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56044490053824516546578929 42033367540368387409934197)
                    ·
                      refine ⟨3940628206909536319681331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42033367540368387409934197 3940628206909536319681331)
                      ·
                        rfl

theorem cell23_7674346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_7674346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7674346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7674346 prefixEnd_7674346 := by exact prefixLift 7674346
  have htrace : WordTrace (prefixWord ++ tailWord_7674346) baseStart_7674346 baseEnd_7674346 := by
    simpa [prefixWord, tailWord_7674346, baseEnd_7674346] using wordTrace_append hprefix tailTrace_7674346
  have hstable : (prefixWord ++ tailWord_7674346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7674346).length < 2 ^ (prefixWord ++ tailWord_7674346).sum := by decide
  have hdescent : baseEnd_7674346 < baseStart_7674346 := by decide
  rcases family_descends (prefixWord ++ tailWord_7674346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7674376 : List Nat := [2, 1, 3, 2, 1, 1, 1, 3, 2, 4, 3]
def baseStart_7674376 : Nat := 118140960795 + 7674376 * 2 ^ 59
def prefixEnd_7674376 : Nat := 4983230072969 + 3 ^ 40 * 7674376 * 2
def baseEnd_7674376 : Nat := 3940643611329171202306193

theorem tailTrace_7674376 : CollatzResearch.WordTrace tailWord_7674376 prefixEnd_7674376 3940643611329171202306193 := by
  unfold tailWord_7674376
  simp only [CollatzResearch.WordTrace]
  refine ⟨139953744022526952958709491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186604992030035937278279321 139953744022526952958709491)
  ·
    refine ⟨209930616033790429438064237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139953744022526952958709491 209930616033790429438064237)
    ·
      refine ⟨78723981012671411039274089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209930616033790429438064237 78723981012671411039274089)
      ·
        refine ⟨59042985759503558279455567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78723981012671411039274089 59042985759503558279455567)
        ·
          refine ⟨88564478639255337419183351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59042985759503558279455567 88564478639255337419183351)
          ·
            refine ⟨132846717958883006128775027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88564478639255337419183351 132846717958883006128775027)
            ·
              refine ⟨199270076938324509193162541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132846717958883006128775027 199270076938324509193162541)
              ·
                refine ⟨74726278851871690947435953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 199270076938324509193162541 74726278851871690947435953)
                ·
                  refine ⟨56044709138903768210576965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74726278851871690947435953 56044709138903768210576965)
                  ·
                    refine ⟨10508382963544456539483181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56044709138903768210576965 10508382963544456539483181)
                    ·
                      refine ⟨3940643611329171202306193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10508382963544456539483181 3940643611329171202306193)
                      ·
                        rfl

theorem cell23_7674376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 2, 4, 3].length) (baseStart_7674376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7674376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7674376 prefixEnd_7674376 := by exact prefixLift 7674376
  have htrace : WordTrace (prefixWord ++ tailWord_7674376) baseStart_7674376 baseEnd_7674376 := by
    simpa [prefixWord, tailWord_7674376, baseEnd_7674376] using wordTrace_append hprefix tailTrace_7674376
  have hstable : (prefixWord ++ tailWord_7674376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7674376).length < 2 ^ (prefixWord ++ tailWord_7674376).sum := by decide
  have hdescent : baseEnd_7674376 < baseStart_7674376 := by decide
  rcases family_descends (prefixWord ++ tailWord_7674376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7674476 : List Nat := [2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 6]
def baseStart_7674476 : Nat := 118140960795 + 7674476 * 2 ^ 59
def prefixEnd_7674476 : Nat := 4983230072969 + 3 ^ 40 * 7674476 * 2
def baseEnd_7674476 : Nat := 3940694959394620811055733

theorem tailTrace_7674476 : CollatzResearch.WordTrace tailWord_7674476 prefixEnd_7674476 3940694959394620811055733 := by
  unfold tailWord_7674476
  simp only [CollatzResearch.WordTrace]
  refine ⟨139955567672345811498029641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186607423563127748664039521 139955567672345811498029641)
  ·
    refine ⟨104966675754259358623522231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139955567672345811498029641 104966675754259358623522231)
    ·
      refine ⟨157450013631389037935283347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104966675754259358623522231 157450013631389037935283347)
      ·
        refine ⟨236175020447083556902925021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157450013631389037935283347 236175020447083556902925021)
        ·
          refine ⟨88565632667656333838596883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 236175020447083556902925021 88565632667656333838596883)
          ·
            refine ⟨132848449001484500757895325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88565632667656333838596883 132848449001484500757895325)
            ·
              refine ⟨49818168375556687784210747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132848449001484500757895325 49818168375556687784210747)
              ·
                refine ⟨74727252563335031676316121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49818168375556687784210747 74727252563335031676316121)
                ·
                  refine ⟨56045439422501273757237091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74727252563335031676316121 56045439422501273757237091)
                  ·
                    refine ⟨84068159133751910635855637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56045439422501273757237091 84068159133751910635855637)
                    ·
                      refine ⟨3940694959394620811055733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84068159133751910635855637 3940694959394620811055733)
                      ·
                        rfl

theorem cell23_7674476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 6].length) (baseStart_7674476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7674476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7674476 prefixEnd_7674476 := by exact prefixLift 7674476
  have htrace : WordTrace (prefixWord ++ tailWord_7674476) baseStart_7674476 baseEnd_7674476 := by
    simpa [prefixWord, tailWord_7674476, baseEnd_7674476] using wordTrace_append hprefix tailTrace_7674476
  have hstable : (prefixWord ++ tailWord_7674476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7674476).length < 2 ^ (prefixWord ++ tailWord_7674476).sum := by decide
  have hdescent : baseEnd_7674476 < baseStart_7674476 := by decide
  rcases family_descends (prefixWord ++ tailWord_7674476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7674524 : List Nat := [2, 2, 3, 2, 2, 3, 1, 3, 1, 4]
def baseStart_7674524 : Nat := 118140960795 + 7674524 * 2 ^ 59
def prefixEnd_7674524 : Nat := 4983230072969 + 3 ^ 40 * 7674524 * 2
def baseEnd_7674524 : Nat := 1313573202155345541085171

theorem tailTrace_7674524 : CollatzResearch.WordTrace tailWord_7674524 prefixEnd_7674524 1313573202155345541085171 := by
  unfold tailWord_7674524
  simp only [CollatzResearch.WordTrace]
  refine ⟨139956443024258863596903313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186608590699011818129204417 139956443024258863596903313)
  ·
    refine ⟨104967332268194147697677485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139956443024258863596903313 104967332268194147697677485)
    ·
      refine ⟨39362749600572805386629057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104967332268194147697677485 39362749600572805386629057)
      ·
        refine ⟨29522062200429604039971793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39362749600572805386629057 29522062200429604039971793)
        ·
          refine ⟨22141546650322203029978845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29522062200429604039971793 22141546650322203029978845)
          ·
            refine ⟨8303079993870826136242067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22141546650322203029978845 8303079993870826136242067)
            ·
              refine ⟨12454619990806239204363101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8303079993870826136242067 12454619990806239204363101)
              ·
                refine ⟨4670482496552339701636163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12454619990806239204363101 4670482496552339701636163)
                ·
                  refine ⟨7005723744828509552454245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4670482496552339701636163 7005723744828509552454245)
                  ·
                    refine ⟨1313573202155345541085171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7005723744828509552454245 1313573202155345541085171)
                    ·
                      rfl

theorem cell23_7674524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 3, 1, 4].length) (baseStart_7674524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7674524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7674524 prefixEnd_7674524 := by exact prefixLift 7674524
  have htrace : WordTrace (prefixWord ++ tailWord_7674524) baseStart_7674524 baseEnd_7674524 := by
    simpa [prefixWord, tailWord_7674524, baseEnd_7674524] using wordTrace_append hprefix tailTrace_7674524
  have hstable : (prefixWord ++ tailWord_7674524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7674524).length < 2 ^ (prefixWord ++ tailWord_7674524).sum := by decide
  have hdescent : baseEnd_7674524 < baseStart_7674524 := by decide
  rcases family_descends (prefixWord ++ tailWord_7674524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7674547 : List Nat := [1, 1, 1, 2, 3, 6, 1, 1, 3, 1, 3]
def baseStart_7674547 : Nat := 118140960795 + 7674547 * 2 ^ 59
def prefixEnd_7674547 : Nat := 4983230072969 + 3 ^ 40 * 7674547 * 2
def baseEnd_7674547 : Nat := 3940731416521090033267907

theorem tailTrace_7674547 : CollatzResearch.WordTrace tailWord_7674547 prefixEnd_7674547 3940731416521090033267907 := by
  unfold tailWord_7674547
  simp only [CollatzResearch.WordTrace]
  refine ⟨279913724927434402121893895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186609149951622934747929263 279913724927434402121893895)
  ·
    refine ⟨419870587391151603182840843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279913724927434402121893895 419870587391151603182840843)
    ·
      refine ⟨629805881086727404774261265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419870587391151603182840843 629805881086727404774261265)
      ·
        refine ⟨472354410815045553580695949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 629805881086727404774261265 472354410815045553580695949)
        ·
          refine ⟨177132904055642082592760981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 472354410815045553580695949 177132904055642082592760981)
          ·
            refine ⟨8303104877608222621535671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 177132904055642082592760981 8303104877608222621535671)
            ·
              refine ⟨12454657316412333932303507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8303104877608222621535671 12454657316412333932303507)
              ·
                refine ⟨18681985974618500898455261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12454657316412333932303507 18681985974618500898455261)
                ·
                  refine ⟨7005744740481937836920723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18681985974618500898455261 7005744740481937836920723)
                  ·
                    refine ⟨10508617110722906755381085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7005744740481937836920723 10508617110722906755381085)
                    ·
                      refine ⟨3940731416521090033267907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10508617110722906755381085 3940731416521090033267907)
                      ·
                        rfl

theorem cell23_7674547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 1, 3, 1, 3].length) (baseStart_7674547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7674547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7674547 prefixEnd_7674547 := by exact prefixLift 7674547
  have htrace : WordTrace (prefixWord ++ tailWord_7674547) baseStart_7674547 baseEnd_7674547 := by
    simpa [prefixWord, tailWord_7674547, baseEnd_7674547] using wordTrace_append hprefix tailTrace_7674547
  have hstable : (prefixWord ++ tailWord_7674547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7674547).length < 2 ^ (prefixWord ++ tailWord_7674547).sum := by decide
  have hdescent : baseEnd_7674547 < baseStart_7674547 := by decide
  rcases family_descends (prefixWord ++ tailWord_7674547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7674553 : List Nat := [1, 2, 1, 4, 1, 1, 1, 4, 3, 1, 4]
def baseStart_7674553 : Nat := 118140960795 + 7674553 * 2 ^ 59
def prefixEnd_7674553 : Nat := 4983230072969 + 3 ^ 40 * 7674553 * 2
def baseEnd_7674553 : Nat := 3940734497405017009792879

theorem tailTrace_7674553 : CollatzResearch.WordTrace tailWord_7674553 prefixEnd_7674553 3940734497405017009792879 := by
  unfold tailWord_7674553
  simp only [CollatzResearch.WordTrace]
  refine ⟨279913943765412665146612313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186609295843608443431074875 279913943765412665146612313)
  ·
    refine ⟨209935457824059498859959235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279913943765412665146612313 209935457824059498859959235)
    ·
      refine ⟨314903186736089248289938853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209935457824059498859959235 314903186736089248289938853)
      ·
        refine ⟨59044347513016734054363535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 314903186736089248289938853 59044347513016734054363535)
        ·
          refine ⟨88566521269525101081545303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59044347513016734054363535 88566521269525101081545303)
          ·
            refine ⟨132849781904287651622317955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88566521269525101081545303 132849781904287651622317955)
            ·
              refine ⟨199274672856431477433476933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132849781904287651622317955 199274672856431477433476933)
              ·
                refine ⟨37364001160580902018776925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 199274672856431477433476933 37364001160580902018776925)
                ·
                  refine ⟨14011500435217838257041347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37364001160580902018776925 14011500435217838257041347)
                  ·
                    refine ⟨21017250652826757385562021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14011500435217838257041347 21017250652826757385562021)
                    ·
                      refine ⟨3940734497405017009792879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21017250652826757385562021 3940734497405017009792879)
                      ·
                        rfl

theorem cell23_7674553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_7674553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7674553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7674553 prefixEnd_7674553 := by exact prefixLift 7674553
  have htrace : WordTrace (prefixWord ++ tailWord_7674553) baseStart_7674553 baseEnd_7674553 := by
    simpa [prefixWord, tailWord_7674553, baseEnd_7674553] using wordTrace_append hprefix tailTrace_7674553
  have hstable : (prefixWord ++ tailWord_7674553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7674553).length < 2 ^ (prefixWord ++ tailWord_7674553).sum := by decide
  have hdescent : baseEnd_7674553 < baseStart_7674553 := by decide
  rcases family_descends (prefixWord ++ tailWord_7674553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7674570 : List Nat := [3, 1, 2, 1, 4, 2, 1, 1, 3, 1, 4]
def baseStart_7674570 : Nat := 118140960795 + 7674570 * 2 ^ 59
def prefixEnd_7674570 : Nat := 4983230072969 + 3 ^ 40 * 7674570 * 2
def baseEnd_7674570 : Nat := 3940743226576143443280301

theorem tailTrace_7674570 : CollatzResearch.WordTrace tailWord_7674570 prefixEnd_7674570 3940743226576143443280301 := by
  unfold tailWord_7674570
  simp only [CollatzResearch.WordTrace]
  refine ⟨69978640951587769262495291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186609709204234051366654109 69978640951587769262495291)
  ·
    refine ⟨104967961427381653893742937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69978640951587769262495291 104967961427381653893742937)
    ·
      refine ⟨78725971070536240420307203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104967961427381653893742937 78725971070536240420307203)
      ·
        refine ⟨118088956605804360630460805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78725971070536240420307203 118088956605804360630460805)
        ·
          refine ⟨22141679363588317618211401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118088956605804360630460805 22141679363588317618211401)
          ·
            refine ⟨16606259522691238213658551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22141679363588317618211401 16606259522691238213658551)
            ·
              refine ⟨24909389284036857320487827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16606259522691238213658551 24909389284036857320487827)
              ·
                refine ⟨37364083926055285980731741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24909389284036857320487827 37364083926055285980731741)
                ·
                  refine ⟨14011531472270732242774403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37364083926055285980731741 14011531472270732242774403)
                  ·
                    refine ⟨21017297208406098364161605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14011531472270732242774403 21017297208406098364161605)
                    ·
                      refine ⟨3940743226576143443280301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21017297208406098364161605 3940743226576143443280301)
                      ·
                        rfl

theorem cell23_7674570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 1, 3, 1, 4].length) (baseStart_7674570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7674570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7674570 prefixEnd_7674570 := by exact prefixLift 7674570
  have htrace : WordTrace (prefixWord ++ tailWord_7674570) baseStart_7674570 baseEnd_7674570 := by
    simpa [prefixWord, tailWord_7674570, baseEnd_7674570] using wordTrace_append hprefix tailTrace_7674570
  have hstable : (prefixWord ++ tailWord_7674570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7674570).length < 2 ^ (prefixWord ++ tailWord_7674570).sum := by decide
  have hdescent : baseEnd_7674570 < baseStart_7674570 := by decide
  rcases family_descends (prefixWord ++ tailWord_7674570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7674583 : List Nat := [1, 1, 3, 2, 1, 4, 1, 1, 3, 2, 4]
def baseStart_7674583 : Nat := 118140960795 + 7674583 * 2 ^ 59
def prefixEnd_7674583 : Nat := 4983230072969 + 3 ^ 40 * 7674583 * 2
def baseEnd_7674583 : Nat := 3940749901824651892417741

theorem tailTrace_7674583 : CollatzResearch.WordTrace tailWord_7674583 prefixEnd_7674583 3940749901824651892417741 := by
  unfold tailWord_7674583
  simp only [CollatzResearch.WordTrace]
  refine ⟨279915037955303980270204403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186610025303535986846802935 279915037955303980270204403)
  ·
    refine ⟨419872556932955970405306605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279915037955303980270204403 419872556932955970405306605)
    ·
      refine ⟨157452208849858488901989977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 419872556932955970405306605 157452208849858488901989977)
      ·
        refine ⟨118089156637393866676492483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157452208849858488901989977 118089156637393866676492483)
        ·
          refine ⟨177133734956090800014738725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118089156637393866676492483 177133734956090800014738725)
          ·
            refine ⟨33212575304267025002763511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 177133734956090800014738725 33212575304267025002763511)
            ·
              refine ⟨49818862956400537504145267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33212575304267025002763511 49818862956400537504145267)
              ·
                refine ⟨74728294434600806256217901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49818862956400537504145267 74728294434600806256217901)
                ·
                  refine ⟨28023110412975302346081713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74728294434600806256217901 28023110412975302346081713)
                  ·
                    refine ⟨21017332809731476759561285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28023110412975302346081713 21017332809731476759561285)
                    ·
                      refine ⟨3940749901824651892417741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21017332809731476759561285 3940749901824651892417741)
                      ·
                        rfl

theorem cell23_7674583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 3, 2, 4].length) (baseStart_7674583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7674583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7674583 prefixEnd_7674583 := by exact prefixLift 7674583
  have htrace : WordTrace (prefixWord ++ tailWord_7674583) baseStart_7674583 baseEnd_7674583 := by
    simpa [prefixWord, tailWord_7674583, baseEnd_7674583] using wordTrace_append hprefix tailTrace_7674583
  have hstable : (prefixWord ++ tailWord_7674583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7674583).length < 2 ^ (prefixWord ++ tailWord_7674583).sum := by decide
  have hdescent : baseEnd_7674583 < baseStart_7674583 := by decide
  rcases family_descends (prefixWord ++ tailWord_7674583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7674597 : List Nat := [1, 3, 1, 4, 1, 3, 2, 2, 2, 4]
def baseStart_7674597 : Nat := 118140960795 + 7674597 * 2 ^ 59
def prefixEnd_7674597 : Nat := 4983230072969 + 3 ^ 40 * 7674597 * 2
def baseEnd_7674597 : Nat := 1313585696851271612547559

theorem tailTrace_7674597 : CollatzResearch.WordTrace tailWord_7674597 prefixEnd_7674597 1313585696851271612547559 := by
  unfold tailWord_7674597
  simp only [CollatzResearch.WordTrace]
  refine ⟨279915548577253260661214045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186610365718168840440809363 279915548577253260661214045)
  ·
    refine ⟨104968330716469972747955267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 279915548577253260661214045 104968330716469972747955267)
    ·
      refine ⟨157452496074704959121932901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104968330716469972747955267 157452496074704959121932901)
      ·
        refine ⟨29522343014007179835362419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157452496074704959121932901 29522343014007179835362419)
        ·
          refine ⟨44283514521010769753043629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29522343014007179835362419 44283514521010769753043629)
          ·
            refine ⟨16606317945379038657391361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44283514521010769753043629 16606317945379038657391361)
            ·
              refine ⟨12454738459034278993043521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16606317945379038657391361 12454738459034278993043521)
              ·
                refine ⟨9341053844275709244782641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12454738459034278993043521 9341053844275709244782641)
                ·
                  refine ⟨7005790383206781933586981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9341053844275709244782641 7005790383206781933586981)
                  ·
                    refine ⟨1313585696851271612547559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7005790383206781933586981 1313585696851271612547559)
                    ·
                      rfl

theorem cell23_7674597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 2, 2, 4].length) (baseStart_7674597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7674597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7674597 prefixEnd_7674597 := by exact prefixLift 7674597
  have htrace : WordTrace (prefixWord ++ tailWord_7674597) baseStart_7674597 baseEnd_7674597 := by
    simpa [prefixWord, tailWord_7674597, baseEnd_7674597] using wordTrace_append hprefix tailTrace_7674597
  have hstable : (prefixWord ++ tailWord_7674597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7674597).length < 2 ^ (prefixWord ++ tailWord_7674597).sum := by decide
  have hdescent : baseEnd_7674597 < baseStart_7674597 := by decide
  rcases family_descends (prefixWord ++ tailWord_7674597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7674603 : List Nat := [1, 1, 1, 1, 2, 4, 1, 1, 5, 3, 3]
def baseStart_7674603 : Nat := 118140960795 + 7674603 * 2 ^ 59
def prefixEnd_7674603 : Nat := 4983230072969 + 3 ^ 40 * 7674603 * 2
def baseEnd_7674603 : Nat := 3940760171437741814167649

theorem tailTrace_7674603 : CollatzResearch.WordTrace tailWord_7674603 prefixEnd_7674603 3940760171437741814167649 := by
  unfold tailWord_7674603
  simp only [CollatzResearch.WordTrace]
  refine ⟨279915767415231523685932463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186610511610154349123954975 279915767415231523685932463)
  ·
    refine ⟨419873651122847285528898695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279915767415231523685932463 419873651122847285528898695)
    ·
      refine ⟨629810476684270928293348043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419873651122847285528898695 629810476684270928293348043)
      ·
        refine ⟨944715715026406392440022065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 629810476684270928293348043 944715715026406392440022065)
        ·
          refine ⟨708536786269804794330016549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 944715715026406392440022065 708536786269804794330016549)
          ·
            refine ⟨132850647425588398936878103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 708536786269804794330016549 132850647425588398936878103)
            ·
              refine ⟨199275971138382598405317155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132850647425588398936878103 199275971138382598405317155)
              ·
                refine ⟨298913956707573897607975733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199275971138382598405317155 298913956707573897607975733)
                ·
                  refine ⟨28023183441335052900747725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 298913956707573897607975733 28023183441335052900747725)
                  ·
                    refine ⟨10508693790500644837780397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28023183441335052900747725 10508693790500644837780397)
                    ·
                      refine ⟨3940760171437741814167649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10508693790500644837780397 3940760171437741814167649)
                      ·
                        rfl

theorem cell23_7674603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 5, 3, 3].length) (baseStart_7674603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7674603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7674603 prefixEnd_7674603 := by exact prefixLift 7674603
  have htrace : WordTrace (prefixWord ++ tailWord_7674603) baseStart_7674603 baseEnd_7674603 := by
    simpa [prefixWord, tailWord_7674603, baseEnd_7674603] using wordTrace_append hprefix tailTrace_7674603
  have hstable : (prefixWord ++ tailWord_7674603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7674603).length < 2 ^ (prefixWord ++ tailWord_7674603).sum := by decide
  have hdescent : baseEnd_7674603 < baseStart_7674603 := by decide
  rcases family_descends (prefixWord ++ tailWord_7674603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7674610 : List Nat := [3, 2, 1, 3, 1, 4, 1, 8]
def baseStart_7674610 : Nat := 118140960795 + 7674610 * 2 ^ 59
def prefixEnd_7674610 : Nat := 4983230072969 + 3 ^ 40 * 7674610 * 2
def baseEnd_7674610 : Nat := 145954213548234195806671

theorem tailTrace_7674610 : CollatzResearch.WordTrace tailWord_7674610 prefixEnd_7674610 145954213548234195806671 := by
  unfold tailWord_7674610
  simp only [CollatzResearch.WordTrace]
  refine ⟨69979005681551540970359321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186610681817470775920958189 69979005681551540970359321)
  ·
    refine ⟨52484254261163655727769491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69979005681551540970359321 52484254261163655727769491)
    ·
      refine ⟨78726381391745483591654237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52484254261163655727769491 78726381391745483591654237)
      ·
        refine ⟨29522393021904556346870339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78726381391745483591654237 29522393021904556346870339)
        ·
          refine ⟨44283589532856834520305509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29522393021904556346870339 44283589532856834520305509)
          ·
            refine ⟨8303173037410656472557283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44283589532856834520305509 8303173037410656472557283)
            ·
              refine ⟨12454759556115984708835925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8303173037410656472557283 12454759556115984708835925)
              ·
                refine ⟨145954213548234195806671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12454759556115984708835925 145954213548234195806671)
                ·
                  rfl

theorem cell23_7674610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 8].length) (baseStart_7674610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7674610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7674610 prefixEnd_7674610 := by exact prefixLift 7674610
  have htrace : WordTrace (prefixWord ++ tailWord_7674610) baseStart_7674610 baseEnd_7674610 := by
    simpa [prefixWord, tailWord_7674610, baseEnd_7674610] using wordTrace_append hprefix tailTrace_7674610
  have hstable : (prefixWord ++ tailWord_7674610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7674610).length < 2 ^ (prefixWord ++ tailWord_7674610).sum := by decide
  have hdescent : baseEnd_7674610 < baseStart_7674610 := by decide
  rcases family_descends (prefixWord ++ tailWord_7674610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7674620 : List Nat := [2, 2, 2, 1, 3, 2, 1, 3, 1, 3, 3]
def baseStart_7674620 : Nat := 118140960795 + 7674620 * 2 ^ 59
def prefixEnd_7674620 : Nat := 4983230072969 + 3 ^ 40 * 7674620 * 2
def baseEnd_7674620 : Nat := 3940768900608868247655071

theorem tailTrace_7674620 : CollatzResearch.WordTrace tailWord_7674620 prefixEnd_7674620 3940768900608868247655071 := by
  unfold tailWord_7674620
  simp only [CollatzResearch.WordTrace]
  refine ⟨139958193728084967794650657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186610924970779957059534209 139958193728084967794650657)
  ·
    refine ⟨104968645296063725845987993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139958193728084967794650657 104968645296063725845987993)
    ·
      refine ⟨78726483972047794384490995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104968645296063725845987993 78726483972047794384490995)
      ·
        refine ⟨118089725958071691576736493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78726483972047794384490995 118089725958071691576736493)
        ·
          refine ⟨44283647234276884341276185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118089725958071691576736493 44283647234276884341276185)
          ·
            refine ⟨33212735425707663255957139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44283647234276884341276185 33212735425707663255957139)
            ·
              refine ⟨49819103138561494883935709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33212735425707663255957139 49819103138561494883935709)
              ·
                refine ⟨18682163676960560581475891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49819103138561494883935709 18682163676960560581475891)
                ·
                  refine ⟨28023245515440840872213837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18682163676960560581475891 28023245515440840872213837)
                  ·
                    refine ⟨10508717068290315327080189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28023245515440840872213837 10508717068290315327080189)
                    ·
                      refine ⟨3940768900608868247655071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10508717068290315327080189 3940768900608868247655071)
                      ·
                        rfl

theorem cell23_7674620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 3, 1, 3, 3].length) (baseStart_7674620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7674620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7674620 prefixEnd_7674620 := by exact prefixLift 7674620
  have htrace : WordTrace (prefixWord ++ tailWord_7674620) baseStart_7674620 baseEnd_7674620 := by
    simpa [prefixWord, tailWord_7674620, baseEnd_7674620] using wordTrace_append hprefix tailTrace_7674620
  have hstable : (prefixWord ++ tailWord_7674620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7674620).length < 2 ^ (prefixWord ++ tailWord_7674620).sum := by decide
  have hdescent : baseEnd_7674620 < baseStart_7674620 := by decide
  rcases family_descends (prefixWord ++ tailWord_7674620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7674728 : List Nat := [2, 1, 4, 2, 1, 4, 2, 1, 2, 2, 2]
def baseStart_7674728 : Nat := 118140960795 + 7674728 * 2 ^ 59
def prefixEnd_7674728 : Nat := 4983230072969 + 3 ^ 40 * 7674728 * 2
def baseEnd_7674728 : Nat := 3940824356519553825104575

theorem tailTrace_7674728 : CollatzResearch.WordTrace tailWord_7674728 prefixEnd_7674728 3940824356519553825104575 := by
  unfold tailWord_7674728
  simp only [CollatzResearch.WordTrace]
  refine ⟨139960163269889335017116419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186613551026519113356155225 139960163269889335017116419)
  ·
    refine ⟨209940244904834002525674629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139960163269889335017116419 209940244904834002525674629)
    ·
      refine ⟨39363795919656375473563993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 209940244904834002525674629 39363795919656375473563993)
      ·
        refine ⟨29522846939742281605172995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39363795919656375473563993 29522846939742281605172995)
        ·
          refine ⟨44284270409613422407759493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29522846939742281605172995 44284270409613422407759493)
          ·
            refine ⟨8303300701802516701454905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44284270409613422407759493 8303300701802516701454905)
            ·
              refine ⟨6227475526351887526091179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8303300701802516701454905 6227475526351887526091179)
              ·
                refine ⟨9341213289527831289136769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6227475526351887526091179 9341213289527831289136769)
                ·
                  refine ⟨7005909967145873466852577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9341213289527831289136769 7005909967145873466852577)
                  ·
                    refine ⟨5254432475359405100139433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7005909967145873466852577 5254432475359405100139433)
                    ·
                      refine ⟨3940824356519553825104575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5254432475359405100139433 3940824356519553825104575)
                      ·
                        rfl

theorem cell23_7674728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 2, 1, 2, 2, 2].length) (baseStart_7674728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7674728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7674728 prefixEnd_7674728 := by exact prefixLift 7674728
  have htrace : WordTrace (prefixWord ++ tailWord_7674728) baseStart_7674728 baseEnd_7674728 := by
    simpa [prefixWord, tailWord_7674728, baseEnd_7674728] using wordTrace_append hprefix tailTrace_7674728
  have hstable : (prefixWord ++ tailWord_7674728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7674728).length < 2 ^ (prefixWord ++ tailWord_7674728).sum := by decide
  have hdescent : baseEnd_7674728 < baseStart_7674728 := by decide
  rcases family_descends (prefixWord ++ tailWord_7674728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7674743 : List Nat := [1, 1, 3, 1, 1, 2, 1, 3, 2, 8]
def baseStart_7674743 : Nat := 118140960795 + 7674743 * 2 ^ 59
def prefixEnd_7674743 : Nat := 4983230072969 + 3 ^ 40 * 7674743 * 2
def baseEnd_7674743 : Nat := 1313610686243123755472335

theorem tailTrace_7674743 : CollatzResearch.WordTrace tailWord_7674743 prefixEnd_7674743 1313610686243123755472335 := by
  unfold tailWord_7674743
  simp only [CollatzResearch.WordTrace]
  refine ⟨279920873634724327596028883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186613915756482885064019255 279920873634724327596028883)
  ·
    refine ⟨419881310452086491394043325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279920873634724327596028883 419881310452086491394043325)
    ·
      refine ⟨157455491419532434272766247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 419881310452086491394043325 157455491419532434272766247)
      ·
        refine ⟨236183237129298651409149371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157455491419532434272766247 236183237129298651409149371)
        ·
          refine ⟨354274855693947977113724057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236183237129298651409149371 354274855693947977113724057)
          ·
            refine ⟨265706141770460982835293043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 354274855693947977113724057 265706141770460982835293043)
            ·
              refine ⟨398559212655691474252939565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265706141770460982835293043 398559212655691474252939565)
              ·
                refine ⟨149459704745884302844852337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 398559212655691474252939565 149459704745884302844852337)
                ·
                  refine ⟨112094778559413227133639253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 149459704745884302844852337 112094778559413227133639253)
                  ·
                    refine ⟨1313610686243123755472335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 112094778559413227133639253 1313610686243123755472335)
                    ·
                      rfl

theorem cell23_7674743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 8].length) (baseStart_7674743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7674743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7674743 prefixEnd_7674743 := by exact prefixLift 7674743
  have htrace : WordTrace (prefixWord ++ tailWord_7674743) baseStart_7674743 baseEnd_7674743 := by
    simpa [prefixWord, tailWord_7674743, baseEnd_7674743] using wordTrace_append hprefix tailTrace_7674743
  have hstable : (prefixWord ++ tailWord_7674743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7674743).length < 2 ^ (prefixWord ++ tailWord_7674743).sum := by decide
  have hdescent : baseEnd_7674743 < baseStart_7674743 := by decide
  rcases family_descends (prefixWord ++ tailWord_7674743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7674801 : List Nat := [1, 2, 2, 4, 4, 1, 1, 1, 2, 1, 4]
def baseStart_7674801 : Nat := 118140960795 + 7674801 * 2 ^ 59
def prefixEnd_7674801 : Nat := 4983230072969 + 3 ^ 40 * 7674801 * 2
def baseEnd_7674801 : Nat := 3940861840607332039491739

theorem tailTrace_7674801 : CollatzResearch.WordTrace tailWord_7674801 prefixEnd_7674801 3940861840607332039491739 := by
  unfold tailWord_7674801
  simp only [CollatzResearch.WordTrace]
  refine ⟨279922989068514203501640257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186615326045676135667760171 279922989068514203501640257)
  ·
    refine ⟨209942241801385652626230193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279922989068514203501640257 209942241801385652626230193)
    ·
      refine ⟨157456681351039239469672645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209942241801385652626230193 157456681351039239469672645)
      ·
        refine ⟨29523127753319857400563621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157456681351039239469672645 29523127753319857400563621)
        ·
          refine ⟨5535586453747473262605679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29523127753319857400563621 5535586453747473262605679)
          ·
            refine ⟨8303379680621209893908519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5535586453747473262605679 8303379680621209893908519)
            ·
              refine ⟨12455069520931814840862779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8303379680621209893908519 12455069520931814840862779)
              ·
                refine ⟨18682604281397722261294169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12455069520931814840862779 18682604281397722261294169)
                ·
                  refine ⟨14011953211048291695970627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18682604281397722261294169 14011953211048291695970627)
                  ·
                    refine ⟨21017929816572437543955941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14011953211048291695970627 21017929816572437543955941)
                    ·
                      refine ⟨3940861840607332039491739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21017929816572437543955941 3940861840607332039491739)
                      ·
                        rfl

theorem cell23_7674801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 1, 2, 1, 4].length) (baseStart_7674801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7674801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7674801 prefixEnd_7674801 := by exact prefixLift 7674801
  have htrace : WordTrace (prefixWord ++ tailWord_7674801) baseStart_7674801 baseEnd_7674801 := by
    simpa [prefixWord, tailWord_7674801, baseEnd_7674801] using wordTrace_append hprefix tailTrace_7674801
  have hstable : (prefixWord ++ tailWord_7674801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7674801).length < 2 ^ (prefixWord ++ tailWord_7674801).sum := by decide
  have hdescent : baseEnd_7674801 < baseStart_7674801 := by decide
  rcases family_descends (prefixWord ++ tailWord_7674801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7674824 : List Nat := [2, 1, 3, 1, 5, 2, 1, 2, 6]
def baseStart_7674824 : Nat := 118140960795 + 7674824 * 2 ^ 59
def prefixEnd_7674824 : Nat := 4983230072969 + 3 ^ 40 * 7674824 * 2
def baseEnd_7674824 : Nat := 437874850073598383278237

theorem tailTrace_7674824 : CollatzResearch.WordTrace tailWord_7674824 prefixEnd_7674824 437874850073598383278237 := by
  unfold tailWord_7674824
  simp only [CollatzResearch.WordTrace]
  refine ⟨139961913973715439214863763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186615885298287252286485017 139961913973715439214863763)
  ·
    refine ⟨209942870960573158822295645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139961913973715439214863763 209942870960573158822295645)
    ·
      refine ⟨78728576610214934558360867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209942870960573158822295645 78728576610214934558360867)
      ·
        refine ⟨118092864915322401837541301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78728576610214934558360867 118092864915322401837541301)
        ·
          refine ⟨11071206085811475172269497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 118092864915322401837541301 11071206085811475172269497)
          ·
            refine ⟨8303404564358606379202123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11071206085811475172269497 8303404564358606379202123)
            ·
              refine ⟨12455106846537909568803185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8303404564358606379202123 12455106846537909568803185)
              ·
                refine ⟨9341330134903432176602389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12455106846537909568803185 9341330134903432176602389)
                ·
                  refine ⟨437874850073598383278237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9341330134903432176602389 437874850073598383278237)
                  ·
                    rfl

theorem cell23_7674824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 2, 6].length) (baseStart_7674824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7674824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7674824 prefixEnd_7674824 := by exact prefixLift 7674824
  have htrace : WordTrace (prefixWord ++ tailWord_7674824) baseStart_7674824 baseEnd_7674824 := by
    simpa [prefixWord, tailWord_7674824, baseEnd_7674824] using wordTrace_append hprefix tailTrace_7674824
  have hstable : (prefixWord ++ tailWord_7674824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7674824).length < 2 ^ (prefixWord ++ tailWord_7674824).sum := by decide
  have hdescent : baseEnd_7674824 < baseStart_7674824 := by decide
  rcases family_descends (prefixWord ++ tailWord_7674824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7674874 : List Nat := [3, 1, 1, 1, 1, 2, 1, 4, 5, 2, 2]
def baseStart_7674874 : Nat := 118140960795 + 7674874 * 2 ^ 59
def prefixEnd_7674874 : Nat := 4983230072969 + 3 ^ 40 * 7674874 * 2
def baseEnd_7674874 : Nat := 3940899324695110253878903

theorem tailTrace_7674874 : CollatzResearch.WordTrace tailWord_7674874 prefixEnd_7674874 3940899324695110253878903 := by
  unfold tailWord_7674874
  simp only [CollatzResearch.WordTrace]
  refine ⟨69981412899312434242261919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186617101064833157979365117 69981412899312434242261919)
  ·
    refine ⟨104972119348968651363392879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69981412899312434242261919 104972119348968651363392879)
    ·
      refine ⟨157458179023452977045089319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104972119348968651363392879 157458179023452977045089319)
      ·
        refine ⟨236187268535179465567633979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157458179023452977045089319 236187268535179465567633979)
        ·
          refine ⟨354280902802769198351450969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236187268535179465567633979 354280902802769198351450969)
          ·
            refine ⟨265710677102076898763588227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 354280902802769198351450969 265710677102076898763588227)
            ·
              refine ⟨398566015653115348145382341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265710677102076898763588227 398566015653115348145382341)
              ·
                refine ⟨74731127934959127777259189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 398566015653115348145382341 74731127934959127777259189)
                ·
                  refine ⟨7006043243902418229118049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74731127934959127777259189 7006043243902418229118049)
                  ·
                    refine ⟨5254532432926813671838537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7006043243902418229118049 5254532432926813671838537)
                    ·
                      refine ⟨3940899324695110253878903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5254532432926813671838537 3940899324695110253878903)
                      ·
                        rfl

theorem cell23_7674874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 5, 2, 2].length) (baseStart_7674874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7674874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7674874 prefixEnd_7674874 := by exact prefixLift 7674874
  have htrace : WordTrace (prefixWord ++ tailWord_7674874) baseStart_7674874 baseEnd_7674874 := by
    simpa [prefixWord, tailWord_7674874, baseEnd_7674874] using wordTrace_append hprefix tailTrace_7674874
  have hstable : (prefixWord ++ tailWord_7674874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7674874).length < 2 ^ (prefixWord ++ tailWord_7674874).sum := by decide
  have hdescent : baseEnd_7674874 < baseStart_7674874 := by decide
  rcases family_descends (prefixWord ++ tailWord_7674874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7674877 : List Nat := [1, 4, 1, 1, 1, 2, 1, 2, 5, 2, 3]
def baseStart_7674877 : Nat := 118140960795 + 7674877 * 2 ^ 59
def prefixEnd_7674877 : Nat := 4983230072969 + 3 ^ 40 * 7674877 * 2
def baseEnd_7674877 : Nat := 3940900865137073742141389

theorem tailTrace_7674877 : CollatzResearch.WordTrace tailWord_7674877 prefixEnd_7674877 3940900865137073742141389 := by
  unfold tailWord_7674877
  simp only [CollatzResearch.WordTrace]
  refine ⟨279925761016238868481406885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186617174010825912320937923 279925761016238868481406885)
  ·
    refine ⟨52486080190544787840263791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 279925761016238868481406885 52486080190544787840263791)
    ·
      refine ⟨78729120285817181760395687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52486080190544787840263791 78729120285817181760395687)
      ·
        refine ⟨118093680428725772640593531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78729120285817181760395687 118093680428725772640593531)
        ·
          refine ⟨177140520643088658960890297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118093680428725772640593531 177140520643088658960890297)
          ·
            refine ⟨132855390482316494220667723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177140520643088658960890297 132855390482316494220667723)
            ·
              refine ⟨199283085723474741331001585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132855390482316494220667723 199283085723474741331001585)
              ·
                refine ⟨149462314292606055998251189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 199283085723474741331001585 149462314292606055998251189)
                ·
                  refine ⟨14012091964931817749836049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 149462314292606055998251189 14012091964931817749836049)
                  ·
                    refine ⟨10509068973698863312377037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14012091964931817749836049 10509068973698863312377037)
                    ·
                      refine ⟨3940900865137073742141389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10509068973698863312377037 3940900865137073742141389)
                      ·
                        rfl

theorem cell23_7674877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 5, 2, 3].length) (baseStart_7674877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7674877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7674877 prefixEnd_7674877 := by exact prefixLift 7674877
  have htrace : WordTrace (prefixWord ++ tailWord_7674877) baseStart_7674877 baseEnd_7674877 := by
    simpa [prefixWord, tailWord_7674877, baseEnd_7674877] using wordTrace_append hprefix tailTrace_7674877
  have hstable : (prefixWord ++ tailWord_7674877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7674877).length < 2 ^ (prefixWord ++ tailWord_7674877).sum := by decide
  have hdescent : baseEnd_7674877 < baseStart_7674877 := by decide
  rcases family_descends (prefixWord ++ tailWord_7674877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7674878 : List Nat := [4, 2, 2, 2, 2, 1, 1, 2, 2, 3, 2]
def baseStart_7674878 : Nat := 118140960795 + 7674878 * 2 ^ 59
def prefixEnd_7674878 : Nat := 4983230072969 + 3 ^ 40 * 7674878 * 2
def baseEnd_7674878 : Nat := 3940901378617728238228885

theorem tailTrace_7674878 : CollatzResearch.WordTrace tailWord_7674878 prefixEnd_7674878 3940901378617728238228885 := by
  unfold tailWord_7674878
  simp only [CollatzResearch.WordTrace]
  refine ⟨34990724686154405706524161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186617198326156830434795525 34990724686154405706524161)
  ·
    refine ⟨26243043514615804279893121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34990724686154405706524161 26243043514615804279893121)
    ·
      refine ⟨19682282635961853209919841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26243043514615804279893121 19682282635961853209919841)
      ·
        refine ⟨14761711976971389907439881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19682282635961853209919841 14761711976971389907439881)
        ·
          refine ⟨11071283982728542430579911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14761711976971389907439881 11071283982728542430579911)
          ·
            refine ⟨16606925974092813645869867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11071283982728542430579911 16606925974092813645869867)
            ·
              refine ⟨24910388961139220468804801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16606925974092813645869867 24910388961139220468804801)
              ·
                refine ⟨18682791720854415351603601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24910388961139220468804801 18682791720854415351603601)
                ·
                  refine ⟨14012093790640811513702701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18682791720854415351603601 14012093790640811513702701)
                  ·
                    refine ⟨5254535171490304317638513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14012093790640811513702701 5254535171490304317638513)
                    ·
                      refine ⟨3940901378617728238228885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5254535171490304317638513 3940901378617728238228885)
                      ·
                        rfl

theorem cell23_7674878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_7674878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7674878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7674878 prefixEnd_7674878 := by exact prefixLift 7674878
  have htrace : WordTrace (prefixWord ++ tailWord_7674878) baseStart_7674878 baseEnd_7674878 := by
    simpa [prefixWord, tailWord_7674878, baseEnd_7674878] using wordTrace_append hprefix tailTrace_7674878
  have hstable : (prefixWord ++ tailWord_7674878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7674878).length < 2 ^ (prefixWord ++ tailWord_7674878).sum := by decide
  have hdescent : baseEnd_7674878 < baseStart_7674878 := by decide
  rcases family_descends (prefixWord ++ tailWord_7674878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7674891 : List Nat := [1, 1, 1, 1, 6, 2, 3, 1, 3, 2, 2]
def baseStart_7674891 : Nat := 118140960795 + 7674891 * 2 ^ 59
def prefixEnd_7674891 : Nat := 4983230072969 + 3 ^ 40 * 7674891 * 2
def baseEnd_7674891 : Nat := 3940908053866236687366325

theorem tailTrace_7674891 : CollatzResearch.WordTrace tailWord_7674891 prefixEnd_7674891 3940908053866236687366325 := by
  unfold tailWord_7674891
  simp only [CollatzResearch.WordTrace]
  refine ⟨279926271638188148872416527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186617514425458765914944351 279926271638188148872416527)
  ·
    refine ⟨419889407457282223308624791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279926271638188148872416527 419889407457282223308624791)
    ·
      refine ⟨629834111185923334962937187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419889407457282223308624791 629834111185923334962937187)
      ·
        refine ⟨944751166778885002444405781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 629834111185923334962937187 944751166778885002444405781)
        ·
          refine ⟨44285210942760234489581521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 944751166778885002444405781 44285210942760234489581521)
          ·
            refine ⟨33213908207070175867186141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44285210942760234489581521 33213908207070175867186141)
            ·
              refine ⟨12455215577651315950194803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33213908207070175867186141 12455215577651315950194803)
              ·
                refine ⟨18682823366476973925292205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12455215577651315950194803 18682823366476973925292205)
                ·
                  refine ⟨7006058762428865221984577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18682823366476973925292205 7006058762428865221984577)
                  ·
                    refine ⟨5254544071821648916488433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7006058762428865221984577 5254544071821648916488433)
                    ·
                      refine ⟨3940908053866236687366325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5254544071821648916488433 3940908053866236687366325)
                      ·
                        rfl

theorem cell23_7674891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 1, 3, 2, 2].length) (baseStart_7674891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7674891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7674891 prefixEnd_7674891 := by exact prefixLift 7674891
  have htrace : WordTrace (prefixWord ++ tailWord_7674891) baseStart_7674891 baseEnd_7674891 := by
    simpa [prefixWord, tailWord_7674891, baseEnd_7674891] using wordTrace_append hprefix tailTrace_7674891
  have hstable : (prefixWord ++ tailWord_7674891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7674891).length < 2 ^ (prefixWord ++ tailWord_7674891).sum := by decide
  have hdescent : baseEnd_7674891 < baseStart_7674891 := by decide
  rcases family_descends (prefixWord ++ tailWord_7674891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7674901 : List Nat := [1, 3, 2, 1, 4, 1, 4, 1, 2, 4]
def baseStart_7674901 : Nat := 118140960795 + 7674901 * 2 ^ 59
def prefixEnd_7674901 : Nat := 4983230072969 + 3 ^ 40 * 7674901 * 2
def baseEnd_7674901 : Nat := 1313637729557593882747093

theorem tailTrace_7674901 : CollatzResearch.WordTrace tailWord_7674901 prefixEnd_7674901 1313637729557593882747093 := by
  unfold tailWord_7674901
  simp only [CollatzResearch.WordTrace]
  refine ⟨279926636368151920580280557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186617757578767947053520371 279926636368151920580280557)
  ·
    refine ⟨104972488638056970217605209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 279926636368151920580280557 104972488638056970217605209)
    ·
      refine ⟨78729366478542727663203907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104972488638056970217605209 78729366478542727663203907)
      ·
        refine ⟨118094049717814091494805861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78729366478542727663203907 118094049717814091494805861)
        ·
          refine ⟨22142634322090142155276099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118094049717814091494805861 22142634322090142155276099)
          ·
            refine ⟨33213951483135213232914149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22142634322090142155276099 33213951483135213232914149)
            ·
              refine ⟨6227615903087852481171403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33213951483135213232914149 6227615903087852481171403)
              ·
                refine ⟨9341423854631778721757105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6227615903087852481171403 9341423854631778721757105)
                ·
                  refine ⟨7006067890973834041317829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9341423854631778721757105 7006067890973834041317829)
                  ·
                    refine ⟨1313637729557593882747093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7006067890973834041317829 1313637729557593882747093)
                    ·
                      rfl

theorem cell23_7674901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 4, 1, 2, 4].length) (baseStart_7674901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7674901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7674901 prefixEnd_7674901 := by exact prefixLift 7674901
  have htrace : WordTrace (prefixWord ++ tailWord_7674901) baseStart_7674901 baseEnd_7674901 := by
    simpa [prefixWord, tailWord_7674901, baseEnd_7674901] using wordTrace_append hprefix tailTrace_7674901
  have hstable : (prefixWord ++ tailWord_7674901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7674901).length < 2 ^ (prefixWord ++ tailWord_7674901).sum := by decide
  have hdescent : baseEnd_7674901 < baseStart_7674901 := by decide
  rcases family_descends (prefixWord ++ tailWord_7674901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7674908 : List Nat := [2, 2, 3, 1, 5, 1, 1, 2, 1, 1, 4]
def baseStart_7674908 : Nat := 118140960795 + 7674908 * 2 ^ 59
def prefixEnd_7674908 : Nat := 4983230072969 + 3 ^ 40 * 7674908 * 2
def baseEnd_7674908 : Nat := 3940916783037363120853747

theorem tailTrace_7674908 : CollatzResearch.WordTrace tailWord_7674908 prefixEnd_7674908 3940916783037363120853747 := by
  unfold tailWord_7674908
  simp only [CollatzResearch.WordTrace]
  refine ⟨139963445839563280387892689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186617927786084373850523585 139963445839563280387892689)
  ·
    refine ⟨104972584379672460290919517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139963445839563280387892689 104972584379672460290919517)
    ·
      refine ⟨39364719142377172609094819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104972584379672460290919517 39364719142377172609094819)
      ·
        refine ⟨59047078713565758913642229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39364719142377172609094819 59047078713565758913642229)
        ·
          refine ⟨5535663629396789898153959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59047078713565758913642229 5535663629396789898153959)
          ·
            refine ⟨8303495444095184847230939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5535663629396789898153959 8303495444095184847230939)
            ·
              refine ⟨12455243166142777270846409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8303495444095184847230939 12455243166142777270846409)
              ·
                refine ⟨9341432374607082953134807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12455243166142777270846409 9341432374607082953134807)
                ·
                  refine ⟨14012148561910624429702211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9341432374607082953134807 14012148561910624429702211)
                  ·
                    refine ⟨21018222842865936644553317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14012148561910624429702211 21018222842865936644553317)
                    ·
                      refine ⟨3940916783037363120853747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21018222842865936644553317 3940916783037363120853747)
                      ·
                        rfl

theorem cell23_7674908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 2, 1, 1, 4].length) (baseStart_7674908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7674908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7674908 prefixEnd_7674908 := by exact prefixLift 7674908
  have htrace : WordTrace (prefixWord ++ tailWord_7674908) baseStart_7674908 baseEnd_7674908 := by
    simpa [prefixWord, tailWord_7674908, baseEnd_7674908] using wordTrace_append hprefix tailTrace_7674908
  have hstable : (prefixWord ++ tailWord_7674908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7674908).length < 2 ^ (prefixWord ++ tailWord_7674908).sum := by decide
  have hdescent : baseEnd_7674908 < baseStart_7674908 := by decide
  rcases family_descends (prefixWord ++ tailWord_7674908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7674911 : List Nat := [1, 1, 2, 4, 1, 5, 1, 2, 1, 2, 3]
def baseStart_7674911 : Nat := 118140960795 + 7674911 * 2 ^ 59
def prefixEnd_7674911 : Nat := 4983230072969 + 3 ^ 40 * 7674911 * 2
def baseEnd_7674911 : Nat := 3940918323479326609116233

theorem tailTrace_7674911 : CollatzResearch.WordTrace tailWord_7674911 prefixEnd_7674911 3940918323479326609116233 := by
  unfold tailWord_7674911
  simp only [CollatzResearch.WordTrace]
  refine ⟨279927001098115692288144587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186618000732077128192096391 279927001098115692288144587)
  ·
    refine ⟨419890501647173538432216881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279927001098115692288144587 419890501647173538432216881)
    ·
      refine ⟨314917876235380153824162661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 419890501647173538432216881 314917876235380153824162661)
      ·
        refine ⟨59047101794133778842030499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 314917876235380153824162661 59047101794133778842030499)
        ·
          refine ⟨88570652691200668263045749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59047101794133778842030499 88570652691200668263045749)
          ·
            refine ⟨8303498689800062649660539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 88570652691200668263045749 8303498689800062649660539)
            ·
              refine ⟨12455248034700093974490809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8303498689800062649660539 12455248034700093974490809)
              ·
                refine ⟨9341436026025070480868107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12455248034700093974490809 9341436026025070480868107)
                ·
                  refine ⟨14012154039037605721302161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9341436026025070480868107 14012154039037605721302161)
                  ·
                    refine ⟨10509115529278204290976621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14012154039037605721302161 10509115529278204290976621)
                    ·
                      refine ⟨3940918323479326609116233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10509115529278204290976621 3940918323479326609116233)
                      ·
                        rfl

theorem cell23_7674911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 2, 1, 2, 3].length) (baseStart_7674911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7674911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7674911 prefixEnd_7674911 := by exact prefixLift 7674911
  have htrace : WordTrace (prefixWord ++ tailWord_7674911) baseStart_7674911 baseEnd_7674911 := by
    simpa [prefixWord, tailWord_7674911, baseEnd_7674911] using wordTrace_append hprefix tailTrace_7674911
  have hstable : (prefixWord ++ tailWord_7674911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7674911).length < 2 ^ (prefixWord ++ tailWord_7674911).sum := by decide
  have hdescent : baseEnd_7674911 < baseStart_7674911 := by decide
  rcases family_descends (prefixWord ++ tailWord_7674911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7674941 : List Nat := [1, 4, 1, 3, 1, 2, 1, 4, 2, 1, 3]
def baseStart_7674941 : Nat := 118140960795 + 7674941 * 2 ^ 59
def prefixEnd_7674941 : Nat := 4983230072969 + 3 ^ 40 * 7674941 * 2
def baseEnd_7674941 : Nat := 3940933727898961491741095

theorem tailTrace_7674941 : CollatzResearch.WordTrace tailWord_7674941 prefixEnd_7674941 3940933727898961491741095 := by
  unfold tailWord_7674941
  simp only [CollatzResearch.WordTrace]
  refine ⟨279928095288007007411736677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186618730192004671607824451 279928095288007007411736677)
  ·
    refine ⟨52486517866501313889700627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 279928095288007007411736677 52486517866501313889700627)
    ·
      refine ⟨78729776799751970834550941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52486517866501313889700627 78729776799751970834550941)
      ·
        refine ⟨29523666299906989062956603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78729776799751970834550941 29523666299906989062956603)
        ·
          refine ⟨44285499449860483594434905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29523666299906989062956603 44285499449860483594434905)
          ·
            refine ⟨33214124587395362695826179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44285499449860483594434905 33214124587395362695826179)
            ·
              refine ⟨49821186881093044043739269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33214124587395362695826179 49821186881093044043739269)
              ·
                refine ⟨9341472540204945758201113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49821186881093044043739269 9341472540204945758201113)
                ·
                  refine ⟨7006104405153709318650835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9341472540204945758201113 7006104405153709318650835)
                  ·
                    refine ⟨10509156607730563977976253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7006104405153709318650835 10509156607730563977976253)
                    ·
                      refine ⟨3940933727898961491741095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10509156607730563977976253 3940933727898961491741095)
                      ·
                        rfl

theorem cell23_7674941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_7674941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7674941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7674941 prefixEnd_7674941 := by exact prefixLift 7674941
  have htrace : WordTrace (prefixWord ++ tailWord_7674941) baseStart_7674941 baseEnd_7674941 := by
    simpa [prefixWord, tailWord_7674941, baseEnd_7674941] using wordTrace_append hprefix tailTrace_7674941
  have hstable : (prefixWord ++ tailWord_7674941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7674941).length < 2 ^ (prefixWord ++ tailWord_7674941).sum := by decide
  have hdescent : baseEnd_7674941 < baseStart_7674941 := by decide
  rcases family_descends (prefixWord ++ tailWord_7674941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7674942 : List Nat := [4, 2, 1, 3, 1, 1, 4, 2, 1, 2, 2]
def baseStart_7674942 : Nat := 118140960795 + 7674942 * 2 ^ 59
def prefixEnd_7674942 : Nat := 4983230072969 + 3 ^ 40 * 7674942 * 2
def baseEnd_7674942 : Nat := 3940934241379615987828591

theorem tailTrace_7674942 : CollatzResearch.WordTrace tailWord_7674942 prefixEnd_7674942 3940934241379615987828591 := by
  unfold tailWord_7674942
  simp only [CollatzResearch.WordTrace]
  refine ⟨34991016470125423072815385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186618754507335589721682053 34991016470125423072815385)
  ·
    refine ⟨26243262352594067304611539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34991016470125423072815385 26243262352594067304611539)
    ·
      refine ⟨39364893528891100956917309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26243262352594067304611539 39364893528891100956917309)
      ·
        refine ⟨14761835073334162858843991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39364893528891100956917309 14761835073334162858843991)
        ·
          refine ⟨22142752610001244288265987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14761835073334162858843991 22142752610001244288265987)
          ·
            refine ⟨33214128915001866432398981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22142752610001244288265987 33214128915001866432398981)
            ·
              refine ⟨6227649171562849956074809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33214128915001866432398981 6227649171562849956074809)
              ·
                refine ⟨4670736878672137467056107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6227649171562849956074809 4670736878672137467056107)
                ·
                  refine ⟨7006105318008206200584161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4670736878672137467056107 7006105318008206200584161)
                  ·
                    refine ⟨5254578988506154650438121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7006105318008206200584161 5254578988506154650438121)
                    ·
                      refine ⟨3940934241379615987828591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5254578988506154650438121 3940934241379615987828591)
                      ·
                        rfl

theorem cell23_7674942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_7674942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7674942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7674942 prefixEnd_7674942 := by exact prefixLift 7674942
  have htrace : WordTrace (prefixWord ++ tailWord_7674942) baseStart_7674942 baseEnd_7674942 := by
    simpa [prefixWord, tailWord_7674942, baseEnd_7674942] using wordTrace_append hprefix tailTrace_7674942
  have hstable : (prefixWord ++ tailWord_7674942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7674942).length < 2 ^ (prefixWord ++ tailWord_7674942).sum := by decide
  have hdescent : baseEnd_7674942 < baseStart_7674942 := by decide
  rcases family_descends (prefixWord ++ tailWord_7674942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7674967 : List Nat := [1, 1, 3, 2, 2, 1, 1, 1, 4, 4, 3]
def baseStart_7674967 : Nat := 118140960795 + 7674967 * 2 ^ 59
def prefixEnd_7674967 : Nat := 4983230072969 + 3 ^ 40 * 7674967 * 2
def baseEnd_7674967 : Nat := 3940947078395978390015975

theorem tailTrace_7674967 : CollatzResearch.WordTrace tailWord_7674967 prefixEnd_7674967 3940947078395978390015975 := by
  unfold tailWord_7674967
  simp only [CollatzResearch.WordTrace]
  refine ⟨279929043585912813852183155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186619362390608542568122103 279929043585912813852183155)
  ·
    refine ⟨419893565378869220778274733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279929043585912813852183155 419893565378869220778274733)
    ·
      refine ⟨157460087017075957791853025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 419893565378869220778274733 157460087017075957791853025)
      ·
        refine ⟨118095065262806968343889769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157460087017075957791853025 118095065262806968343889769)
        ·
          refine ⟨88571298947105226257917327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118095065262806968343889769 88571298947105226257917327)
          ·
            refine ⟨132856948420657839386875991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88571298947105226257917327 132856948420657839386875991)
            ·
              refine ⟨199285422630986759080313987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132856948420657839386875991 199285422630986759080313987)
              ·
                refine ⟨298928133946480138620470981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199285422630986759080313987 298928133946480138620470981)
                ·
                  refine ⟨56049025114965025991338309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 298928133946480138620470981 56049025114965025991338309)
                  ·
                    refine ⟨10509192209055942373375933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56049025114965025991338309 10509192209055942373375933)
                    ·
                      refine ⟨3940947078395978390015975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10509192209055942373375933 3940947078395978390015975)
                      ·
                        rfl

theorem cell23_7674967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 4, 4, 3].length) (baseStart_7674967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7674967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7674967 prefixEnd_7674967 := by exact prefixLift 7674967
  have htrace : WordTrace (prefixWord ++ tailWord_7674967) baseStart_7674967 baseEnd_7674967 := by
    simpa [prefixWord, tailWord_7674967, baseEnd_7674967] using wordTrace_append hprefix tailTrace_7674967
  have hstable : (prefixWord ++ tailWord_7674967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7674967).length < 2 ^ (prefixWord ++ tailWord_7674967).sum := by decide
  have hdescent : baseEnd_7674967 < baseStart_7674967 := by decide
  rcases family_descends (prefixWord ++ tailWord_7674967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7674981 : List Nat := [1, 3, 1, 3, 2, 1, 2, 2, 4, 2, 2]
def baseStart_7674981 : Nat := 118140960795 + 7674981 * 2 ^ 59
def prefixEnd_7674981 : Nat := 4983230072969 + 3 ^ 40 * 7674981 * 2
def baseEnd_7674981 : Nat := 3940954267125141335240911

theorem tailTrace_7674981 : CollatzResearch.WordTrace tailWord_7674981 prefixEnd_7674981 3940954267125141335240911 := by
  unfold tailWord_7674981
  simp only [CollatzResearch.WordTrace]
  refine ⟨279929554207862094243192797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186619702805241396162128531 279929554207862094243192797)
  ·
    refine ⟨104973582827948285341197299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 279929554207862094243192797 104973582827948285341197299)
    ·
      refine ⟨157460374241922428011795949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104973582827948285341197299 157460374241922428011795949)
      ·
        refine ⟨59047640340720910504423481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157460374241922428011795949 59047640340720910504423481)
        ·
          refine ⟨44285730255540682878317611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59047640340720910504423481 44285730255540682878317611)
          ·
            refine ⟨66428595383311024317476417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44285730255540682878317611 66428595383311024317476417)
            ·
              refine ⟨49821446537483268238107313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66428595383311024317476417 49821446537483268238107313)
              ·
                refine ⟨37366084903112451178580485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49821446537483268238107313 37366084903112451178580485)
                ·
                  refine ⟨7006140919333584595983841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37366084903112451178580485 7006140919333584595983841)
                  ·
                    refine ⟨5254605689500188446987881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7006140919333584595983841 5254605689500188446987881)
                    ·
                      refine ⟨3940954267125141335240911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5254605689500188446987881 3940954267125141335240911)
                      ·
                        rfl

theorem cell23_7674981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 2, 4, 2, 2].length) (baseStart_7674981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7674981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7674981 prefixEnd_7674981 := by exact prefixLift 7674981
  have htrace : WordTrace (prefixWord ++ tailWord_7674981) baseStart_7674981 baseEnd_7674981 := by
    simpa [prefixWord, tailWord_7674981, baseEnd_7674981] using wordTrace_append hprefix tailTrace_7674981
  have hstable : (prefixWord ++ tailWord_7674981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7674981).length < 2 ^ (prefixWord ++ tailWord_7674981).sum := by decide
  have hdescent : baseEnd_7674981 < baseStart_7674981 := by decide
  rcases family_descends (prefixWord ++ tailWord_7674981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7674998 : List Nat := [5, 1, 1, 2, 1, 1, 3, 1, 4, 2, 2]
def baseStart_7674998 : Nat := 118140960795 + 7674998 * 2 ^ 59
def prefixEnd_7674998 : Nat := 4983230072969 + 3 ^ 40 * 7674998 * 2
def baseEnd_7674998 : Nat := 3940962996296267768728333

theorem tailTrace_7674998 : CollatzResearch.WordTrace tailWord_7674998 prefixEnd_7674998 3940962996296267768728333 := by
  unfold tailWord_7674998
  simp only [CollatzResearch.WordTrace]
  refine ⟨17495635890550031634160103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 186620116165867004097707765 17495635890550031634160103)
  ·
    refine ⟨26243453835825047451240155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17495635890550031634160103 26243453835825047451240155)
    ·
      refine ⟨39365180753737571176860233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26243453835825047451240155 39365180753737571176860233)
      ·
        refine ⟨29523885565303178382645175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39365180753737571176860233 29523885565303178382645175)
        ·
          refine ⟨44285828347954767573967763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29523885565303178382645175 44285828347954767573967763)
          ·
            refine ⟨66428742521932151360951645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44285828347954767573967763 66428742521932151360951645)
            ·
              refine ⟨24910778445724556760356867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66428742521932151360951645 24910778445724556760356867)
              ·
                refine ⟨37366167668586835140535301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24910778445724556760356867 37366167668586835140535301)
                ·
                  refine ⟨7006156437860031588850369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37366167668586835140535301 7006156437860031588850369)
                  ·
                    refine ⟨5254617328395023691637777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7006156437860031588850369 5254617328395023691637777)
                    ·
                      refine ⟨3940962996296267768728333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5254617328395023691637777 3940962996296267768728333)
                      ·
                        rfl

theorem cell23_7674998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 1, 4, 2, 2].length) (baseStart_7674998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7674998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7674998 prefixEnd_7674998 := by exact prefixLift 7674998
  have htrace : WordTrace (prefixWord ++ tailWord_7674998) baseStart_7674998 baseEnd_7674998 := by
    simpa [prefixWord, tailWord_7674998, baseEnd_7674998] using wordTrace_append hprefix tailTrace_7674998
  have hstable : (prefixWord ++ tailWord_7674998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7674998).length < 2 ^ (prefixWord ++ tailWord_7674998).sum := by decide
  have hdescent : baseEnd_7674998 < baseStart_7674998 := by decide
  rcases family_descends (prefixWord ++ tailWord_7674998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7675004 : List Nat := [2, 2, 2, 1, 1, 3, 1, 6, 5]
def baseStart_7675004 : Nat := 118140960795 + 7675004 * 2 ^ 59
def prefixEnd_7675004 : Nat := 4983230072969 + 3 ^ 40 * 7675004 * 2
def baseEnd_7675004 : Nat := 437885119686688305028145

theorem tailTrace_7675004 : CollatzResearch.WordTrace tailWord_7675004 prefixEnd_7675004 437885119686688305028145 := by
  unfold tailWord_7675004
  simp only [CollatzResearch.WordTrace]
  refine ⟨139965196543389384585640033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186620262057852512780853377 139965196543389384585640033)
  ·
    refine ⟨104973897407542038439230025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139965196543389384585640033 104973897407542038439230025)
    ·
      refine ⟨78730423055656528829422519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104973897407542038439230025 78730423055656528829422519)
      ·
        refine ⟨118095634583484793244133779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78730423055656528829422519 118095634583484793244133779)
        ·
          refine ⟨177143451875227189866200669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118095634583484793244133779 177143451875227189866200669)
          ·
            refine ⟨66428794453210196199825251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177143451875227189866200669 66428794453210196199825251)
            ·
              refine ⟨99643191679815294299737877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66428794453210196199825251 99643191679815294299737877)
              ·
                refine ⟨4670774609991341920300213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 99643191679815294299737877 4670774609991341920300213)
                ·
                  refine ⟨437885119686688305028145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4670774609991341920300213 437885119686688305028145)
                  ·
                    rfl

theorem cell23_7675004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 6, 5].length) (baseStart_7675004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7675004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7675004 prefixEnd_7675004 := by exact prefixLift 7675004
  have htrace : WordTrace (prefixWord ++ tailWord_7675004) baseStart_7675004 baseEnd_7675004 := by
    simpa [prefixWord, tailWord_7675004, baseEnd_7675004] using wordTrace_append hprefix tailTrace_7675004
  have hstable : (prefixWord ++ tailWord_7675004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7675004).length < 2 ^ (prefixWord ++ tailWord_7675004).sum := by decide
  have hdescent : baseEnd_7675004 < baseStart_7675004 := by decide
  rcases family_descends (prefixWord ++ tailWord_7675004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7675017 : List Nat := [1, 2, 1, 1, 4, 3, 1, 2, 1, 7]
def baseStart_7675017 : Nat := 118140960795 + 7675017 * 2 ^ 59
def prefixEnd_7675017 : Nat := 4983230072969 + 3 ^ 40 * 7675017 * 2
def baseEnd_7675017 : Nat := 1313657584142901064796915

theorem tailTrace_7675017 : CollatzResearch.WordTrace tailWord_7675017 prefixEnd_7675017 1313657584142901064796915 := by
  unfold tailWord_7675017
  simp only [CollatzResearch.WordTrace]
  refine ⟨279930867235731672391503305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186620578157154448261002203 279930867235731672391503305)
  ·
    refine ⟨209948150426798754293627479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279930867235731672391503305 209948150426798754293627479)
    ·
      refine ⟨314922225640198131440441219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209948150426798754293627479 314922225640198131440441219)
      ·
        refine ⟨472383338460297197160661829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314922225640198131440441219 472383338460297197160661829)
        ·
          refine ⟨88571875961305724467624093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 472383338460297197160661829 88571875961305724467624093)
          ·
            refine ⟨33214453485489646675359035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88571875961305724467624093 33214453485489646675359035)
            ·
              refine ⟨49821680228234470013038553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33214453485489646675359035 49821680228234470013038553)
              ·
                refine ⟨37366260171175852509778915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49821680228234470013038553 37366260171175852509778915)
                ·
                  refine ⟨56049390256763778764668373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37366260171175852509778915 56049390256763778764668373)
                  ·
                    refine ⟨1313657584142901064796915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56049390256763778764668373 1313657584142901064796915)
                    ·
                      rfl

theorem cell23_7675017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 2, 1, 7].length) (baseStart_7675017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7675017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7675017 prefixEnd_7675017 := by exact prefixLift 7675017
  have htrace : WordTrace (prefixWord ++ tailWord_7675017) baseStart_7675017 baseEnd_7675017 := by
    simpa [prefixWord, tailWord_7675017, baseEnd_7675017] using wordTrace_append hprefix tailTrace_7675017
  have hstable : (prefixWord ++ tailWord_7675017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7675017).length < 2 ^ (prefixWord ++ tailWord_7675017).sum := by decide
  have hdescent : baseEnd_7675017 < baseStart_7675017 := by decide
  rcases family_descends (prefixWord ++ tailWord_7675017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7675034 : List Nat := [3, 1, 1, 5, 1, 1, 2, 1, 1, 7]
def baseStart_7675034 : Nat := 118140960795 + 7675034 * 2 ^ 59
def prefixEnd_7675034 : Nat := 4983230072969 + 3 ^ 40 * 7675034 * 2
def baseEnd_7675034 : Nat := 1313660493866609875959389

theorem tailTrace_7675034 : CollatzResearch.WordTrace tailWord_7675034 prefixEnd_7675034 1313660493866609875959389 := by
  unfold tailWord_7675034
  simp only [CollatzResearch.WordTrace]
  refine ⟨69982871819167521073718039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186620991517780056196581437 69982871819167521073718039)
  ·
    refine ⟨104974307728751281610577059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69982871819167521073718039 104974307728751281610577059)
    ·
      refine ⟨157461461593126922415865589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104974307728751281610577059 157461461593126922415865589)
      ·
        refine ⟨14762012024355648976487399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 157461461593126922415865589 14762012024355648976487399)
        ·
          refine ⟨22143018036533473464731099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14762012024355648976487399 22143018036533473464731099)
          ·
            refine ⟨33214527054800210197096649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22143018036533473464731099 33214527054800210197096649)
            ·
              refine ⟨24910895291100157647822487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33214527054800210197096649 24910895291100157647822487)
              ·
                refine ⟨37366342936650236471733731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24910895291100157647822487 37366342936650236471733731)
                ·
                  refine ⟨56049514404975354707600597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37366342936650236471733731 56049514404975354707600597)
                  ·
                    refine ⟨1313660493866609875959389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56049514404975354707600597 1313660493866609875959389)
                    ·
                      rfl

theorem cell23_7675034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 1, 1, 7].length) (baseStart_7675034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7675034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7675034 prefixEnd_7675034 := by exact prefixLift 7675034
  have htrace : WordTrace (prefixWord ++ tailWord_7675034) baseStart_7675034 baseEnd_7675034 := by
    simpa [prefixWord, tailWord_7675034, baseEnd_7675034] using wordTrace_append hprefix tailTrace_7675034
  have hstable : (prefixWord ++ tailWord_7675034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7675034).length < 2 ^ (prefixWord ++ tailWord_7675034).sum := by decide
  have hdescent : baseEnd_7675034 < baseStart_7675034 := by decide
  rcases family_descends (prefixWord ++ tailWord_7675034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7675038 : List Nat := [4, 3, 1, 1, 2, 1, 3, 3, 5]
def baseStart_7675038 : Nat := 118140960795 + 7675038 * 2 ^ 59
def prefixEnd_7675038 : Nat := 4983230072969 + 3 ^ 40 * 7675038 * 2
def baseEnd_7675038 : Nat := 437887059502494179136461

theorem tailTrace_7675038 : CollatzResearch.WordTrace tailWord_7675038 prefixEnd_7675038 437887059502494179136461 := by
  unfold tailWord_7675038
  simp only [CollatzResearch.WordTrace]
  refine ⟨34991454146081949122252221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186621088779103728652011845 34991454146081949122252221)
  ·
    refine ⟨13121795304780730920844583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34991454146081949122252221 13121795304780730920844583)
    ·
      refine ⟨19682692957171096381266875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13121795304780730920844583 19682692957171096381266875)
      ·
        refine ⟨29524039435756644571900313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19682692957171096381266875 29524039435756644571900313)
        ·
          refine ⟨22143029576817483428925235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29524039435756644571900313 22143029576817483428925235)
          ·
            refine ⟨33214544365226225143387853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22143029576817483428925235 33214544365226225143387853)
            ·
              refine ⟨12455454136959834428770445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33214544365226225143387853 12455454136959834428770445)
              ·
                refine ⟨4670795301359937910788917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12455454136959834428770445 4670795301359937910788917)
                ·
                  refine ⟨437887059502494179136461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4670795301359937910788917 437887059502494179136461)
                  ·
                    rfl

theorem cell23_7675038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 3, 5].length) (baseStart_7675038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7675038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7675038 prefixEnd_7675038 := by exact prefixLift 7675038
  have htrace : WordTrace (prefixWord ++ tailWord_7675038) baseStart_7675038 baseEnd_7675038 := by
    simpa [prefixWord, tailWord_7675038, baseEnd_7675038] using wordTrace_append hprefix tailTrace_7675038
  have hstable : (prefixWord ++ tailWord_7675038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7675038).length < 2 ^ (prefixWord ++ tailWord_7675038).sum := by decide
  have hdescent : baseEnd_7675038 < baseStart_7675038 := by decide
  rcases family_descends (prefixWord ++ tailWord_7675038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7675064 : List Nat := [2, 1, 2, 1, 2, 1, 2, 5, 3, 4]
def baseStart_7675064 : Nat := 118140960795 + 7675064 * 2 ^ 59
def prefixEnd_7675064 : Nat := 4983230072969 + 3 ^ 40 * 7675064 * 2
def baseEnd_7675064 : Nat := 1313665628673154836834343

theorem tailTrace_7675064 : CollatzResearch.WordTrace tailWord_7675064 prefixEnd_7675064 1313665628673154836834343 := by
  unfold tailWord_7675064
  simp only [CollatzResearch.WordTrace]
  refine ⟨139966290733280699709232123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186621720977707599612309497 139966290733280699709232123)
  ·
    refine ⟨209949436099921049563848185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139966290733280699709232123 209949436099921049563848185)
    ·
      refine ⟨157462077074940787172886139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209949436099921049563848185 157462077074940787172886139)
      ·
        refine ⟨236193115612411180759329209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157462077074940787172886139 236193115612411180759329209)
        ·
          refine ⟨177144836709308385569496907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236193115612411180759329209 177144836709308385569496907)
          ·
            refine ⟨265717255063962578354245361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177144836709308385569496907 265717255063962578354245361)
            ·
              refine ⟨199287941297971933765684021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 265717255063962578354245361 199287941297971933765684021)
              ·
                refine ⟨18683244496684868790532877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 199287941297971933765684021 18683244496684868790532877)
                ·
                  refine ⟨7006216686256825796449829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18683244496684868790532877 7006216686256825796449829)
                  ·
                    refine ⟨1313665628673154836834343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7006216686256825796449829 1313665628673154836834343)
                    ·
                      rfl

theorem cell23_7675064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 5, 3, 4].length) (baseStart_7675064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7675064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7675064 prefixEnd_7675064 := by exact prefixLift 7675064
  have htrace : WordTrace (prefixWord ++ tailWord_7675064) baseStart_7675064 baseEnd_7675064 := by
    simpa [prefixWord, tailWord_7675064, baseEnd_7675064] using wordTrace_append hprefix tailTrace_7675064
  have hstable : (prefixWord ++ tailWord_7675064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7675064).length < 2 ^ (prefixWord ++ tailWord_7675064).sum := by decide
  have hdescent : baseEnd_7675064 < baseStart_7675064 := by decide
  rcases family_descends (prefixWord ++ tailWord_7675064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7675067 : List Nat := [1, 1, 1, 1, 1, 2, 4, 2, 2, 4, 4]
def baseStart_7675067 : Nat := 118140960795 + 7675067 * 2 ^ 59
def prefixEnd_7675067 : Nat := 4983230072969 + 3 ^ 40 * 7675067 * 2
def baseEnd_7675067 : Nat := 3940998426461427998765515

theorem tailTrace_7675067 : CollatzResearch.WordTrace tailWord_7675067 prefixEnd_7675067 3940998426461427998765515 := by
  unfold tailWord_7675067
  simp only [CollatzResearch.WordTrace]
  refine ⟨279932690885550530930823455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186621793923700353953882303 279932690885550530930823455)
  ·
    refine ⟨419899036328325796396235183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279932690885550530930823455 419899036328325796396235183)
    ·
      refine ⟨629848554492488694594352775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419899036328325796396235183 629848554492488694594352775)
      ·
        refine ⟨944772831738733041891529163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 629848554492488694594352775 944772831738733041891529163)
        ·
          refine ⟨1417159247608099562837293745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 944772831738733041891529163 1417159247608099562837293745)
          ·
            refine ⟨1062869435706074672127970309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1417159247608099562837293745 1062869435706074672127970309)
            ·
              refine ⟨199288019194889001023994433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1062869435706074672127970309 199288019194889001023994433)
              ·
                refine ⟨149466014396166750767995825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 199288019194889001023994433 149466014396166750767995825)
                ·
                  refine ⟨112099510797125063075996869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 149466014396166750767995825 112099510797125063075996869)
                  ·
                    refine ⟨21018658274460949326749413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 112099510797125063075996869 21018658274460949326749413)
                    ·
                      refine ⟨3940998426461427998765515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21018658274460949326749413 3940998426461427998765515)
                      ·
                        rfl

theorem cell23_7675067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 4, 4].length) (baseStart_7675067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7675067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7675067 prefixEnd_7675067 := by exact prefixLift 7675067
  have htrace : WordTrace (prefixWord ++ tailWord_7675067) baseStart_7675067 baseEnd_7675067 := by
    simpa [prefixWord, tailWord_7675067, baseEnd_7675067] using wordTrace_append hprefix tailTrace_7675067
  have hstable : (prefixWord ++ tailWord_7675067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7675067).length < 2 ^ (prefixWord ++ tailWord_7675067).sum := by decide
  have hdescent : baseEnd_7675067 < baseStart_7675067 := by decide
  rcases family_descends (prefixWord ++ tailWord_7675067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7675085 : List Nat := [1, 6, 2, 2, 1, 1, 2, 1, 2, 5]
def baseStart_7675085 : Nat := 118140960795 + 7675085 * 2 ^ 59
def prefixEnd_7675085 : Nat := 4983230072969 + 3 ^ 40 * 7675085 * 2
def baseEnd_7675085 : Nat := 1313669223037736309446811

theorem tailTrace_7675085 : CollatzResearch.WordTrace tailWord_7675085 prefixEnd_7675085 1313669223037736309446811 := by
  unfold tailWord_7675085
  simp only [CollatzResearch.WordTrace]
  refine ⟨279933347399485320004978709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186622231599656880003319139 279933347399485320004978709)
  ·
    refine ⟨13121875659350874375233377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 279933347399485320004978709 13121875659350874375233377)
    ·
      refine ⟨9841406744513155781425033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13121875659350874375233377 9841406744513155781425033)
      ·
        refine ⟨7381055058384866836068775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9841406744513155781425033 7381055058384866836068775)
        ·
          refine ⟨11071582587577300254103163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7381055058384866836068775 11071582587577300254103163)
          ·
            refine ⟨16607373881365950381154745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11071582587577300254103163 16607373881365950381154745)
            ·
              refine ⟨12455530411024462785866059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16607373881365950381154745 12455530411024462785866059)
              ·
                refine ⟨18683295616536694178799089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12455530411024462785866059 18683295616536694178799089)
                ·
                  refine ⟨14012471712402520634099317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18683295616536694178799089 14012471712402520634099317)
                  ·
                    refine ⟨1313669223037736309446811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14012471712402520634099317 1313669223037736309446811)
                    ·
                      rfl

theorem cell23_7675085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_7675085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7675085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7675085 prefixEnd_7675085 := by exact prefixLift 7675085
  have htrace : WordTrace (prefixWord ++ tailWord_7675085) baseStart_7675085 baseEnd_7675085 := by
    simpa [prefixWord, tailWord_7675085, baseEnd_7675085] using wordTrace_append hprefix tailTrace_7675085
  have hstable : (prefixWord ++ tailWord_7675085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7675085).length < 2 ^ (prefixWord ++ tailWord_7675085).sum := by decide
  have hdescent : baseEnd_7675085 < baseStart_7675085 := by decide
  rcases family_descends (prefixWord ++ tailWord_7675085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7675097 : List Nat := [1, 2, 1, 2, 3, 1, 1, 2, 1, 1, 8]
def baseStart_7675097 : Nat := 118140960795 + 7675097 * 2 ^ 59
def prefixEnd_7675097 : Nat := 4983230072969 + 3 ^ 40 * 7675097 * 2
def baseEnd_7675097 : Nat := 3941013830881062881390377

theorem tailTrace_7675097 : CollatzResearch.WordTrace tailWord_7675097 prefixEnd_7675097 3941013830881062881390377 := by
  unfold tailWord_7675097
  simp only [CollatzResearch.WordTrace]
  refine ⟨279933785075441846054415545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186622523383627897369610363 279933785075441846054415545)
  ·
    refine ⟨209950338806581384540811659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279933785075441846054415545 209950338806581384540811659)
    ·
      refine ⟨314925508209872076811217489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209950338806581384540811659 314925508209872076811217489)
      ·
        refine ⟨236194131157404057608413117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 314925508209872076811217489 236194131157404057608413117)
        ·
          refine ⟨88572799184026521603154919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 236194131157404057608413117 88572799184026521603154919)
          ·
            refine ⟨132859198776039782404732379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88572799184026521603154919 132859198776039782404732379)
            ·
              refine ⟨199288798164059673607098569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132859198776039782404732379 199288798164059673607098569)
              ·
                refine ⟨149466598623044755205323927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 199288798164059673607098569 149466598623044755205323927)
                ·
                  refine ⟨224199897934567132807985891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 149466598623044755205323927 224199897934567132807985891)
                  ·
                    refine ⟨336299846901850699211978837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 224199897934567132807985891 336299846901850699211978837)
                    ·
                      refine ⟨3941013830881062881390377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 336299846901850699211978837 3941013830881062881390377)
                      ·
                        rfl

theorem cell23_7675097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 1, 8].length) (baseStart_7675097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7675097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7675097 prefixEnd_7675097 := by exact prefixLift 7675097
  have htrace : WordTrace (prefixWord ++ tailWord_7675097) baseStart_7675097 baseEnd_7675097 := by
    simpa [prefixWord, tailWord_7675097, baseEnd_7675097] using wordTrace_append hprefix tailTrace_7675097
  have hstable : (prefixWord ++ tailWord_7675097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7675097).length < 2 ^ (prefixWord ++ tailWord_7675097).sum := by decide
  have hdescent : baseEnd_7675097 < baseStart_7675097 := by decide
  rcases family_descends (prefixWord ++ tailWord_7675097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7675115 : List Nat := [1, 1, 1, 1, 2, 8, 2, 2, 1, 4]
def baseStart_7675115 : Nat := 118140960795 + 7675115 * 2 ^ 59
def prefixEnd_7675115 : Nat := 4983230072969 + 3 ^ 40 * 7675115 * 2
def baseEnd_7675115 : Nat := 1313674357844281270321765

theorem tailTrace_7675115 : CollatzResearch.WordTrace tailWord_7675115 prefixEnd_7675115 1313674357844281270321765 := by
  unfold tailWord_7675115
  simp only [CollatzResearch.WordTrace]
  refine ⟨279934441589376635128570799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186622961059584423419047199 279934441589376635128570799)
  ·
    refine ⟨419901662384064952692856199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279934441589376635128570799 419901662384064952692856199)
    ·
      refine ⟨629852493576097429039284299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419901662384064952692856199 629852493576097429039284299)
      ·
        refine ⟨944778740364146143558926449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 629852493576097429039284299 944778740364146143558926449)
        ·
          refine ⟨708584055273109607669194837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 944778740364146143558926449 708584055273109607669194837)
          ·
            refine ⟨8303719397731753214873377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 708584055273109607669194837 8303719397731753214873377)
            ·
              refine ⟨6227789548298814911155033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8303719397731753214873377 6227789548298814911155033)
              ·
                refine ⟨4670842161224111183366275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6227789548298814911155033 4670842161224111183366275)
                ·
                  refine ⟨7006263241836166775049413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4670842161224111183366275 7006263241836166775049413)
                  ·
                    refine ⟨1313674357844281270321765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7006263241836166775049413 1313674357844281270321765)
                    ·
                      rfl

theorem cell23_7675115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 2, 2, 1, 4].length) (baseStart_7675115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7675115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7675115 prefixEnd_7675115 := by exact prefixLift 7675115
  have htrace : WordTrace (prefixWord ++ tailWord_7675115) baseStart_7675115 baseEnd_7675115 := by
    simpa [prefixWord, tailWord_7675115, baseEnd_7675115] using wordTrace_append hprefix tailTrace_7675115
  have hstable : (prefixWord ++ tailWord_7675115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7675115).length < 2 ^ (prefixWord ++ tailWord_7675115).sum := by decide
  have hdescent : baseEnd_7675115 < baseStart_7675115 := by decide
  rcases family_descends (prefixWord ++ tailWord_7675115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7675121 : List Nat := [1, 2, 2, 2, 2, 1, 1, 5, 3, 1, 3]
def baseStart_7675121 : Nat := 118140960795 + 7675121 * 2 ^ 59
def prefixEnd_7675121 : Nat := 4983230072969 + 3 ^ 40 * 7675121 * 2
def baseEnd_7675121 : Nat := 3941026154416770787490267

theorem tailTrace_7675121 : CollatzResearch.WordTrace tailWord_7675121 prefixEnd_7675121 3941026154416770787490267 := by
  unfold tailWord_7675121
  simp only [CollatzResearch.WordTrace]
  refine ⟨279934660427354898153289217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186623106951569932102192811 279934660427354898153289217)
  ·
    refine ⟨209950995320516173614966913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279934660427354898153289217 209950995320516173614966913)
    ·
      refine ⟨157463246490387130211225185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209950995320516173614966913 157463246490387130211225185)
      ·
        refine ⟨118097434867790347658418889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157463246490387130211225185 118097434867790347658418889)
        ·
          refine ⟨88573076150842760743814167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118097434867790347658418889 88573076150842760743814167)
          ·
            refine ⟨132859614226264141115721251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88573076150842760743814167 132859614226264141115721251)
            ·
              refine ⟨199289421339396211673581877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132859614226264141115721251 199289421339396211673581877)
              ·
                refine ⟨18683383250568394844398301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 199289421339396211673581877 18683383250568394844398301)
                ·
                  refine ⟨7006268718963148066649363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18683383250568394844398301 7006268718963148066649363)
                  ·
                    refine ⟨10509403078444722099974045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7006268718963148066649363 10509403078444722099974045)
                    ·
                      refine ⟨3941026154416770787490267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10509403078444722099974045 3941026154416770787490267)
                      ·
                        rfl

theorem cell23_7675121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 5, 3, 1, 3].length) (baseStart_7675121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7675121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7675121 prefixEnd_7675121 := by exact prefixLift 7675121
  have htrace : WordTrace (prefixWord ++ tailWord_7675121) baseStart_7675121 baseEnd_7675121 := by
    simpa [prefixWord, tailWord_7675121, baseEnd_7675121] using wordTrace_append hprefix tailTrace_7675121
  have hstable : (prefixWord ++ tailWord_7675121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7675121).length < 2 ^ (prefixWord ++ tailWord_7675121).sum := by decide
  have hdescent : baseEnd_7675121 < baseStart_7675121 := by decide
  rcases family_descends (prefixWord ++ tailWord_7675121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7675148 : List Nat := [2, 2, 1, 2, 2, 3, 3, 1, 2, 3, 2]
def baseStart_7675148 : Nat := 118140960795 + 7675148 * 2 ^ 59
def prefixEnd_7675148 : Nat := 4983230072969 + 3 ^ 40 * 7675148 * 2
def baseEnd_7675148 : Nat := 3941040018394442181852643

theorem tailTrace_7675148 : CollatzResearch.WordTrace tailWord_7675148 prefixEnd_7675148 3941040018394442181852643 := by
  unfold tailWord_7675148
  simp only [CollatzResearch.WordTrace]
  refine ⟨139967822599128540882261049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186623763465504721176348065 139967822599128540882261049)
  ·
    refine ⟨104975866949346405661695787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139967822599128540882261049 104975866949346405661695787)
    ·
      refine ⟨157463800424019608492543681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104975866949346405661695787 157463800424019608492543681)
      ·
        refine ⟨118097850318014706369407761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157463800424019608492543681 118097850318014706369407761)
        ·
          refine ⟨88573387738511029777055821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118097850318014706369407761 88573387738511029777055821)
          ·
            refine ⟨33215020401941636166395933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88573387738511029777055821 33215020401941636166395933)
            ·
              refine ⟨12455632650728113562398475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33215020401941636166395933 12455632650728113562398475)
              ·
                refine ⟨18683448976092170343597713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12455632650728113562398475 18683448976092170343597713)
                ·
                  refine ⟨14012586732069127757698285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18683448976092170343597713 14012586732069127757698285)
                  ·
                    refine ⟨5254720024525922909136857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14012586732069127757698285 5254720024525922909136857)
                    ·
                      refine ⟨3941040018394442181852643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5254720024525922909136857 3941040018394442181852643)
                      ·
                        rfl

theorem cell23_7675148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 1, 2, 3, 2].length) (baseStart_7675148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7675148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7675148 prefixEnd_7675148 := by exact prefixLift 7675148
  have htrace : WordTrace (prefixWord ++ tailWord_7675148) baseStart_7675148 baseEnd_7675148 := by
    simpa [prefixWord, tailWord_7675148, baseEnd_7675148] using wordTrace_append hprefix tailTrace_7675148
  have hstable : (prefixWord ++ tailWord_7675148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7675148).length < 2 ^ (prefixWord ++ tailWord_7675148).sum := by decide
  have hdescent : baseEnd_7675148 < baseStart_7675148 := by decide
  rcases family_descends (prefixWord ++ tailWord_7675148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7675171 : List Nat := [1, 1, 1, 4, 2, 4, 1, 1, 4, 4]
def baseStart_7675171 : Nat := 118140960795 + 7675171 * 2 ^ 59
def prefixEnd_7675171 : Nat := 4983230072969 + 3 ^ 40 * 7675171 * 2
def baseEnd_7675171 : Nat := 1313683942816498530621679

theorem tailTrace_7675171 : CollatzResearch.WordTrace tailWord_7675171 prefixEnd_7675171 1313683942816498530621679 := by
  unfold tailWord_7675171
  simp only [CollatzResearch.WordTrace]
  refine ⟨279936484077173756692609367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186624322718115837795072911 279936484077173756692609367)
  ·
    refine ⟨419904726115760635038914051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279936484077173756692609367 419904726115760635038914051)
    ·
      refine ⟨629857089173640952558371077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419904726115760635038914051 629857089173640952558371077)
      ·
        refine ⟨118098204220057678604694577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 629857089173640952558371077 118098204220057678604694577)
        ·
          refine ⟨88573653165043258953520933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118098204220057678604694577 88573653165043258953520933)
          ·
            refine ⟨16607559968445611053785175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88573653165043258953520933 16607559968445611053785175)
            ·
              refine ⟨24911339952668416580677763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16607559968445611053785175 24911339952668416580677763)
              ·
                refine ⟨37367009929002624871016645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24911339952668416580677763 37367009929002624871016645)
                ·
                  refine ⟨7006314361687992163315621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37367009929002624871016645 7006314361687992163315621)
                  ·
                    refine ⟨1313683942816498530621679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7006314361687992163315621 1313683942816498530621679)
                    ·
                      rfl

theorem cell23_7675171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 1, 4, 4].length) (baseStart_7675171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7675171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7675171 prefixEnd_7675171 := by exact prefixLift 7675171
  have htrace : WordTrace (prefixWord ++ tailWord_7675171) baseStart_7675171 baseEnd_7675171 := by
    simpa [prefixWord, tailWord_7675171, baseEnd_7675171] using wordTrace_append hprefix tailTrace_7675171
  have hstable : (prefixWord ++ tailWord_7675171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7675171).length < 2 ^ (prefixWord ++ tailWord_7675171).sum := by decide
  have hdescent : baseEnd_7675171 < baseStart_7675171 := by decide
  rcases family_descends (prefixWord ++ tailWord_7675171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7675201 : List Nat := [1, 2, 5, 2, 1, 2, 1, 9]
def baseStart_7675201 : Nat := 118140960795 + 7675201 * 2 ^ 59
def prefixEnd_7675201 : Nat := 4983230072969 + 3 ^ 40 * 7675201 * 2
def baseEnd_7675201 : Nat := 145965453069227054610737

theorem tailTrace_7675201 : CollatzResearch.WordTrace tailWord_7675201 prefixEnd_7675201 145965453069227054610737 := by
  unfold tailWord_7675201
  simp only [CollatzResearch.WordTrace]
  refine ⟨279937578267065071816201457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186625052178043381210800971 279937578267065071816201457)
  ·
    refine ⟨209953183700298803862151093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279937578267065071816201457 209953183700298803862151093)
    ·
      refine ⟨19683110971903012862076665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 209953183700298803862151093 19683110971903012862076665)
      ·
        refine ⟨14762333228927259646557499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19683110971903012862076665 14762333228927259646557499)
        ·
          refine ⟨22143499843390889469836249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14762333228927259646557499 22143499843390889469836249)
          ·
            refine ⟨16607624882543167102377187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22143499843390889469836249 16607624882543167102377187)
            ·
              refine ⟨24911437323814750653565781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16607624882543167102377187 24911437323814750653565781)
              ·
                refine ⟨145965453069227054610737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24911437323814750653565781 145965453069227054610737)
                ·
                  rfl

theorem cell23_7675201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 9].length) (baseStart_7675201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7675201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7675201 prefixEnd_7675201 := by exact prefixLift 7675201
  have htrace : WordTrace (prefixWord ++ tailWord_7675201) baseStart_7675201 baseEnd_7675201 := by
    simpa [prefixWord, tailWord_7675201, baseEnd_7675201] using wordTrace_append hprefix tailTrace_7675201
  have hstable : (prefixWord ++ tailWord_7675201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7675201).length < 2 ^ (prefixWord ++ tailWord_7675201).sum := by decide
  have hdescent : baseEnd_7675201 < baseStart_7675201 := by decide
  rcases family_descends (prefixWord ++ tailWord_7675201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7675212 : List Nat := [2, 2, 1, 3, 2, 2, 3, 3, 1, 2, 2]
def baseStart_7675212 : Nat := 118140960795 + 7675212 * 2 ^ 59
def prefixEnd_7675212 : Nat := 4983230072969 + 3 ^ 40 * 7675212 * 2
def baseEnd_7675212 : Nat := 3941072881156329931452349

theorem tailTrace_7675212 : CollatzResearch.WordTrace tailWord_7675212 prefixEnd_7675212 3941072881156329931452349 := by
  unfold tailWord_7675212
  simp only [CollatzResearch.WordTrace]
  refine ⟨139968989735012610347425945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186625319646683480463234593 139968989735012610347425945)
  ·
    refine ⟨104976742301259457760569459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139968989735012610347425945 104976742301259457760569459)
    ·
      refine ⟨157465113451889186640854189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104976742301259457760569459 157465113451889186640854189)
      ·
        refine ⟨59049417544458444990320321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157465113451889186640854189 59049417544458444990320321)
        ·
          refine ⟨44287063158343833742740241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59049417544458444990320321 44287063158343833742740241)
          ·
            refine ⟨33215297368757875307055181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44287063158343833742740241 33215297368757875307055181)
            ·
              refine ⟨12455736513284203240145693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33215297368757875307055181 12455736513284203240145693)
              ·
                refine ⟨4670901192481576215054635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12455736513284203240145693 4670901192481576215054635)
                ·
                  refine ⟨7006351788722364322581953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4670901192481576215054635 7006351788722364322581953)
                  ·
                    refine ⟨5254763841541773241936465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7006351788722364322581953 5254763841541773241936465)
                    ·
                      refine ⟨3941072881156329931452349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5254763841541773241936465 3941072881156329931452349)
                      ·
                        rfl

theorem cell23_7675212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 3, 1, 2, 2].length) (baseStart_7675212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7675212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7675212 prefixEnd_7675212 := by exact prefixLift 7675212
  have htrace : WordTrace (prefixWord ++ tailWord_7675212) baseStart_7675212 baseEnd_7675212 := by
    simpa [prefixWord, tailWord_7675212, baseEnd_7675212] using wordTrace_append hprefix tailTrace_7675212
  have hstable : (prefixWord ++ tailWord_7675212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7675212).length < 2 ^ (prefixWord ++ tailWord_7675212).sum := by decide
  have hdescent : baseEnd_7675212 < baseStart_7675212 := by decide
  rcases family_descends (prefixWord ++ tailWord_7675212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7675224 : List Nat := [2, 1, 2, 2, 1, 1, 3, 2, 2, 2, 5]
def baseStart_7675224 : Nat := 118140960795 + 7675224 * 2 ^ 59
def prefixEnd_7675224 : Nat := 4983230072969 + 3 ^ 40 * 7675224 * 2
def baseEnd_7675224 : Nat := 3941079042924183884502293

theorem tailTrace_7675224 : CollatzResearch.WordTrace tailWord_7675224 prefixEnd_7675224 3941079042924183884502293 := by
  unfold tailWord_7675224
  simp only [CollatzResearch.WordTrace]
  refine ⟨139969208572990873372144363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186625611430654497829525817 139969208572990873372144363)
  ·
    refine ⟨209953812859486310058216545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139969208572990873372144363 209953812859486310058216545)
    ·
      refine ⟨157465359644614732543662409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209953812859486310058216545 157465359644614732543662409)
      ·
        refine ⟨118099019733461049407746807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157465359644614732543662409 118099019733461049407746807)
        ·
          refine ⟨177148529600191574111620211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118099019733461049407746807 177148529600191574111620211)
          ·
            refine ⟨265722794400287361167430317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177148529600191574111620211 265722794400287361167430317)
            ·
              refine ⟨99646047900107760437786369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 265722794400287361167430317 99646047900107760437786369)
              ·
                refine ⟨74734535925080820328339777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99646047900107760437786369 74734535925080820328339777)
                ·
                  refine ⟨56050901943810615246254833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74734535925080820328339777 56050901943810615246254833)
                  ·
                    refine ⟨42038176457857961434691125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56050901943810615246254833 42038176457857961434691125)
                    ·
                      refine ⟨3941079042924183884502293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42038176457857961434691125 3941079042924183884502293)
                      ·
                        rfl

theorem cell23_7675224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 2, 2, 5].length) (baseStart_7675224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7675224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7675224 prefixEnd_7675224 := by exact prefixLift 7675224
  have htrace : WordTrace (prefixWord ++ tailWord_7675224) baseStart_7675224 baseEnd_7675224 := by
    simpa [prefixWord, tailWord_7675224, baseEnd_7675224] using wordTrace_append hprefix tailTrace_7675224
  have hstable : (prefixWord ++ tailWord_7675224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7675224).length < 2 ^ (prefixWord ++ tailWord_7675224).sum := by decide
  have hdescent : baseEnd_7675224 < baseStart_7675224 := by decide
  rcases family_descends (prefixWord ++ tailWord_7675224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7675245 : List Nat := [1, 5, 1, 1, 1, 4, 1, 3, 2, 1, 3]
def baseStart_7675245 : Nat := 118140960795 + 7675245 * 2 ^ 59
def prefixEnd_7675245 : Nat := 4983230072969 + 3 ^ 40 * 7675245 * 2
def baseEnd_7675245 : Nat := 3941089826017928302339697

theorem tailTrace_7675245 : CollatzResearch.WordTrace tailWord_7675245 prefixEnd_7675245 3941089826017928302339697 := by
  unfold tailWord_7675245
  simp only [CollatzResearch.WordTrace]
  refine ⟨279939183078905667330803189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186626122052603778220535459 279939183078905667330803189)
  ·
    refine ⟨26244298413647406312262799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 279939183078905667330803189 26244298413647406312262799)
    ·
      refine ⟨39366447620471109468394199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26244298413647406312262799 39366447620471109468394199)
      ·
        refine ⟨59049671430706664202591299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39366447620471109468394199 59049671430706664202591299)
        ·
          refine ⟨88574507146059996303886949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59049671430706664202591299 88574507146059996303886949)
          ·
            refine ⟨16607720089886249306978803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88574507146059996303886949 16607720089886249306978803)
            ·
              refine ⟨24911580134829373960468205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16607720089886249306978803 24911580134829373960468205)
              ·
                refine ⟨9341842550561015235175577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24911580134829373960468205 9341842550561015235175577)
                ·
                  refine ⟨7006381912920761426381683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9341842550561015235175577 7006381912920761426381683)
                  ·
                    refine ⟨10509572869381142139572525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7006381912920761426381683 10509572869381142139572525)
                    ·
                      refine ⟨3941089826017928302339697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10509572869381142139572525 3941089826017928302339697)
                      ·
                        rfl

theorem cell23_7675245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 3, 2, 1, 3].length) (baseStart_7675245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7675245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7675245 prefixEnd_7675245 := by exact prefixLift 7675245
  have htrace : WordTrace (prefixWord ++ tailWord_7675245) baseStart_7675245 baseEnd_7675245 := by
    simpa [prefixWord, tailWord_7675245, baseEnd_7675245] using wordTrace_append hprefix tailTrace_7675245
  have hstable : (prefixWord ++ tailWord_7675245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7675245).length < 2 ^ (prefixWord ++ tailWord_7675245).sum := by decide
  have hdescent : baseEnd_7675245 < baseStart_7675245 := by decide
  rcases family_descends (prefixWord ++ tailWord_7675245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7675262 : List Nat := [4, 2, 3, 2, 1, 1, 1, 2, 1, 3, 3]
def baseStart_7675262 : Nat := 118140960795 + 7675262 * 2 ^ 59
def prefixEnd_7675262 : Nat := 4983230072969 + 3 ^ 40 * 7675262 * 2
def baseEnd_7675262 : Nat := 3941098555189054735827119

theorem tailTrace_7675262 : CollatzResearch.WordTrace tailWord_7675262 prefixEnd_7675262 3941098555189054735827119 := by
  unfold tailWord_7675262
  simp only [CollatzResearch.WordTrace]
  refine ⟨34992475389980509904271505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186626535413229386156114693 34992475389980509904271505)
  ·
    refine ⟨26244356542485382428203629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34992475389980509904271505 26244356542485382428203629)
    ·
      refine ⟨9841633703432018410576361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26244356542485382428203629 9841633703432018410576361)
      ·
        refine ⟨7381225277574013807932271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9841633703432018410576361 7381225277574013807932271)
        ·
          refine ⟨11071837916361020711898407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7381225277574013807932271 11071837916361020711898407)
          ·
            refine ⟨16607756874541531067847611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11071837916361020711898407 16607756874541531067847611)
            ·
              refine ⟨24911635311812296601771417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16607756874541531067847611 24911635311812296601771417)
              ·
                refine ⟨18683726483859222451328563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24911635311812296601771417 18683726483859222451328563)
                ·
                  refine ⟨28025589725788833676992845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18683726483859222451328563 28025589725788833676992845)
                  ·
                    refine ⟨10509596147170812628872317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28025589725788833676992845 10509596147170812628872317)
                    ·
                      refine ⟨3941098555189054735827119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10509596147170812628872317 3941098555189054735827119)
                      ·
                        rfl

theorem cell23_7675262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_7675262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7675262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7675262 prefixEnd_7675262 := by exact prefixLift 7675262
  have htrace : WordTrace (prefixWord ++ tailWord_7675262) baseStart_7675262 baseEnd_7675262 := by
    simpa [prefixWord, tailWord_7675262, baseEnd_7675262] using wordTrace_append hprefix tailTrace_7675262
  have hstable : (prefixWord ++ tailWord_7675262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7675262).length < 2 ^ (prefixWord ++ tailWord_7675262).sum := by decide
  have hdescent : baseEnd_7675262 < baseStart_7675262 := by decide
  rcases family_descends (prefixWord ++ tailWord_7675262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7675268 : List Nat := [2, 3, 2, 1, 1, 3, 1, 1, 3, 4, 2]
def baseStart_7675268 : Nat := 118140960795 + 7675268 * 2 ^ 59
def prefixEnd_7675268 : Nat := 4983230072969 + 3 ^ 40 * 7675268 * 2
def baseEnd_7675268 : Nat := 3941101636072981712352091

theorem tailTrace_7675268 : CollatzResearch.WordTrace tailWord_7675268 prefixEnd_7675268 3941101636072981712352091 := by
  unfold tailWord_7675268
  simp only [CollatzResearch.WordTrace]
  refine ⟨139970010978911171129445229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186626681305214894839260305 139970010978911171129445229)
  ·
    refine ⟨52488754117091689173541961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139970010978911171129445229 52488754117091689173541961)
    ·
      refine ⟨39366565587818766880156471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52488754117091689173541961 39366565587818766880156471)
      ·
        refine ⟨59049848381728150320234707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39366565587818766880156471 59049848381728150320234707)
        ·
          refine ⟨88574772572592225480352061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59049848381728150320234707 88574772572592225480352061)
          ·
            refine ⟨33215539714722084555132023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88574772572592225480352061 33215539714722084555132023)
            ·
              refine ⟨49823309572083126832698035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33215539714722084555132023 49823309572083126832698035)
              ·
                refine ⟨74734964358124690249047053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49823309572083126832698035 74734964358124690249047053)
                ·
                  refine ⟨28025611634296758843392645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74734964358124690249047053 28025611634296758843392645)
                  ·
                    refine ⟨5254802181430642283136121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28025611634296758843392645 5254802181430642283136121)
                    ·
                      refine ⟨3941101636072981712352091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5254802181430642283136121 3941101636072981712352091)
                      ·
                        rfl

theorem cell23_7675268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 3, 4, 2].length) (baseStart_7675268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7675268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7675268 prefixEnd_7675268 := by exact prefixLift 7675268
  have htrace : WordTrace (prefixWord ++ tailWord_7675268) baseStart_7675268 baseEnd_7675268 := by
    simpa [prefixWord, tailWord_7675268, baseEnd_7675268] using wordTrace_append hprefix tailTrace_7675268
  have hstable : (prefixWord ++ tailWord_7675268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7675268).length < 2 ^ (prefixWord ++ tailWord_7675268).sum := by decide
  have hdescent : baseEnd_7675268 < baseStart_7675268 := by decide
  rcases family_descends (prefixWord ++ tailWord_7675268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7675271 : List Nat := [1, 1, 4, 2, 2, 2, 2, 1, 2, 1, 5]
def baseStart_7675271 : Nat := 118140960795 + 7675271 * 2 ^ 59
def prefixEnd_7675271 : Nat := 4983230072969 + 3 ^ 40 * 7675271 * 2
def baseEnd_7675271 : Nat := 3941103176514945200614577

theorem tailTrace_7675271 : CollatzResearch.WordTrace tailWord_7675271 prefixEnd_7675271 3941103176514945200614577 := by
  unfold tailWord_7675271
  simp only [CollatzResearch.WordTrace]
  refine ⟨279940131376811473771249667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186626754251207649180833111 279940131376811473771249667)
  ·
    refine ⟨419910197065217210656874501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279940131376811473771249667 419910197065217210656874501)
    ·
      refine ⟨78733161949728226998163969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 419910197065217210656874501 78733161949728226998163969)
      ·
        refine ⟨59049871462296170248622977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78733161949728226998163969 59049871462296170248622977)
        ·
          refine ⟨44287403596722127686467233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59049871462296170248622977 44287403596722127686467233)
          ·
            refine ⟨33215552697541595764850425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44287403596722127686467233 33215552697541595764850425)
            ·
              refine ⟨24911664523156196823637819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33215552697541595764850425 24911664523156196823637819)
              ·
                refine ⟨37367496784734295235456729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24911664523156196823637819 37367496784734295235456729)
                ·
                  refine ⟨28025622588550721426592547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37367496784734295235456729 28025622588550721426592547)
                  ·
                    refine ⟨42038433882826082139888821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28025622588550721426592547 42038433882826082139888821)
                    ·
                      refine ⟨3941103176514945200614577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42038433882826082139888821 3941103176514945200614577)
                      ·
                        rfl

theorem cell23_7675271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_7675271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7675271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7675271 prefixEnd_7675271 := by exact prefixLift 7675271
  have htrace : WordTrace (prefixWord ++ tailWord_7675271) baseStart_7675271 baseEnd_7675271 := by
    simpa [prefixWord, tailWord_7675271, baseEnd_7675271] using wordTrace_append hprefix tailTrace_7675271
  have hstable : (prefixWord ++ tailWord_7675271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7675271).length < 2 ^ (prefixWord ++ tailWord_7675271).sum := by decide
  have hdescent : baseEnd_7675271 < baseStart_7675271 := by decide
  rcases family_descends (prefixWord ++ tailWord_7675271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7675272 : List Nat := [2, 1, 3, 3, 1, 3, 3, 1, 1, 3, 2]
def baseStart_7675272 : Nat := 118140960795 + 7675272 * 2 ^ 59
def prefixEnd_7675272 : Nat := 4983230072969 + 3 ^ 40 * 7675272 * 2
def baseEnd_7675272 : Nat := 3941103689995599696702073

theorem tailTrace_7675272 : CollatzResearch.WordTrace tailWord_7675272 prefixEnd_7675272 3941103689995599696702073 := by
  unfold tailWord_7675272
  simp only [CollatzResearch.WordTrace]
  refine ⟨139970083924903925471018035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186626778566538567294690713 139970083924903925471018035)
  ·
    refine ⟨209955125887355888206527053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139970083924903925471018035 209955125887355888206527053)
    ·
      refine ⟨78733172207758458077447645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209955125887355888206527053 78733172207758458077447645)
      ·
        refine ⟨29524939577909421779042867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78733172207758458077447645 29524939577909421779042867)
        ·
          refine ⟨44287409366864132668564301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29524939577909421779042867 44287409366864132668564301)
          ·
            refine ⟨16607778512574049750711613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44287409366864132668564301 16607778512574049750711613)
            ·
              refine ⟨6227916942215268656516855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16607778512574049750711613 6227916942215268656516855)
              ·
                refine ⟨9341875413322902984775283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6227916942215268656516855 9341875413322902984775283)
                ·
                  refine ⟨14012813119984354477162925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9341875413322902984775283 14012813119984354477162925)
                  ·
                    refine ⟨5254804919994132928936097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14012813119984354477162925 5254804919994132928936097)
                    ·
                      refine ⟨3941103689995599696702073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5254804919994132928936097 3941103689995599696702073)
                      ·
                        rfl

theorem cell23_7675272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 3, 1, 1, 3, 2].length) (baseStart_7675272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7675272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7675272 prefixEnd_7675272 := by exact prefixLift 7675272
  have htrace : WordTrace (prefixWord ++ tailWord_7675272) baseStart_7675272 baseEnd_7675272 := by
    simpa [prefixWord, tailWord_7675272, baseEnd_7675272] using wordTrace_append hprefix tailTrace_7675272
  have hstable : (prefixWord ++ tailWord_7675272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7675272).length < 2 ^ (prefixWord ++ tailWord_7675272).sum := by decide
  have hdescent : baseEnd_7675272 < baseStart_7675272 := by decide
  rcases family_descends (prefixWord ++ tailWord_7675272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7675285 : List Nat := [1, 3, 2, 1, 1, 2, 3, 4, 2, 2, 2]
def baseStart_7675285 : Nat := 118140960795 + 7675285 * 2 ^ 59
def prefixEnd_7675285 : Nat := 4983230072969 + 3 ^ 40 * 7675285 * 2
def baseEnd_7675285 : Nat := 3941110365244108145839513

theorem tailTrace_7675285 : CollatzResearch.WordTrace tailWord_7675285 prefixEnd_7675285 3941110365244108145839513 := by
  unfold tailWord_7675285
  simp only [CollatzResearch.WordTrace]
  refine ⟨279940641998760754162259309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186627094665840502774839539 279940641998760754162259309)
  ·
    refine ⟨104977740749535282810847241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 279940641998760754162259309 104977740749535282810847241)
    ·
      refine ⟨78733305562151462108135431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104977740749535282810847241 78733305562151462108135431)
      ·
        refine ⟨118099958343227193162203147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78733305562151462108135431 118099958343227193162203147)
        ·
          refine ⟨177149937514840789743304721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118099958343227193162203147 177149937514840789743304721)
          ·
            refine ⟨132862453136130592307478541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177149937514840789743304721 132862453136130592307478541)
            ·
              refine ⟨49823419926048972115304453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132862453136130592307478541 49823419926048972115304453)
              ·
                refine ⟨9341891236134182271619585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49823419926048972115304453 9341891236134182271619585)
                ·
                  refine ⟨7006418427100636703714689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9341891236134182271619585 7006418427100636703714689)
                  ·
                    refine ⟨5254813820325477527786017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7006418427100636703714689 5254813820325477527786017)
                    ·
                      refine ⟨3941110365244108145839513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5254813820325477527786017 3941110365244108145839513)
                      ·
                        rfl

theorem cell23_7675285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 4, 2, 2, 2].length) (baseStart_7675285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7675285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7675285 prefixEnd_7675285 := by exact prefixLift 7675285
  have htrace : WordTrace (prefixWord ++ tailWord_7675285) baseStart_7675285 baseEnd_7675285 := by
    simpa [prefixWord, tailWord_7675285, baseEnd_7675285] using wordTrace_append hprefix tailTrace_7675285
  have hstable : (prefixWord ++ tailWord_7675285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7675285).length < 2 ^ (prefixWord ++ tailWord_7675285).sum := by decide
  have hdescent : baseEnd_7675285 < baseStart_7675285 := by decide
  rcases family_descends (prefixWord ++ tailWord_7675285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7675298 : List Nat := [3, 3, 1, 2, 1, 3, 1, 1, 2, 2, 4]
def baseStart_7675298 : Nat := 118140960795 + 7675298 * 2 ^ 59
def prefixEnd_7675298 : Nat := 4983230072969 + 3 ^ 40 * 7675298 * 2
def baseEnd_7675298 : Nat := 3941117040492616594976953

theorem tailTrace_7675298 : CollatzResearch.WordTrace tailWord_7675298 prefixEnd_7675298 3941117040492616594976953 := by
  unfold tailWord_7675298
  simp only [CollatzResearch.WordTrace]
  refine ⟨69985279036928414345620637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186627410765142438254988365 69985279036928414345620637)
  ·
    refine ⟨26244479638848155379607739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69985279036928414345620637 26244479638848155379607739)
    ·
      refine ⟨39366719458272233069411609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26244479638848155379607739 39366719458272233069411609)
      ·
        refine ⟨29525039593704174802058707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39366719458272233069411609 29525039593704174802058707)
        ·
          refine ⟨44287559390556262203088061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29525039593704174802058707 44287559390556262203088061)
          ·
            refine ⟨16607834771458598326158023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44287559390556262203088061 16607834771458598326158023)
            ·
              refine ⟨24911752157187897489237035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16607834771458598326158023 24911752157187897489237035)
              ·
                refine ⟨37367628235781846233855553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24911752157187897489237035 37367628235781846233855553)
                ·
                  refine ⟨28025721176836384675391665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37367628235781846233855553 28025721176836384675391665)
                  ·
                    refine ⟨21019290882627288506543749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28025721176836384675391665 21019290882627288506543749)
                    ·
                      refine ⟨3941117040492616594976953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21019290882627288506543749 3941117040492616594976953)
                      ·
                        rfl

theorem cell23_7675298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_7675298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7675298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7675298 prefixEnd_7675298 := by exact prefixLift 7675298
  have htrace : WordTrace (prefixWord ++ tailWord_7675298) baseStart_7675298 baseEnd_7675298 := by
    simpa [prefixWord, tailWord_7675298, baseEnd_7675298] using wordTrace_append hprefix tailTrace_7675298
  have hstable : (prefixWord ++ tailWord_7675298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7675298).length < 2 ^ (prefixWord ++ tailWord_7675298).sum := by decide
  have hdescent : baseEnd_7675298 < baseStart_7675298 := by decide
  rcases family_descends (prefixWord ++ tailWord_7675298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7675330 : List Nat := [3, 5, 2, 1, 2, 1, 1, 2, 2, 1, 3]
def baseStart_7675330 : Nat := 118140960795 + 7675330 * 2 ^ 59
def prefixEnd_7675330 : Nat := 4983230072969 + 3 ^ 40 * 7675330 * 2
def baseEnd_7675330 : Nat := 3941133471873560469776807

theorem tailTrace_7675330 : CollatzResearch.WordTrace tailWord_7675330 prefixEnd_7675330 3941133471873560469776807 := by
  unfold tailWord_7675330
  simp only [CollatzResearch.WordTrace]
  refine ⟨69985570820899431711911861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186628188855731817898431629 69985570820899431711911861)
  ·
    refine ⟨6561147264459321722991737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69985570820899431711911861 6561147264459321722991737)
    ·
      refine ⟨4920860448344491292243803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6561147264459321722991737 4920860448344491292243803)
      ·
        refine ⟨7381290672516736938365705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4920860448344491292243803 7381290672516736938365705)
        ·
          refine ⟨5535968004387552703774279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7381290672516736938365705 5535968004387552703774279)
          ·
            refine ⟨8303952006581329055661419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5535968004387552703774279 8303952006581329055661419)
            ·
              refine ⟨12455928009871993583492129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8303952006581329055661419 12455928009871993583492129)
              ·
                refine ⟨9341946007403995187619097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12455928009871993583492129 9341946007403995187619097)
                ·
                  refine ⟨7006459505552996390714323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9341946007403995187619097 7006459505552996390714323)
                  ·
                    refine ⟨10509689258329494586071485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7006459505552996390714323 10509689258329494586071485)
                    ·
                      refine ⟨3941133471873560469776807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10509689258329494586071485 3941133471873560469776807)
                      ·
                        rfl

theorem cell23_7675330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_7675330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7675330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7675330 prefixEnd_7675330 := by exact prefixLift 7675330
  have htrace : WordTrace (prefixWord ++ tailWord_7675330) baseStart_7675330 baseEnd_7675330 := by
    simpa [prefixWord, tailWord_7675330, baseEnd_7675330] using wordTrace_append hprefix tailTrace_7675330
  have hstable : (prefixWord ++ tailWord_7675330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7675330).length < 2 ^ (prefixWord ++ tailWord_7675330).sum := by decide
  have hdescent : baseEnd_7675330 < baseStart_7675330 := by decide
  rcases family_descends (prefixWord ++ tailWord_7675330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7675368 : List Nat := [2, 1, 4, 1, 1, 2, 1, 4, 3, 4]
def baseStart_7675368 : Nat := 118140960795 + 7675368 * 2 ^ 59
def prefixEnd_7675368 : Nat := 4983230072969 + 3 ^ 40 * 7675368 * 2
def baseEnd_7675368 : Nat := 1313717661379477107033877

theorem tailTrace_7675368 : CollatzResearch.WordTrace tailWord_7675368 prefixEnd_7675368 1313717661379477107033877 := by
  unfold tailWord_7675368
  simp only [CollatzResearch.WordTrace]
  refine ⟨139971834628730029668765379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186629112838306706225020505 139971834628730029668765379)
  ·
    refine ⟨209957751943095044503148069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139971834628730029668765379 209957751943095044503148069)
    ·
      refine ⟨39367078489330320844340263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 209957751943095044503148069 39367078489330320844340263)
      ·
        refine ⟨59050617733995481266510395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39367078489330320844340263 59050617733995481266510395)
        ·
          refine ⟨88575926600993221899765593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59050617733995481266510395 88575926600993221899765593)
          ·
            refine ⟨66431944950744916424824195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88575926600993221899765593 66431944950744916424824195)
            ·
              refine ⟨99647917426117374637236293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66431944950744916424824195 99647917426117374637236293)
              ·
                refine ⟨18683984517397007744481805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99647917426117374637236293 18683984517397007744481805)
                ·
                  refine ⟨7006494194023877904180677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18683984517397007744481805 7006494194023877904180677)
                  ·
                    refine ⟨1313717661379477107033877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7006494194023877904180677 1313717661379477107033877)
                    ·
                      rfl

theorem cell23_7675368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 4, 3, 4].length) (baseStart_7675368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7675368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7675368 prefixEnd_7675368 := by exact prefixLift 7675368
  have htrace : WordTrace (prefixWord ++ tailWord_7675368) baseStart_7675368 baseEnd_7675368 := by
    simpa [prefixWord, tailWord_7675368, baseEnd_7675368] using wordTrace_append hprefix tailTrace_7675368
  have hstable : (prefixWord ++ tailWord_7675368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7675368).length < 2 ^ (prefixWord ++ tailWord_7675368).sum := by decide
  have hdescent : baseEnd_7675368 < baseStart_7675368 := by decide
  rcases family_descends (prefixWord ++ tailWord_7675368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7675442 : List Nat := [3, 2, 1, 1, 2, 1, 1, 7, 1, 1, 3]
def baseStart_7675442 : Nat := 118140960795 + 7675442 * 2 ^ 59
def prefixEnd_7675442 : Nat := 4983230072969 + 3 ^ 40 * 7675442 * 2
def baseEnd_7675442 : Nat := 3941190981706864031576291

theorem tailTrace_7675442 : CollatzResearch.WordTrace tailWord_7675442 prefixEnd_7675442 3941190981706864031576291 := by
  unfold tailWord_7675442
  simp only [CollatzResearch.WordTrace]
  refine ⟨69986592064797992493931145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186630912172794646650483053 69986592064797992493931145)
  ·
    refine ⟨52489944048598494370448359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69986592064797992493931145 52489944048598494370448359)
    ·
      refine ⟨78734916072897741555672539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52489944048598494370448359 78734916072897741555672539)
      ·
        refine ⟨118102374109346612333508809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78734916072897741555672539 118102374109346612333508809)
        ·
          refine ⟨88576780582009959250131607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118102374109346612333508809 88576780582009959250131607)
          ·
            refine ⟨132865170873014938875197411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88576780582009959250131607 132865170873014938875197411)
            ·
              refine ⟨199297756309522408312796117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132865170873014938875197411 199297756309522408312796117)
              ·
                refine ⟨4671041163504431444831159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 199297756309522408312796117 4671041163504431444831159)
                ·
                  refine ⟨7006561745256647167246739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4671041163504431444831159 7006561745256647167246739)
                  ·
                    refine ⟨10509842617884970750870109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7006561745256647167246739 10509842617884970750870109)
                    ·
                      refine ⟨3941190981706864031576291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10509842617884970750870109 3941190981706864031576291)
                      ·
                        rfl

theorem cell23_7675442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 7, 1, 1, 3].length) (baseStart_7675442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7675442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7675442 prefixEnd_7675442 := by exact prefixLift 7675442
  have htrace : WordTrace (prefixWord ++ tailWord_7675442) baseStart_7675442 baseEnd_7675442 := by
    simpa [prefixWord, tailWord_7675442, baseEnd_7675442] using wordTrace_append hprefix tailTrace_7675442
  have hstable : (prefixWord ++ tailWord_7675442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7675442).length < 2 ^ (prefixWord ++ tailWord_7675442).sum := by decide
  have hdescent : baseEnd_7675442 < baseStart_7675442 := by decide
  rcases family_descends (prefixWord ++ tailWord_7675442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7675465 : List Nat := [1, 2, 1, 1, 2, 2, 1, 2, 7, 2, 2]
def baseStart_7675465 : Nat := 118140960795 + 7675465 * 2 ^ 59
def prefixEnd_7675465 : Nat := 4983230072969 + 3 ^ 40 * 7675465 * 2
def baseEnd_7675465 : Nat := 3941202791761917441588685

theorem tailTrace_7675465 : CollatzResearch.WordTrace tailWord_7675465 prefixEnd_7675465 3941202791761917441588685 := by
  unfold tailWord_7675465
  simp only [CollatzResearch.WordTrace]
  refine ⟨279947207138108644903811849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186631471425405763269207899 279947207138108644903811849)
  ·
    refine ⟨209960405353581483677858887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279947207138108644903811849 209960405353581483677858887)
    ·
      refine ⟨314940608030372225516788331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209960405353581483677858887 314940608030372225516788331)
      ·
        refine ⟨472410912045558338275182497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314940608030372225516788331 472410912045558338275182497)
        ·
          refine ⟨354308184034168753706386873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 472410912045558338275182497 354308184034168753706386873)
          ·
            refine ⟨265731138025626565279790155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 354308184034168753706386873 265731138025626565279790155)
            ·
              refine ⟨398596707038439847919685233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265731138025626565279790155 398596707038439847919685233)
              ·
                refine ⟨298947530278829885939763925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 398596707038439847919685233 298947530278829885939763925)
                ·
                  refine ⟨7006582740910075451713217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 298947530278829885939763925 7006582740910075451713217)
                  ·
                    refine ⟨5254937055682556588784913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7006582740910075451713217 5254937055682556588784913)
                    ·
                      refine ⟨3941202791761917441588685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5254937055682556588784913 3941202791761917441588685)
                      ·
                        rfl

theorem cell23_7675465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 7, 2, 2].length) (baseStart_7675465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7675465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7675465 prefixEnd_7675465 := by exact prefixLift 7675465
  have htrace : WordTrace (prefixWord ++ tailWord_7675465) baseStart_7675465 baseEnd_7675465 := by
    simpa [prefixWord, tailWord_7675465, baseEnd_7675465] using wordTrace_append hprefix tailTrace_7675465
  have hstable : (prefixWord ++ tailWord_7675465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7675465).length < 2 ^ (prefixWord ++ tailWord_7675465).sum := by decide
  have hdescent : baseEnd_7675465 < baseStart_7675465 := by decide
  rcases family_descends (prefixWord ++ tailWord_7675465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7675481 : List Nat := [1, 2, 1, 2, 2, 1, 1, 2, 2, 2, 7]
def baseStart_7675481 : Nat := 118140960795 + 7675481 * 2 ^ 59
def prefixEnd_7675481 : Nat := 4983230072969 + 3 ^ 40 * 7675481 * 2
def baseEnd_7675481 : Nat := 3941211007452389378988611

theorem tailTrace_7675481 : CollatzResearch.WordTrace tailWord_7675481 prefixEnd_7675481 3941211007452389378988611 := by
  unfold tailWord_7675481
  simp only [CollatzResearch.WordTrace]
  refine ⟨279947790706050679636394297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186631860470700453090929531 279947790706050679636394297)
  ·
    refine ⟨209960843029538009727295723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279947790706050679636394297 209960843029538009727295723)
    ·
      refine ⟨314941264544307014590943585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209960843029538009727295723 314941264544307014590943585)
      ·
        refine ⟨236205948408230260943207689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 314941264544307014590943585 236205948408230260943207689)
        ·
          refine ⟨177154461306172695707405767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236205948408230260943207689 177154461306172695707405767)
          ·
            refine ⟨265731691959259043561108651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177154461306172695707405767 265731691959259043561108651)
            ·
              refine ⟨398597537938888565341662977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265731691959259043561108651 398597537938888565341662977)
              ·
                refine ⟨298948153454166424006247233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 398597537938888565341662977 298948153454166424006247233)
                ·
                  refine ⟨224211115090624818004685425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 298948153454166424006247233 224211115090624818004685425)
                  ·
                    refine ⟨168158336317968613503514069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 224211115090624818004685425 168158336317968613503514069)
                    ·
                      refine ⟨3941211007452389378988611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 168158336317968613503514069 3941211007452389378988611)
                      ·
                        rfl

theorem cell23_7675481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 2, 7].length) (baseStart_7675481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7675481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7675481 prefixEnd_7675481 := by exact prefixLift 7675481
  have htrace : WordTrace (prefixWord ++ tailWord_7675481) baseStart_7675481 baseEnd_7675481 := by
    simpa [prefixWord, tailWord_7675481, baseEnd_7675481] using wordTrace_append hprefix tailTrace_7675481
  have hstable : (prefixWord ++ tailWord_7675481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7675481).length < 2 ^ (prefixWord ++ tailWord_7675481).sum := by decide
  have hdescent : baseEnd_7675481 < baseStart_7675481 := by decide
  rcases family_descends (prefixWord ++ tailWord_7675481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7675509 : List Nat := [1, 3, 4, 2, 1, 3, 1, 2, 2, 4]
def baseStart_7675509 : Nat := 118140960795 + 7675509 * 2 ^ 59
def prefixEnd_7675509 : Nat := 4983230072969 + 3 ^ 40 * 7675509 * 2
def baseEnd_7675509 : Nat := 1313741794970238423146161

theorem tailTrace_7675509 : CollatzResearch.WordTrace tailWord_7675509 prefixEnd_7675509 1313741794970238423146161 := by
  unfold tailWord_7675509
  simp only [CollatzResearch.WordTrace]
  refine ⟨279948811949949240418413581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186632541299966160278942387 279948811949949240418413581)
  ·
    refine ⟨104980804481230965156905093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 279948811949949240418413581 104980804481230965156905093)
    ·
      refine ⟨19683900840230805966919705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104980804481230965156905093 19683900840230805966919705)
      ·
        refine ⟨14762925630173104475189779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19683900840230805966919705 14762925630173104475189779)
        ·
          refine ⟨22144388445259656712784669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14762925630173104475189779 22144388445259656712784669)
          ·
            refine ⟨8304145666972371267294251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22144388445259656712784669 8304145666972371267294251)
            ·
              refine ⟨12456218500458556900941377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8304145666972371267294251 12456218500458556900941377)
              ·
                refine ⟨9342163875343917675706033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12456218500458556900941377 9342163875343917675706033)
                ·
                  refine ⟨7006622906507938256779525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9342163875343917675706033 7006622906507938256779525)
                  ·
                    refine ⟨1313741794970238423146161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7006622906507938256779525 1313741794970238423146161)
                    ·
                      rfl

theorem cell23_7675509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_7675509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7675509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7675509 prefixEnd_7675509 := by exact prefixLift 7675509
  have htrace : WordTrace (prefixWord ++ tailWord_7675509) baseStart_7675509 baseEnd_7675509 := by
    simpa [prefixWord, tailWord_7675509, baseEnd_7675509] using wordTrace_append hprefix tailTrace_7675509
  have hstable : (prefixWord ++ tailWord_7675509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7675509).length < 2 ^ (prefixWord ++ tailWord_7675509).sum := by decide
  have hdescent : baseEnd_7675509 < baseStart_7675509 := by decide
  rcases family_descends (prefixWord ++ tailWord_7675509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7675515 : List Nat := [1, 1, 1, 1, 1, 4, 5, 1, 4, 1, 3]
def baseStart_7675515 : Nat := 118140960795 + 7675515 * 2 ^ 59
def prefixEnd_7675515 : Nat := 4983230072969 + 3 ^ 40 * 7675515 * 2
def baseEnd_7675515 : Nat := 3941228465794642245963455

theorem tailTrace_7675515 : CollatzResearch.WordTrace tailWord_7675515 prefixEnd_7675515 3941228465794642245963455 := by
  unfold tailWord_7675515
  simp only [CollatzResearch.WordTrace]
  refine ⟨279949030787927503443131999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186632687191951668962087999 279949030787927503443131999)
  ·
    refine ⟨419923546181891255164697999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279949030787927503443131999 419923546181891255164697999)
    ·
      refine ⟨629885319272836882747046999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419923546181891255164697999 629885319272836882747046999)
      ·
        refine ⟨944827978909255324120570499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 629885319272836882747046999 944827978909255324120570499)
        ·
          refine ⟨1417241968363882986180855749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 944827978909255324120570499 1417241968363882986180855749)
          ·
            refine ⟨265732869068228059908910453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1417241968363882986180855749 265732869068228059908910453)
            ·
              refine ⟨24912456475146380616460355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 265732869068228059908910453 24912456475146380616460355)
              ·
                refine ⟨37368684712719570924690533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24912456475146380616460355 37368684712719570924690533)
                ·
                  refine ⟨7006628383634919548379475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37368684712719570924690533 7006628383634919548379475)
                  ·
                    refine ⟨10509942575452379322569213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7006628383634919548379475 10509942575452379322569213)
                    ·
                      refine ⟨3941228465794642245963455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10509942575452379322569213 3941228465794642245963455)
                      ·
                        rfl

theorem cell23_7675515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 1, 4, 1, 3].length) (baseStart_7675515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7675515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7675515 prefixEnd_7675515 := by exact prefixLift 7675515
  have htrace : WordTrace (prefixWord ++ tailWord_7675515) baseStart_7675515 baseEnd_7675515 := by
    simpa [prefixWord, tailWord_7675515, baseEnd_7675515] using wordTrace_append hprefix tailTrace_7675515
  have hstable : (prefixWord ++ tailWord_7675515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7675515).length < 2 ^ (prefixWord ++ tailWord_7675515).sum := by decide
  have hdescent : baseEnd_7675515 < baseStart_7675515 := by decide
  rcases family_descends (prefixWord ++ tailWord_7675515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7675555 : List Nat := [1, 1, 1, 4, 1, 1, 4, 1, 3, 4, 2]
def baseStart_7675555 : Nat := 118140960795 + 7675555 * 2 ^ 59
def prefixEnd_7675555 : Nat := 4983230072969 + 3 ^ 40 * 7675555 * 2
def baseEnd_7675555 : Nat := 3941249005020822089463271

theorem tailTrace_7675555 : CollatzResearch.WordTrace tailWord_7675555 prefixEnd_7675555 3941249005020822089463271 := by
  unfold tailWord_7675555
  simp only [CollatzResearch.WordTrace]
  refine ⟨279950489707782590274588119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186633659805188393516392079 279950489707782590274588119)
  ·
    refine ⟨419925734561673885411882179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279950489707782590274588119 419925734561673885411882179)
    ·
      refine ⟨629888601842510828117823269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419925734561673885411882179 629888601842510828117823269)
      ·
        refine ⟨118104112845470780272091863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 629888601842510828117823269 118104112845470780272091863)
        ·
          refine ⟨177156169268206170408137795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118104112845470780272091863 177156169268206170408137795)
          ·
            refine ⟨265734253902309255612206693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177156169268206170408137795 265734253902309255612206693)
            ·
              refine ⟨49825172606682985427288755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 265734253902309255612206693 49825172606682985427288755)
              ·
                refine ⟨74737758910024478140933133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49825172606682985427288755 74737758910024478140933133)
                ·
                  refine ⟨28026659591259179302849925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74737758910024478140933133 28026659591259179302849925)
                  ·
                    refine ⟨5254998673361096119284361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28026659591259179302849925 5254998673361096119284361)
                    ·
                      refine ⟨3941249005020822089463271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5254998673361096119284361 3941249005020822089463271)
                      ·
                        rfl

theorem cell23_7675555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 3, 4, 2].length) (baseStart_7675555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7675555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7675555 prefixEnd_7675555 := by exact prefixLift 7675555
  have htrace : WordTrace (prefixWord ++ tailWord_7675555) baseStart_7675555 baseEnd_7675555 := by
    simpa [prefixWord, tailWord_7675555, baseEnd_7675555] using wordTrace_append hprefix tailTrace_7675555
  have hstable : (prefixWord ++ tailWord_7675555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7675555).length < 2 ^ (prefixWord ++ tailWord_7675555).sum := by decide
  have hdescent : baseEnd_7675555 < baseStart_7675555 := by decide
  rcases family_descends (prefixWord ++ tailWord_7675555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7675568 : List Nat := [2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 4]
def baseStart_7675568 : Nat := 118140960795 + 7675568 * 2 ^ 59
def prefixEnd_7675568 : Nat := 4983230072969 + 3 ^ 40 * 7675568 * 2
def baseEnd_7675568 : Nat := 3941255680269330538600711

theorem tailTrace_7675568 : CollatzResearch.WordTrace tailWord_7675568 prefixEnd_7675568 3941255680269330538600711 := by
  unfold tailWord_7675568
  simp only [CollatzResearch.WordTrace]
  refine ⟨139975481928367746747405679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186633975904490328996540905 139975481928367746747405679)
  ·
    refine ⟨209963222892551620121108519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139975481928367746747405679 209963222892551620121108519)
    ·
      refine ⟨314944834338827430181662779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209963222892551620121108519 314944834338827430181662779)
      ·
        refine ⟨472417251508241145272494169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314944834338827430181662779 472417251508241145272494169)
        ·
          refine ⟨354312938631180858954370627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 472417251508241145272494169 354312938631180858954370627)
          ·
            refine ⟨531469407946771288431555941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 354312938631180858954370627 531469407946771288431555941)
            ·
              refine ⟨99650513990019616580916739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 531469407946771288431555941 99650513990019616580916739)
              ·
                refine ⟨149475770985029424871375109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99650513990019616580916739 149475770985029424871375109)
                ·
                  refine ⟨28026707059693017163382833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 149475770985029424871375109 28026707059693017163382833)
                  ·
                    refine ⟨21020030294769762872537125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28026707059693017163382833 21020030294769762872537125)
                    ·
                      refine ⟨3941255680269330538600711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21020030294769762872537125 3941255680269330538600711)
                      ·
                        rfl

theorem cell23_7675568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 4].length) (baseStart_7675568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7675568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7675568 prefixEnd_7675568 := by exact prefixLift 7675568
  have htrace : WordTrace (prefixWord ++ tailWord_7675568) baseStart_7675568 baseEnd_7675568 := by
    simpa [prefixWord, tailWord_7675568, baseEnd_7675568] using wordTrace_append hprefix tailTrace_7675568
  have hstable : (prefixWord ++ tailWord_7675568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7675568).length < 2 ^ (prefixWord ++ tailWord_7675568).sum := by decide
  have hdescent : baseEnd_7675568 < baseStart_7675568 := by decide
  rcases family_descends (prefixWord ++ tailWord_7675568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7675623 : List Nat := [1, 1, 5, 4, 1, 1, 2, 2, 2, 2, 2]
def baseStart_7675623 : Nat := 118140960795 + 7675623 * 2 ^ 59
def prefixEnd_7675623 : Nat := 4983230072969 + 3 ^ 40 * 7675623 * 2
def baseEnd_7675623 : Nat := 3941283921705327823412959

theorem tailTrace_7675623 : CollatzResearch.WordTrace tailWord_7675623 prefixEnd_7675623 3941283921705327823412959 := by
  unfold tailWord_7675623
  simp only [CollatzResearch.WordTrace]
  refine ⟨279952969871536237888063523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186635313247690825258709015 279952969871536237888063523)
  ·
    refine ⟨419929454807304356832095285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279952969871536237888063523 419929454807304356832095285)
    ·
      refine ⟨39368386388184783453008933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 419929454807304356832095285 39368386388184783453008933)
      ·
        refine ⟨7381572447784646897439175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39368386388184783453008933 7381572447784646897439175)
        ·
          refine ⟨11072358671676970346158763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7381572447784646897439175 11072358671676970346158763)
          ·
            refine ⟨16608538007515455519238145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11072358671676970346158763 16608538007515455519238145)
            ·
              refine ⟨12456403505636591639428609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16608538007515455519238145 12456403505636591639428609)
              ·
                refine ⟨9342302629227443729571457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12456403505636591639428609 9342302629227443729571457)
                ·
                  refine ⟨7006726971920582797178593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9342302629227443729571457 7006726971920582797178593)
                  ·
                    refine ⟨5255045228940437097883945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7006726971920582797178593 5255045228940437097883945)
                    ·
                      refine ⟨3941283921705327823412959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5255045228940437097883945 3941283921705327823412959)
                      ·
                        rfl

theorem cell23_7675623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_7675623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7675623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7675623 prefixEnd_7675623 := by exact prefixLift 7675623
  have htrace : WordTrace (prefixWord ++ tailWord_7675623) baseStart_7675623 baseEnd_7675623 := by
    simpa [prefixWord, tailWord_7675623, baseEnd_7675623] using wordTrace_append hprefix tailTrace_7675623
  have hstable : (prefixWord ++ tailWord_7675623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7675623).length < 2 ^ (prefixWord ++ tailWord_7675623).sum := by decide
  have hdescent : baseEnd_7675623 < baseStart_7675623 := by decide
  rcases family_descends (prefixWord ++ tailWord_7675623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7675629 : List Nat := [1, 5, 1, 2, 1, 2, 4, 2, 5]
def baseStart_7675629 : Nat := 118140960795 + 7675629 * 2 ^ 59
def prefixEnd_7675629 : Nat := 4983230072969 + 3 ^ 40 * 7675629 * 2
def baseEnd_7675629 : Nat := 437920778065472755548659

theorem tailTrace_7675629 : CollatzResearch.WordTrace tailWord_7675629 prefixEnd_7675629 437920778065472755548659 := by
  unfold tailWord_7675629
  simp only [CollatzResearch.WordTrace]
  refine ⟨279953188709514500912781941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186635459139676333941854627 279953188709514500912781941)
  ·
    refine ⟨26245611441516984460573307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 279953188709514500912781941 26245611441516984460573307)
    ·
      refine ⟨39368417162275476690859961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26245611441516984460573307 39368417162275476690859961)
      ·
        refine ⟨29526312871706607518144971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39368417162275476690859961 29526312871706607518144971)
        ·
          refine ⟨44289469307559911277217457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29526312871706607518144971 44289469307559911277217457)
          ·
            refine ⟨33217101980669933457913093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44289469307559911277217457 33217101980669933457913093)
            ·
              refine ⟨6228206621375612523358705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33217101980669933457913093 6228206621375612523358705)
              ·
                refine ⟨4671154966031709392519029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6228206621375612523358705 4671154966031709392519029)
                ·
                  refine ⟨437920778065472755548659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4671154966031709392519029 437920778065472755548659)
                  ·
                    rfl

theorem cell23_7675629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 4, 2, 5].length) (baseStart_7675629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7675629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7675629 prefixEnd_7675629 := by exact prefixLift 7675629
  have htrace : WordTrace (prefixWord ++ tailWord_7675629) baseStart_7675629 baseEnd_7675629 := by
    simpa [prefixWord, tailWord_7675629, baseEnd_7675629] using wordTrace_append hprefix tailTrace_7675629
  have hstable : (prefixWord ++ tailWord_7675629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7675629).length < 2 ^ (prefixWord ++ tailWord_7675629).sum := by decide
  have hdescent : baseEnd_7675629 < baseStart_7675629 := by decide
  rcases family_descends (prefixWord ++ tailWord_7675629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7675648 : List Nat := [2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 5]
def baseStart_7675648 : Nat := 118140960795 + 7675648 * 2 ^ 59
def prefixEnd_7675648 : Nat := 4983230072969 + 3 ^ 40 * 7675648 * 2
def baseEnd_7675648 : Nat := 3941296758721690225600343

theorem tailTrace_7675648 : CollatzResearch.WordTrace tailWord_7675648 prefixEnd_7675648 3941296758721690225600343 := by
  unfold tailWord_7675648
  simp only [CollatzResearch.WordTrace]
  refine ⟨139976940848222833578861799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186635921130963778105149065 139976940848222833578861799)
  ·
    refine ⟨209965411272334250368292699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139976940848222833578861799 209965411272334250368292699)
    ·
      refine ⟨314948116908501375552439049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209965411272334250368292699 314948116908501375552439049)
      ·
        refine ⟨236211087681376031664329287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 314948116908501375552439049 236211087681376031664329287)
        ·
          refine ⟨354316631522064047496493931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236211087681376031664329287 354316631522064047496493931)
          ·
            refine ⟨531474947283096071244740897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 354316631522064047496493931 531474947283096071244740897)
            ·
              refine ⟨398606210462322053433555673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 531474947283096071244740897 398606210462322053433555673)
              ·
                refine ⟨298954657846741540075166755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 398606210462322053433555673 298954657846741540075166755)
                ·
                  refine ⟨448431986770112310112750133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 298954657846741540075166755 448431986770112310112750133)
                  ·
                    refine ⟨42040498759698029073070325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 448431986770112310112750133 42040498759698029073070325)
                    ·
                      refine ⟨3941296758721690225600343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42040498759698029073070325 3941296758721690225600343)
                      ·
                        rfl

theorem cell23_7675648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 5].length) (baseStart_7675648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7675648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7675648 prefixEnd_7675648 := by exact prefixLift 7675648
  have htrace : WordTrace (prefixWord ++ tailWord_7675648) baseStart_7675648 baseEnd_7675648 := by
    simpa [prefixWord, tailWord_7675648, baseEnd_7675648] using wordTrace_append hprefix tailTrace_7675648
  have hstable : (prefixWord ++ tailWord_7675648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7675648).length < 2 ^ (prefixWord ++ tailWord_7675648).sum := by decide
  have hdescent : baseEnd_7675648 < baseStart_7675648 := by decide
  rcases family_descends (prefixWord ++ tailWord_7675648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7675662 : List Nat := [4, 1, 1, 2, 1, 1, 5, 1, 2, 1, 4]
def baseStart_7675662 : Nat := 118140960795 + 7675662 * 2 ^ 59
def prefixEnd_7675662 : Nat := 4983230072969 + 3 ^ 40 * 7675662 * 2
def baseEnd_7675662 : Nat := 3941303947450853170825279

theorem tailTrace_7675662 : CollatzResearch.WordTrace tailWord_7675662 prefixEnd_7675662 3941303947450853170825279 := by
  unfold tailWord_7675662
  simp only [CollatzResearch.WordTrace]
  refine ⟨34994299039799368443591655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186636261545596631699155493 34994299039799368443591655)
  ·
    refine ⟨52491448559699052665387483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34994299039799368443591655 52491448559699052665387483)
    ·
      refine ⟨78737172839548578998081225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52491448559699052665387483 78737172839548578998081225)
      ·
        refine ⟨59052879629661434248560919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78737172839548578998081225 59052879629661434248560919)
        ·
          refine ⟨88579319444492151372841379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59052879629661434248560919 88579319444492151372841379)
          ·
            refine ⟨132868979166738227059262069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88579319444492151372841379 132868979166738227059262069)
            ·
              refine ⟨12456466796881708786805819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 132868979166738227059262069 12456466796881708786805819)
              ·
                refine ⟨18684700195322563180208729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12456466796881708786805819 18684700195322563180208729)
                ·
                  refine ⟨14013525146491922385156547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18684700195322563180208729 14013525146491922385156547)
                  ·
                    refine ⟨21020287719737883577734821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14013525146491922385156547 21020287719737883577734821)
                    ·
                      refine ⟨3941303947450853170825279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21020287719737883577734821 3941303947450853170825279)
                      ·
                        rfl

theorem cell23_7675662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 1, 2, 1, 4].length) (baseStart_7675662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7675662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7675662 prefixEnd_7675662 := by exact prefixLift 7675662
  have htrace : WordTrace (prefixWord ++ tailWord_7675662) baseStart_7675662 baseEnd_7675662 := by
    simpa [prefixWord, tailWord_7675662, baseEnd_7675662] using wordTrace_append hprefix tailTrace_7675662
  have hstable : (prefixWord ++ tailWord_7675662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7675662).length < 2 ^ (prefixWord ++ tailWord_7675662).sum := by decide
  have hdescent : baseEnd_7675662 < baseStart_7675662 := by decide
  rcases family_descends (prefixWord ++ tailWord_7675662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7675682 : List Nat := [3, 3, 1, 1, 2, 1, 2, 1, 4, 2, 3]
def baseStart_7675682 : Nat := 118140960795 + 7675682 * 2 ^ 59
def prefixEnd_7675682 : Nat := 4983230072969 + 3 ^ 40 * 7675682 * 2
def baseEnd_7675682 : Nat := 3941314217063943092575187

theorem tailTrace_7675682 : CollatzResearch.WordTrace tailWord_7675682 prefixEnd_7675682 3941314217063943092575187 := by
  unfold tailWord_7675682
  simp only [CollatzResearch.WordTrace]
  refine ⟨69988780444580622741115325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186636747852214993976307533 69988780444580622741115325)
  ·
    refine ⟨26245792666717733527918247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69988780444580622741115325 26245792666717733527918247)
    ·
      refine ⟨39368689000076600291877371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26245792666717733527918247 39368689000076600291877371)
      ·
        refine ⟨59053033500114900437816057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39368689000076600291877371 59053033500114900437816057)
        ·
          refine ⟨44289775125086175328362043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59053033500114900437816057 44289775125086175328362043)
          ·
            refine ⟨66434662687629262992543065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44289775125086175328362043 66434662687629262992543065)
            ·
              refine ⟨49825997015721947244407299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66434662687629262992543065 49825997015721947244407299)
              ·
                refine ⟨74738995523582920866610949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49825997015721947244407299 74738995523582920866610949)
                ·
                  refine ⟨14013561660671797662489553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74738995523582920866610949 14013561660671797662489553)
                  ·
                    refine ⟨10510171245503848246867165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14013561660671797662489553 10510171245503848246867165)
                    ·
                      refine ⟨3941314217063943092575187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10510171245503848246867165 3941314217063943092575187)
                      ·
                        rfl

theorem cell23_7675682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 4, 2, 3].length) (baseStart_7675682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7675682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7675682 prefixEnd_7675682 := by exact prefixLift 7675682
  have htrace : WordTrace (prefixWord ++ tailWord_7675682) baseStart_7675682 baseEnd_7675682 := by
    simpa [prefixWord, tailWord_7675682, baseEnd_7675682] using wordTrace_append hprefix tailTrace_7675682
  have hstable : (prefixWord ++ tailWord_7675682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7675682).length < 2 ^ (prefixWord ++ tailWord_7675682).sum := by decide
  have hdescent : baseEnd_7675682 < baseStart_7675682 := by decide
  rcases family_descends (prefixWord ++ tailWord_7675682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7675685 : List Nat := [1, 3, 1, 2, 3, 3, 1, 1, 8]
def baseStart_7675685 : Nat := 118140960795 + 7675685 * 2 ^ 59
def prefixEnd_7675685 : Nat := 4983230072969 + 3 ^ 40 * 7675685 * 2
def baseEnd_7675685 : Nat := 437923973056211842315297

theorem tailTrace_7675685 : CollatzResearch.WordTrace tailWord_7675685 prefixEnd_7675685 437923973056211842315297 := by
  unfold tailWord_7675685
  simp only [CollatzResearch.WordTrace]
  refine ⟨279955231197311622476820509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186636820798207748317880339 279955231197311622476820509)
  ·
    refine ⟨104983211698991858428807691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 279955231197311622476820509 104983211698991858428807691)
    ·
      refine ⟨157474817548487787643211537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104983211698991858428807691 157474817548487787643211537)
      ·
        refine ⟨118106113161365840732408653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157474817548487787643211537 118106113161365840732408653)
        ·
          refine ⟨44289792435512190274653245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118106113161365840732408653 44289792435512190274653245)
          ·
            refine ⟨16608672163317071352994967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44289792435512190274653245 16608672163317071352994967)
            ·
              refine ⟨24913008244975607029492451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16608672163317071352994967 24913008244975607029492451)
              ·
                refine ⟨37369512367463410544238677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24913008244975607029492451 37369512367463410544238677)
                ·
                  refine ⟨437923973056211842315297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37369512367463410544238677 437923973056211842315297)
                  ·
                    rfl

theorem cell23_7675685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 1, 8].length) (baseStart_7675685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7675685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7675685 prefixEnd_7675685 := by exact prefixLift 7675685
  have htrace : WordTrace (prefixWord ++ tailWord_7675685) baseStart_7675685 baseEnd_7675685 := by
    simpa [prefixWord, tailWord_7675685, baseEnd_7675685] using wordTrace_append hprefix tailTrace_7675685
  have hstable : (prefixWord ++ tailWord_7675685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7675685).length < 2 ^ (prefixWord ++ tailWord_7675685).sum := by decide
  have hdescent : baseEnd_7675685 < baseStart_7675685 := by decide
  rcases family_descends (prefixWord ++ tailWord_7675685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7675722 : List Nat := [3, 1, 2, 1, 1, 1, 3, 3, 1, 5, 2]
def baseStart_7675722 : Nat := 118140960795 + 7675722 * 2 ^ 59
def prefixEnd_7675722 : Nat := 4983230072969 + 3 ^ 40 * 7675722 * 2
def baseEnd_7675722 : Nat := 3941334756290122936075003

theorem tailTrace_7675722 : CollatzResearch.WordTrace tailWord_7675722 prefixEnd_7675722 3941334756290122936075003 := by
  unfold tailWord_7675722
  simp only [CollatzResearch.WordTrace]
  refine ⟨69989145174544394448979355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186637720465451718530611613 69989145174544394448979355)
  ·
    refine ⟨104983717761816591673469033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69989145174544394448979355 104983717761816591673469033)
    ·
      refine ⟨78737788321362443755101775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104983717761816591673469033 78737788321362443755101775)
      ·
        refine ⟨118106682482043665632652663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78737788321362443755101775 118106682482043665632652663)
        ·
          refine ⟨177160023723065498448978995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118106682482043665632652663 177160023723065498448978995)
          ·
            refine ⟨265740035584598247673468493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177160023723065498448978995 265740035584598247673468493)
            ·
              refine ⟨99652513344224342877550685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 265740035584598247673468493 99652513344224342877550685)
              ·
                refine ⟨37369692504084128579081507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99652513344224342877550685 37369692504084128579081507)
                ·
                  refine ⟨56054538756126192868622261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37369692504084128579081507 56054538756126192868622261)
                  ·
                    refine ⟨5255113008386830581433337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56054538756126192868622261 5255113008386830581433337)
                    ·
                      refine ⟨3941334756290122936075003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5255113008386830581433337 3941334756290122936075003)
                      ·
                        rfl

theorem cell23_7675722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 3, 1, 5, 2].length) (baseStart_7675722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7675722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7675722 prefixEnd_7675722 := by exact prefixLift 7675722
  have htrace : WordTrace (prefixWord ++ tailWord_7675722) baseStart_7675722 baseEnd_7675722 := by
    simpa [prefixWord, tailWord_7675722, baseEnd_7675722] using wordTrace_append hprefix tailTrace_7675722
  have hstable : (prefixWord ++ tailWord_7675722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7675722).length < 2 ^ (prefixWord ++ tailWord_7675722).sum := by decide
  have hdescent : baseEnd_7675722 < baseStart_7675722 := by decide
  rcases family_descends (prefixWord ++ tailWord_7675722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7675746 : List Nat := [3, 3, 2, 1, 2, 1, 3, 1, 3, 1, 3]
def baseStart_7675746 : Nat := 118140960795 + 7675746 * 2 ^ 59
def prefixEnd_7675746 : Nat := 4983230072969 + 3 ^ 40 * 7675746 * 2
def baseEnd_7675746 : Nat := 3941347079825830842174893

theorem tailTrace_7675746 : CollatzResearch.WordTrace tailWord_7675746 prefixEnd_7675746 3941347079825830842174893 := by
  unfold tailWord_7675746
  simp only [CollatzResearch.WordTrace]
  refine ⟨69989364012522657473697773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186638304033393753263194061 69989364012522657473697773)
  ·
    refine ⟨26246011504695996552636665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69989364012522657473697773 26246011504695996552636665)
    ·
      refine ⟨19684508628521997414477499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26246011504695996552636665 19684508628521997414477499)
      ·
        refine ⟨29526762942782996121716249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19684508628521997414477499 29526762942782996121716249)
        ·
          refine ⟨22145072207087247091287187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29526762942782996121716249 22145072207087247091287187)
          ·
            refine ⟨33217608310630870636930781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22145072207087247091287187 33217608310630870636930781)
            ·
              refine ⟨12456603116486576488849043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33217608310630870636930781 12456603116486576488849043)
              ·
                refine ⟨18684904674729864733273565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12456603116486576488849043 18684904674729864733273565)
                ·
                  refine ⟨7006839253023699274977587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18684904674729864733273565 7006839253023699274977587)
                  ·
                    refine ⟨10510258879535548912466381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7006839253023699274977587 10510258879535548912466381)
                    ·
                      refine ⟨3941347079825830842174893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10510258879535548912466381 3941347079825830842174893)
                      ·
                        rfl

theorem cell23_7675746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_7675746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7675746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7675746 prefixEnd_7675746 := by exact prefixLift 7675746
  have htrace : WordTrace (prefixWord ++ tailWord_7675746) baseStart_7675746 baseEnd_7675746 := by
    simpa [prefixWord, tailWord_7675746, baseEnd_7675746] using wordTrace_append hprefix tailTrace_7675746
  have hstable : (prefixWord ++ tailWord_7675746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7675746).length < 2 ^ (prefixWord ++ tailWord_7675746).sum := by decide
  have hdescent : baseEnd_7675746 < baseStart_7675746 := by decide
  rcases family_descends (prefixWord ++ tailWord_7675746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7675752 : List Nat := [2, 1, 4, 2, 1, 1, 2, 2, 3, 1, 4]
def baseStart_7675752 : Nat := 118140960795 + 7675752 * 2 ^ 59
def prefixEnd_7675752 : Nat := 4983230072969 + 3 ^ 40 * 7675752 * 2
def baseEnd_7675752 : Nat := 3941350160709757818699865

theorem tailTrace_7675752 : CollatzResearch.WordTrace tailWord_7675752 prefixEnd_7675752 3941350160709757818699865 := by
  unfold tailWord_7675752
  simp only [CollatzResearch.WordTrace]
  refine ⟨139978837444034446459754755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186638449925379261946339673 139978837444034446459754755)
  ·
    refine ⟨209968256166051669689632133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139978837444034446459754755 209968256166051669689632133)
    ·
      refine ⟨39369048031134688066806025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 209968256166051669689632133 39369048031134688066806025)
      ·
        refine ⟨29526786023351016050104519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39369048031134688066806025 29526786023351016050104519)
        ·
          refine ⟨44290179035026524075156779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29526786023351016050104519 44290179035026524075156779)
          ·
            refine ⟨66435268552539786112735169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44290179035026524075156779 66435268552539786112735169)
            ·
              refine ⟨49826451414404839584551377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66435268552539786112735169 49826451414404839584551377)
              ·
                refine ⟨37369838560803629688413533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49826451414404839584551377 37369838560803629688413533)
                ·
                  refine ⟨14013689460301361133155075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37369838560803629688413533 14013689460301361133155075)
                  ·
                    refine ⟨21020534190452041699732613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14013689460301361133155075 21020534190452041699732613)
                    ·
                      refine ⟨3941350160709757818699865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21020534190452041699732613 3941350160709757818699865)
                      ·
                        rfl

theorem cell23_7675752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_7675752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7675752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7675752 prefixEnd_7675752 := by exact prefixLift 7675752
  have htrace : WordTrace (prefixWord ++ tailWord_7675752) baseStart_7675752 baseEnd_7675752 := by
    simpa [prefixWord, tailWord_7675752, baseEnd_7675752] using wordTrace_append hprefix tailTrace_7675752
  have hstable : (prefixWord ++ tailWord_7675752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7675752).length < 2 ^ (prefixWord ++ tailWord_7675752).sum := by decide
  have hdescent : baseEnd_7675752 < baseStart_7675752 := by decide
  rcases family_descends (prefixWord ++ tailWord_7675752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7675755 : List Nat := [1, 1, 1, 1, 2, 2, 3, 1, 2, 6, 3]
def baseStart_7675755 : Nat := 118140960795 + 7675755 * 2 ^ 59
def prefixEnd_7675755 : Nat := 4983230072969 + 3 ^ 40 * 7675755 * 2
def baseEnd_7675755 : Nat := 3941351701151721306962351

theorem tailTrace_7675755 : CollatzResearch.WordTrace tailWord_7675755 prefixEnd_7675755 3941351701151721306962351 := by
  unfold tailWord_7675755
  simp only [CollatzResearch.WordTrace]
  refine ⟨279957784307058024431868719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186638522871372016287912479 279957784307058024431868719)
  ·
    refine ⟨419936676460587036647803079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279957784307058024431868719 419936676460587036647803079)
    ·
      refine ⟨629905014690880554971704619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419936676460587036647803079 629905014690880554971704619)
      ·
        refine ⟨944857522036320832457556929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 629905014690880554971704619 944857522036320832457556929)
        ·
          refine ⟨708643141527240624343167697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 944857522036320832457556929 708643141527240624343167697)
          ·
            refine ⟨531482356145430468257375773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 708643141527240624343167697 531482356145430468257375773)
            ·
              refine ⟨199305883554536425596515915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 531482356145430468257375773 199305883554536425596515915)
              ·
                refine ⟨298958825331804638394773873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199305883554536425596515915 298958825331804638394773873)
                ·
                  refine ⟨224219118998853478796080405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 298958825331804638394773873 224219118998853478796080405)
                  ·
                    refine ⟨10510271203071256818566269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 224219118998853478796080405 10510271203071256818566269)
                    ·
                      refine ⟨3941351701151721306962351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10510271203071256818566269 3941351701151721306962351)
                      ·
                        rfl

theorem cell23_7675755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 6, 3].length) (baseStart_7675755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7675755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7675755 prefixEnd_7675755 := by exact prefixLift 7675755
  have htrace : WordTrace (prefixWord ++ tailWord_7675755) baseStart_7675755 baseEnd_7675755 := by
    simpa [prefixWord, tailWord_7675755, baseEnd_7675755] using wordTrace_append hprefix tailTrace_7675755
  have hstable : (prefixWord ++ tailWord_7675755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7675755).length < 2 ^ (prefixWord ++ tailWord_7675755).sum := by decide
  have hdescent : baseEnd_7675755 < baseStart_7675755 := by decide
  rcases family_descends (prefixWord ++ tailWord_7675755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7675769 : List Nat := [1, 2, 1, 3, 2, 2, 2, 1, 5, 2, 2]
def baseStart_7675769 : Nat := 118140960795 + 7675769 * 2 ^ 59
def prefixEnd_7675769 : Nat := 4983230072969 + 3 ^ 40 * 7675769 * 2
def baseEnd_7675769 : Nat := 3941358889880884252187287

theorem tailTrace_7675769 : CollatzResearch.WordTrace tailWord_7675769 prefixEnd_7675769 3941358889880884252187287 := by
  unfold tailWord_7675769
  simp only [CollatzResearch.WordTrace]
  refine ⟨279958294929007304822878361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186638863286004869881918907 279958294929007304822878361)
  ·
    refine ⟨209968721196755478617158771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279958294929007304822878361 209968721196755478617158771)
    ·
      refine ⟨314953081795133217925738157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209968721196755478617158771 314953081795133217925738157)
      ·
        refine ⟨118107405673174956722151809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 314953081795133217925738157 118107405673174956722151809)
        ·
          refine ⟨88580554254881217541613857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118107405673174956722151809 88580554254881217541613857)
          ·
            refine ⟨66435415691160913156210393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88580554254881217541613857 66435415691160913156210393)
            ·
              refine ⟨49826561768370684867157795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66435415691160913156210393 49826561768370684867157795)
              ·
                refine ⟨74739842652556027300736693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49826561768370684867157795 74739842652556027300736693)
                ·
                  refine ⟨7006860248677127559444065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74739842652556027300736693 7006860248677127559444065)
                  ·
                    refine ⟨5255145186507845669583049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7006860248677127559444065 5255145186507845669583049)
                    ·
                      refine ⟨3941358889880884252187287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5255145186507845669583049 3941358889880884252187287)
                      ·
                        rfl

theorem cell23_7675769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 5, 2, 2].length) (baseStart_7675769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7675769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7675769 prefixEnd_7675769 := by exact prefixLift 7675769
  have htrace : WordTrace (prefixWord ++ tailWord_7675769) baseStart_7675769 baseEnd_7675769 := by
    simpa [prefixWord, tailWord_7675769, baseEnd_7675769] using wordTrace_append hprefix tailTrace_7675769
  have hstable : (prefixWord ++ tailWord_7675769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7675769).length < 2 ^ (prefixWord ++ tailWord_7675769).sum := by decide
  have hdescent : baseEnd_7675769 < baseStart_7675769 := by decide
  rcases family_descends (prefixWord ++ tailWord_7675769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7675796 : List Nat := [2, 4, 2, 1, 1, 3, 2, 2, 2, 4]
def baseStart_7675796 : Nat := 118140960795 + 7675796 * 2 ^ 59
def prefixEnd_7675796 : Nat := 4983230072969 + 3 ^ 40 * 7675796 * 2
def baseEnd_7675796 : Nat := 1313790917952851882183221

theorem tailTrace_7675796 : CollatzResearch.WordTrace tailWord_7675796 prefixEnd_7675796 1313790917952851882183221 := by
  unfold tailWord_7675796
  simp only [CollatzResearch.WordTrace]
  refine ⟨139979639849954744217055621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186639519799939658956074161 139979639849954744217055621)
  ·
    refine ⟨26246182471866514540697929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139979639849954744217055621 26246182471866514540697929)
    ·
      refine ⟨19684636853899885905523447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26246182471866514540697929 19684636853899885905523447)
      ·
        refine ⟨29526955280849828858285171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19684636853899885905523447 29526955280849828858285171)
        ·
          refine ⟨44290432921274743287427757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29526955280849828858285171 44290432921274743287427757)
          ·
            refine ⟨16608912345478028732785409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44290432921274743287427757 16608912345478028732785409)
            ·
              refine ⟨12456684259108521549589057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16608912345478028732785409 12456684259108521549589057)
              ·
                refine ⟨9342513194331391162191793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12456684259108521549589057 9342513194331391162191793)
                ·
                  refine ⟨7006884895748543371643845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9342513194331391162191793 7006884895748543371643845)
                  ·
                    refine ⟨1313790917952851882183221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7006884895748543371643845 1313790917952851882183221)
                    ·
                      rfl

theorem cell23_7675796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_7675796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7675796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7675796 prefixEnd_7675796 := by exact prefixLift 7675796
  have htrace : WordTrace (prefixWord ++ tailWord_7675796) baseStart_7675796 baseEnd_7675796 := by
    simpa [prefixWord, tailWord_7675796, baseEnd_7675796] using wordTrace_append hprefix tailTrace_7675796
  have hstable : (prefixWord ++ tailWord_7675796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7675796).length < 2 ^ (prefixWord ++ tailWord_7675796).sum := by decide
  have hdescent : baseEnd_7675796 < baseStart_7675796 := by decide
  rcases family_descends (prefixWord ++ tailWord_7675796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7675809 : List Nat := [1, 2, 3, 4, 2, 2, 1, 8]
def baseStart_7675809 : Nat := 118140960795 + 7675809 * 2 ^ 59
def prefixEnd_7675809 : Nat := 4983230072969 + 3 ^ 40 * 7675809 * 2
def baseEnd_7675809 : Nat := 145977015892854225766189

theorem tailTrace_7675809 : CollatzResearch.WordTrace tailWord_7675809 prefixEnd_7675809 145977015892854225766189 := by
  unfold tailWord_7675809
  simp only [CollatzResearch.WordTrace]
  refine ⟨279959753848862391654334481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186639835899241594436222987 279959753848862391654334481)
  ·
    refine ⟨209969815386646793740750861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279959753848862391654334481 209969815386646793740750861)
    ·
      refine ⟨78738680769992547652781573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209969815386646793740750861 78738680769992547652781573)
      ·
        refine ⟨14763502644373602684896545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78738680769992547652781573 14763502644373602684896545)
        ·
          refine ⟨11072626983280202013672409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14763502644373602684896545 11072626983280202013672409)
          ·
            refine ⟨8304470237460151510254307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11072626983280202013672409 8304470237460151510254307)
            ·
              refine ⟨12456705356190227265381461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8304470237460151510254307 12456705356190227265381461)
              ·
                refine ⟨145977015892854225766189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12456705356190227265381461 145977015892854225766189)
                ·
                  rfl

theorem cell23_7675809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 8].length) (baseStart_7675809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7675809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7675809 prefixEnd_7675809 := by exact prefixLift 7675809
  have htrace : WordTrace (prefixWord ++ tailWord_7675809) baseStart_7675809 baseEnd_7675809 := by
    simpa [prefixWord, tailWord_7675809, baseEnd_7675809] using wordTrace_append hprefix tailTrace_7675809
  have hstable : (prefixWord ++ tailWord_7675809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7675809).length < 2 ^ (prefixWord ++ tailWord_7675809).sum := by decide
  have hdescent : baseEnd_7675809 < baseStart_7675809 := by decide
  rcases family_descends (prefixWord ++ tailWord_7675809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7675835 : List Nat := [1, 1, 1, 1, 1, 2, 2, 4, 4, 6]
def baseStart_7675835 : Nat := 118140960795 + 7675835 * 2 ^ 59
def prefixEnd_7675835 : Nat := 4983230072969 + 3 ^ 40 * 7675835 * 2
def baseEnd_7675835 : Nat := 1313797593201360331320661

theorem tailTrace_7675835 : CollatzResearch.WordTrace tailWord_7675835 prefixEnd_7675835 1313797593201360331320661 := by
  unfold tailWord_7675835
  simp only [CollatzResearch.WordTrace]
  refine ⟨279960702146768198094780959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186640468097845465396520639 279960702146768198094780959)
  ·
    refine ⟨419941053220152297142171439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279960702146768198094780959 419941053220152297142171439)
    ·
      refine ⟨629911579830228445713257159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419941053220152297142171439 629911579830228445713257159)
      ·
        refine ⟨944867369745342668569885739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 629911579830228445713257159 944867369745342668569885739)
        ·
          refine ⟨1417301054618014002854828609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 944867369745342668569885739 1417301054618014002854828609)
          ·
            refine ⟨1062975790963510502141121457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1417301054618014002854828609 1062975790963510502141121457)
            ·
              refine ⟨797231843222632876605841093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1062975790963510502141121457 797231843222632876605841093)
              ·
                refine ⟨149480970604243664363595205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 797231843222632876605841093 149480970604243664363595205)
                ·
                  refine ⟨28027681988295687068174101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 149480970604243664363595205 28027681988295687068174101)
                  ·
                    refine ⟨1313797593201360331320661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28027681988295687068174101 1313797593201360331320661)
                    ·
                      rfl

theorem cell23_7675835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4, 6].length) (baseStart_7675835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7675835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7675835 prefixEnd_7675835 := by exact prefixLift 7675835
  have htrace : WordTrace (prefixWord ++ tailWord_7675835) baseStart_7675835 baseEnd_7675835 := by
    simpa [prefixWord, tailWord_7675835, baseEnd_7675835] using wordTrace_append hprefix tailTrace_7675835
  have hstable : (prefixWord ++ tailWord_7675835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7675835).length < 2 ^ (prefixWord ++ tailWord_7675835).sum := by decide
  have hdescent : baseEnd_7675835 < baseStart_7675835 := by decide
  rcases family_descends (prefixWord ++ tailWord_7675835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7675852 : List Nat := [2, 2, 1, 4, 1, 2, 1, 2, 2, 6]
def baseStart_7675852 : Nat := 118140960795 + 7675852 * 2 ^ 59
def prefixEnd_7675852 : Nat := 4983230072969 + 3 ^ 40 * 7675852 * 2
def baseEnd_7675852 : Nat := 1313800502925069142483135

theorem tailTrace_7675852 : CollatzResearch.WordTrace tailWord_7675852 prefixEnd_7675852 1313800502925069142483135 := by
  unfold tailWord_7675852
  simp only [CollatzResearch.WordTrace]
  refine ⟨139980661093853304999074905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186640881458471073332099873 139980661093853304999074905)
  ·
    refine ⟨104985495820389978749306179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139980661093853304999074905 104985495820389978749306179)
    ·
      refine ⟨157478243730584968123959269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104985495820389978749306179 157478243730584968123959269)
      ·
        refine ⟨29527170699484681523242363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157478243730584968123959269 29527170699484681523242363)
        ·
          refine ⟨44290756049227022284863545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29527170699484681523242363 44290756049227022284863545)
          ·
            refine ⟨33218067036920266713647659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44290756049227022284863545 33218067036920266713647659)
            ·
              refine ⟨49827100555380400070471489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33218067036920266713647659 49827100555380400070471489)
              ·
                refine ⟨37370325416535300052853617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49827100555380400070471489 37370325416535300052853617)
                ·
                  refine ⟨28027744062401475039640213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37370325416535300052853617 28027744062401475039640213)
                  ·
                    refine ⟨1313800502925069142483135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28027744062401475039640213 1313800502925069142483135)
                    ·
                      rfl

theorem cell23_7675852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 2, 2, 6].length) (baseStart_7675852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7675852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7675852 prefixEnd_7675852 := by exact prefixLift 7675852
  have htrace : WordTrace (prefixWord ++ tailWord_7675852) baseStart_7675852 baseEnd_7675852 := by
    simpa [prefixWord, tailWord_7675852, baseEnd_7675852] using wordTrace_append hprefix tailTrace_7675852
  have hstable : (prefixWord ++ tailWord_7675852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7675852).length < 2 ^ (prefixWord ++ tailWord_7675852).sum := by decide
  have hdescent : baseEnd_7675852 < baseStart_7675852 := by decide
  rcases family_descends (prefixWord ++ tailWord_7675852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7675882 : List Nat := [3, 1, 3, 1, 2, 1, 1, 4, 7]
def baseStart_7675882 : Nat := 118140960795 + 7675882 * 2 ^ 59
def prefixEnd_7675882 : Nat := 4983230072969 + 3 ^ 40 * 7675882 * 2
def baseEnd_7675882 : Nat := 437935212577204701119363

theorem tailTrace_7675882 : CollatzResearch.WordTrace tailWord_7675882 prefixEnd_7675882 437935212577204701119363 := by
  unfold tailWord_7675882
  simp only [CollatzResearch.WordTrace]
  refine ⟨69990604094399481280435475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186641610918398616747827933 69990604094399481280435475)
  ·
    refine ⟨104985906141599221920653213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69990604094399481280435475 104985906141599221920653213)
    ·
      refine ⟨39369714803099708220244955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104985906141599221920653213 39369714803099708220244955)
      ·
        refine ⟨59054572204649562330367433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39369714803099708220244955 59054572204649562330367433)
        ·
          refine ⟨44290929153487171747775575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59054572204649562330367433 44290929153487171747775575)
          ·
            refine ⟨66436393730230757621663363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44290929153487171747775575 66436393730230757621663363)
            ·
              refine ⟨99654590595346136432495045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66436393730230757621663363 99654590595346136432495045)
              ·
                refine ⟨18685235736627400581092821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99654590595346136432495045 18685235736627400581092821)
                ·
                  refine ⟨437935212577204701119363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18685235736627400581092821 437935212577204701119363)
                  ·
                    rfl

theorem cell23_7675882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 4, 7].length) (baseStart_7675882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7675882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7675882 prefixEnd_7675882 := by exact prefixLift 7675882
  have htrace : WordTrace (prefixWord ++ tailWord_7675882) baseStart_7675882 baseEnd_7675882 := by
    simpa [prefixWord, tailWord_7675882, baseEnd_7675882] using wordTrace_append hprefix tailTrace_7675882
  have hstable : (prefixWord ++ tailWord_7675882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7675882).length < 2 ^ (prefixWord ++ tailWord_7675882).sum := by decide
  have hdescent : baseEnd_7675882 < baseStart_7675882 := by decide
  rcases family_descends (prefixWord ++ tailWord_7675882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7675899 : List Nat := [1, 1, 1, 1, 1, 3, 7, 3, 5]
def baseStart_7675899 : Nat := 118140960795 + 7675899 * 2 ^ 59
def prefixEnd_7675899 : Nat := 4983230072969 + 3 ^ 40 * 7675899 * 2
def baseEnd_7675899 : Nat := 437936182485107638173521

theorem tailTrace_7675899 : CollatzResearch.WordTrace tailWord_7675899 prefixEnd_7675899 437936182485107638173521 := by
  unfold tailWord_7675899
  simp only [CollatzResearch.WordTrace]
  refine ⟨279963036418536337025110751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186642024279024224683407167 279963036418536337025110751)
  ·
    refine ⟨419944554627804505537666127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279963036418536337025110751 419944554627804505537666127)
    ·
      refine ⟨629916831941706758306499191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419944554627804505537666127 629916831941706758306499191)
      ·
        refine ⟨944875247912560137459748787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 629916831941706758306499191 944875247912560137459748787)
        ·
          refine ⟨1417312871868840206189623181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 944875247912560137459748787 1417312871868840206189623181)
          ·
            refine ⟨531492326950815077321108693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1417312871868840206189623181 531492326950815077321108693)
            ·
              refine ⟨12456851412909728374713485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 531492326950815077321108693 12456851412909728374713485)
              ·
                refine ⟨4671319279841148140517557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12456851412909728374713485 4671319279841148140517557)
                ·
                  refine ⟨437936182485107638173521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4671319279841148140517557 437936182485107638173521)
                  ·
                    rfl

theorem cell23_7675899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 3, 5].length) (baseStart_7675899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7675899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7675899 prefixEnd_7675899 := by exact prefixLift 7675899
  have htrace : WordTrace (prefixWord ++ tailWord_7675899) baseStart_7675899 baseEnd_7675899 := by
    simpa [prefixWord, tailWord_7675899, baseEnd_7675899] using wordTrace_append hprefix tailTrace_7675899
  have hstable : (prefixWord ++ tailWord_7675899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7675899).length < 2 ^ (prefixWord ++ tailWord_7675899).sum := by decide
  have hdescent : baseEnd_7675899 < baseStart_7675899 := by decide
  rcases family_descends (prefixWord ++ tailWord_7675899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7675916 : List Nat := [2, 2, 1, 2, 3, 1, 5, 2, 5]
def baseStart_7675916 : Nat := 118140960795 + 7675916 * 2 ^ 59
def prefixEnd_7675916 : Nat := 4983230072969 + 3 ^ 40 * 7675916 * 2
def baseEnd_7675916 : Nat := 437937152393010575227679

theorem tailTrace_7675916 : CollatzResearch.WordTrace tailWord_7675916 prefixEnd_7675916 437937152393010575227679 := by
  unfold tailWord_7675916
  simp only [CollatzResearch.WordTrace]
  refine ⟨139981828229737374464239801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186642437639649832618986401 139981828229737374464239801)
  ·
    refine ⟨104986371172303030848179851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139981828229737374464239801 104986371172303030848179851)
    ·
      refine ⟨157479556758454546272269777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104986371172303030848179851 157479556758454546272269777)
      ·
        refine ⟨118109667568840909704202333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157479556758454546272269777 118109667568840909704202333)
        ·
          refine ⟨44291125338315341139075875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118109667568840909704202333 44291125338315341139075875)
          ·
            refine ⟨66436688007473011708613813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44291125338315341139075875 66436688007473011708613813)
            ·
              refine ⟨6228439500700594847682545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66436688007473011708613813 6228439500700594847682545)
              ·
                refine ⟨4671329625525446135761909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6228439500700594847682545 4671329625525446135761909)
                ·
                  refine ⟨437937152393010575227679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4671329625525446135761909 437937152393010575227679)
                  ·
                    rfl

theorem cell23_7675916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 5, 2, 5].length) (baseStart_7675916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7675916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7675916 prefixEnd_7675916 := by exact prefixLift 7675916
  have htrace : WordTrace (prefixWord ++ tailWord_7675916) baseStart_7675916 baseEnd_7675916 := by
    simpa [prefixWord, tailWord_7675916, baseEnd_7675916] using wordTrace_append hprefix tailTrace_7675916
  have hstable : (prefixWord ++ tailWord_7675916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7675916).length < 2 ^ (prefixWord ++ tailWord_7675916).sum := by decide
  have hdescent : baseEnd_7675916 < baseStart_7675916 := by decide
  rcases family_descends (prefixWord ++ tailWord_7675916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7675927 : List Nat := [1, 1, 3, 5, 2, 2, 2, 1, 2, 2, 2]
def baseStart_7675927 : Nat := 118140960795 + 7675927 * 2 ^ 59
def prefixEnd_7675927 : Nat := 4983230072969 + 3 ^ 40 * 7675927 * 2
def baseEnd_7675927 : Nat := 3941440019824294634011561

theorem tailTrace_7675927 : CollatzResearch.WordTrace tailWord_7675927 prefixEnd_7675927 3941440019824294634011561 := by
  unfold tailWord_7675927
  simp only [CollatzResearch.WordTrace]
  refine ⟨279964057662434897807130035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186642705108289931871420023 279964057662434897807130035)
  ·
    refine ⟨419946086493652346710695053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279964057662434897807130035 419946086493652346710695053)
    ·
      refine ⟨157479782435119630016510645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 419946086493652346710695053 157479782435119630016510645)
      ·
        refine ⟨14763729603292465314047873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 157479782435119630016510645 14763729603292465314047873)
        ·
          refine ⟨11072797202469348985535905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14763729603292465314047873 11072797202469348985535905)
          ·
            refine ⟨8304597901852011739151929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11072797202469348985535905 8304597901852011739151929)
            ·
              refine ⟨6228448426389008804363947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8304597901852011739151929 6228448426389008804363947)
              ·
                refine ⟨9342672639583513206545921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6228448426389008804363947 9342672639583513206545921)
                ·
                  refine ⟨7007004479687634904909441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9342672639583513206545921 7007004479687634904909441)
                  ·
                    refine ⟨5255253359765726178682081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7007004479687634904909441 5255253359765726178682081)
                    ·
                      refine ⟨3941440019824294634011561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5255253359765726178682081 3941440019824294634011561)
                      ·
                        rfl

theorem cell23_7675927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_7675927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7675927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7675927 prefixEnd_7675927 := by exact prefixLift 7675927
  have htrace : WordTrace (prefixWord ++ tailWord_7675927) baseStart_7675927 baseEnd_7675927 := by
    simpa [prefixWord, tailWord_7675927, baseEnd_7675927] using wordTrace_append hprefix tailTrace_7675927
  have hstable : (prefixWord ++ tailWord_7675927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7675927).length < 2 ^ (prefixWord ++ tailWord_7675927).sum := by decide
  have hdescent : baseEnd_7675927 < baseStart_7675927 := by decide
  rcases family_descends (prefixWord ++ tailWord_7675927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7675946 : List Nat := [3, 1, 4, 1, 2, 2, 2, 1, 2, 5]
def baseStart_7675946 : Nat := 118140960795 + 7675946 * 2 ^ 59
def prefixEnd_7675946 : Nat := 4983230072969 + 3 ^ 40 * 7675946 * 2
def baseEnd_7675946 : Nat := 1313816591985576686557991

theorem tailTrace_7675946 : CollatzResearch.WordTrace tailWord_7675946 prefixEnd_7675946 1313816591985576686557991 := by
  unfold tailWord_7675946
  simp only [CollatzResearch.WordTrace]
  refine ⟨69991187662341516013017923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186643167099577376034714461 69991187662341516013017923)
  ·
    refine ⟨104986781493512274019526885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69991187662341516013017923 104986781493512274019526885)
    ·
      refine ⟨19685021530033551378661291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104986781493512274019526885 19685021530033551378661291)
      ·
        refine ⟨29527532295050327067991937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19685021530033551378661291 29527532295050327067991937)
        ·
          refine ⟨22145649221287745300993953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29527532295050327067991937 22145649221287745300993953)
          ·
            refine ⟨16609236915965808975745465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22145649221287745300993953 16609236915965808975745465)
            ·
              refine ⟨12456927686974356731809099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16609236915965808975745465 12456927686974356731809099)
              ·
                refine ⟨18685391530461535097713649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12456927686974356731809099 18685391530461535097713649)
                ·
                  refine ⟨14014043647846151323285237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18685391530461535097713649 14014043647846151323285237)
                  ·
                    refine ⟨1313816591985576686557991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14014043647846151323285237 1313816591985576686557991)
                    ·
                      rfl

theorem cell23_7675946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_7675946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7675946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7675946 prefixEnd_7675946 := by exact prefixLift 7675946
  have htrace : WordTrace (prefixWord ++ tailWord_7675946) baseStart_7675946 baseEnd_7675946 := by
    simpa [prefixWord, tailWord_7675946, baseEnd_7675946] using wordTrace_append hprefix tailTrace_7675946
  have hstable : (prefixWord ++ tailWord_7675946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7675946).length < 2 ^ (prefixWord ++ tailWord_7675946).sum := by decide
  have hdescent : baseEnd_7675946 < baseStart_7675946 := by decide
  rcases family_descends (prefixWord ++ tailWord_7675946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7675962 : List Nat := [3, 1, 1, 1, 3, 1, 1, 3, 2, 1, 6]
def baseStart_7675962 : Nat := 118140960795 + 7675962 * 2 ^ 59
def prefixEnd_7675962 : Nat := 4983230072969 + 3 ^ 40 * 7675962 * 2
def baseEnd_7675962 : Nat := 3941457991647201997073899

theorem tailTrace_7675962 : CollatzResearch.WordTrace tailWord_7675962 prefixEnd_7675962 3941457991647201997073899 := by
  unfold tailWord_7675962
  simp only [CollatzResearch.WordTrace]
  refine ⟨69991333554327024696163535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186643556144872065856436093 69991333554327024696163535)
  ·
    refine ⟨104987000331490537044245303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69991333554327024696163535 104987000331490537044245303)
    ·
      refine ⟨157480500497235805566367955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104987000331490537044245303 157480500497235805566367955)
      ·
        refine ⟨236220750745853708349551933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157480500497235805566367955 236220750745853708349551933)
        ·
          refine ⟨88582781529695140631081975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 236220750745853708349551933 88582781529695140631081975)
          ·
            refine ⟨132874172294542710946622963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88582781529695140631081975 132874172294542710946622963)
            ·
              refine ⟨199311258441814066419934445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132874172294542710946622963 199311258441814066419934445)
              ·
                refine ⟨74741721915680274907475417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 199311258441814066419934445 74741721915680274907475417)
                ·
                  refine ⟨56056291436760206180606563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74741721915680274907475417 56056291436760206180606563)
                  ·
                    refine ⟨84084437155140309270909845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56056291436760206180606563 84084437155140309270909845)
                    ·
                      refine ⟨3941457991647201997073899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84084437155140309270909845 3941457991647201997073899)
                      ·
                        rfl

theorem cell23_7675962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 2, 1, 6].length) (baseStart_7675962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7675962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7675962 prefixEnd_7675962 := by exact prefixLift 7675962
  have htrace : WordTrace (prefixWord ++ tailWord_7675962) baseStart_7675962 baseEnd_7675962 := by
    simpa [prefixWord, tailWord_7675962, baseEnd_7675962] using wordTrace_append hprefix tailTrace_7675962
  have hstable : (prefixWord ++ tailWord_7675962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7675962).length < 2 ^ (prefixWord ++ tailWord_7675962).sum := by decide
  have hdescent : baseEnd_7675962 < baseStart_7675962 := by decide
  rcases family_descends (prefixWord ++ tailWord_7675962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7675989 : List Nat := [1, 3, 2, 2, 1, 3, 2, 3, 6]
def baseStart_7675989 : Nat := 118140960795 + 7675989 * 2 ^ 59
def prefixEnd_7675989 : Nat := 4983230072969 + 3 ^ 40 * 7675989 * 2
def baseEnd_7675989 : Nat := 437941317291652599048475

theorem tailTrace_7675989 : CollatzResearch.WordTrace tailWord_7675989 prefixEnd_7675989 437941317291652599048475 := by
  unfold tailWord_7675989
  simp only [CollatzResearch.WordTrace]
  refine ⟨279966318988210282395887021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186644212658806854930591347 279966318988210282395887021)
  ·
    refine ⟨104987369620578855898457633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 279966318988210282395887021 104987369620578855898457633)
    ·
      refine ⟨78740527215434141923843225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104987369620578855898457633 78740527215434141923843225)
      ·
        refine ⟨59055395411575606442882419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78740527215434141923843225 59055395411575606442882419)
        ·
          refine ⟨88583093117363409664323629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59055395411575606442882419 88583093117363409664323629)
          ·
            refine ⟨33218659919011278624121361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88583093117363409664323629 33218659919011278624121361)
            ·
              refine ⟨24913994939258458968091021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33218659919011278624121361 24913994939258458968091021)
              ·
                refine ⟨9342748102221922113034133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24913994939258458968091021 9342748102221922113034133)
                ·
                  refine ⟨437941317291652599048475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9342748102221922113034133 437941317291652599048475)
                  ·
                    rfl

theorem cell23_7675989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 3, 6].length) (baseStart_7675989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7675989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7675989 prefixEnd_7675989 := by exact prefixLift 7675989
  have htrace : WordTrace (prefixWord ++ tailWord_7675989) baseStart_7675989 baseEnd_7675989 := by
    simpa [prefixWord, tailWord_7675989, baseEnd_7675989] using wordTrace_append hprefix tailTrace_7675989
  have hstable : (prefixWord ++ tailWord_7675989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7675989).length < 2 ^ (prefixWord ++ tailWord_7675989).sum := by decide
  have hdescent : baseEnd_7675989 < baseStart_7675989 := by decide
  rcases family_descends (prefixWord ++ tailWord_7675989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7676010 : List Nat := [3, 1, 3, 2, 3, 1, 2, 3, 1, 4]
def baseStart_7676010 : Nat := 118140960795 + 7676010 * 2 ^ 59
def prefixEnd_7676010 : Nat := 4983230072969 + 3 ^ 40 * 7676010 * 2
def baseEnd_7676010 : Nat := 1313827546239539269757893

theorem tailTrace_7676010 : CollatzResearch.WordTrace tailWord_7676010 prefixEnd_7676010 1313827546239539269757893 := by
  unfold tailWord_7676010
  simp only [CollatzResearch.WordTrace]
  refine ⟨69991771230283550745600371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186644723280756135321600989 69991771230283550745600371)
  ·
    refine ⟨104987656845425326118400557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69991771230283550745600371 104987656845425326118400557)
    ·
      refine ⟨39370371317034497294400209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104987656845425326118400557 39370371317034497294400209)
      ·
        refine ⟨29527778487775872970800157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39370371317034497294400209 29527778487775872970800157)
        ·
          refine ⟨11072916932915952364050059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29527778487775872970800157 11072916932915952364050059)
          ·
            refine ⟨16609375399373928546075089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11072916932915952364050059 16609375399373928546075089)
            ·
              refine ⟨12457031549530446409556317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16609375399373928546075089 12457031549530446409556317)
              ·
                refine ⟨4671386831073917403583619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12457031549530446409556317 4671386831073917403583619)
                ·
                  refine ⟨7007080246610876105375429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4671386831073917403583619 7007080246610876105375429)
                  ·
                    refine ⟨1313827546239539269757893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7007080246610876105375429 1313827546239539269757893)
                    ·
                      rfl

theorem cell23_7676010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 3, 1, 4].length) (baseStart_7676010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7676010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7676010 prefixEnd_7676010 := by exact prefixLift 7676010
  have htrace : WordTrace (prefixWord ++ tailWord_7676010) baseStart_7676010 baseEnd_7676010 := by
    simpa [prefixWord, tailWord_7676010, baseEnd_7676010] using wordTrace_append hprefix tailTrace_7676010
  have hstable : (prefixWord ++ tailWord_7676010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7676010).length < 2 ^ (prefixWord ++ tailWord_7676010).sum := by decide
  have hdescent : baseEnd_7676010 < baseStart_7676010 := by decide
  rcases family_descends (prefixWord ++ tailWord_7676010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7676039 : List Nat := [1, 1, 4, 2, 1, 1, 2, 1, 5, 1, 4]
def baseStart_7676039 : Nat := 118140960795 + 7676039 * 2 ^ 59
def prefixEnd_7676039 : Nat := 4983230072969 + 3 ^ 40 * 7676039 * 2
def baseEnd_7676039 : Nat := 3941497529657598195811045

theorem tailTrace_7676039 : CollatzResearch.WordTrace tailWord_7676039 prefixEnd_7676039 3941497529657598195811045 := by
  unfold tailWord_7676039
  simp only [CollatzResearch.WordTrace]
  refine ⟨279968142638029140935207171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186645428425352760623471447 279968142638029140935207171)
  ·
    refine ⟨419952213957043711402810757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279968142638029140935207171 419952213957043711402810757)
    ·
      refine ⟨78741040116945695888027017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 419952213957043711402810757 78741040116945695888027017)
      ·
        refine ⟨59055780087709271916020263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78741040116945695888027017 59055780087709271916020263)
        ·
          refine ⟨88583670131563907874030395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59055780087709271916020263 88583670131563907874030395)
          ·
            refine ⟨132875505197345861811045593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88583670131563907874030395 132875505197345861811045593)
            ·
              refine ⟨99656628898009396358284195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132875505197345861811045593 99656628898009396358284195)
              ·
                refine ⟨149484943347014094537426293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99656628898009396358284195 149484943347014094537426293)
                ·
                  refine ⟨14014213438782571362883715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 149484943347014094537426293 14014213438782571362883715)
                  ·
                    refine ⟨21021320158173857044325573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14014213438782571362883715 21021320158173857044325573)
                    ·
                      refine ⟨3941497529657598195811045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21021320158173857044325573 3941497529657598195811045)
                      ·
                        rfl

theorem cell23_7676039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_7676039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7676039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7676039 prefixEnd_7676039 := by exact prefixLift 7676039
  have htrace : WordTrace (prefixWord ++ tailWord_7676039) baseStart_7676039 baseEnd_7676039 := by
    simpa [prefixWord, tailWord_7676039, baseEnd_7676039] using wordTrace_append hprefix tailTrace_7676039
  have hstable : (prefixWord ++ tailWord_7676039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7676039).length < 2 ^ (prefixWord ++ tailWord_7676039).sum := by decide
  have hdescent : baseEnd_7676039 < baseStart_7676039 := by decide
  rcases family_descends (prefixWord ++ tailWord_7676039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7676069 : List Nat := [1, 3, 1, 2, 1, 3, 2, 1, 3, 2, 4]
def baseStart_7676069 : Nat := 118140960795 + 7676069 * 2 ^ 59
def prefixEnd_7676069 : Nat := 4983230072969 + 3 ^ 40 * 7676069 * 2
def baseEnd_7676069 : Nat := 3941512934077233078435907

theorem tailTrace_7676069 : CollatzResearch.WordTrace tailWord_7676069 prefixEnd_7676069 3941512934077233078435907 := by
  unfold tailWord_7676069
  simp only [CollatzResearch.WordTrace]
  refine ⟨279969236827920456058799261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186646157885280304039199507 279969236827920456058799261)
  ·
    refine ⟨104988463810470171022049723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 279969236827920456058799261 104988463810470171022049723)
    ·
      refine ⟨157482695715705256533074585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104988463810470171022049723 157482695715705256533074585)
      ·
        refine ⟨118112021786778942399805939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157482695715705256533074585 118112021786778942399805939)
        ·
          refine ⟨177168032680168413599708909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118112021786778942399805939 177168032680168413599708909)
          ·
            refine ⟨66438012255063155099890841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177168032680168413599708909 66438012255063155099890841)
            ·
              refine ⟨49828509191297366324918131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66438012255063155099890841 49828509191297366324918131)
              ·
                refine ⟨74742763786946049487377197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49828509191297366324918131 74742763786946049487377197)
                ·
                  refine ⟨28028536420104768557766449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74742763786946049487377197 28028536420104768557766449)
                  ·
                    refine ⟨21021402315078576418324837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28028536420104768557766449 21021402315078576418324837)
                    ·
                      refine ⟨3941512934077233078435907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21021402315078576418324837 3941512934077233078435907)
                      ·
                        rfl

theorem cell23_7676069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 3, 2, 4].length) (baseStart_7676069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7676069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7676069 prefixEnd_7676069 := by exact prefixLift 7676069
  have htrace : WordTrace (prefixWord ++ tailWord_7676069) baseStart_7676069 baseEnd_7676069 := by
    simpa [prefixWord, tailWord_7676069, baseEnd_7676069] using wordTrace_append hprefix tailTrace_7676069
  have hstable : (prefixWord ++ tailWord_7676069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7676069).length < 2 ^ (prefixWord ++ tailWord_7676069).sum := by decide
  have hdescent : baseEnd_7676069 < baseStart_7676069 := by decide
  rcases family_descends (prefixWord ++ tailWord_7676069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
