import V185TrunkScan22Chunk122

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1100798 : List Nat := [4, 2, 2, 2, 2, 2, 1, 1, 2, 4]
def baseStart_1100798 : Nat := 118140960795 + 1100798 * 2 ^ 59
def prefixEnd_1100798 : Nat := 4983230072969 + 3 ^ 40 * 1100798 * 2
def baseEnd_1100798 : Nat := 376825651672059570975019

theorem tailTrace_1100798 : CollatzResearch.WordTrace tailWord_1100798 prefixEnd_1100798 376825651672059570975019 := by
  unfold tailWord_1100798
  simp only [CollatzResearch.WordTrace]
  refine ⟨5018675183250540271994881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26766267644002881450639365 5018675183250540271994881)
  ·
    refine ⟨3764006387437905203996161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5018675183250540271994881 3764006387437905203996161)
    ·
      refine ⟨2823004790578428902997121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3764006387437905203996161 2823004790578428902997121)
      ·
        refine ⟨2117253592933821677247841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2823004790578428902997121 2117253592933821677247841)
        ·
          refine ⟨1587940194700366257935881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2117253592933821677247841 1587940194700366257935881)
          ·
            refine ⟨1190955146025274693451911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1587940194700366257935881 1190955146025274693451911)
            ·
              refine ⟨1786432719037912040177867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1190955146025274693451911 1786432719037912040177867)
              ·
                refine ⟨2679649078556868060266801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1786432719037912040177867 2679649078556868060266801)
                ·
                  refine ⟨2009736808917651045200101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2679649078556868060266801 2009736808917651045200101)
                  ·
                    refine ⟨376825651672059570975019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2009736808917651045200101 376825651672059570975019)
                    ·
                      rfl

theorem cell22_1100798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_1100798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1100798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1100798 prefixEnd_1100798 := by exact prefixLift 1100798
  have htrace : WordTrace (prefixWord ++ tailWord_1100798) baseStart_1100798 baseEnd_1100798 := by
    simpa [prefixWord, tailWord_1100798, baseEnd_1100798] using wordTrace_append hprefix tailTrace_1100798
  have hstable : (prefixWord ++ tailWord_1100798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100798).length < 2 ^ (prefixWord ++ tailWord_1100798).sum := by decide
  have hdescent : baseEnd_1100798 < baseStart_1100798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100807 : List Nat := [1, 1, 4, 3, 1, 1, 2, 2, 7]
def baseStart_1100807 : Nat := 118140960795 + 1100807 * 2 ^ 59
def prefixEnd_1100807 : Nat := 4983230072969 + 3 ^ 40 * 1100807 * 2
def baseEnd_1100807 : Nat := 125609577518662182499997

theorem tailTrace_1100807 : CollatzResearch.WordTrace tailWord_1100807 prefixEnd_1100807 125609577518662182499997 := by
  unfold tailWord_1100807
  simp only [CollatzResearch.WordTrace]
  refine ⟨40149729722971716713036675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26766486481981144475357783 40149729722971716713036675)
  ·
    refine ⟨60224594584457575069555013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40149729722971716713036675 60224594584457575069555013)
    ·
      refine ⟨11292111484585795325541565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60224594584457575069555013 11292111484585795325541565)
      ·
        refine ⟨4234541806719673247078087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11292111484585795325541565 4234541806719673247078087)
        ·
          refine ⟨6351812710079509870617131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4234541806719673247078087 6351812710079509870617131)
          ·
            refine ⟨9527719065119264805925697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6351812710079509870617131 9527719065119264805925697)
            ·
              refine ⟨7145789298839448604444273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9527719065119264805925697 7145789298839448604444273)
              ·
                refine ⟨5359341974129586453333205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7145789298839448604444273 5359341974129586453333205)
                ·
                  refine ⟨125609577518662182499997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5359341974129586453333205 125609577518662182499997)
                  ·
                    rfl

theorem cell22_1100807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 2, 7].length) (baseStart_1100807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1100807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1100807 prefixEnd_1100807 := by exact prefixLift 1100807
  have htrace : WordTrace (prefixWord ++ tailWord_1100807) baseStart_1100807 baseEnd_1100807 := by
    simpa [prefixWord, tailWord_1100807, baseEnd_1100807] using wordTrace_append hprefix tailTrace_1100807
  have hstable : (prefixWord ++ tailWord_1100807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100807).length < 2 ^ (prefixWord ++ tailWord_1100807).sum := by decide
  have hdescent : baseEnd_1100807 < baseStart_1100807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100811 : List Nat := [1, 1, 1, 1, 6, 2, 1, 5, 1, 3]
def baseStart_1100811 : Nat := 118140960795 + 1100811 * 2 ^ 59
def prefixEnd_1100811 : Nat := 4983230072969 + 3 ^ 40 * 1100811 * 2
def baseEnd_1100811 : Nat := 376830101837731870399979

theorem tailTrace_1100811 : CollatzResearch.WordTrace tailWord_1100811 prefixEnd_1100811 376830101837731870399979 := by
  unfold tailWord_1100811
  simp only [CollatzResearch.WordTrace]
  refine ⟨40149875614957225396182287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26766583743304816930788191 40149875614957225396182287)
  ·
    refine ⟨60224813422435838094273431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40149875614957225396182287 60224813422435838094273431)
    ·
      refine ⟨90337220133653757141410147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60224813422435838094273431 90337220133653757141410147)
      ·
        refine ⟨135505830200480635712115221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90337220133653757141410147 135505830200480635712115221)
        ·
          refine ⟨6351835790647529799005401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 135505830200480635712115221 6351835790647529799005401)
          ·
            refine ⟨4763876842985647349254051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6351835790647529799005401 4763876842985647349254051)
            ·
              refine ⟨7145815264478471023881077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4763876842985647349254051 7145815264478471023881077)
              ·
                refine ⟨669920181044856658488851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7145815264478471023881077 669920181044856658488851)
                ·
                  refine ⟨1004880271567284987733277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 669920181044856658488851 1004880271567284987733277)
                  ·
                    refine ⟨376830101837731870399979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1004880271567284987733277 376830101837731870399979)
                    ·
                      rfl

theorem cell22_1100811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 5, 1, 3].length) (baseStart_1100811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1100811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1100811 prefixEnd_1100811 := by exact prefixLift 1100811
  have htrace : WordTrace (prefixWord ++ tailWord_1100811) baseStart_1100811 baseEnd_1100811 := by
    simpa [prefixWord, tailWord_1100811, baseEnd_1100811] using wordTrace_append hprefix tailTrace_1100811
  have hstable : (prefixWord ++ tailWord_1100811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100811).length < 2 ^ (prefixWord ++ tailWord_1100811).sum := by decide
  have hdescent : baseEnd_1100811 < baseStart_1100811 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100824 : List Nat := [2, 1, 2, 3, 2, 2, 3, 2, 5]
def baseStart_1100824 : Nat := 118140960795 + 1100824 * 2 ^ 59
def prefixEnd_1100824 : Nat := 4983230072969 + 3 ^ 40 * 1100824 * 2
def baseEnd_1100824 : Nat := 125611517334468056608313

theorem tailTrace_1100824 : CollatzResearch.WordTrace tailWord_1100824 prefixEnd_1100824 125611517334468056608313 := by
  unfold tailWord_1100824
  simp only [CollatzResearch.WordTrace]
  refine ⟨20075174881955064308202763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26766899842606752410937017 20075174881955064308202763)
  ·
    refine ⟨30112762322932596462304145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20075174881955064308202763 30112762322932596462304145)
    ·
      refine ⟨22584571742199447346728109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30112762322932596462304145 22584571742199447346728109)
      ·
        refine ⟨8469214403324792755023041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22584571742199447346728109 8469214403324792755023041)
        ·
          refine ⟨6351910802493594566267281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8469214403324792755023041 6351910802493594566267281)
          ·
            refine ⟨4763933101870195924700461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6351910802493594566267281 4763933101870195924700461)
            ·
              refine ⟨1786474913201323471762673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4763933101870195924700461 1786474913201323471762673)
              ·
                refine ⟨1339856184900992603822005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1786474913201323471762673 1339856184900992603822005)
                ·
                  refine ⟨125611517334468056608313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1339856184900992603822005 125611517334468056608313)
                  ·
                    rfl

theorem cell22_1100824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 2, 5].length) (baseStart_1100824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1100824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1100824 prefixEnd_1100824 := by exact prefixLift 1100824
  have htrace : WordTrace (prefixWord ++ tailWord_1100824) baseStart_1100824 baseEnd_1100824 := by
    simpa [prefixWord, tailWord_1100824, baseEnd_1100824] using wordTrace_append hprefix tailTrace_1100824
  have hstable : (prefixWord ++ tailWord_1100824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100824).length < 2 ^ (prefixWord ++ tailWord_1100824).sum := by decide
  have hdescent : baseEnd_1100824 < baseStart_1100824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100867 : List Nat := [1, 1, 1, 3, 1, 2, 4, 1, 3, 5]
def baseStart_1100867 : Nat := 118140960795 + 1100867 * 2 ^ 59
def prefixEnd_1100867 : Nat := 4983230072969 + 3 ^ 40 * 1100867 * 2
def baseEnd_1100867 : Nat := 376849271782166390999807

theorem tailTrace_1100867 : CollatzResearch.WordTrace tailWord_1100867 prefixEnd_1100867 376849271782166390999807 := by
  unfold tailWord_1100867
  simp only [CollatzResearch.WordTrace]
  refine ⟨40151918102754346960220855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26767945401836231306813903 40151918102754346960220855)
  ·
    refine ⟨60227877154131520440331283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40151918102754346960220855 60227877154131520440331283)
    ·
      refine ⟨90341815731197280660496925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60227877154131520440331283 90341815731197280660496925)
      ·
        refine ⟨33878180899198980247686347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90341815731197280660496925 33878180899198980247686347)
        ·
          refine ⟨50817271348798470371529521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33878180899198980247686347 50817271348798470371529521)
          ·
            refine ⟨38112953511598852778647141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50817271348798470371529521 38112953511598852778647141)
            ·
              refine ⟨7146178783424784895996339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38112953511598852778647141 7146178783424784895996339)
              ·
                refine ⟨10719268175137177343994509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7146178783424784895996339 10719268175137177343994509)
                ·
                  refine ⟨4019725565676441503997941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10719268175137177343994509 4019725565676441503997941)
                  ·
                    refine ⟨376849271782166390999807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4019725565676441503997941 376849271782166390999807)
                    ·
                      rfl

theorem cell22_1100867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 3, 5].length) (baseStart_1100867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1100867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1100867 prefixEnd_1100867 := by exact prefixLift 1100867
  have htrace : WordTrace (prefixWord ++ tailWord_1100867) baseStart_1100867 baseEnd_1100867 := by
    simpa [prefixWord, tailWord_1100867, baseEnd_1100867] using wordTrace_append hprefix tailTrace_1100867
  have hstable : (prefixWord ++ tailWord_1100867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100867).length < 2 ^ (prefixWord ++ tailWord_1100867).sum := by decide
  have hdescent : baseEnd_1100867 < baseStart_1100867 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100897 : List Nat := [1, 2, 3, 1, 1, 2, 3, 9]
def baseStart_1100897 : Nat := 118140960795 + 1100897 * 2 ^ 59
def prefixEnd_1100897 : Nat := 4983230072969 + 3 ^ 40 * 1100897 * 2
def baseEnd_1100897 : Nat := 41873282377250701416635

theorem tailTrace_1100897 : CollatzResearch.WordTrace tailWord_1100897 prefixEnd_1100897 41873282377250701416635 := by
  unfold tailWord_1100897
  simp only [CollatzResearch.WordTrace]
  refine ⟨40153012292645662083812945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26768674861763774722541963 40153012292645662083812945)
  ·
    refine ⟨30114759219484246562859709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40153012292645662083812945 30114759219484246562859709)
    ·
      refine ⟨11293034707306592461072391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30114759219484246562859709 11293034707306592461072391)
      ·
        refine ⟨16939552060959888691608587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11293034707306592461072391 16939552060959888691608587)
        ·
          refine ⟨25409328091439833037412881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16939552060959888691608587 25409328091439833037412881)
          ·
            refine ⟨19056996068579874778059661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25409328091439833037412881 19056996068579874778059661)
            ·
              refine ⟨7146373525717453041772373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19056996068579874778059661 7146373525717453041772373)
              ·
                refine ⟨41873282377250701416635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7146373525717453041772373 41873282377250701416635)
                ·
                  rfl

theorem cell22_1100897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 9].length) (baseStart_1100897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1100897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1100897 prefixEnd_1100897 := by exact prefixLift 1100897
  have htrace : WordTrace (prefixWord ++ tailWord_1100897) baseStart_1100897 baseEnd_1100897 := by
    simpa [prefixWord, tailWord_1100897, baseEnd_1100897] using wordTrace_append hprefix tailTrace_1100897
  have hstable : (prefixWord ++ tailWord_1100897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100897).length < 2 ^ (prefixWord ++ tailWord_1100897).sum := by decide
  have hdescent : baseEnd_1100897 < baseStart_1100897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100901 : List Nat := [1, 3, 1, 3, 2, 1, 3, 3, 2, 3]
def baseStart_1100901 : Nat := 118140960795 + 1100901 * 2 ^ 59
def prefixEnd_1100901 : Nat := 4983230072969 + 3 ^ 40 * 1100901 * 2
def baseEnd_1100901 : Nat := 376860910677001635649703

theorem tailTrace_1100901 : CollatzResearch.WordTrace tailWord_1100901 prefixEnd_1100901 376860910677001635649703 := by
  unfold tailWord_1100901
  simp only [CollatzResearch.WordTrace]
  refine ⟨40153158184631170766958557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26768772123087447177972371 40153158184631170766958557)
  ·
    refine ⟨15057434319236689037609459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40153158184631170766958557 15057434319236689037609459)
    ·
      refine ⟨22586151478855033556414189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15057434319236689037609459 22586151478855033556414189)
      ·
        refine ⟨8469806804570637583655321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22586151478855033556414189 8469806804570637583655321)
        ·
          refine ⟨6352355103427978187741491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8469806804570637583655321 6352355103427978187741491)
          ·
            refine ⟨9528532655141967281612237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6352355103427978187741491 9528532655141967281612237)
            ·
              refine ⟨3573199745678237730604589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9528532655141967281612237 3573199745678237730604589)
              ·
                refine ⟨1339949904629339148976721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3573199745678237730604589 1339949904629339148976721)
                ·
                  refine ⟨1004962428472004361732541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1339949904629339148976721 1004962428472004361732541)
                  ·
                    refine ⟨376860910677001635649703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1004962428472004361732541 376860910677001635649703)
                    ·
                      rfl

theorem cell22_1100901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 3, 2, 3].length) (baseStart_1100901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1100901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1100901 prefixEnd_1100901 := by exact prefixLift 1100901
  have htrace : WordTrace (prefixWord ++ tailWord_1100901) baseStart_1100901 baseEnd_1100901 := by
    simpa [prefixWord, tailWord_1100901, baseEnd_1100901] using wordTrace_append hprefix tailTrace_1100901
  have hstable : (prefixWord ++ tailWord_1100901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100901).length < 2 ^ (prefixWord ++ tailWord_1100901).sum := by decide
  have hdescent : baseEnd_1100901 < baseStart_1100901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100927 : List Nat := [1, 1, 2, 2, 1, 1, 1, 1, 6, 6]
def baseStart_1100927 : Nat := 118140960795 + 1100927 * 2 ^ 59
def prefixEnd_1100927 : Nat := 4983230072969 + 3 ^ 40 * 1100927 * 2
def baseEnd_1100927 : Nat := 376869811008346234499623

theorem tailTrace_1100927 : CollatzResearch.WordTrace tailWord_1100927 prefixEnd_1100927 376869811008346234499623 := by
  unfold tailWord_1100927
  simp only [CollatzResearch.WordTrace]
  refine ⟨40154106482536977207405035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26769404321691318138270023 40154106482536977207405035)
  ·
    refine ⟨60231159723805465811107553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40154106482536977207405035 60231159723805465811107553)
    ·
      refine ⟨45173369792854099358330665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60231159723805465811107553 45173369792854099358330665)
      ·
        refine ⟨33880027344640574518747999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45173369792854099358330665 33880027344640574518747999)
        ·
          refine ⟨50820041016960861778121999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33880027344640574518747999 50820041016960861778121999)
          ·
            refine ⟨76230061525441292667182999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50820041016960861778121999 76230061525441292667182999)
            ·
              refine ⟨114345092288161939000774499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76230061525441292667182999 114345092288161939000774499)
              ·
                refine ⟨171517638432242908501161749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114345092288161939000774499 171517638432242908501161749)
                ·
                  refine ⟨8039889301511386335991957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 171517638432242908501161749 8039889301511386335991957)
                  ·
                    refine ⟨376869811008346234499623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8039889301511386335991957 376869811008346234499623)
                    ·
                      rfl

theorem cell22_1100927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 6, 6].length) (baseStart_1100927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1100927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1100927 prefixEnd_1100927 := by exact prefixLift 1100927
  have htrace : WordTrace (prefixWord ++ tailWord_1100927) baseStart_1100927 baseEnd_1100927 := by
    simpa [prefixWord, tailWord_1100927, baseEnd_1100927] using wordTrace_append hprefix tailTrace_1100927
  have hstable : (prefixWord ++ tailWord_1100927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100927).length < 2 ^ (prefixWord ++ tailWord_1100927).sum := by decide
  have hdescent : baseEnd_1100927 < baseStart_1100927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100993 : List Nat := [1, 2, 6, 1, 1, 1, 3, 2, 5]
def baseStart_1100993 : Nat := 118140960795 + 1100993 * 2 ^ 59
def prefixEnd_1100993 : Nat := 4983230072969 + 3 ^ 40 * 1100993 * 2
def baseEnd_1100993 : Nat := 125630801385714687449807

theorem tailTrace_1100993 : CollatzResearch.WordTrace tailWord_1100993 prefixEnd_1100993 125630801385714687449807 := by
  unfold tailWord_1100993
  simp only [CollatzResearch.WordTrace]
  refine ⟨40156513700297870479307633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26771009133531913652871755 40156513700297870479307633)
  ·
    refine ⟨30117385275223402859480725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40156513700297870479307633 30117385275223402859480725)
    ·
      refine ⟨1411752434776097009038159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 30117385275223402859480725 1411752434776097009038159)
      ·
        refine ⟨2117628652164145513557239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1411752434776097009038159 2117628652164145513557239)
        ·
          refine ⟨3176442978246218270335859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2117628652164145513557239 3176442978246218270335859)
          ·
            refine ⟨4764664467369327405503789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3176442978246218270335859 4764664467369327405503789)
            ·
              refine ⟨1786749175263497777063921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4764664467369327405503789 1786749175263497777063921)
              ·
                refine ⟨1340061881447623332797941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1786749175263497777063921 1340061881447623332797941)
                ·
                  refine ⟨125630801385714687449807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1340061881447623332797941 125630801385714687449807)
                  ·
                    rfl

theorem cell22_1100993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 2, 5].length) (baseStart_1100993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1100993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1100993 prefixEnd_1100993 := by exact prefixLift 1100993
  have htrace : WordTrace (prefixWord ++ tailWord_1100993) baseStart_1100993 baseEnd_1100993 := by
    simpa [prefixWord, tailWord_1100993, baseEnd_1100993] using wordTrace_append hprefix tailTrace_1100993
  have hstable : (prefixWord ++ tailWord_1100993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100993).length < 2 ^ (prefixWord ++ tailWord_1100993).sum := by decide
  have hdescent : baseEnd_1100993 < baseStart_1100993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101036 : List Nat := [2, 2, 1, 1, 2, 4, 1, 2, 4, 3]
def baseStart_1101036 : Nat := 118140960795 + 1101036 * 2 ^ 59
def prefixEnd_1101036 : Nat := 4983230072969 + 3 ^ 40 * 1101036 * 2
def baseEnd_1101036 : Nat := 376907123935906283524289

theorem tailTrace_1101036 : CollatzResearch.WordTrace tailWord_1101036 prefixEnd_1101036 376907123935906283524289 := by
  unfold tailWord_1101036
  simp only [CollatzResearch.WordTrace]
  refine ⟨20079041019571044411561481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26772054692761392548748641 20079041019571044411561481)
  ·
    refine ⟨15059280764678283308671111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20079041019571044411561481 15059280764678283308671111)
    ·
      refine ⟨22588921147017424963006667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15059280764678283308671111 22588921147017424963006667)
      ·
        refine ⟨33883381720526137444510001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22588921147017424963006667 33883381720526137444510001)
        ·
          refine ⟨25412536290394603083382501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33883381720526137444510001 25412536290394603083382501)
          ·
            refine ⟨4764850554448988078134219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25412536290394603083382501 4764850554448988078134219)
            ·
              refine ⟨7147275831673482117201329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4764850554448988078134219 7147275831673482117201329)
              ·
                refine ⟨5360456873755111587900997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7147275831673482117201329 5360456873755111587900997)
                ·
                  refine ⟨1005085663829083422731437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5360456873755111587900997 1005085663829083422731437)
                  ·
                    refine ⟨376907123935906283524289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1005085663829083422731437 376907123935906283524289)
                    ·
                      rfl

theorem cell22_1101036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 3].length) (baseStart_1101036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1101036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1101036 prefixEnd_1101036 := by exact prefixLift 1101036
  have htrace : WordTrace (prefixWord ++ tailWord_1101036) baseStart_1101036 baseEnd_1101036 := by
    simpa [prefixWord, tailWord_1101036, baseEnd_1101036] using wordTrace_append hprefix tailTrace_1101036
  have hstable : (prefixWord ++ tailWord_1101036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101036).length < 2 ^ (prefixWord ++ tailWord_1101036).sum := by decide
  have hdescent : baseEnd_1101036 < baseStart_1101036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101038 : List Nat := [4, 1, 2, 1, 1, 1, 5, 3, 4]
def baseStart_1101038 : Nat := 118140960795 + 1101038 * 2 ^ 59
def prefixEnd_1101038 : Nat := 4983230072969 + 3 ^ 40 * 1101038 * 2
def baseEnd_1101038 : Nat := 125635936192259648324761

theorem tailTrace_1101038 : CollatzResearch.WordTrace tailWord_1101038 prefixEnd_1101038 125635936192259648324761 := by
  unfold tailWord_1101038
  simp only [CollatzResearch.WordTrace]
  refine ⟨5019769373141855395586971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26772103323423228776463845 5019769373141855395586971)
  ·
    refine ⟨7529654059712783093380457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5019769373141855395586971 7529654059712783093380457)
    ·
      refine ⟨5647240544784587320035343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7529654059712783093380457 5647240544784587320035343)
      ·
        refine ⟨8470860817176880980053015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5647240544784587320035343 8470860817176880980053015)
        ·
          refine ⟨12706291225765321470079523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8470860817176880980053015 12706291225765321470079523)
          ·
            refine ⟨19059436838647982205119285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12706291225765321470079523 19059436838647982205119285)
            ·
              refine ⟨1786822203623248331729933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19059436838647982205119285 1786822203623248331729933)
              ·
                refine ⟨670058326358718124398725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1786822203623248331729933 670058326358718124398725)
                ·
                  refine ⟨125635936192259648324761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 670058326358718124398725 125635936192259648324761)
                  ·
                    rfl

theorem cell22_1101038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 3, 4].length) (baseStart_1101038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1101038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1101038 prefixEnd_1101038 := by exact prefixLift 1101038
  have htrace : WordTrace (prefixWord ++ tailWord_1101038) baseStart_1101038 baseEnd_1101038 := by
    simpa [prefixWord, tailWord_1101038, baseEnd_1101038] using wordTrace_append hprefix tailTrace_1101038
  have hstable : (prefixWord ++ tailWord_1101038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101038).length < 2 ^ (prefixWord ++ tailWord_1101038).sum := by decide
  have hdescent : baseEnd_1101038 < baseStart_1101038 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101070 : List Nat := [4, 1, 1, 2, 1, 3, 4, 1, 2, 3]
def baseStart_1101070 : Nat := 118140960795 + 1101070 * 2 ^ 59
def prefixEnd_1101070 : Nat := 4983230072969 + 3 ^ 40 * 1101070 * 2
def baseEnd_1101070 : Nat := 376918762830741528174185

theorem tailTrace_1101070 : CollatzResearch.WordTrace tailWord_1101070 prefixEnd_1101070 376918762830741528174185 := by
  unfold tailWord_1101070
  simp only [CollatzResearch.WordTrace]
  refine ⟨5019915265127364078732583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26772881414012608419907109 5019915265127364078732583)
  ·
    refine ⟨7529872897691046118098875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5019915265127364078732583 7529872897691046118098875)
    ·
      refine ⟨11294809346536569177148313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7529872897691046118098875 11294809346536569177148313)
      ·
        refine ⟨8471107009902426882861235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11294809346536569177148313 8471107009902426882861235)
        ·
          refine ⟨12706660514853640324291853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8471107009902426882861235 12706660514853640324291853)
          ·
            refine ⟨4764997693070115121609445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12706660514853640324291853 4764997693070115121609445)
            ·
              refine ⟨893437067450646585301771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4764997693070115121609445 893437067450646585301771)
              ·
                refine ⟨1340155601175969877952657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 893437067450646585301771 1340155601175969877952657)
                ·
                  refine ⟨1005116700881977408464493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1340155601175969877952657 1005116700881977408464493)
                  ·
                    refine ⟨376918762830741528174185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1005116700881977408464493 376918762830741528174185)
                    ·
                      rfl

theorem cell22_1101070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 4, 1, 2, 3].length) (baseStart_1101070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1101070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1101070 prefixEnd_1101070 := by exact prefixLift 1101070
  have htrace : WordTrace (prefixWord ++ tailWord_1101070) baseStart_1101070 baseEnd_1101070 := by
    simpa [prefixWord, tailWord_1101070, baseEnd_1101070] using wordTrace_append hprefix tailTrace_1101070
  have hstable : (prefixWord ++ tailWord_1101070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101070).length < 2 ^ (prefixWord ++ tailWord_1101070).sum := by decide
  have hdescent : baseEnd_1101070 < baseStart_1101070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101074 : List Nat := [3, 2, 4, 2, 2, 1, 1, 2, 1, 4]
def baseStart_1101074 : Nat := 118140960795 + 1101074 * 2 ^ 59
def prefixEnd_1101074 : Nat := 4983230072969 + 3 ^ 40 * 1101074 * 2
def baseEnd_1101074 : Nat := 376920132112486851074173

theorem tailTrace_1101074 : CollatzResearch.WordTrace tailWord_1101074 prefixEnd_1101074 376920132112486851074173 := by
  unfold tailWord_1101074
  simp only [CollatzResearch.WordTrace]
  refine ⟨10039867003251105328251569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26772978675336280875337517 10039867003251105328251569)
  ·
    refine ⟨7529900252438328996188677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10039867003251105328251569 7529900252438328996188677)
    ·
      refine ⟨1411856297332186686785377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7529900252438328996188677 1411856297332186686785377)
      ·
        refine ⟨1058892222999140015089033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1411856297332186686785377 1058892222999140015089033)
        ·
          refine ⟨794169167249355011316775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1058892222999140015089033 794169167249355011316775)
          ·
            refine ⟨1191253750874032516975163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 794169167249355011316775 1191253750874032516975163)
            ·
              refine ⟨1786880626311048775462745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1191253750874032516975163 1786880626311048775462745)
              ·
                refine ⟨1340160469733286581597059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1786880626311048775462745 1340160469733286581597059)
                ·
                  refine ⟨2010240704599929872395589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1340160469733286581597059 2010240704599929872395589)
                  ·
                    refine ⟨376920132112486851074173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2010240704599929872395589 376920132112486851074173)
                    ·
                      rfl

theorem cell22_1101074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_1101074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1101074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1101074 prefixEnd_1101074 := by exact prefixLift 1101074
  have htrace : WordTrace (prefixWord ++ tailWord_1101074) baseStart_1101074 baseEnd_1101074 := by
    simpa [prefixWord, tailWord_1101074, baseEnd_1101074] using wordTrace_append hprefix tailTrace_1101074
  have hstable : (prefixWord ++ tailWord_1101074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101074).length < 2 ^ (prefixWord ++ tailWord_1101074).sum := by decide
  have hdescent : baseEnd_1101074 < baseStart_1101074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101162 : List Nat := [3, 1, 3, 3, 3, 1, 1, 2, 5]
def baseStart_1101162 : Nat := 118140960795 + 1101162 * 2 ^ 59
def prefixEnd_1101162 : Nat := 4983230072969 + 3 ^ 40 * 1101162 * 2
def baseEnd_1101162 : Nat := 125650085436961318291301

theorem tailTrace_1101162 : CollatzResearch.WordTrace tailWord_1101162 prefixEnd_1101162 125650085436961318291301 := by
  unfold tailWord_1101162
  simp only [CollatzResearch.WordTrace]
  refine ⟨10040669409171403085552435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26775118424457074894806493 10040669409171403085552435)
  ·
    refine ⟨15061004113757104628328653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10040669409171403085552435 15061004113757104628328653)
    ·
      refine ⟨5647876542658914235623245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15061004113757104628328653 5647876542658914235623245)
      ·
        refine ⟨2117953703497092838358717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5647876542658914235623245 2117953703497092838358717)
        ·
          refine ⟨794232638811409814384519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2117953703497092838358717 794232638811409814384519)
          ·
            refine ⟨1191348958217114721576779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 794232638811409814384519 1191348958217114721576779)
            ·
              refine ⟨1787023437325672082365169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1191348958217114721576779 1787023437325672082365169)
              ·
                refine ⟨1340267577994254061773877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1787023437325672082365169 1340267577994254061773877)
                ·
                  refine ⟨125650085436961318291301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1340267577994254061773877 125650085436961318291301)
                  ·
                    rfl

theorem cell22_1101162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 2, 5].length) (baseStart_1101162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1101162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1101162 prefixEnd_1101162 := by exact prefixLift 1101162
  have htrace : WordTrace (prefixWord ++ tailWord_1101162) baseStart_1101162 baseEnd_1101162 := by
    simpa [prefixWord, tailWord_1101162, baseEnd_1101162] using wordTrace_append hprefix tailTrace_1101162
  have hstable : (prefixWord ++ tailWord_1101162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101162).length < 2 ^ (prefixWord ++ tailWord_1101162).sum := by decide
  have hdescent : baseEnd_1101162 < baseStart_1101162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101188 : List Nat := [2, 3, 2, 1, 1, 3, 3, 1, 1, 5]
def baseStart_1101188 : Nat := 118140960795 + 1101188 * 2 ^ 59
def prefixEnd_1101188 : Nat := 4983230072969 + 3 ^ 40 * 1101188 * 2
def baseEnd_1101188 : Nat := 376959156642228553723823

theorem tailTrace_1101188 : CollatzResearch.WordTrace tailWord_1101188 prefixEnd_1101188 376959156642228553723823 := by
  unfold tailWord_1101188
  simp only [CollatzResearch.WordTrace]
  refine ⟨20081812967295709391328109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26775750623060945855104145 20081812967295709391328109)
  ·
    refine ⟨7530679862735891021748041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20081812967295709391328109 7530679862735891021748041)
    ·
      refine ⟨5648009897051918266311031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7530679862735891021748041 5648009897051918266311031)
      ·
        refine ⟨8472014845577877399466547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5648009897051918266311031 8472014845577877399466547)
        ·
          refine ⟨12708022268366816099199821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8472014845577877399466547 12708022268366816099199821)
          ·
            refine ⟨4765508350637556037199933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12708022268366816099199821 4765508350637556037199933)
            ·
              refine ⟨1787065631489083513949975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4765508350637556037199933 1787065631489083513949975)
              ·
                refine ⟨2680598447233625270924963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1787065631489083513949975 2680598447233625270924963)
                ·
                  refine ⟨4020897670850437906387445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2680598447233625270924963 4020897670850437906387445)
                  ·
                    refine ⟨376959156642228553723823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4020897670850437906387445 376959156642228553723823)
                    ·
                      rfl

theorem cell22_1101188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_1101188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1101188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1101188 prefixEnd_1101188 := by exact prefixLift 1101188
  have htrace : WordTrace (prefixWord ++ tailWord_1101188) baseStart_1101188 baseEnd_1101188 := by
    simpa [prefixWord, tailWord_1101188, baseEnd_1101188] using wordTrace_append hprefix tailTrace_1101188
  have hstable : (prefixWord ++ tailWord_1101188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101188).length < 2 ^ (prefixWord ++ tailWord_1101188).sum := by decide
  have hdescent : baseEnd_1101188 < baseStart_1101188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101218 : List Nat := [3, 3, 1, 2, 1, 4, 8]
def baseStart_1101218 : Nat := 118140960795 + 1101218 * 2 ^ 59
def prefixEnd_1101218 : Nat := 4983230072969 + 3 ^ 40 * 1101218 * 2
def baseEnd_1101218 : Nat := 13961830602048832424953

theorem tailTrace_1101218 : CollatzResearch.WordTrace tailWord_1101218 prefixEnd_1101218 13961830602048832424953 := by
  unfold tailWord_1101218
  simp only [CollatzResearch.WordTrace]
  refine ⟨10041180031120683476562077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26776480082988489270832205 10041180031120683476562077)
  ·
    refine ⟨3765442511670256303710779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10041180031120683476562077 3765442511670256303710779)
    ·
      refine ⟨5648163767505384455566169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3765442511670256303710779 5648163767505384455566169)
      ·
        refine ⟨4236122825629038341674627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5648163767505384455566169 4236122825629038341674627)
        ·
          refine ⟨6354184238443557512511941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4236122825629038341674627 6354184238443557512511941)
          ·
            refine ⟨1191409544708167033595989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6354184238443557512511941 1191409544708167033595989)
            ·
              refine ⟨13961830602048832424953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1191409544708167033595989 13961830602048832424953)
              ·
                rfl

theorem cell22_1101218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 8].length) (baseStart_1101218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1101218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1101218 prefixEnd_1101218 := by exact prefixLift 1101218
  have htrace : WordTrace (prefixWord ++ tailWord_1101218) baseStart_1101218 baseEnd_1101218 := by
    simpa [prefixWord, tailWord_1101218, baseEnd_1101218] using wordTrace_append hprefix tailTrace_1101218
  have hstable : (prefixWord ++ tailWord_1101218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101218).length < 2 ^ (prefixWord ++ tailWord_1101218).sum := by decide
  have hdescent : baseEnd_1101218 < baseStart_1101218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101224 : List Nat := [2, 1, 6, 1, 2, 1, 3, 2, 4]
def baseStart_1101224 : Nat := 118140960795 + 1101224 * 2 ^ 59
def prefixEnd_1101224 : Nat := 4983230072969 + 3 ^ 40 * 1101224 * 2
def baseEnd_1101224 : Nat := 125657160059312153274571

theorem tailTrace_1101224 : CollatzResearch.WordTrace tailWord_1101224 prefixEnd_1101224 125657160059312153274571 := by
  unfold tailWord_1101224
  simp only [CollatzResearch.WordTrace]
  refine ⟨20082469481230498465483363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26776625974973997953977817 20082469481230498465483363)
  ·
    refine ⟨30123704221845747698225045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20082469481230498465483363 30123704221845747698225045)
    ·
      refine ⟨1412048635399019423354299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 30123704221845747698225045 1412048635399019423354299)
      ·
        refine ⟨2118072953098529135031449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1412048635399019423354299 2118072953098529135031449)
        ·
          refine ⟨1588554714823896851273587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2118072953098529135031449 1588554714823896851273587)
          ·
            refine ⟨2382832072235845276910381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1588554714823896851273587 2382832072235845276910381)
            ·
              refine ⟨893562027088441978841393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2382832072235845276910381 893562027088441978841393)
              ·
                refine ⟨670171520316331484131045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 893562027088441978841393 670171520316331484131045)
                ·
                  refine ⟨125657160059312153274571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 670171520316331484131045 125657160059312153274571)
                  ·
                    rfl

theorem cell22_1101224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 3, 2, 4].length) (baseStart_1101224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1101224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1101224 prefixEnd_1101224 := by exact prefixLift 1101224
  have htrace : WordTrace (prefixWord ++ tailWord_1101224) baseStart_1101224 baseEnd_1101224 := by
    simpa [prefixWord, tailWord_1101224, baseEnd_1101224] using wordTrace_append hprefix tailTrace_1101224
  have hstable : (prefixWord ++ tailWord_1101224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101224).length < 2 ^ (prefixWord ++ tailWord_1101224).sum := by decide
  have hdescent : baseEnd_1101224 < baseStart_1101224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101338 : List Nat := [3, 1, 1, 3, 1, 1, 1, 3, 4, 4]
def baseStart_1101338 : Nat := 118140960795 + 1101338 * 2 ^ 59
def prefixEnd_1101338 : Nat := 4983230072969 + 3 ^ 40 * 1101338 * 2
def baseEnd_1101338 : Nat := 377010504707678162473363

theorem tailTrace_1101338 : CollatzResearch.WordTrace tailWord_1101338 prefixEnd_1101338 377010504707678162473363 := by
  unfold tailWord_1101338
  simp only [CollatzResearch.WordTrace]
  refine ⟨10042274221011998600154167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26779397922698662933744445 10042274221011998600154167)
  ·
    refine ⟨15063411331517997900231251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10042274221011998600154167 15063411331517997900231251)
    ·
      refine ⟨22595116997276996850346877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15063411331517997900231251 22595116997276996850346877)
      ·
        refine ⟨8473168873978873818880079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22595116997276996850346877 8473168873978873818880079)
        ·
          refine ⟨12709753310968310728320119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8473168873978873818880079 12709753310968310728320119)
          ·
            refine ⟨19064629966452466092480179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12709753310968310728320119 19064629966452466092480179)
            ·
              refine ⟨28596944949678699138720269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19064629966452466092480179 28596944949678699138720269)
              ·
                refine ⟨10723854356129512177020101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28596944949678699138720269 10723854356129512177020101)
                ·
                  refine ⟨2010722691774283533191269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10723854356129512177020101 2010722691774283533191269)
                  ·
                    refine ⟨377010504707678162473363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2010722691774283533191269 377010504707678162473363)
                    ·
                      rfl

theorem cell22_1101338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 4, 4].length) (baseStart_1101338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1101338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1101338 prefixEnd_1101338 := by exact prefixLift 1101338
  have htrace : WordTrace (prefixWord ++ tailWord_1101338) baseStart_1101338 baseEnd_1101338 := by
    simpa [prefixWord, tailWord_1101338, baseEnd_1101338] using wordTrace_append hprefix tailTrace_1101338
  have hstable : (prefixWord ++ tailWord_1101338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101338).length < 2 ^ (prefixWord ++ tailWord_1101338).sum := by decide
  have hdescent : baseEnd_1101338 < baseStart_1101338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101340 : List Nat := [2, 2, 3, 1, 2, 1, 3, 1, 4, 3]
def baseStart_1101340 : Nat := 118140960795 + 1101340 * 2 ^ 59
def prefixEnd_1101340 : Nat := 4983230072969 + 3 ^ 40 * 1101340 * 2
def baseEnd_1101340 : Nat := 377011189348550823923357

theorem tailTrace_1101340 : CollatzResearch.WordTrace tailWord_1101340 prefixEnd_1101340 377011189348550823923357 := by
  unfold tailWord_1101340
  simp only [CollatzResearch.WordTrace]
  refine ⟨20084584915020374371094737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26779446553360499161459649 20084584915020374371094737)
  ·
    refine ⟨15063438686265280778321053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20084584915020374371094737 15063438686265280778321053)
    ·
      refine ⟨5648789507349480291870395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15063438686265280778321053 5648789507349480291870395)
      ·
        refine ⟨8473184261024220437805593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5648789507349480291870395 8473184261024220437805593)
        ·
          refine ⟨6354888195768165328354195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8473184261024220437805593 6354888195768165328354195)
          ·
            refine ⟨9532332293652247992531293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6354888195768165328354195 9532332293652247992531293)
            ·
              refine ⟨3574624610119592997199235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9532332293652247992531293 3574624610119592997199235)
              ·
                refine ⟨5361936915179389495798853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3574624610119592997199235 5361936915179389495798853)
                ·
                  refine ⟨1005363171596135530462285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5361936915179389495798853 1005363171596135530462285)
                  ·
                    refine ⟨377011189348550823923357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1005363171596135530462285 377011189348550823923357)
                    ·
                      rfl

theorem cell22_1101340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 1, 4, 3].length) (baseStart_1101340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1101340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1101340 prefixEnd_1101340 := by exact prefixLift 1101340
  have htrace : WordTrace (prefixWord ++ tailWord_1101340) baseStart_1101340 baseEnd_1101340 := by
    simpa [prefixWord, tailWord_1101340, baseEnd_1101340] using wordTrace_append hprefix tailTrace_1101340
  have hstable : (prefixWord ++ tailWord_1101340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101340).length < 2 ^ (prefixWord ++ tailWord_1101340).sum := by decide
  have hdescent : baseEnd_1101340 < baseStart_1101340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101402 : List Nat := [3, 1, 1, 2, 1, 1, 1, 8, 1, 3]
def baseStart_1101402 : Nat := 118140960795 + 1101402 * 2 ^ 59
def prefixEnd_1101402 : Nat := 4983230072969 + 3 ^ 40 * 1101402 * 2
def baseEnd_1101402 : Nat := 377032413215603328873167

theorem tailTrace_1101402 : CollatzResearch.WordTrace tailWord_1101402 prefixEnd_1101402 377032413215603328873167 := by
  unfold tailWord_1101402
  simp only [CollatzResearch.WordTrace]
  refine ⟨10042857788954033332736615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26780954103877422220630973 10042857788954033332736615)
  ·
    refine ⟨15064286683431049999104923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10042857788954033332736615 15064286683431049999104923)
    ·
      refine ⟨22596430025146574998657385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15064286683431049999104923 22596430025146574998657385)
      ·
        refine ⟨16947322518859931248993039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22596430025146574998657385 16947322518859931248993039)
        ·
          refine ⟨25420983778289896873489559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16947322518859931248993039 25420983778289896873489559)
          ·
            refine ⟨38131475667434845310234339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25420983778289896873489559 38131475667434845310234339)
            ·
              refine ⟨57197213501152267965351509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38131475667434845310234339 57197213501152267965351509)
              ·
                refine ⟨670279845716628140218963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 57197213501152267965351509 670279845716628140218963)
                ·
                  refine ⟨1005419768574942210328445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 670279845716628140218963 1005419768574942210328445)
                  ·
                    refine ⟨377032413215603328873167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1005419768574942210328445 377032413215603328873167)
                    ·
                      rfl

theorem cell22_1101402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 8, 1, 3].length) (baseStart_1101402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1101402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1101402 prefixEnd_1101402 := by exact prefixLift 1101402
  have htrace : WordTrace (prefixWord ++ tailWord_1101402) baseStart_1101402 baseEnd_1101402 := by
    simpa [prefixWord, tailWord_1101402, baseEnd_1101402] using wordTrace_append hprefix tailTrace_1101402
  have hstable : (prefixWord ++ tailWord_1101402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101402).length < 2 ^ (prefixWord ++ tailWord_1101402).sum := by decide
  have hdescent : baseEnd_1101402 < baseStart_1101402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101475 : List Nat := [1, 1, 1, 4, 1, 1, 6, 1, 1, 5]
def baseStart_1101475 : Nat := 118140960795 + 1101475 * 2 ^ 59
def prefixEnd_1101475 : Nat := 4983230072969 + 3 ^ 40 * 1101475 * 2
def baseEnd_1101475 : Nat := 377057402607455471797943

theorem tailTrace_1101475 : CollatzResearch.WordTrace tailWord_1101475 prefixEnd_1101475 377057402607455471797943 := by
  unfold tailWord_1101475
  simp only [CollatzResearch.WordTrace]
  refine ⟨40174093684551666798353879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26782729123034444532235919 40174093684551666798353879)
  ·
    refine ⟨60261140526827500197530819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40174093684551666798353879 60261140526827500197530819)
    ·
      refine ⟨90391710790241250296296229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60261140526827500197530819 90391710790241250296296229)
      ·
        refine ⟨16948445773170234430555543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 90391710790241250296296229 16948445773170234430555543)
        ·
          refine ⟨25422668659755351645833315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16948445773170234430555543 25422668659755351645833315)
          ·
            refine ⟨38134002989633027468749973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25422668659755351645833315 38134002989633027468749973)
            ·
              refine ⟨1787531390139048162597655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 38134002989633027468749973 1787531390139048162597655)
              ·
                refine ⟨2681297085208572243896483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1787531390139048162597655 2681297085208572243896483)
                ·
                  refine ⟨4021945627812858365844725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2681297085208572243896483 4021945627812858365844725)
                  ·
                    refine ⟨377057402607455471797943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4021945627812858365844725 377057402607455471797943)
                    ·
                      rfl

theorem cell22_1101475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 1, 1, 5].length) (baseStart_1101475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1101475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1101475 prefixEnd_1101475 := by exact prefixLift 1101475
  have htrace : WordTrace (prefixWord ++ tailWord_1101475) baseStart_1101475 baseEnd_1101475 := by
    simpa [prefixWord, tailWord_1101475, baseEnd_1101475] using wordTrace_append hprefix tailTrace_1101475
  have hstable : (prefixWord ++ tailWord_1101475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101475).length < 2 ^ (prefixWord ++ tailWord_1101475).sum := by decide
  have hdescent : baseEnd_1101475 < baseStart_1101475 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101488 : List Nat := [2, 1, 1, 1, 2, 1, 4, 10]
def baseStart_1101488 : Nat := 118140960795 + 1101488 * 2 ^ 59
def prefixEnd_1101488 : Nat := 4983230072969 + 3 ^ 40 * 1101488 * 2
def baseEnd_1101488 : Nat := 41895761419236419024767

theorem tailTrace_1101488 : CollatzResearch.WordTrace tailWord_1101488 prefixEnd_1101488 41895761419236419024767 := by
  unfold tailWord_1101488
  simp only [CollatzResearch.WordTrace]
  refine ⟨20087283916752285009288559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26783045222336380012384745 20087283916752285009288559)
  ·
    refine ⟨30130925875128427513932839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20087283916752285009288559 30130925875128427513932839)
    ·
      refine ⟨45196388812692641270899259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30130925875128427513932839 45196388812692641270899259)
      ·
        refine ⟨67794583219038961906348889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45196388812692641270899259 67794583219038961906348889)
        ·
          refine ⟨50845937414279221429761667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67794583219038961906348889 50845937414279221429761667)
          ·
            refine ⟨76268906121418832144642501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50845937414279221429761667 76268906121418832144642501)
            ·
              refine ⟨14300419897766031027120469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 76268906121418832144642501 14300419897766031027120469)
              ·
                refine ⟨41895761419236419024767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 14300419897766031027120469 41895761419236419024767)
                ·
                  rfl

theorem cell22_1101488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 10].length) (baseStart_1101488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1101488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1101488 prefixEnd_1101488 := by exact prefixLift 1101488
  have htrace : WordTrace (prefixWord ++ tailWord_1101488) baseStart_1101488 baseEnd_1101488 := by
    simpa [prefixWord, tailWord_1101488, baseEnd_1101488] using wordTrace_append hprefix tailTrace_1101488
  have hstable : (prefixWord ++ tailWord_1101488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101488).length < 2 ^ (prefixWord ++ tailWord_1101488).sum := by decide
  have hdescent : baseEnd_1101488 < baseStart_1101488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101539 : List Nat := [1, 1, 1, 7, 2, 2, 2, 6]
def baseStart_1101539 : Nat := 118140960795 + 1101539 * 2 ^ 59
def prefixEnd_1101539 : Nat := 4983230072969 + 3 ^ 40 * 1101539 * 2
def baseEnd_1101539 : Nat := 41897701235042293133083

theorem tailTrace_1101539 : CollatzResearch.WordTrace tailWord_1101539 prefixEnd_1101539 41897701235042293133083 := by
  unfold tailWord_1101539
  simp only [CollatzResearch.WordTrace]
  refine ⟨40176427956319805728683671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26784285304213203819122447 40176427956319805728683671)
  ·
    refine ⟨60264641934479708593025507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40176427956319805728683671 60264641934479708593025507)
    ·
      refine ⟨90396962901719562889538261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60264641934479708593025507 90396962901719562889538261)
      ·
        refine ⟨2118678818009052255223553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 90396962901719562889538261 2118678818009052255223553)
        ·
          refine ⟨1589009113506789191417665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2118678818009052255223553 1589009113506789191417665)
          ·
            refine ⟨1191756835130091893563249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1589009113506789191417665 1191756835130091893563249)
            ·
              refine ⟨893817626347568920172437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1191756835130091893563249 893817626347568920172437)
              ·
                refine ⟨41897701235042293133083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 893817626347568920172437 41897701235042293133083)
                ·
                  rfl

theorem cell22_1101539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 2, 6].length) (baseStart_1101539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1101539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1101539 prefixEnd_1101539 := by exact prefixLift 1101539
  have htrace : WordTrace (prefixWord ++ tailWord_1101539) baseStart_1101539 baseEnd_1101539 := by
    simpa [prefixWord, tailWord_1101539, baseEnd_1101539] using wordTrace_append hprefix tailTrace_1101539
  have hstable : (prefixWord ++ tailWord_1101539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101539).length < 2 ^ (prefixWord ++ tailWord_1101539).sum := by decide
  have hdescent : baseEnd_1101539 < baseStart_1101539 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101550 : List Nat := [4, 1, 2, 1, 1, 2, 1, 1, 9]
def baseStart_1101550 : Nat := 118140960795 + 1101550 * 2 ^ 59
def prefixEnd_1101550 : Nat := 4983230072969 + 3 ^ 40 * 1101550 * 2
def baseEnd_1101550 : Nat := 125694358880060092057571

theorem tailTrace_1101550 : CollatzResearch.WordTrace tailWord_1101550 prefixEnd_1101550 125694358880060092057571 := by
  unfold tailWord_1101550
  simp only [CollatzResearch.WordTrace]
  refine ⟨5022103644909994325916763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26784552772853303071556069 5022103644909994325916763)
  ·
    refine ⟨7533155467364991488875145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5022103644909994325916763 7533155467364991488875145)
    ·
      refine ⟨5649866600523743616656359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7533155467364991488875145 5649866600523743616656359)
      ·
        refine ⟨8474799900785615424984539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5649866600523743616656359 8474799900785615424984539)
        ·
          refine ⟨12712199851178423137476809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8474799900785615424984539 12712199851178423137476809)
          ·
            refine ⟨9534149888383817353107607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12712199851178423137476809 9534149888383817353107607)
            ·
              refine ⟨14301224832575726029661411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9534149888383817353107607 14301224832575726029661411)
              ·
                refine ⟨21451837248863589044492117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14301224832575726029661411 21451837248863589044492117)
                ·
                  refine ⟨125694358880060092057571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 21451837248863589044492117 125694358880060092057571)
                  ·
                    rfl

theorem cell22_1101550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 9].length) (baseStart_1101550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1101550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1101550 prefixEnd_1101550 := by exact prefixLift 1101550
  have htrace : WordTrace (prefixWord ++ tailWord_1101550) baseStart_1101550 baseEnd_1101550 := by
    simpa [prefixWord, tailWord_1101550, baseEnd_1101550] using wordTrace_append hprefix tailTrace_1101550
  have hstable : (prefixWord ++ tailWord_1101550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101550).length < 2 ^ (prefixWord ++ tailWord_1101550).sum := by decide
  have hdescent : baseEnd_1101550 < baseStart_1101550 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101565 : List Nat := [1, 4, 1, 1, 1, 1, 2, 4, 2, 5]
def baseStart_1101565 : Nat := 118140960795 + 1101565 * 2 ^ 59
def prefixEnd_1101565 : Nat := 4983230072969 + 3 ^ 40 * 1101565 * 2
def baseEnd_1101565 : Nat := 377088211446725237047667

theorem tailTrace_1101565 : CollatzResearch.WordTrace tailWord_1101565 prefixEnd_1101565 377088211446725237047667 := by
  unfold tailWord_1101565
  simp only [CollatzResearch.WordTrace]
  refine ⟨40177376254225612169130149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26784917502817074779420099 40177376254225612169130149)
  ·
    refine ⟨7533258047667302281711903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40177376254225612169130149 7533258047667302281711903)
    ·
      refine ⟨11299887071500953422567855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7533258047667302281711903 11299887071500953422567855)
      ·
        refine ⟨16949830607251430133851783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11299887071500953422567855 16949830607251430133851783)
        ·
          refine ⟨25424745910877145200777675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16949830607251430133851783 25424745910877145200777675)
          ·
            refine ⟨38137118866315717801166513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25424745910877145200777675 38137118866315717801166513)
            ·
              refine ⟨28602839149736788350874885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38137118866315717801166513 28602839149736788350874885)
              ·
                refine ⟨5363032340575647815789041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28602839149736788350874885 5363032340575647815789041)
                ·
                  refine ⟨4022274255431735861841781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5363032340575647815789041 4022274255431735861841781)
                  ·
                    refine ⟨377088211446725237047667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4022274255431735861841781 377088211446725237047667)
                    ·
                      rfl

theorem cell22_1101565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 4, 2, 5].length) (baseStart_1101565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1101565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1101565 prefixEnd_1101565 := by exact prefixLift 1101565
  have htrace : WordTrace (prefixWord ++ tailWord_1101565) baseStart_1101565 baseEnd_1101565 := by
    simpa [prefixWord, tailWord_1101565, baseEnd_1101565] using wordTrace_append hprefix tailTrace_1101565
  have hstable : (prefixWord ++ tailWord_1101565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101565).length < 2 ^ (prefixWord ++ tailWord_1101565).sum := by decide
  have hdescent : baseEnd_1101565 < baseStart_1101565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101644 : List Nat := [2, 2, 1, 3, 4, 1, 2, 1, 1, 5]
def baseStart_1101644 : Nat := 118140960795 + 1101644 * 2 ^ 59
def prefixEnd_1101644 : Nat := 4983230072969 + 3 ^ 40 * 1101644 * 2
def baseEnd_1101644 : Nat := 377115254761195364322425

theorem tailTrace_1101644 : CollatzResearch.WordTrace tailWord_1101644 prefixEnd_1101644 377115254761195364322425 := by
  unfold tailWord_1101644
  simp only [CollatzResearch.WordTrace]
  refine ⟨20090128810469704330627993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26786838413959605774170657 20090128810469704330627993)
  ·
    refine ⟨15067596607852278247970995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20090128810469704330627993 15067596607852278247970995)
    ·
      refine ⟨22601394911778417371956493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15067596607852278247970995 22601394911778417371956493)
      ·
        refine ⟨8475523091916906514483685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22601394911778417371956493 8475523091916906514483685)
        ·
          refine ⟨1589160579734419971465691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8475523091916906514483685 1589160579734419971465691)
          ·
            refine ⟨2383740869601629957198537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1589160579734419971465691 2383740869601629957198537)
            ·
              refine ⟨1787805652201222467898903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2383740869601629957198537 1787805652201222467898903)
              ·
                refine ⟨2681708478301833701848355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1787805652201222467898903 2681708478301833701848355)
                ·
                  refine ⟨4022562717452750552772533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2681708478301833701848355 4022562717452750552772533)
                  ·
                    refine ⟨377115254761195364322425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4022562717452750552772533 377115254761195364322425)
                    ·
                      rfl

theorem cell22_1101644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 1, 1, 5].length) (baseStart_1101644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1101644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1101644 prefixEnd_1101644 := by exact prefixLift 1101644
  have htrace : WordTrace (prefixWord ++ tailWord_1101644) baseStart_1101644 baseEnd_1101644 := by
    simpa [prefixWord, tailWord_1101644, baseEnd_1101644] using wordTrace_append hprefix tailTrace_1101644
  have hstable : (prefixWord ++ tailWord_1101644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101644).length < 2 ^ (prefixWord ++ tailWord_1101644).sum := by decide
  have hdescent : baseEnd_1101644 < baseStart_1101644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101657 : List Nat := [1, 2, 1, 2, 2, 3, 5, 6]
def baseStart_1101657 : Nat := 118140960795 + 1101657 * 2 ^ 59
def prefixEnd_1101657 : Nat := 4983230072969 + 3 ^ 40 * 1101657 * 2
def baseEnd_1101657 : Nat := 41902189436318629305265

theorem tailTrace_1101657 : CollatzResearch.WordTrace tailWord_1101657 prefixEnd_1101657 41902189436318629305265 := by
  unfold tailWord_1101657
  simp only [CollatzResearch.WordTrace]
  refine ⟨40180731769892311881479225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26787154513261541254319483 40180731769892311881479225)
  ·
    refine ⟨30135548827419233911109419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40180731769892311881479225 30135548827419233911109419)
    ·
      refine ⟨45203323241128850866664129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30135548827419233911109419 45203323241128850866664129)
      ·
        refine ⟨33902492430846638149998097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45203323241128850866664129 33902492430846638149998097)
        ·
          refine ⟨25426869323134978612498573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33902492430846638149998097 25426869323134978612498573)
          ·
            refine ⟨9535075996175616979686965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25426869323134978612498573 9535075996175616979686965)
            ·
              refine ⟨893913374641464091845653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9535075996175616979686965 893913374641464091845653)
              ·
                refine ⟨41902189436318629305265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 893913374641464091845653 41902189436318629305265)
                ·
                  rfl

theorem cell22_1101657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 5, 6].length) (baseStart_1101657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1101657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1101657 prefixEnd_1101657 := by exact prefixLift 1101657
  have htrace : WordTrace (prefixWord ++ tailWord_1101657) baseStart_1101657 baseEnd_1101657 := by
    simpa [prefixWord, tailWord_1101657, baseEnd_1101657] using wordTrace_append hprefix tailTrace_1101657
  have hstable : (prefixWord ++ tailWord_1101657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101657).length < 2 ^ (prefixWord ++ tailWord_1101657).sum := by decide
  have hdescent : baseEnd_1101657 < baseStart_1101657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101674 : List Nat := [3, 1, 3, 4, 1, 1, 9]
def baseStart_1101674 : Nat := 118140960795 + 1101674 * 2 ^ 59
def prefixEnd_1101674 : Nat := 4983230072969 + 3 ^ 40 * 1101674 * 2
def baseEnd_1101674 : Nat := 13967612013862418002679

theorem tailTrace_1101674 : CollatzResearch.WordTrace tailWord_1101674 prefixEnd_1101674 13967612013862418002679 := by
  unfold tailWord_1101674
  simp only [CollatzResearch.WordTrace]
  refine ⟨10045337952707680946212019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26787567873887149189898717 10045337952707680946212019)
  ·
    refine ⟨15068006929061521419318029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10045337952707680946212019 15068006929061521419318029)
    ·
      refine ⟨5650502598398070532244261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15068006929061521419318029 5650502598398070532244261)
      ·
        refine ⟨1059469237199638224795799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5650502598398070532244261 1059469237199638224795799)
        ·
          refine ⟨1589203855799457337193699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1059469237199638224795799 1589203855799457337193699)
          ·
            refine ⟨2383805783699186005790549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1589203855799457337193699 2383805783699186005790549)
            ·
              refine ⟨13967612013862418002679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2383805783699186005790549 13967612013862418002679)
              ·
                rfl

theorem cell22_1101674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 9].length) (baseStart_1101674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1101674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1101674 prefixEnd_1101674 := by exact prefixLift 1101674
  have htrace : WordTrace (prefixWord ++ tailWord_1101674) baseStart_1101674 baseEnd_1101674 := by
    simpa [prefixWord, tailWord_1101674, baseEnd_1101674] using wordTrace_append hprefix tailTrace_1101674
  have hstable : (prefixWord ++ tailWord_1101674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101674).length < 2 ^ (prefixWord ++ tailWord_1101674).sum := by decide
  have hdescent : baseEnd_1101674 < baseStart_1101674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101678 : List Nat := [4, 1, 2, 3, 1, 3, 1, 2, 2, 3]
def baseStart_1101678 : Nat := 118140960795 + 1101678 * 2 ^ 59
def prefixEnd_1101678 : Nat := 4983230072969 + 3 ^ 40 * 1101678 * 2
def baseEnd_1101678 : Nat := 377126893656030608972321

theorem tailTrace_1101678 : CollatzResearch.WordTrace tailWord_1101678 prefixEnd_1101678 377126893656030608972321 := by
  unfold tailWord_1101678
  simp only [CollatzResearch.WordTrace]
  refine ⟨5022687212852029058499211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26787665135210821645329125 5022687212852029058499211)
  ·
    refine ⟨7534030819278043587748817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5022687212852029058499211 7534030819278043587748817)
    ·
      refine ⟨5650523114458532690811613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7534030819278043587748817 5650523114458532690811613)
      ·
        refine ⟨2118946167921949759054355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5650523114458532690811613 2118946167921949759054355)
        ·
          refine ⟨3178419251882924638581533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2118946167921949759054355 3178419251882924638581533)
          ·
            refine ⟨1191907219456096739468075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3178419251882924638581533 1191907219456096739468075)
            ·
              refine ⟨1787860829184145109202113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1191907219456096739468075 1787860829184145109202113)
              ·
                refine ⟨1340895621888108831901585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1787860829184145109202113 1340895621888108831901585)
                ·
                  refine ⟨1005671716416081623926189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1340895621888108831901585 1005671716416081623926189)
                  ·
                    refine ⟨377126893656030608972321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1005671716416081623926189 377126893656030608972321)
                    ·
                      rfl

theorem cell22_1101678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 2, 2, 3].length) (baseStart_1101678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1101678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1101678 prefixEnd_1101678 := by exact prefixLift 1101678
  have htrace : WordTrace (prefixWord ++ tailWord_1101678) baseStart_1101678 baseEnd_1101678 := by
    simpa [prefixWord, tailWord_1101678, baseEnd_1101678] using wordTrace_append hprefix tailTrace_1101678
  have hstable : (prefixWord ++ tailWord_1101678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101678).length < 2 ^ (prefixWord ++ tailWord_1101678).sum := by decide
  have hdescent : baseEnd_1101678 < baseStart_1101678 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101689 : List Nat := [1, 2, 1, 3, 2, 2, 4, 1, 3, 3]
def baseStart_1101689 : Nat := 118140960795 + 1101689 * 2 ^ 59
def prefixEnd_1101689 : Nat := 4983230072969 + 3 ^ 40 * 1101689 * 2
def baseEnd_1101689 : Nat := 377130659180830246947287

theorem tailTrace_1101689 : CollatzResearch.WordTrace tailWord_1101689 prefixEnd_1101689 377130659180830246947287 := by
  unfold tailWord_1101689
  simp only [CollatzResearch.WordTrace]
  refine ⟨40181898905776381346644121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26787932603850920897762747 40181898905776381346644121)
  ·
    refine ⟨30136424179332286009983091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40181898905776381346644121 30136424179332286009983091)
    ·
      refine ⟨45204636268998429014974637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30136424179332286009983091 45204636268998429014974637)
      ·
        refine ⟨16951738600874410880615489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45204636268998429014974637 16951738600874410880615489)
        ·
          refine ⟨12713803950655808160461617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16951738600874410880615489 12713803950655808160461617)
          ·
            refine ⟨9535352962991856120346213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12713803950655808160461617 9535352962991856120346213)
            ·
              refine ⟨1787878680560973022564915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9535352962991856120346213 1787878680560973022564915)
              ·
                refine ⟨2681818020841459533847373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1787878680560973022564915 2681818020841459533847373)
                ·
                  refine ⟨1005681757815547325192765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2681818020841459533847373 1005681757815547325192765)
                  ·
                    refine ⟨377130659180830246947287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1005681757815547325192765 377130659180830246947287)
                    ·
                      rfl

theorem cell22_1101689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 1, 3, 3].length) (baseStart_1101689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1101689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1101689 prefixEnd_1101689 := by exact prefixLift 1101689
  have htrace : WordTrace (prefixWord ++ tailWord_1101689) baseStart_1101689 baseEnd_1101689 := by
    simpa [prefixWord, tailWord_1101689, baseEnd_1101689] using wordTrace_append hprefix tailTrace_1101689
  have hstable : (prefixWord ++ tailWord_1101689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101689).length < 2 ^ (prefixWord ++ tailWord_1101689).sum := by decide
  have hdescent : baseEnd_1101689 < baseStart_1101689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101796 : List Nat := [2, 3, 1, 1, 1, 1, 6, 2, 2, 3]
def baseStart_1101796 : Nat := 118140960795 + 1101796 * 2 ^ 59
def prefixEnd_1101796 : Nat := 4983230072969 + 3 ^ 40 * 1101796 * 2
def baseEnd_1101796 : Nat := 377167287467517634521959

theorem tailTrace_1101796 : CollatzResearch.WordTrace tailWord_1101796 prefixEnd_1101796 377167287467517634521959 := by
  unfold tailWord_1101796
  simp only [CollatzResearch.WordTrace]
  refine ⟨20092900758194369310394621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26790534344259159080526161 20092900758194369310394621)
  ·
    refine ⟨7534837784322888491397983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20092900758194369310394621 7534837784322888491397983)
    ·
      refine ⟨11302256676484332737096975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7534837784322888491397983 11302256676484332737096975)
      ·
        refine ⟨16953385014726499105645463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11302256676484332737096975 16953385014726499105645463)
        ·
          refine ⟨25430077522089748658468195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16953385014726499105645463 25430077522089748658468195)
          ·
            refine ⟨38145116283134622987702293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25430077522089748658468195 38145116283134622987702293)
            ·
              refine ⟨1788052325771935452548545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 38145116283134622987702293 1788052325771935452548545)
              ·
                refine ⟨1341039244328951589411409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1788052325771935452548545 1341039244328951589411409)
                ·
                  refine ⟨1005779433246713692058557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1341039244328951589411409 1005779433246713692058557)
                  ·
                    refine ⟨377167287467517634521959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1005779433246713692058557 377167287467517634521959)
                    ·
                      rfl

theorem cell22_1101796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 2, 2, 3].length) (baseStart_1101796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1101796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1101796 prefixEnd_1101796 := by exact prefixLift 1101796
  have htrace : WordTrace (prefixWord ++ tailWord_1101796) baseStart_1101796 baseEnd_1101796 := by
    simpa [prefixWord, tailWord_1101796, baseEnd_1101796] using wordTrace_append hprefix tailTrace_1101796
  have hstable : (prefixWord ++ tailWord_1101796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101796).length < 2 ^ (prefixWord ++ tailWord_1101796).sum := by decide
  have hdescent : baseEnd_1101796 < baseStart_1101796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101858 : List Nat := [3, 3, 1, 1, 1, 2, 1, 6, 1, 3]
def baseStart_1101858 : Nat := 118140960795 + 1101858 * 2 ^ 59
def prefixEnd_1101858 : Nat := 4983230072969 + 3 ^ 40 * 1101858 * 2
def baseEnd_1101858 : Nat := 377188511334570139471769

theorem tailTrace_1101858 : CollatzResearch.WordTrace tailWord_1101858 prefixEnd_1101858 377188511334570139471769 := by
  unfold tailWord_1101858
  simp only [CollatzResearch.WordTrace]
  refine ⟨10047015710541030802386557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26792041894776082139697485 10047015710541030802386557)
  ·
    refine ⟨3767630891452886550894959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10047015710541030802386557 3767630891452886550894959)
    ·
      refine ⟨5651446337179329826342439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3767630891452886550894959 5651446337179329826342439)
      ·
        refine ⟨8477169505768994739513659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5651446337179329826342439 8477169505768994739513659)
        ·
          refine ⟨12715754258653492109270489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8477169505768994739513659 12715754258653492109270489)
          ·
            refine ⟨9536815693990119081952867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12715754258653492109270489 9536815693990119081952867)
            ·
              refine ⟨14305223540985178622929301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9536815693990119081952867 14305223540985178622929301)
              ·
                refine ⟨670557353483680247949811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14305223540985178622929301 670557353483680247949811)
                ·
                  refine ⟨1005836030225520371924717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 670557353483680247949811 1005836030225520371924717)
                  ·
                    refine ⟨377188511334570139471769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1005836030225520371924717 377188511334570139471769)
                    ·
                      rfl

theorem cell22_1101858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 6, 1, 3].length) (baseStart_1101858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1101858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1101858 prefixEnd_1101858 := by exact prefixLift 1101858
  have htrace : WordTrace (prefixWord ++ tailWord_1101858) baseStart_1101858 baseEnd_1101858 := by
    simpa [prefixWord, tailWord_1101858, baseEnd_1101858] using wordTrace_append hprefix tailTrace_1101858
  have hstable : (prefixWord ++ tailWord_1101858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101858).length < 2 ^ (prefixWord ++ tailWord_1101858).sum := by decide
  have hdescent : baseEnd_1101858 < baseStart_1101858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101867 : List Nat := [1, 1, 1, 1, 2, 1, 4, 1, 2, 8]
def baseStart_1101867 : Nat := 118140960795 + 1101867 * 2 ^ 59
def prefixEnd_1101867 : Nat := 4983230072969 + 3 ^ 40 * 1101867 * 2
def baseEnd_1101867 : Nat := 377191592218497115996741

theorem tailTrace_1101867 : CollatzResearch.WordTrace tailWord_1101867 prefixEnd_1101867 377191592218497115996741 := by
  unfold tailWord_1101867
  simp only [CollatzResearch.WordTrace]
  refine ⟨40188391099131517746623855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26792260732754345164415903 40188391099131517746623855)
  ·
    refine ⟨60282586648697276619935783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40188391099131517746623855 60282586648697276619935783)
    ·
      refine ⟨90423879973045914929903675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60282586648697276619935783 90423879973045914929903675)
      ·
        refine ⟨135635819959568872394855513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90423879973045914929903675 135635819959568872394855513)
        ·
          refine ⟨101726864969676654296141635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135635819959568872394855513 101726864969676654296141635)
          ·
            refine ⟨152590297454514981444212453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101726864969676654296141635 152590297454514981444212453)
            ·
              refine ⟨28610680772721559020789835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 152590297454514981444212453 28610680772721559020789835)
              ·
                refine ⟨42916021159082338531184753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28610680772721559020789835 42916021159082338531184753)
                ·
                  refine ⟨32187015869311753898388565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42916021159082338531184753 32187015869311753898388565)
                  ·
                    refine ⟨377191592218497115996741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 32187015869311753898388565 377191592218497115996741)
                    ·
                      rfl

theorem cell22_1101867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 8].length) (baseStart_1101867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1101867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1101867 prefixEnd_1101867 := by exact prefixLift 1101867
  have htrace : WordTrace (prefixWord ++ tailWord_1101867) baseStart_1101867 baseEnd_1101867 := by
    simpa [prefixWord, tailWord_1101867, baseEnd_1101867] using wordTrace_append hprefix tailTrace_1101867
  have hstable : (prefixWord ++ tailWord_1101867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101867).length < 2 ^ (prefixWord ++ tailWord_1101867).sum := by decide
  have hdescent : baseEnd_1101867 < baseStart_1101867 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101916 : List Nat := [2, 2, 4, 1, 1, 2, 3, 1, 6]
def baseStart_1101916 : Nat := 118140960795 + 1101916 * 2 ^ 59
def prefixEnd_1101916 : Nat := 4983230072969 + 3 ^ 40 * 1101916 * 2
def baseEnd_1101916 : Nat := 125736121973292440507197

theorem tailTrace_1101916 : CollatzResearch.WordTrace tailWord_1101916 prefixEnd_1101916 125736121973292440507197 := by
  unfold tailWord_1101916
  simp only [CollatzResearch.WordTrace]
  refine ⟨20095089137976999557578801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26793452183969332743438401 20095089137976999557578801)
  ·
    refine ⟨15071316853482749668184101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20095089137976999557578801 15071316853482749668184101)
    ·
      refine ⟨2825871910028015562784519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15071316853482749668184101 2825871910028015562784519)
      ·
        refine ⟨4238807865042023344176779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2825871910028015562784519 4238807865042023344176779)
        ·
          refine ⟨6358211797563035016265169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4238807865042023344176779 6358211797563035016265169)
          ·
            refine ⟨4768658848172276262198877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6358211797563035016265169 4768658848172276262198877)
            ·
              refine ⟨1788247068064603598324579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4768658848172276262198877 1788247068064603598324579)
              ·
                refine ⟨2682370602096905397486869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1788247068064603598324579 2682370602096905397486869)
                ·
                  refine ⟨125736121973292440507197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2682370602096905397486869 125736121973292440507197)
                  ·
                    rfl

theorem cell22_1101916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 1, 6].length) (baseStart_1101916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1101916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1101916 prefixEnd_1101916 := by exact prefixLift 1101916
  have htrace : WordTrace (prefixWord ++ tailWord_1101916) baseStart_1101916 baseEnd_1101916 := by
    simpa [prefixWord, tailWord_1101916, baseEnd_1101916] using wordTrace_append hprefix tailTrace_1101916
  have hstable : (prefixWord ++ tailWord_1101916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101916).length < 2 ^ (prefixWord ++ tailWord_1101916).sum := by decide
  have hdescent : baseEnd_1101916 < baseStart_1101916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101922 : List Nat := [3, 3, 2, 2, 3, 1, 2, 1, 5]
def baseStart_1101922 : Nat := 118140960795 + 1101922 * 2 ^ 59
def prefixEnd_1101922 : Nat := 4983230072969 + 3 ^ 40 * 1101922 * 2
def baseEnd_1101922 : Nat := 125736806614165101957191

theorem tailTrace_1101922 : CollatzResearch.WordTrace tailWord_1101922 prefixEnd_1101922 125736806614165101957191 := by
  unfold tailWord_1101922
  simp only [CollatzResearch.WordTrace]
  refine ⟨10047599278483065534969005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26793598075954841426584013 10047599278483065534969005)
  ·
    refine ⟨3767849729431149575613377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10047599278483065534969005 3767849729431149575613377)
    ·
      refine ⟨2825887297073362181710033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3767849729431149575613377 2825887297073362181710033)
      ·
        refine ⟨2119415472805021636282525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2825887297073362181710033 2119415472805021636282525)
        ·
          refine ⟨794780802301883113605947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2119415472805021636282525 794780802301883113605947)
          ·
            refine ⟨1192171203452824670408921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 794780802301883113605947 1192171203452824670408921)
            ·
              refine ⟨894128402589618502806691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1192171203452824670408921 894128402589618502806691)
              ·
                refine ⟨1341192603884427754210037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 894128402589618502806691 1341192603884427754210037)
                ·
                  refine ⟨125736806614165101957191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1341192603884427754210037 125736806614165101957191)
                  ·
                    rfl

theorem cell22_1101922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 2, 1, 5].length) (baseStart_1101922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1101922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1101922 prefixEnd_1101922 := by exact prefixLift 1101922
  have htrace : WordTrace (prefixWord ++ tailWord_1101922) baseStart_1101922 baseEnd_1101922 := by
    simpa [prefixWord, tailWord_1101922, baseEnd_1101922] using wordTrace_append hprefix tailTrace_1101922
  have hstable : (prefixWord ++ tailWord_1101922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101922).length < 2 ^ (prefixWord ++ tailWord_1101922).sum := by decide
  have hdescent : baseEnd_1101922 < baseStart_1101922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101929 : List Nat := [1, 2, 1, 1, 1, 5, 1, 2, 4, 4]
def baseStart_1101929 : Nat := 118140960795 + 1101929 * 2 ^ 59
def prefixEnd_1101929 : Nat := 4983230072969 + 3 ^ 40 * 1101929 * 2
def baseEnd_1101929 : Nat := 377212816085549620946551

theorem tailTrace_1101929 : CollatzResearch.WordTrace tailWord_1101929 prefixEnd_1101929 377212816085549620946551 := by
  unfold tailWord_1101929
  simp only [CollatzResearch.WordTrace]
  refine ⟨40190652424906902335380841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26793768283271268223587227 40190652424906902335380841)
  ·
    refine ⟨30142989318680176751535631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40190652424906902335380841 30142989318680176751535631)
    ·
      refine ⟨45214483978020265127303447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30142989318680176751535631 45214483978020265127303447)
      ·
        refine ⟨67821725967030397690955171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45214483978020265127303447 67821725967030397690955171)
        ·
          refine ⟨101732588950545596536432757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67821725967030397690955171 101732588950545596536432757)
          ·
            refine ⟨9537430214113649675290571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 101732588950545596536432757 9537430214113649675290571)
            ·
              refine ⟨14306145321170474512935857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9537430214113649675290571 14306145321170474512935857)
              ·
                refine ⟨10729608990877855884701893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14306145321170474512935857 10729608990877855884701893)
                ·
                  refine ⟨2011801685789597978381605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10729608990877855884701893 2011801685789597978381605)
                  ·
                    refine ⟨377212816085549620946551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2011801685789597978381605 377212816085549620946551)
                    ·
                      rfl

theorem cell22_1101929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 4, 4].length) (baseStart_1101929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1101929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1101929 prefixEnd_1101929 := by exact prefixLift 1101929
  have htrace : WordTrace (prefixWord ++ tailWord_1101929) baseStart_1101929 baseEnd_1101929 := by
    simpa [prefixWord, tailWord_1101929, baseEnd_1101929] using wordTrace_append hprefix tailTrace_1101929
  have hstable : (prefixWord ++ tailWord_1101929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101929).length < 2 ^ (prefixWord ++ tailWord_1101929).sum := by decide
  have hdescent : baseEnd_1101929 < baseStart_1101929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101978 : List Nat := [3, 1, 1, 5, 2, 2, 1, 7]
def baseStart_1101978 : Nat := 118140960795 + 1101978 * 2 ^ 59
def prefixEnd_1101978 : Nat := 4983230072969 + 3 ^ 40 * 1101978 * 2
def baseEnd_1101978 : Nat := 41914398865214425163489

theorem tailTrace_1101978 : CollatzResearch.WordTrace tailWord_1101978 prefixEnd_1101978 41914398865214425163489 := by
  unfold tailWord_1101978
  simp only [CollatzResearch.WordTrace]
  refine ⟨10048109900432345925978647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26794959734486255802609725 10048109900432345925978647)
  ·
    refine ⟨15072164850648518888967971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10048109900432345925978647 15072164850648518888967971)
    ·
      refine ⟨22608247275972778333451957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15072164850648518888967971 22608247275972778333451957)
      ·
        refine ⟨2119523182122447968761121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22608247275972778333451957 2119523182122447968761121)
        ·
          refine ⟨1589642386591835976570841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2119523182122447968761121 1589642386591835976570841)
          ·
            refine ⟨1192231789943876982428131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1589642386591835976570841 1192231789943876982428131)
            ·
              refine ⟨1788347684915815473642197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1192231789943876982428131 1788347684915815473642197)
              ·
                refine ⟨41914398865214425163489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1788347684915815473642197 41914398865214425163489)
                ·
                  rfl

theorem cell22_1101978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 7].length) (baseStart_1101978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1101978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1101978 prefixEnd_1101978 := by exact prefixLift 1101978
  have htrace : WordTrace (prefixWord ++ tailWord_1101978) baseStart_1101978 baseEnd_1101978 := by
    simpa [prefixWord, tailWord_1101978, baseEnd_1101978] using wordTrace_append hprefix tailTrace_1101978
  have hstable : (prefixWord ++ tailWord_1101978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101978).length < 2 ^ (prefixWord ++ tailWord_1101978).sum := by decide
  have hdescent : baseEnd_1101978 < baseStart_1101978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102053 : List Nat := [1, 3, 1, 4, 2, 1, 1, 4, 1, 4]
def baseStart_1102053 : Nat := 118140960795 + 1102053 * 2 ^ 59
def prefixEnd_1102053 : Nat := 4983230072969 + 3 ^ 40 * 1102053 * 2
def baseEnd_1102053 : Nat := 377255263819654630846171

theorem tailTrace_1102053 : CollatzResearch.WordTrace tailWord_1102053 prefixEnd_1102053 377255263819654630846171 := by
  unfold tailWord_1102053
  simp only [CollatzResearch.WordTrace]
  refine ⟨40195175076457671512894813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26796783384305114341929875 40195175076457671512894813)
  ·
    refine ⟨15073190653671626817335555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40195175076457671512894813 15073190653671626817335555)
    ·
      refine ⟨22609785980507440226003333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15073190653671626817335555 22609785980507440226003333)
      ·
        refine ⟨4239334871345145042375625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22609785980507440226003333 4239334871345145042375625)
        ·
          refine ⟨3179501153508858781781719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4239334871345145042375625 3179501153508858781781719)
          ·
            refine ⟨4769251730263288172672579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3179501153508858781781719 4769251730263288172672579)
            ·
              refine ⟨7153877595394932259008869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4769251730263288172672579 7153877595394932259008869)
              ·
                refine ⟨1341352049136549798564163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7153877595394932259008869 1341352049136549798564163)
                ·
                  refine ⟨2012028073704824697846245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1341352049136549798564163 2012028073704824697846245)
                  ·
                    refine ⟨377255263819654630846171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2012028073704824697846245 377255263819654630846171)
                    ·
                      rfl

theorem cell22_1102053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 4, 1, 4].length) (baseStart_1102053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1102053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1102053 prefixEnd_1102053 := by exact prefixLift 1102053
  have htrace : WordTrace (prefixWord ++ tailWord_1102053) baseStart_1102053 baseEnd_1102053 := by
    simpa [prefixWord, tailWord_1102053, baseEnd_1102053] using wordTrace_append hprefix tailTrace_1102053
  have hstable : (prefixWord ++ tailWord_1102053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102053).length < 2 ^ (prefixWord ++ tailWord_1102053).sum := by decide
  have hdescent : baseEnd_1102053 < baseStart_1102053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102083 : List Nat := [1, 1, 1, 3, 2, 3, 2, 4, 2, 3]
def baseStart_1102083 : Nat := 118140960795 + 1102083 * 2 ^ 59
def prefixEnd_1102083 : Nat := 4983230072969 + 3 ^ 40 * 1102083 * 2
def baseEnd_1102083 : Nat := 377265533432744552596079

theorem tailTrace_1102083 : CollatzResearch.WordTrace tailWord_1102083 prefixEnd_1102083 377265533432744552596079 := by
  unfold tailWord_1102083
  simp only [CollatzResearch.WordTrace]
  refine ⟨40196269266348986636486903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26797512844232657757657935 40196269266348986636486903)
  ·
    refine ⟨60294403899523479954730355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40196269266348986636486903 60294403899523479954730355)
    ·
      refine ⟨90441605849285219932095533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60294403899523479954730355 90441605849285219932095533)
      ·
        refine ⟨33915602193481957474535825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90441605849285219932095533 33915602193481957474535825)
        ·
          refine ⟨25436701645111468105901869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33915602193481957474535825 25436701645111468105901869)
          ·
            refine ⟨9538763116916800539713201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25436701645111468105901869 9538763116916800539713201)
            ·
              refine ⟨7154072337687600404784901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9538763116916800539713201 7154072337687600404784901)
              ·
                refine ⟨1341388563316425075897169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7154072337687600404784901 1341388563316425075897169)
                ·
                  refine ⟨1006041422487318806922877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1341388563316425075897169 1006041422487318806922877)
                  ·
                    refine ⟨377265533432744552596079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1006041422487318806922877 377265533432744552596079)
                    ·
                      rfl

theorem cell22_1102083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 4, 2, 3].length) (baseStart_1102083 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1102083 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1102083 prefixEnd_1102083 := by exact prefixLift 1102083
  have htrace : WordTrace (prefixWord ++ tailWord_1102083) baseStart_1102083 baseEnd_1102083 := by
    simpa [prefixWord, tailWord_1102083, baseEnd_1102083] using wordTrace_append hprefix tailTrace_1102083
  have hstable : (prefixWord ++ tailWord_1102083).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102083).length < 2 ^ (prefixWord ++ tailWord_1102083).sum := by decide
  have hdescent : baseEnd_1102083 < baseStart_1102083 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102203 : List Nat := [1, 1, 1, 1, 1, 8, 2, 1, 6]
def baseStart_1102203 : Nat := 118140960795 + 1102203 * 2 ^ 59
def prefixEnd_1102203 : Nat := 4983230072969 + 3 ^ 40 * 1102203 * 2
def baseEnd_1102203 : Nat := 125768870628368079865237

theorem tailTrace_1102203 : CollatzResearch.WordTrace tailWord_1102203 prefixEnd_1102203 125768870628368079865237 := by
  unfold tailWord_1102203
  simp only [CollatzResearch.WordTrace]
  refine ⟨40200646025914247130855263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26800430683942831420570175 40200646025914247130855263)
  ·
    refine ⟨60300969038871370696282895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40200646025914247130855263 60300969038871370696282895)
    ·
      refine ⟨90451453558307056044424343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60300969038871370696282895 90451453558307056044424343)
      ·
        refine ⟨135677180337460584066636515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90451453558307056044424343 135677180337460584066636515)
        ·
          refine ⟨203515770506190876099954773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135677180337460584066636515 203515770506190876099954773)
          ·
            refine ⟨2384950435619424329296345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 203515770506190876099954773 2384950435619424329296345)
            ·
              refine ⟨1788712826714568246972259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2384950435619424329296345 1788712826714568246972259)
              ·
                refine ⟨2683069240071852370458389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1788712826714568246972259 2683069240071852370458389)
                ·
                  refine ⟨125768870628368079865237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2683069240071852370458389 125768870628368079865237)
                  ·
                    rfl

theorem cell22_1102203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 1, 6].length) (baseStart_1102203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1102203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1102203 prefixEnd_1102203 := by exact prefixLift 1102203
  have htrace : WordTrace (prefixWord ++ tailWord_1102203) baseStart_1102203 baseEnd_1102203 := by
    simpa [prefixWord, tailWord_1102203, baseEnd_1102203] using wordTrace_append hprefix tailTrace_1102203
  have hstable : (prefixWord ++ tailWord_1102203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102203).length < 2 ^ (prefixWord ++ tailWord_1102203).sum := by decide
  have hdescent : baseEnd_1102203 < baseStart_1102203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102222 : List Nat := [4, 1, 1, 4, 1, 2, 2, 2, 1, 4]
def baseStart_1102222 : Nat := 118140960795 + 1102222 * 2 ^ 59
def prefixEnd_1102222 : Nat := 4983230072969 + 3 ^ 40 * 1102222 * 2
def baseEnd_1102222 : Nat := 377313115973394523370653

theorem tailTrace_1102222 : CollatzResearch.WordTrace tailWord_1102222 prefixEnd_1102222 377313115973394523370653 := by
  unfold tailWord_1102222
  simp only [CollatzResearch.WordTrace]
  refine ⟨5025167376605676671974615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26800892675230275583864613 5025167376605676671974615)
  ·
    refine ⟨7537751064908515007961923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5025167376605676671974615 7537751064908515007961923)
    ·
      refine ⟨11306626597362772511942885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7537751064908515007961923 11306626597362772511942885)
      ·
        refine ⟨2119992487005519845989291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11306626597362772511942885 2119992487005519845989291)
        ·
          refine ⟨3179988730508279768983937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2119992487005519845989291 3179988730508279768983937)
          ·
            refine ⟨2384991547881209826737953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3179988730508279768983937 2384991547881209826737953)
            ·
              refine ⟨1788743660910907370053465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2384991547881209826737953 1788743660910907370053465)
              ·
                refine ⟨1341557745683180527540099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1788743660910907370053465 1341557745683180527540099)
                ·
                  refine ⟨2012336618524770791310149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1341557745683180527540099 2012336618524770791310149)
                  ·
                    refine ⟨377313115973394523370653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2012336618524770791310149 377313115973394523370653)
                    ·
                      rfl

theorem cell22_1102222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 2, 1, 4].length) (baseStart_1102222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1102222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1102222 prefixEnd_1102222 := by exact prefixLift 1102222
  have htrace : WordTrace (prefixWord ++ tailWord_1102222) baseStart_1102222 baseEnd_1102222 := by
    simpa [prefixWord, tailWord_1102222, baseEnd_1102222] using wordTrace_append hprefix tailTrace_1102222
  have hstable : (prefixWord ++ tailWord_1102222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102222).length < 2 ^ (prefixWord ++ tailWord_1102222).sum := by decide
  have hdescent : baseEnd_1102222 < baseStart_1102222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102230 : List Nat := [5, 3, 1, 2, 1, 2, 1, 3, 1, 3]
def baseStart_1102230 : Nat := 118140960795 + 1102230 * 2 ^ 59
def prefixEnd_1102230 : Nat := 4983230072969 + 3 ^ 40 * 1102230 * 2
def baseEnd_1102230 : Nat := 377315854536885169170629

theorem tailTrace_1102230 : CollatzResearch.WordTrace tailWord_1102230 prefixEnd_1102230 377315854536885169170629 := by
  unfold tailWord_1102230
  simp only [CollatzResearch.WordTrace]
  refine ⟨2512601924801026921380509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26801087197877620494725429 2512601924801026921380509)
  ·
    refine ⟨942225721800385095517691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2512601924801026921380509 942225721800385095517691)
    ·
      refine ⟨1413338582700577643276537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 942225721800385095517691 1413338582700577643276537)
      ·
        refine ⟨1060003937025433232457403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1413338582700577643276537 1060003937025433232457403)
        ·
          refine ⟨1590005905538149848686105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1060003937025433232457403 1590005905538149848686105)
          ·
            refine ⟨1192504429153612386514579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1590005905538149848686105 1192504429153612386514579)
            ·
              refine ⟨1788756643730418579771869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1192504429153612386514579 1788756643730418579771869)
              ·
                refine ⟨670783741398906967414451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1788756643730418579771869 670783741398906967414451)
                ·
                  refine ⟨1006175612098360451121677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 670783741398906967414451 1006175612098360451121677)
                  ·
                    refine ⟨377315854536885169170629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1006175612098360451121677 377315854536885169170629)
                    ·
                      rfl

theorem cell22_1102230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_1102230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1102230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1102230 prefixEnd_1102230 := by exact prefixLift 1102230
  have htrace : WordTrace (prefixWord ++ tailWord_1102230) baseStart_1102230 baseEnd_1102230 := by
    simpa [prefixWord, tailWord_1102230, baseEnd_1102230] using wordTrace_append hprefix tailTrace_1102230
  have hstable : (prefixWord ++ tailWord_1102230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102230).length < 2 ^ (prefixWord ++ tailWord_1102230).sum := by decide
  have hdescent : baseEnd_1102230 < baseStart_1102230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102233 : List Nat := [1, 2, 1, 2, 1, 4, 2, 3, 2, 4]
def baseStart_1102233 : Nat := 118140960795 + 1102233 * 2 ^ 59
def prefixEnd_1102233 : Nat := 4983230072969 + 3 ^ 40 * 1102233 * 2
def baseEnd_1102233 : Nat := 377316881498194161345619

theorem tailTrace_1102233 : CollatzResearch.WordTrace tailWord_1102233 prefixEnd_1102233 377316881498194161345619 := by
  unfold tailWord_1102233
  simp only [CollatzResearch.WordTrace]
  refine ⟨40201740215805562254447353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26801160143870374836298235 40201740215805562254447353)
  ·
    refine ⟨30151305161854171690835515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40201740215805562254447353 30151305161854171690835515)
    ·
      refine ⟨45226957742781257536253273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30151305161854171690835515 45226957742781257536253273)
      ·
        refine ⟨33920218307085943152189955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45226957742781257536253273 33920218307085943152189955)
        ·
          refine ⟨50880327460628914728284933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33920218307085943152189955 50880327460628914728284933)
          ·
            refine ⟨9540061398867921511553425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50880327460628914728284933 9540061398867921511553425)
            ·
              refine ⟨7155046049150941133665069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9540061398867921511553425 7155046049150941133665069)
              ·
                refine ⟨2683142268431602925124401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7155046049150941133665069 2683142268431602925124401)
                ·
                  refine ⟨2012356701323702193843301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2683142268431602925124401 2012356701323702193843301)
                  ·
                    refine ⟨377316881498194161345619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2012356701323702193843301 377316881498194161345619)
                    ·
                      rfl

theorem cell22_1102233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 3, 2, 4].length) (baseStart_1102233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1102233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1102233 prefixEnd_1102233 := by exact prefixLift 1102233
  have htrace : WordTrace (prefixWord ++ tailWord_1102233) baseStart_1102233 baseEnd_1102233 := by
    simpa [prefixWord, tailWord_1102233, baseEnd_1102233] using wordTrace_append hprefix tailTrace_1102233
  have hstable : (prefixWord ++ tailWord_1102233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102233).length < 2 ^ (prefixWord ++ tailWord_1102233).sum := by decide
  have hdescent : baseEnd_1102233 < baseStart_1102233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102269 : List Nat := [1, 4, 1, 2, 2, 4, 2, 1, 2, 3]
def baseStart_1102269 : Nat := 118140960795 + 1102269 * 2 ^ 59
def prefixEnd_1102269 : Nat := 4983230072969 + 3 ^ 40 * 1102269 * 2
def baseEnd_1102269 : Nat := 377329205033902067445509

theorem tailTrace_1102269 : CollatzResearch.WordTrace tailWord_1102269 prefixEnd_1102269 377329205033902067445509 := by
  unfold tailWord_1102269
  simp only [CollatzResearch.WordTrace]
  refine ⟨40203053243675140402757861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26802035495783426935171907 40203053243675140402757861)
  ·
    refine ⟨7538072483189088825517099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40203053243675140402757861 7538072483189088825517099)
    ·
      refine ⟨11307108724783633238275649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7538072483189088825517099 11307108724783633238275649)
      ·
        refine ⟨8480331543587724928706737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11307108724783633238275649 8480331543587724928706737)
        ·
          refine ⟨6360248657690793696530053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8480331543587724928706737 6360248657690793696530053)
          ·
            refine ⟨1192546623317023818099385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6360248657690793696530053 1192546623317023818099385)
            ·
              refine ⟨894409967487767863574539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1192546623317023818099385 894409967487767863574539)
              ·
                refine ⟨1341614951231651795361809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 894409967487767863574539 1341614951231651795361809)
                ·
                  refine ⟨1006211213423738846521357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1341614951231651795361809 1006211213423738846521357)
                  ·
                    refine ⟨377329205033902067445509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1006211213423738846521357 377329205033902067445509)
                    ·
                      rfl

theorem cell22_1102269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 2, 1, 2, 3].length) (baseStart_1102269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1102269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1102269 prefixEnd_1102269 := by exact prefixLift 1102269
  have htrace : WordTrace (prefixWord ++ tailWord_1102269) baseStart_1102269 baseEnd_1102269 := by
    simpa [prefixWord, tailWord_1102269, baseEnd_1102269] using wordTrace_append hprefix tailTrace_1102269
  have hstable : (prefixWord ++ tailWord_1102269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102269).length < 2 ^ (prefixWord ++ tailWord_1102269).sum := by decide
  have hdescent : baseEnd_1102269 < baseStart_1102269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102273 : List Nat := [1, 2, 7, 1, 2, 1, 1, 2, 1, 4]
def baseStart_1102273 : Nat := 118140960795 + 1102273 * 2 ^ 59
def prefixEnd_1102273 : Nat := 4983230072969 + 3 ^ 40 * 1102273 * 2
def baseEnd_1102273 : Nat := 377330574315647390345497

theorem tailTrace_1102273 : CollatzResearch.WordTrace tailWord_1102273 prefixEnd_1102273 377330574315647390345497 := by
  unfold tailWord_1102273
  simp only [CollatzResearch.WordTrace]
  refine ⟨40203199135660649085903473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26802132757107099390602315 40203199135660649085903473)
  ·
    refine ⟨30152399351745486814427605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40203199135660649085903473 30152399351745486814427605)
    ·
      refine ⟨706696859806534847213147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 30152399351745486814427605 706696859806534847213147)
      ·
        refine ⟨1060045289709802270819721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 706696859806534847213147 1060045289709802270819721)
        ·
          refine ⟨795033967282351703114791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1060045289709802270819721 795033967282351703114791)
          ·
            refine ⟨1192550950923527554672187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 795033967282351703114791 1192550950923527554672187)
            ·
              refine ⟨1788826426385291332008281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1192550950923527554672187 1788826426385291332008281)
              ·
                refine ⟨1341619819788968499006211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1788826426385291332008281 1341619819788968499006211)
                ·
                  refine ⟨2012429729683452748509317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1341619819788968499006211 2012429729683452748509317)
                  ·
                    refine ⟨377330574315647390345497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2012429729683452748509317 377330574315647390345497)
                    ·
                      rfl

theorem cell22_1102273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_1102273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1102273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1102273 prefixEnd_1102273 := by exact prefixLift 1102273
  have htrace : WordTrace (prefixWord ++ tailWord_1102273) baseStart_1102273 baseEnd_1102273 := by
    simpa [prefixWord, tailWord_1102273, baseEnd_1102273] using wordTrace_append hprefix tailTrace_1102273
  have hstable : (prefixWord ++ tailWord_1102273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102273).length < 2 ^ (prefixWord ++ tailWord_1102273).sum := by decide
  have hdescent : baseEnd_1102273 < baseStart_1102273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102297 : List Nat := [1, 2, 1, 2, 4, 1, 2, 5, 1, 3]
def baseStart_1102297 : Nat := 118140960795 + 1102297 * 2 ^ 59
def prefixEnd_1102297 : Nat := 4983230072969 + 3 ^ 40 * 1102297 * 2
def baseEnd_1102297 : Nat := 377338790006119327745423

theorem tailTrace_1102297 : CollatzResearch.WordTrace tailWord_1102297 prefixEnd_1102297 377338790006119327745423 := by
  unfold tailWord_1102297
  simp only [CollatzResearch.WordTrace]
  refine ⟨40204074487573701184777145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26802716325049134123184763 40204074487573701184777145)
  ·
    refine ⟨30153055865680275888582859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40204074487573701184777145 30153055865680275888582859)
    ·
      refine ⟨45229583798520413832874289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30153055865680275888582859 45229583798520413832874289)
      ·
        refine ⟨33922187848890310374655717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45229583798520413832874289 33922187848890310374655717)
        ·
          refine ⟨6360410221666933195247947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33922187848890310374655717 6360410221666933195247947)
          ·
            refine ⟨9540615332500399792871921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6360410221666933195247947 9540615332500399792871921)
            ·
              refine ⟨7155461499375299844653941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9540615332500399792871921 7155461499375299844653941)
              ·
                refine ⟨670824515566434360436307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7155461499375299844653941 670824515566434360436307)
                ·
                  refine ⟨1006236773349651540654461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 670824515566434360436307 1006236773349651540654461)
                  ·
                    refine ⟨377338790006119327745423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1006236773349651540654461 377338790006119327745423)
                    ·
                      rfl

theorem cell22_1102297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 5, 1, 3].length) (baseStart_1102297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1102297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1102297 prefixEnd_1102297 := by exact prefixLift 1102297
  have htrace : WordTrace (prefixWord ++ tailWord_1102297) baseStart_1102297 baseEnd_1102297 := by
    simpa [prefixWord, tailWord_1102297, baseEnd_1102297] using wordTrace_append hprefix tailTrace_1102297
  have hstable : (prefixWord ++ tailWord_1102297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102297).length < 2 ^ (prefixWord ++ tailWord_1102297).sum := by decide
  have hdescent : baseEnd_1102297 < baseStart_1102297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102314 : List Nat := [3, 1, 3, 1, 3, 2, 1, 4, 1, 3]
def baseStart_1102314 : Nat := 118140960795 + 1102314 * 2 ^ 59
def prefixEnd_1102314 : Nat := 4983230072969 + 3 ^ 40 * 1102314 * 2
def baseEnd_1102314 : Nat := 377344609453536950070371

theorem tailTrace_1102314 : CollatzResearch.WordTrace tailWord_1102314 prefixEnd_1102314 377344609453536950070371 := by
  unfold tailWord_1102314
  simp only [CollatzResearch.WordTrace]
  refine ⟨10051173632128028272036499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26803129685674742058763997 10051173632128028272036499)
  ·
    refine ⟨15076760448192042408054749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10051173632128028272036499 15076760448192042408054749)
    ·
      refine ⟨5653785168072015903020531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15076760448192042408054749 5653785168072015903020531)
      ·
        refine ⟨8480677752108023854530797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5653785168072015903020531 8480677752108023854530797)
        ·
          refine ⟨3180254157040508945449049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8480677752108023854530797 3180254157040508945449049)
          ·
            refine ⟨2385190617780381709086787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3180254157040508945449049 2385190617780381709086787)
            ·
              refine ⟨3577785926670572563630181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2385190617780381709086787 3577785926670572563630181)
              ·
                refine ⟨670834861250732355680659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3577785926670572563630181 670834861250732355680659)
                ·
                  refine ⟨1006252291876098533520989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 670834861250732355680659 1006252291876098533520989)
                  ·
                    refine ⟨377344609453536950070371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1006252291876098533520989 377344609453536950070371)
                    ·
                      rfl

theorem cell22_1102314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 4, 1, 3].length) (baseStart_1102314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1102314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1102314 prefixEnd_1102314 := by exact prefixLift 1102314
  have htrace : WordTrace (prefixWord ++ tailWord_1102314) baseStart_1102314 baseEnd_1102314 := by
    simpa [prefixWord, tailWord_1102314, baseEnd_1102314] using wordTrace_append hprefix tailTrace_1102314
  have hstable : (prefixWord ++ tailWord_1102314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102314).length < 2 ^ (prefixWord ++ tailWord_1102314).sum := by decide
  have hdescent : baseEnd_1102314 < baseStart_1102314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102323 : List Nat := [1, 1, 1, 2, 2, 2, 3, 1, 5, 4]
def baseStart_1102323 : Nat := 118140960795 + 1102323 * 2 ^ 59
def prefixEnd_1102323 : Nat := 4983230072969 + 3 ^ 40 * 1102323 * 2
def baseEnd_1102323 : Nat := 377347690337463926595343

theorem tailTrace_1102323 : CollatzResearch.WordTrace tailWord_1102323 prefixEnd_1102323 377347690337463926595343 := by
  unfold tailWord_1102323
  simp only [CollatzResearch.WordTrace]
  refine ⟨40205022785479507625223623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26803348523653005083482415 40205022785479507625223623)
  ·
    refine ⟨60307534178219261437835435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40205022785479507625223623 60307534178219261437835435)
    ·
      refine ⟨90461301267328892156753153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60307534178219261437835435 90461301267328892156753153)
      ·
        refine ⟨67845975950496669117564865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90461301267328892156753153 67845975950496669117564865)
        ·
          refine ⟨50884481962872501838173649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67845975950496669117564865 50884481962872501838173649)
          ·
            refine ⟨38163361472154376378630237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50884481962872501838173649 38163361472154376378630237)
            ·
              refine ⟨14311260552057891141986339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38163361472154376378630237 14311260552057891141986339)
              ·
                refine ⟨21466890828086836712979509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14311260552057891141986339 21466890828086836712979509)
                ·
                  refine ⟨2012521015133140941841829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21466890828086836712979509 2012521015133140941841829)
                  ·
                    refine ⟨377347690337463926595343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2012521015133140941841829 377347690337463926595343)
                    ·
                      rfl

theorem cell22_1102323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 5, 4].length) (baseStart_1102323 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1102323 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1102323 prefixEnd_1102323 := by exact prefixLift 1102323
  have htrace : WordTrace (prefixWord ++ tailWord_1102323) baseStart_1102323 baseEnd_1102323 := by
    simpa [prefixWord, tailWord_1102323, baseEnd_1102323] using wordTrace_append hprefix tailTrace_1102323
  have hstable : (prefixWord ++ tailWord_1102323).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102323).length < 2 ^ (prefixWord ++ tailWord_1102323).sum := by decide
  have hdescent : baseEnd_1102323 < baseStart_1102323 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102353 : List Nat := [1, 2, 2, 1, 1, 2, 2, 3, 3, 5]
def baseStart_1102353 : Nat := 118140960795 + 1102353 * 2 ^ 59
def prefixEnd_1102353 : Nat := 4983230072969 + 3 ^ 40 * 1102353 * 2
def baseEnd_1102353 : Nat := 377357959950553848345251

theorem tailTrace_1102353 : CollatzResearch.WordTrace tailWord_1102353 prefixEnd_1102353 377357959950553848345251 := by
  unfold tailWord_1102353
  simp only [CollatzResearch.WordTrace]
  refine ⟨40206116975370822748815713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26804077983580548499210475 40206116975370822748815713)
  ·
    refine ⟨30154587731528117061611785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40206116975370822748815713 30154587731528117061611785)
    ·
      refine ⟨22615940798646087796208839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30154587731528117061611785 22615940798646087796208839)
      ·
        refine ⟨33923911197969131694313259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22615940798646087796208839 33923911197969131694313259)
        ·
          refine ⟨50885866796953697541469889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33923911197969131694313259 50885866796953697541469889)
          ·
            refine ⟨38164400097715273156102417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50885866796953697541469889 38164400097715273156102417)
            ·
              refine ⟨28623300073286454867076813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38164400097715273156102417 28623300073286454867076813)
              ·
                refine ⟨10733737527482420575153805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28623300073286454867076813 10733737527482420575153805)
                ·
                  refine ⟨4025151572805907715682677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10733737527482420575153805 4025151572805907715682677)
                  ·
                    refine ⟨377357959950553848345251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4025151572805907715682677 377357959950553848345251)
                    ·
                      rfl

theorem cell22_1102353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 5].length) (baseStart_1102353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1102353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1102353 prefixEnd_1102353 := by exact prefixLift 1102353
  have htrace : WordTrace (prefixWord ++ tailWord_1102353) baseStart_1102353 baseEnd_1102353 := by
    simpa [prefixWord, tailWord_1102353, baseEnd_1102353] using wordTrace_append hprefix tailTrace_1102353
  have hstable : (prefixWord ++ tailWord_1102353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102353).length < 2 ^ (prefixWord ++ tailWord_1102353).sum := by decide
  have hdescent : baseEnd_1102353 < baseStart_1102353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102400 : List Nat := [2, 1, 1, 2, 2, 2, 6, 6]
def baseStart_1102400 : Nat := 118140960795 + 1102400 * 2 ^ 59
def prefixEnd_1102400 : Nat := 4983230072969 + 3 ^ 40 * 1102400 * 2
def baseEnd_1102400 : Nat := 41930449890117932491123

theorem tailTrace_1102400 : CollatzResearch.WordTrace tailWord_1102400 prefixEnd_1102400 41930449890117932491123 := by
  unfold tailWord_1102400
  simp only [CollatzResearch.WordTrace]
  refine ⟨20103915603100274887888327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26805220804133699850517769 20103915603100274887888327)
  ·
    refine ⟨30155873404650412331832491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20103915603100274887888327 30155873404650412331832491)
    ·
      refine ⟨45233810106975618497748737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30155873404650412331832491 45233810106975618497748737)
      ·
        refine ⟨33925357580231713873311553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45233810106975618497748737 33925357580231713873311553)
        ·
          refine ⟨25444018185173785404983665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33925357580231713873311553 25444018185173785404983665)
          ·
            refine ⟨19083013638880339053737749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25444018185173785404983665 19083013638880339053737749)
            ·
              refine ⟨894516264322515893143957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 19083013638880339053737749 894516264322515893143957)
              ·
                refine ⟨41930449890117932491123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 894516264322515893143957 41930449890117932491123)
                ·
                  rfl

theorem cell22_1102400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 6, 6].length) (baseStart_1102400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1102400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1102400 prefixEnd_1102400 := by exact prefixLift 1102400
  have htrace : WordTrace (prefixWord ++ tailWord_1102400) baseStart_1102400 baseEnd_1102400 := by
    simpa [prefixWord, tailWord_1102400, baseEnd_1102400] using wordTrace_append hprefix tailTrace_1102400
  have hstable : (prefixWord ++ tailWord_1102400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102400).length < 2 ^ (prefixWord ++ tailWord_1102400).sum := by decide
  have hdescent : baseEnd_1102400 < baseStart_1102400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102406 : List Nat := [6, 1, 1, 1, 2, 1, 3, 3, 4]
def baseStart_1102406 : Nat := 118140960795 + 1102406 * 2 ^ 59
def prefixEnd_1102406 : Nat := 4983230072969 + 3 ^ 40 * 1102406 * 2
def baseEnd_1102406 : Nat := 125792034311226458923363

theorem tailTrace_1102406 : CollatzResearch.WordTrace tailWord_1102406 prefixEnd_1102406 125792034311226458923363 := by
  unfold tailWord_1102406
  simp only [CollatzResearch.WordTrace]
  refine ⟨1256501563880587900015471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 26805366696119208533663381 1256501563880587900015471)
  ·
    refine ⟨1884752345820881850023207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1256501563880587900015471 1884752345820881850023207)
    ·
      refine ⟨2827128518731322775034811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1884752345820881850023207 2827128518731322775034811)
      ·
        refine ⟨4240692778096984162552217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2827128518731322775034811 4240692778096984162552217)
        ·
          refine ⟨3180519583572738121914163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4240692778096984162552217 3180519583572738121914163)
          ·
            refine ⟨4770779375359107182871245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3180519583572738121914163 4770779375359107182871245)
            ·
              refine ⟨1789042265759665193576717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4770779375359107182871245 1789042265759665193576717)
              ·
                refine ⟨670890849659874447591269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1789042265759665193576717 670890849659874447591269)
                ·
                  refine ⟨125792034311226458923363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 670890849659874447591269 125792034311226458923363)
                  ·
                    rfl

theorem cell22_1102406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_1102406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1102406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1102406 prefixEnd_1102406 := by exact prefixLift 1102406
  have htrace : WordTrace (prefixWord ++ tailWord_1102406) baseStart_1102406 baseEnd_1102406 := by
    simpa [prefixWord, tailWord_1102406, baseEnd_1102406] using wordTrace_append hprefix tailTrace_1102406
  have hstable : (prefixWord ++ tailWord_1102406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102406).length < 2 ^ (prefixWord ++ tailWord_1102406).sum := by decide
  have hdescent : baseEnd_1102406 < baseStart_1102406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102415 : List Nat := [1, 1, 2, 1, 1, 2, 4, 2, 5, 3]
def baseStart_1102415 : Nat := 118140960795 + 1102415 * 2 ^ 59
def prefixEnd_1102415 : Nat := 4983230072969 + 3 ^ 40 * 1102415 * 2
def baseEnd_1102415 : Nat := 377379183817606353295061

theorem tailTrace_1102415 : CollatzResearch.WordTrace tailWord_1102415 prefixEnd_1102415 377379183817606353295061 := by
  unfold tailWord_1102415
  simp only [CollatzResearch.WordTrace]
  refine ⟨40208378301146207337572699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26805585534097471558381799 40208378301146207337572699)
  ·
    refine ⟨60312567451719311006359049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40208378301146207337572699 60312567451719311006359049)
    ·
      refine ⟨45234425588789483254769287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60312567451719311006359049 45234425588789483254769287)
      ·
        refine ⟨67851638383184224882153931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45234425588789483254769287 67851638383184224882153931)
        ·
          refine ⟨101777457574776337323230897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67851638383184224882153931 101777457574776337323230897)
          ·
            refine ⟨76333093181082252992423173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101777457574776337323230897 76333093181082252992423173)
            ·
              refine ⟨14312454971452922436079345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 76333093181082252992423173 14312454971452922436079345)
              ·
                refine ⟨10734341228589691827059509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14312454971452922436079345 10734341228589691827059509)
                ·
                  refine ⟨1006344490180283608786829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10734341228589691827059509 1006344490180283608786829)
                  ·
                    refine ⟨377379183817606353295061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1006344490180283608786829 377379183817606353295061)
                    ·
                      rfl

theorem cell22_1102415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 5, 3].length) (baseStart_1102415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1102415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1102415 prefixEnd_1102415 := by exact prefixLift 1102415
  have htrace : WordTrace (prefixWord ++ tailWord_1102415) baseStart_1102415 baseEnd_1102415 := by
    simpa [prefixWord, tailWord_1102415, baseEnd_1102415] using wordTrace_append hprefix tailTrace_1102415
  have hstable : (prefixWord ++ tailWord_1102415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102415).length < 2 ^ (prefixWord ++ tailWord_1102415).sum := by decide
  have hdescent : baseEnd_1102415 < baseStart_1102415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102432 : List Nat := [2, 1, 1, 3, 2, 1, 5, 1, 3, 3]
def baseStart_1102432 : Nat := 118140960795 + 1102432 * 2 ^ 59
def prefixEnd_1102432 : Nat := 4983230072969 + 3 ^ 40 * 1102432 * 2
def baseEnd_1102432 : Nat := 377385003265023975620009

theorem tailTrace_1102432 : CollatzResearch.WordTrace tailWord_1102432 prefixEnd_1102432 377385003265023975620009 := by
  unfold tailWord_1102432
  simp only [CollatzResearch.WordTrace]
  refine ⟨20104499171042309620470775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26805998894723079493961033 20104499171042309620470775)
  ·
    refine ⟨30156748756563464430706163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20104499171042309620470775 30156748756563464430706163)
    ·
      refine ⟨45235123134845196646059245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30156748756563464430706163 45235123134845196646059245)
      ·
        refine ⟨16963171175566948742272217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45235123134845196646059245 16963171175566948742272217)
        ·
          refine ⟨12722378381675211556704163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16963171175566948742272217 12722378381675211556704163)
          ·
            refine ⟨19083567572512817335056245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12722378381675211556704163 19083567572512817335056245)
            ·
              refine ⟨1789084459923076625161523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19083567572512817335056245 1789084459923076625161523)
              ·
                refine ⟨2683626689884614937742285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1789084459923076625161523 2683626689884614937742285)
                ·
                  refine ⟨1006360008706730601653357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2683626689884614937742285 1006360008706730601653357)
                  ·
                    refine ⟨377385003265023975620009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1006360008706730601653357 377385003265023975620009)
                    ·
                      rfl

theorem cell22_1102432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 1, 3, 3].length) (baseStart_1102432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1102432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1102432 prefixEnd_1102432 := by exact prefixLift 1102432
  have htrace : WordTrace (prefixWord ++ tailWord_1102432) baseStart_1102432 baseEnd_1102432 := by
    simpa [prefixWord, tailWord_1102432, baseEnd_1102432] using wordTrace_append hprefix tailTrace_1102432
  have hstable : (prefixWord ++ tailWord_1102432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102432).length < 2 ^ (prefixWord ++ tailWord_1102432).sum := by decide
  have hdescent : baseEnd_1102432 < baseStart_1102432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102434 : List Nat := [3, 3, 2, 3, 1, 1, 2, 7]
def baseStart_1102434 : Nat := 118140960795 + 1102434 * 2 ^ 59
def prefixEnd_1102434 : Nat := 4983230072969 + 3 ^ 40 * 1102434 * 2
def baseEnd_1102434 : Nat := 41931743100655181896667

theorem tailTrace_1102434 : CollatzResearch.WordTrace tailWord_1102434 prefixEnd_1102434 41931743100655181896667 := by
  unfold tailWord_1102434
  simp only [CollatzResearch.WordTrace]
  refine ⟨10052267822019343395628589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26806047525384915721676237 10052267822019343395628589)
  ·
    refine ⟨3769600433257253773360721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10052267822019343395628589 3769600433257253773360721)
    ·
      refine ⟨2827200324942940330020541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3769600433257253773360721 2827200324942940330020541)
      ·
        refine ⟨1060200121853602623757703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2827200324942940330020541 1060200121853602623757703)
        ·
          refine ⟨1590300182780403935636555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1060200121853602623757703 1590300182780403935636555)
          ·
            refine ⟨2385450274170605903454833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1590300182780403935636555 2385450274170605903454833)
            ·
              refine ⟨1789087705627954427591125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2385450274170605903454833 1789087705627954427591125)
              ·
                refine ⟨41931743100655181896667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1789087705627954427591125 41931743100655181896667)
                ·
                  rfl

theorem cell22_1102434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 7].length) (baseStart_1102434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1102434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1102434 prefixEnd_1102434 := by exact prefixLift 1102434
  have htrace : WordTrace (prefixWord ++ tailWord_1102434) baseStart_1102434 baseEnd_1102434 := by
    simpa [prefixWord, tailWord_1102434, baseEnd_1102434] using wordTrace_append hprefix tailTrace_1102434
  have hstable : (prefixWord ++ tailWord_1102434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102434).length < 2 ^ (prefixWord ++ tailWord_1102434).sum := by decide
  have hdescent : baseEnd_1102434 < baseStart_1102434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102492 : List Nat := [2, 2, 3, 2, 2, 1, 1, 2, 3, 4]
def baseStart_1102492 : Nat := 118140960795 + 1102492 * 2 ^ 59
def prefixEnd_1102492 : Nat := 4983230072969 + 3 ^ 40 * 1102492 * 2
def baseEnd_1102492 : Nat := 377405542491203819119825

theorem tailTrace_1102492 : CollatzResearch.WordTrace tailWord_1102492 prefixEnd_1102492 377405542491203819119825 := by
  unfold tailWord_1102492
  simp only [CollatzResearch.WordTrace]
  refine ⟨20105593360933624744062865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26807457814578166325417153 20105593360933624744062865)
  ·
    refine ⟨15079195020700218558047149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20105593360933624744062865 15079195020700218558047149)
    ·
      refine ⟨5654698132762581959267681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15079195020700218558047149 5654698132762581959267681)
      ·
        refine ⟨4241023599571936469450761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5654698132762581959267681 4241023599571936469450761)
        ·
          refine ⟨3180767699678952352088071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4241023599571936469450761 3180767699678952352088071)
          ·
            refine ⟨4771151549518428528132107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3180767699678952352088071 4771151549518428528132107)
            ·
              refine ⟨7156727324277642792198161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4771151549518428528132107 7156727324277642792198161)
              ·
                refine ⟨5367545493208232094148621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7156727324277642792198161 5367545493208232094148621)
                ·
                  refine ⟨2012829559953087035305733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5367545493208232094148621 2012829559953087035305733)
                  ·
                    refine ⟨377405542491203819119825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2012829559953087035305733 377405542491203819119825)
                    ·
                      rfl

theorem cell22_1102492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_1102492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1102492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1102492 prefixEnd_1102492 := by exact prefixLift 1102492
  have htrace : WordTrace (prefixWord ++ tailWord_1102492) baseStart_1102492 baseEnd_1102492 := by
    simpa [prefixWord, tailWord_1102492, baseEnd_1102492] using wordTrace_append hprefix tailTrace_1102492
  have hstable : (prefixWord ++ tailWord_1102492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102492).length < 2 ^ (prefixWord ++ tailWord_1102492).sum := by decide
  have hdescent : baseEnd_1102492 < baseStart_1102492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102505 : List Nat := [1, 2, 1, 1, 1, 1, 2, 7, 1, 5]
def baseStart_1102505 : Nat := 118140960795 + 1102505 * 2 ^ 59
def prefixEnd_1102505 : Nat := 4983230072969 + 3 ^ 40 * 1102505 * 2
def baseEnd_1102505 : Nat := 377409992656876118544785

theorem tailTrace_1102505 : CollatzResearch.WordTrace tailWord_1102505 prefixEnd_1102505 377409992656876118544785 := by
  unfold tailWord_1102505
  simp only [CollatzResearch.WordTrace]
  refine ⟨40211660870820152708348969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26807773913880101805565979 40211660870820152708348969)
  ·
    refine ⟨30158745653115114531261727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40211660870820152708348969 30158745653115114531261727)
    ·
      refine ⟨45238118479672671796892591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30158745653115114531261727 45238118479672671796892591)
      ·
        refine ⟨67857177719509007695338887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45238118479672671796892591 67857177719509007695338887)
        ·
          refine ⟨101785766579263511543008331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67857177719509007695338887 101785766579263511543008331)
          ·
            refine ⟨152678649868895267314512497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101785766579263511543008331 152678649868895267314512497)
            ·
              refine ⟨114508987401671450485884373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 152678649868895267314512497 114508987401671450485884373)
              ·
                refine ⟨2683804392226674620762915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 114508987401671450485884373 2683804392226674620762915)
                ·
                  refine ⟨4025706588340011931144373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2683804392226674620762915 4025706588340011931144373)
                  ·
                    refine ⟨377409992656876118544785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4025706588340011931144373 377409992656876118544785)
                    ·
                      rfl

theorem cell22_1102505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 7, 1, 5].length) (baseStart_1102505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1102505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1102505 prefixEnd_1102505 := by exact prefixLift 1102505
  have htrace : WordTrace (prefixWord ++ tailWord_1102505) baseStart_1102505 baseEnd_1102505 := by
    simpa [prefixWord, tailWord_1102505, baseEnd_1102505] using wordTrace_append hprefix tailTrace_1102505
  have hstable : (prefixWord ++ tailWord_1102505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102505).length < 2 ^ (prefixWord ++ tailWord_1102505).sum := by decide
  have hdescent : baseEnd_1102505 < baseStart_1102505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102522 : List Nat := [3, 1, 1, 1, 2, 3, 2, 2, 4, 3]
def baseStart_1102522 : Nat := 118140960795 + 1102522 * 2 ^ 59
def prefixEnd_1102522 : Nat := 4983230072969 + 3 ^ 40 * 1102522 * 2
def baseEnd_1102522 : Nat := 377415812104293740869733

theorem tailTrace_1102522 : CollatzResearch.WordTrace tailWord_1102522 prefixEnd_1102522 377415812104293740869733 := by
  unfold tailWord_1102522
  simp only [CollatzResearch.WordTrace]
  refine ⟨10053070227939641152929455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26808187274505709741145213 10053070227939641152929455)
  ·
    refine ⟨15079605341909461729394183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10053070227939641152929455 15079605341909461729394183)
    ·
      refine ⟨22619408012864192594091275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15079605341909461729394183 22619408012864192594091275)
      ·
        refine ⟨33929112019296288891136913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22619408012864192594091275 33929112019296288891136913)
        ·
          refine ⟨25446834014472216668352685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33929112019296288891136913 25446834014472216668352685)
          ·
            refine ⟨9542562755427081250632257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25446834014472216668352685 9542562755427081250632257)
            ·
              refine ⟨7156922066570310937974193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9542562755427081250632257 7156922066570310937974193)
              ·
                refine ⟨5367691549927733203480645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7156922066570310937974193 5367691549927733203480645)
                ·
                  refine ⟨1006442165611449975652621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5367691549927733203480645 1006442165611449975652621)
                  ·
                    refine ⟨377415812104293740869733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1006442165611449975652621 377415812104293740869733)
                    ·
                      rfl

theorem cell22_1102522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 2, 4, 3].length) (baseStart_1102522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1102522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1102522 prefixEnd_1102522 := by exact prefixLift 1102522
  have htrace : WordTrace (prefixWord ++ tailWord_1102522) baseStart_1102522 baseEnd_1102522 := by
    simpa [prefixWord, tailWord_1102522, baseEnd_1102522] using wordTrace_append hprefix tailTrace_1102522
  have hstable : (prefixWord ++ tailWord_1102522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102522).length < 2 ^ (prefixWord ++ tailWord_1102522).sum := by decide
  have hdescent : baseEnd_1102522 < baseStart_1102522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102524 : List Nat := [2, 2, 2, 3, 1, 1, 4, 3, 4]
def baseStart_1102524 : Nat := 118140960795 + 1102524 * 2 ^ 59
def prefixEnd_1102524 : Nat := 4983230072969 + 3 ^ 40 * 1102524 * 2
def baseEnd_1102524 : Nat := 125805498915055467439909

theorem tailTrace_1102524 : CollatzResearch.WordTrace tailWord_1102524 prefixEnd_1102524 125805498915055467439909 := by
  unfold tailWord_1102524
  simp only [CollatzResearch.WordTrace]
  refine ⟨20106176928875659476645313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26808235905167545968860417 20106176928875659476645313)
  ·
    refine ⟨15079632696656744607483985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20106176928875659476645313 15079632696656744607483985)
    ·
      refine ⟨11309724522492558455612989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15079632696656744607483985 11309724522492558455612989)
      ·
        refine ⟨4241146695934709420854871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11309724522492558455612989 4241146695934709420854871)
        ·
          refine ⟨6361720043902064131282307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4241146695934709420854871 6361720043902064131282307)
          ·
            refine ⟨9542580065853096196923461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6361720043902064131282307 9542580065853096196923461)
            ·
              refine ⟨1789233762347455536923149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9542580065853096196923461 1789233762347455536923149)
              ·
                refine ⟨670962660880295826346181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1789233762347455536923149 670962660880295826346181)
                ·
                  refine ⟨125805498915055467439909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 670962660880295826346181 125805498915055467439909)
                  ·
                    rfl

theorem cell22_1102524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 3, 4].length) (baseStart_1102524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1102524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1102524 prefixEnd_1102524 := by exact prefixLift 1102524
  have htrace : WordTrace (prefixWord ++ tailWord_1102524) baseStart_1102524 baseEnd_1102524 := by
    simpa [prefixWord, tailWord_1102524, baseEnd_1102524] using wordTrace_append hprefix tailTrace_1102524
  have hstable : (prefixWord ++ tailWord_1102524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102524).length < 2 ^ (prefixWord ++ tailWord_1102524).sum := by decide
  have hdescent : baseEnd_1102524 < baseStart_1102524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102541 : List Nat := [1, 6, 2, 1, 2, 1, 2, 1, 6]
def baseStart_1102541 : Nat := 118140960795 + 1102541 * 2 ^ 59
def prefixEnd_1102541 : Nat := 4983230072969 + 3 ^ 40 * 1102541 * 2
def baseEnd_1102541 : Nat := 125807438730861341548225

theorem tailTrace_1102541 : CollatzResearch.WordTrace tailWord_1102541 prefixEnd_1102541 125807438730861341548225 := by
  unfold tailWord_1102541
  simp only [CollatzResearch.WordTrace]
  refine ⟨40212973898689730856659477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26808649265793153904439651 40212973898689730856659477)
  ·
    refine ⟨1884983151501081133905913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 40212973898689730856659477 1884983151501081133905913)
    ·
      refine ⟨1413737363625810850429435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1884983151501081133905913 1413737363625810850429435)
      ·
        refine ⟨2120606045438716275644153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1413737363625810850429435 2120606045438716275644153)
        ·
          refine ⟨1590454534079037206733115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2120606045438716275644153 1590454534079037206733115)
          ·
            refine ⟨2385681801118555810099673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1590454534079037206733115 2385681801118555810099673)
            ·
              refine ⟨1789261350838916857574755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2385681801118555810099673 1789261350838916857574755)
              ·
                refine ⟨2683892026258375286362133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1789261350838916857574755 2683892026258375286362133)
                ·
                  refine ⟨125807438730861341548225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2683892026258375286362133 125807438730861341548225)
                  ·
                    rfl

theorem cell22_1102541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_1102541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1102541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1102541 prefixEnd_1102541 := by exact prefixLift 1102541
  have htrace : WordTrace (prefixWord ++ tailWord_1102541) baseStart_1102541 baseEnd_1102541 := by
    simpa [prefixWord, tailWord_1102541, baseEnd_1102541] using wordTrace_append hprefix tailTrace_1102541
  have hstable : (prefixWord ++ tailWord_1102541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102541).length < 2 ^ (prefixWord ++ tailWord_1102541).sum := by decide
  have hdescent : baseEnd_1102541 < baseStart_1102541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102556 : List Nat := [2, 2, 5, 1, 1, 3, 1, 1, 1, 5]
def baseStart_1102556 : Nat := 118140960795 + 1102556 * 2 ^ 59
def prefixEnd_1102556 : Nat := 4983230072969 + 3 ^ 40 * 1102556 * 2
def baseEnd_1102556 : Nat := 377427450999128985519629

theorem tailTrace_1102556 : CollatzResearch.WordTrace tailWord_1102556 prefixEnd_1102556 377427450999128985519629 := by
  unfold tailWord_1102556
  simp only [CollatzResearch.WordTrace]
  refine ⟨20106760496817694209227761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26809013995756925612303681 20106760496817694209227761)
  ·
    refine ⟨15080070372613270656920821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20106760496817694209227761 15080070372613270656920821)
    ·
      refine ⟨1413756597432494124086327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15080070372613270656920821 1413756597432494124086327)
      ·
        refine ⟨2120634896148741186129491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1413756597432494124086327 2120634896148741186129491)
        ·
          refine ⟨3180952344223111779194237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2120634896148741186129491 3180952344223111779194237)
          ·
            refine ⟨1192857129083666917197839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3180952344223111779194237 1192857129083666917197839)
            ·
              refine ⟨1789285693625500375796759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1192857129083666917197839 1789285693625500375796759)
              ·
                refine ⟨2683928540438250563695139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1789285693625500375796759 2683928540438250563695139)
                ·
                  refine ⟨4025892810657375845542709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2683928540438250563695139 4025892810657375845542709)
                  ·
                    refine ⟨377427450999128985519629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4025892810657375845542709 377427450999128985519629)
                    ·
                      rfl

theorem cell22_1102556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_1102556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1102556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1102556 prefixEnd_1102556 := by exact prefixLift 1102556
  have htrace : WordTrace (prefixWord ++ tailWord_1102556) baseStart_1102556 baseEnd_1102556 := by
    simpa [prefixWord, tailWord_1102556, baseEnd_1102556] using wordTrace_append hprefix tailTrace_1102556
  have hstable : (prefixWord ++ tailWord_1102556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102556).length < 2 ^ (prefixWord ++ tailWord_1102556).sum := by decide
  have hdescent : baseEnd_1102556 < baseStart_1102556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102659 : List Nat := [1, 1, 1, 3, 1, 4, 3, 4, 4]
def baseStart_1102659 : Nat := 118140960795 + 1102659 * 2 ^ 59
def prefixEnd_1102659 : Nat := 4983230072969 + 3 ^ 40 * 1102659 * 2
def baseEnd_1102659 : Nat := 125820903334690350064771

theorem tailTrace_1102659 : CollatzResearch.WordTrace tailWord_1102659 prefixEnd_1102659 125820903334690350064771 := by
  unfold tailWord_1102659
  simp only [CollatzResearch.WordTrace]
  refine ⟨40217277712262237009455031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26811518474841491339636687 40217277712262237009455031)
  ·
    refine ⟨60325916568393355514182547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40217277712262237009455031 60325916568393355514182547)
    ·
      refine ⟨90488874852590033271273821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60325916568393355514182547 90488874852590033271273821)
      ·
        refine ⟨33933328069721262476727683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90488874852590033271273821 33933328069721262476727683)
        ·
          refine ⟨50899992104581893715091525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33933328069721262476727683 50899992104581893715091525)
          ·
            refine ⟨9543748519609105071579661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50899992104581893715091525 9543748519609105071579661)
            ·
              refine ⟨3578905694853414401842373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9543748519609105071579661 3578905694853414401842373)
              ·
                refine ⟨671044817785015200345445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3578905694853414401842373 671044817785015200345445)
                ·
                  refine ⟨125820903334690350064771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 671044817785015200345445 125820903334690350064771)
                  ·
                    rfl

theorem cell22_1102659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 4, 4].length) (baseStart_1102659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1102659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1102659 prefixEnd_1102659 := by exact prefixLift 1102659
  have htrace : WordTrace (prefixWord ++ tailWord_1102659) baseStart_1102659 baseEnd_1102659 := by
    simpa [prefixWord, tailWord_1102659, baseEnd_1102659] using wordTrace_append hprefix tailTrace_1102659
  have hstable : (prefixWord ++ tailWord_1102659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102659).length < 2 ^ (prefixWord ++ tailWord_1102659).sum := by decide
  have hdescent : baseEnd_1102659 < baseStart_1102659 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102672 : List Nat := [2, 1, 1, 1, 1, 4, 2, 2, 4, 4]
def baseStart_1102672 : Nat := 118140960795 + 1102672 * 2 ^ 59
def prefixEnd_1102672 : Nat := 4983230072969 + 3 ^ 40 * 1102672 * 2
def baseEnd_1102672 : Nat := 377467160169743349619273

theorem tailTrace_1102672 : CollatzResearch.WordTrace tailWord_1102672 prefixEnd_1102672 377467160169743349619273 := by
  unfold tailWord_1102672
  simp only [CollatzResearch.WordTrace]
  refine ⟨20108875930607570114839135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26811834574143426819785513 20108875930607570114839135)
  ·
    refine ⟨30163313895911355172258703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20108875930607570114839135 30163313895911355172258703)
    ·
      refine ⟨45244970843867032758388055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30163313895911355172258703 45244970843867032758388055)
      ·
        refine ⟨67867456265800549137582083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45244970843867032758388055 67867456265800549137582083)
        ·
          refine ⟨101801184398700823706373125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67867456265800549137582083 101801184398700823706373125)
          ·
            refine ⟨19087722074756404444944961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 101801184398700823706373125 19087722074756404444944961)
            ·
              refine ⟨14315791556067303333708721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19087722074756404444944961 14315791556067303333708721)
              ·
                refine ⟨10736843667050477500281541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14315791556067303333708721 10736843667050477500281541)
                ·
                  refine ⟨2013158187571964531302789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10736843667050477500281541 2013158187571964531302789)
                  ·
                    refine ⟨377467160169743349619273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2013158187571964531302789 377467160169743349619273)
                    ·
                      rfl

theorem cell22_1102672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 4, 4].length) (baseStart_1102672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1102672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1102672 prefixEnd_1102672 := by exact prefixLift 1102672
  have htrace : WordTrace (prefixWord ++ tailWord_1102672) baseStart_1102672 baseEnd_1102672 := by
    simpa [prefixWord, tailWord_1102672, baseEnd_1102672] using wordTrace_append hprefix tailTrace_1102672
  have hstable : (prefixWord ++ tailWord_1102672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102672).length < 2 ^ (prefixWord ++ tailWord_1102672).sum := by decide
  have hdescent : baseEnd_1102672 < baseStart_1102672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102674 : List Nat := [3, 2, 2, 1, 1, 2, 4, 1, 1, 5]
def baseStart_1102674 : Nat := 118140960795 + 1102674 * 2 ^ 59
def prefixEnd_1102674 : Nat := 4983230072969 + 3 ^ 40 * 1102674 * 2
def baseEnd_1102674 : Nat := 377467844810616011069267

theorem tailTrace_1102674 : CollatzResearch.WordTrace tailWord_1102674 prefixEnd_1102674 377467844810616011069267 := by
  unfold tailWord_1102674
  simp only [CollatzResearch.WordTrace]
  refine ⟨10054456201801973642812769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26811883204805263047500717 10054456201801973642812769)
  ·
    refine ⟨7540842151351480232109577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10054456201801973642812769 7540842151351480232109577)
    ·
      refine ⟨5655631613513610174082183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7540842151351480232109577 5655631613513610174082183)
      ·
        refine ⟨8483447420270415261123275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5655631613513610174082183 8483447420270415261123275)
        ·
          refine ⟨12725171130405622891684913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8483447420270415261123275 12725171130405622891684913)
          ·
            refine ⟨9543878347804217168763685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12725171130405622891684913 9543878347804217168763685)
            ·
              refine ⟨1789477190213290719143191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9543878347804217168763685 1789477190213290719143191)
              ·
                refine ⟨2684215785319936078714787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1789477190213290719143191 2684215785319936078714787)
                ·
                  refine ⟨4026323677979904118072181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2684215785319936078714787 4026323677979904118072181)
                  ·
                    refine ⟨377467844810616011069267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4026323677979904118072181 377467844810616011069267)
                    ·
                      rfl

theorem cell22_1102674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_1102674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1102674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1102674 prefixEnd_1102674 := by exact prefixLift 1102674
  have htrace : WordTrace (prefixWord ++ tailWord_1102674) baseStart_1102674 baseEnd_1102674 := by
    simpa [prefixWord, tailWord_1102674, baseEnd_1102674] using wordTrace_append hprefix tailTrace_1102674
  have hstable : (prefixWord ++ tailWord_1102674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102674).length < 2 ^ (prefixWord ++ tailWord_1102674).sum := by decide
  have hdescent : baseEnd_1102674 < baseStart_1102674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102717 : List Nat := [1, 4, 1, 1, 2, 1, 2, 1, 1, 8]
def baseStart_1102717 : Nat := 118140960795 + 1102717 * 2 ^ 59
def prefixEnd_1102717 : Nat := 4983230072969 + 3 ^ 40 * 1102717 * 2
def baseEnd_1102717 : Nat := 377482564589378232244135

theorem tailTrace_1102717 : CollatzResearch.WordTrace tailWord_1102717 prefixEnd_1102717 377482564589378232244135 := by
  unfold tailWord_1102717
  simp only [CollatzResearch.WordTrace]
  refine ⟨40219393146052112915066405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26812928764034741943377603 40219393146052112915066405)
  ·
    refine ⟨7541136214884771171574951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40219393146052112915066405 7541136214884771171574951)
    ·
      refine ⟨11311704322327156757362427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7541136214884771171574951 11311704322327156757362427)
      ·
        refine ⟨16967556483490735136043641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11311704322327156757362427 16967556483490735136043641)
        ·
          refine ⟨12725667362618051352032731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16967556483490735136043641 12725667362618051352032731)
          ·
            refine ⟨19088501043927077028049097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12725667362618051352032731 19088501043927077028049097)
            ·
              refine ⟨14316375782945307771036823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19088501043927077028049097 14316375782945307771036823)
              ·
                refine ⟨21474563674417961656555235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14316375782945307771036823 21474563674417961656555235)
                ·
                  refine ⟨32211845511626942484832853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21474563674417961656555235 32211845511626942484832853)
                  ·
                    refine ⟨377482564589378232244135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 32211845511626942484832853 377482564589378232244135)
                    ·
                      rfl

theorem cell22_1102717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 8].length) (baseStart_1102717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1102717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1102717 prefixEnd_1102717 := by exact prefixLift 1102717
  have htrace : WordTrace (prefixWord ++ tailWord_1102717) baseStart_1102717 baseEnd_1102717 := by
    simpa [prefixWord, tailWord_1102717, baseEnd_1102717] using wordTrace_append hprefix tailTrace_1102717
  have hstable : (prefixWord ++ tailWord_1102717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102717).length < 2 ^ (prefixWord ++ tailWord_1102717).sum := by decide
  have hdescent : baseEnd_1102717 < baseStart_1102717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102719 : List Nat := [1, 1, 2, 2, 1, 1, 5, 3, 3, 3]
def baseStart_1102719 : Nat := 118140960795 + 1102719 * 2 ^ 59
def prefixEnd_1102719 : Nat := 4983230072969 + 3 ^ 40 * 1102719 * 2
def baseEnd_1102719 : Nat := 377483249230250893694129

theorem tailTrace_1102719 : CollatzResearch.WordTrace tailWord_1102719 prefixEnd_1102719 377483249230250893694129 := by
  unfold tailWord_1102719
  simp only [CollatzResearch.WordTrace]
  refine ⟨40219466092044867256639211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26812977394696578171092807 40219466092044867256639211)
  ·
    refine ⟨60329199138067300884958817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40219466092044867256639211 60329199138067300884958817)
    ·
      refine ⟨45246899353550475663719113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60329199138067300884958817 45246899353550475663719113)
      ·
        refine ⟨33935174515162856747789335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45246899353550475663719113 33935174515162856747789335)
        ·
          refine ⟨50902761772744285121684003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33935174515162856747789335 50902761772744285121684003)
          ·
            refine ⟨76354142659116427682526005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50902761772744285121684003 76354142659116427682526005)
            ·
              refine ⟨7158200874292165095236813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 76354142659116427682526005 7158200874292165095236813)
              ·
                refine ⟨2684325327859561910713805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7158200874292165095236813 2684325327859561910713805)
                ·
                  refine ⟨1006621997947335716517677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2684325327859561910713805 1006621997947335716517677)
                  ·
                    refine ⟨377483249230250893694129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1006621997947335716517677 377483249230250893694129)
                    ·
                      rfl

theorem cell22_1102719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 3, 3, 3].length) (baseStart_1102719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1102719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1102719 prefixEnd_1102719 := by exact prefixLift 1102719
  have htrace : WordTrace (prefixWord ++ tailWord_1102719) baseStart_1102719 baseEnd_1102719 := by
    simpa [prefixWord, tailWord_1102719, baseEnd_1102719] using wordTrace_append hprefix tailTrace_1102719
  have hstable : (prefixWord ++ tailWord_1102719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102719).length < 2 ^ (prefixWord ++ tailWord_1102719).sum := by decide
  have hdescent : baseEnd_1102719 < baseStart_1102719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102738 : List Nat := [3, 2, 3, 2, 2, 2, 2, 6]
def baseStart_1102738 : Nat := 118140960795 + 1102738 * 2 ^ 59
def prefixEnd_1102738 : Nat := 4983230072969 + 3 ^ 40 * 1102738 * 2
def baseEnd_1102738 : Nat := 41943305924282353052119

theorem tailTrace_1102738 : CollatzResearch.WordTrace tailWord_1102738 prefixEnd_1102738 41943305924282353052119 := by
  unfold tailWord_1102738
  simp only [CollatzResearch.WordTrace]
  refine ⟨10055039769744008375395217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26813439385984022334387245 10055039769744008375395217)
  ·
    refine ⟨7541279827308006281546413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10055039769744008375395217 7541279827308006281546413)
    ·
      refine ⟨2827979935240502355579905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7541279827308006281546413 2827979935240502355579905)
      ·
        refine ⟨2120984951430376766684929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2827979935240502355579905 2120984951430376766684929)
        ·
          refine ⟨1590738713572782575013697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2120984951430376766684929 1590738713572782575013697)
          ·
            refine ⟨1193054035179586931260273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1590738713572782575013697 1193054035179586931260273)
            ·
              refine ⟨894790526384690198445205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1193054035179586931260273 894790526384690198445205)
              ·
                refine ⟨41943305924282353052119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 894790526384690198445205 41943305924282353052119)
                ·
                  rfl

theorem cell22_1102738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 2, 6].length) (baseStart_1102738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1102738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1102738 prefixEnd_1102738 := by exact prefixLift 1102738
  have htrace : WordTrace (prefixWord ++ tailWord_1102738) baseStart_1102738 baseEnd_1102738 := by
    simpa [prefixWord, tailWord_1102738, baseEnd_1102738] using wordTrace_append hprefix tailTrace_1102738
  have hstable : (prefixWord ++ tailWord_1102738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102738).length < 2 ^ (prefixWord ++ tailWord_1102738).sum := by decide
  have hdescent : baseEnd_1102738 < baseStart_1102738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102809 : List Nat := [1, 2, 1, 2, 5, 1, 1, 1, 3, 5]
def baseStart_1102809 : Nat := 118140960795 + 1102809 * 2 ^ 59
def prefixEnd_1102809 : Nat := 4983230072969 + 3 ^ 40 * 1102809 * 2
def baseEnd_1102809 : Nat := 377514058069520658943853

theorem tailTrace_1102809 : CollatzResearch.WordTrace tailWord_1102809 prefixEnd_1102809 377514058069520658943853 := by
  unfold tailWord_1102809
  simp only [CollatzResearch.WordTrace]
  refine ⟨40222748661718812627415481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26815165774479208418276987 40222748661718812627415481)
  ·
    refine ⟨30167061496289109470561611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40222748661718812627415481 30167061496289109470561611)
    ·
      refine ⟨45250592244433664205842417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30167061496289109470561611 45250592244433664205842417)
      ·
        refine ⟨33937944183325248154381813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45250592244433664205842417 33937944183325248154381813)
        ·
          refine ⟨3181682267186742014473295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33937944183325248154381813 3181682267186742014473295)
          ·
            refine ⟨4772523400780113021709943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3181682267186742014473295 4772523400780113021709943)
            ·
              refine ⟨7158785101170169532564915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4772523400780113021709943 7158785101170169532564915)
              ·
                refine ⟨10738177651755254298847373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7158785101170169532564915 10738177651755254298847373)
                ·
                  refine ⟨4026816619408220362067765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10738177651755254298847373 4026816619408220362067765)
                  ·
                    refine ⟨377514058069520658943853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4026816619408220362067765 377514058069520658943853)
                    ·
                      rfl

theorem cell22_1102809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 3, 5].length) (baseStart_1102809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1102809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1102809 prefixEnd_1102809 := by exact prefixLift 1102809
  have htrace : WordTrace (prefixWord ++ tailWord_1102809) baseStart_1102809 baseEnd_1102809 := by
    simpa [prefixWord, tailWord_1102809, baseEnd_1102809] using wordTrace_append hprefix tailTrace_1102809
  have hstable : (prefixWord ++ tailWord_1102809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102809).length < 2 ^ (prefixWord ++ tailWord_1102809).sum := by decide
  have hdescent : baseEnd_1102809 < baseStart_1102809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102856 : List Nat := [2, 1, 3, 2, 1, 4, 3, 6]
def baseStart_1102856 : Nat := 118140960795 + 1102856 * 2 ^ 59
def prefixEnd_1102856 : Nat := 4983230072969 + 3 ^ 40 * 1102856 * 2
def baseEnd_1102856 : Nat := 41947794125558689224301

theorem tailTrace_1102856 : CollatzResearch.WordTrace tailWord_1102856 prefixEnd_1102856 41947794125558689224301 := by
  unfold tailWord_1102856
  simp only [CollatzResearch.WordTrace]
  refine ⟨20112231446274269827188211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26816308595032359769584281 20112231446274269827188211)
  ·
    refine ⟨30168347169411404740782317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20112231446274269827188211 30168347169411404740782317)
    ·
      refine ⟨11313130188529276777793369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30168347169411404740782317 11313130188529276777793369)
      ·
        refine ⟨8484847641396957583345027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11313130188529276777793369 8484847641396957583345027)
        ·
          refine ⟨12727271462095436375017541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8484847641396957583345027 12727271462095436375017541)
          ·
            refine ⟨2386363399142894320315789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12727271462095436375017541 2386363399142894320315789)
            ·
              refine ⟨894886274678585370118421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2386363399142894320315789 894886274678585370118421)
              ·
                refine ⟨41947794125558689224301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 894886274678585370118421 41947794125558689224301)
                ·
                  rfl

theorem cell22_1102856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 3, 6].length) (baseStart_1102856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1102856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1102856 prefixEnd_1102856 := by exact prefixLift 1102856
  have htrace : WordTrace (prefixWord ++ tailWord_1102856) baseStart_1102856 baseEnd_1102856 := by
    simpa [prefixWord, tailWord_1102856, baseEnd_1102856] using wordTrace_append hprefix tailTrace_1102856
  have hstable : (prefixWord ++ tailWord_1102856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102856).length < 2 ^ (prefixWord ++ tailWord_1102856).sum := by decide
  have hdescent : baseEnd_1102856 < baseStart_1102856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102858 : List Nat := [3, 1, 2, 2, 3, 3, 1, 1, 2, 4]
def baseStart_1102858 : Nat := 118140960795 + 1102858 * 2 ^ 59
def prefixEnd_1102858 : Nat := 4983230072969 + 3 ^ 40 * 1102858 * 2
def baseEnd_1102858 : Nat := 377530831770900864468703

theorem tailTrace_1102858 : CollatzResearch.WordTrace tailWord_1102858 prefixEnd_1102858 377530831770900864468703 := by
  unfold tailWord_1102858
  simp only [CollatzResearch.WordTrace]
  refine ⟨10056133959635323498987307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26816357225694195997299485 10056133959635323498987307)
  ·
    refine ⟨15084200939452985248480961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10056133959635323498987307 15084200939452985248480961)
    ·
      refine ⟨11313150704589738936360721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15084200939452985248480961 11313150704589738936360721)
      ·
        refine ⟨8484863028442304202270541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11313150704589738936360721 8484863028442304202270541)
        ·
          refine ⟨3181823635665864075851453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8484863028442304202270541 3181823635665864075851453)
          ·
            refine ⟨1193183863374699028444295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3181823635665864075851453 1193183863374699028444295)
            ·
              refine ⟨1789775795062048542666443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1193183863374699028444295 1789775795062048542666443)
              ·
                refine ⟨2684663692593072813999665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1789775795062048542666443 2684663692593072813999665)
                ·
                  refine ⟨2013497769444804610499749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2684663692593072813999665 2013497769444804610499749)
                  ·
                    refine ⟨377530831770900864468703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2013497769444804610499749 377530831770900864468703)
                    ·
                      rfl

theorem cell22_1102858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 1, 2, 4].length) (baseStart_1102858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1102858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1102858 prefixEnd_1102858 := by exact prefixLift 1102858
  have htrace : WordTrace (prefixWord ++ tailWord_1102858) baseStart_1102858 baseEnd_1102858 := by
    simpa [prefixWord, tailWord_1102858, baseEnd_1102858] using wordTrace_append hprefix tailTrace_1102858
  have hstable : (prefixWord ++ tailWord_1102858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102858).length < 2 ^ (prefixWord ++ tailWord_1102858).sum := by decide
  have hdescent : baseEnd_1102858 < baseStart_1102858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102877 : List Nat := [1, 4, 2, 2, 4, 1, 1, 2, 2, 3]
def baseStart_1102877 : Nat := 118140960795 + 1102877 * 2 ^ 59
def prefixEnd_1102877 : Nat := 4983230072969 + 3 ^ 40 * 1102877 * 2
def baseEnd_1102877 : Nat := 377537335859191148243645

theorem tailTrace_1102877 : CollatzResearch.WordTrace tailWord_1102877 prefixEnd_1102877 377537335859191148243645 := by
  unfold tailWord_1102877
  simp only [CollatzResearch.WordTrace]
  refine ⟨40225228825472460240890885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26816819216981640160593923 40225228825472460240890885)
  ·
    refine ⟨7542230404776086295167041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40225228825472460240890885 7542230404776086295167041)
    ·
      refine ⟨5656672803582064721375281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7542230404776086295167041 5656672803582064721375281)
      ·
        refine ⟨4242504602686548541031461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5656672803582064721375281 4242504602686548541031461)
        ·
          refine ⟨795469613003727851443399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4242504602686548541031461 795469613003727851443399)
          ·
            refine ⟨1193204419505591777165099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 795469613003727851443399 1193204419505591777165099)
            ·
              refine ⟨1789806629258387665747649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1193204419505591777165099 1789806629258387665747649)
              ·
                refine ⟨1342354971943790749310737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1789806629258387665747649 1342354971943790749310737)
                ·
                  refine ⟨1006766228957843061983053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1342354971943790749310737 1006766228957843061983053)
                  ·
                    refine ⟨377537335859191148243645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1006766228957843061983053 377537335859191148243645)
                    ·
                      rfl

theorem cell22_1102877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 2, 2, 3].length) (baseStart_1102877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1102877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1102877 prefixEnd_1102877 := by exact prefixLift 1102877
  have htrace : WordTrace (prefixWord ++ tailWord_1102877) baseStart_1102877 baseEnd_1102877 := by
    simpa [prefixWord, tailWord_1102877, baseEnd_1102877] using wordTrace_append hprefix tailTrace_1102877
  have hstable : (prefixWord ++ tailWord_1102877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102877).length < 2 ^ (prefixWord ++ tailWord_1102877).sum := by decide
  have hdescent : baseEnd_1102877 < baseStart_1102877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102918 : List Nat := [6, 1, 1, 1, 1, 2, 1, 2, 7]
def baseStart_1102918 : Nat := 118140960795 + 1102918 * 2 ^ 59
def prefixEnd_1102918 : Nat := 4983230072969 + 3 ^ 40 * 1102918 * 2
def baseEnd_1102918 : Nat := 125850456999026902656173

theorem tailTrace_1102918 : CollatzResearch.WordTrace tailWord_1102918 prefixEnd_1102918 125850456999026902656173 := by
  unfold tailWord_1102918
  simp only [CollatzResearch.WordTrace]
  refine ⟨1257085131822622632597919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 26817816145549282828755605 1257085131822622632597919)
  ·
    refine ⟨1885627697733933948896879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1257085131822622632597919 1885627697733933948896879)
    ·
      refine ⟨2828441546600900923345319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1885627697733933948896879 2828441546600900923345319)
      ·
        refine ⟨4242662319901351385017979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2828441546600900923345319 4242662319901351385017979)
        ·
          refine ⟨6363993479852027077526969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4242662319901351385017979 6363993479852027077526969)
          ·
            refine ⟨4772995109889020308145227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6363993479852027077526969 4772995109889020308145227)
            ·
              refine ⟨7159492664833530462217841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4772995109889020308145227 7159492664833530462217841)
              ·
                refine ⟨5369619498625147846663381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7159492664833530462217841 5369619498625147846663381)
                ·
                  refine ⟨125850456999026902656173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5369619498625147846663381 125850456999026902656173)
                  ·
                    rfl

theorem cell22_1102918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_1102918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1102918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1102918 prefixEnd_1102918 := by exact prefixLift 1102918
  have htrace : WordTrace (prefixWord ++ tailWord_1102918) baseStart_1102918 baseEnd_1102918 := by
    simpa [prefixWord, tailWord_1102918, baseEnd_1102918] using wordTrace_append hprefix tailTrace_1102918
  have hstable : (prefixWord ++ tailWord_1102918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102918).length < 2 ^ (prefixWord ++ tailWord_1102918).sum := by decide
  have hdescent : baseEnd_1102918 < baseStart_1102918 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102929 : List Nat := [1, 2, 2, 1, 3, 1, 2, 2, 8]
def baseStart_1102929 : Nat := 118140960795 + 1102929 * 2 ^ 59
def prefixEnd_1102929 : Nat := 4983230072969 + 3 ^ 40 * 1102929 * 2
def baseEnd_1102929 : Nat := 125851712173960115314495

theorem tailTrace_1102929 : CollatzResearch.WordTrace tailWord_1102929 prefixEnd_1102929 125851712173960115314495 := by
  unfold tailWord_1102929
  simp only [CollatzResearch.WordTrace]
  refine ⟨40227125421284073121783841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26818083614189382081189227 40227125421284073121783841)
  ·
    refine ⟨30170344065963054841337881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40227125421284073121783841 30170344065963054841337881)
    ·
      refine ⟨22627758049472291131003411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30170344065963054841337881 22627758049472291131003411)
      ·
        refine ⟨33941637074208436696505117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22627758049472291131003411 33941637074208436696505117)
        ·
          refine ⟨12728113902828163761189419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33941637074208436696505117 12728113902828163761189419)
          ·
            refine ⟨19092170854242245641784129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12728113902828163761189419 19092170854242245641784129)
            ·
              refine ⟨14319128140681684231338097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19092170854242245641784129 14319128140681684231338097)
              ·
                refine ⟨10739346105511263173503573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14319128140681684231338097 10739346105511263173503573)
                ·
                  refine ⟨125851712173960115314495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10739346105511263173503573 125851712173960115314495)
                  ·
                    rfl

theorem cell22_1102929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 8].length) (baseStart_1102929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1102929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1102929 prefixEnd_1102929 := by exact prefixLift 1102929
  have htrace : WordTrace (prefixWord ++ tailWord_1102929) baseStart_1102929 baseEnd_1102929 := by
    simpa [prefixWord, tailWord_1102929, baseEnd_1102929] using wordTrace_append hprefix tailTrace_1102929
  have hstable : (prefixWord ++ tailWord_1102929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102929).length < 2 ^ (prefixWord ++ tailWord_1102929).sum := by decide
  have hdescent : baseEnd_1102929 < baseStart_1102929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102952 : List Nat := [2, 1, 4, 4, 1, 2, 2, 1, 5]
def baseStart_1102952 : Nat := 118140960795 + 1102952 * 2 ^ 59
def prefixEnd_1102952 : Nat := 4983230072969 + 3 ^ 40 * 1102952 * 2
def baseEnd_1102952 : Nat := 125854336630638650872805

theorem tailTrace_1102952 : CollatzResearch.WordTrace tailWord_1102952 prefixEnd_1102952 125854336630638650872805 := by
  unfold tailWord_1102952
  simp only [CollatzResearch.WordTrace]
  refine ⟨20113982150100374024935555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26818642866800498699914073 20113982150100374024935555)
  ·
    refine ⟨30170973225150561037403333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20113982150100374024935555 30170973225150561037403333)
    ·
      refine ⟨5657057479715730194513125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30170973225150561037403333 5657057479715730194513125)
      ·
        refine ⟨1060698277446699411471211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5657057479715730194513125 1060698277446699411471211)
        ·
          refine ⟨1591047416170049117206817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1060698277446699411471211 1591047416170049117206817)
          ·
            refine ⟨1193285562127536837905113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1591047416170049117206817 1193285562127536837905113)
            ·
              refine ⟨894964171595652628428835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1193285562127536837905113 894964171595652628428835)
              ·
                refine ⟨1342446257393478942643253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 894964171595652628428835 1342446257393478942643253)
                ·
                  refine ⟨125854336630638650872805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1342446257393478942643253 125854336630638650872805)
                  ·
                    rfl

theorem cell22_1102952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 2, 1, 5].length) (baseStart_1102952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1102952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1102952 prefixEnd_1102952 := by exact prefixLift 1102952
  have htrace : WordTrace (prefixWord ++ tailWord_1102952) baseStart_1102952 baseEnd_1102952 := by
    simpa [prefixWord, tailWord_1102952, baseEnd_1102952] using wordTrace_append hprefix tailTrace_1102952
  have hstable : (prefixWord ++ tailWord_1102952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102952).length < 2 ^ (prefixWord ++ tailWord_1102952).sum := by decide
  have hdescent : baseEnd_1102952 < baseStart_1102952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102961 : List Nat := [1, 2, 2, 2, 1, 1, 2, 2, 6, 3]
def baseStart_1102961 : Nat := 118140960795 + 1102961 * 2 ^ 59
def prefixEnd_1102961 : Nat := 4983230072969 + 3 ^ 40 * 1102961 * 2
def baseEnd_1102961 : Nat := 377566090775842929143387

theorem tailTrace_1102961 : CollatzResearch.WordTrace tailWord_1102961 prefixEnd_1102961 377566090775842929143387 := by
  unfold tailWord_1102961
  simp only [CollatzResearch.WordTrace]
  refine ⟨40228292557168142586948737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26818861704778761724632491 40228292557168142586948737)
  ·
    refine ⟨30171219417876106940211553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40228292557168142586948737 30171219417876106940211553)
    ·
      refine ⟨22628414563407080205158665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30171219417876106940211553 22628414563407080205158665)
      ·
        refine ⟨16971310922555310153868999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22628414563407080205158665 16971310922555310153868999)
        ·
          refine ⟨25456966383832965230803499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16971310922555310153868999 25456966383832965230803499)
          ·
            refine ⟨38185449575749447846205249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25456966383832965230803499 38185449575749447846205249)
            ·
              refine ⟨28639087181812085884653937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38185449575749447846205249 28639087181812085884653937)
              ·
                refine ⟨21479315386359064413490453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28639087181812085884653937 21479315386359064413490453)
                ·
                  refine ⟨1006842908735581144382365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 21479315386359064413490453 1006842908735581144382365)
                  ·
                    refine ⟨377566090775842929143387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1006842908735581144382365 377566090775842929143387)
                    ·
                      rfl

theorem cell22_1102961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 6, 3].length) (baseStart_1102961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1102961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1102961 prefixEnd_1102961 := by exact prefixLift 1102961
  have htrace : WordTrace (prefixWord ++ tailWord_1102961) baseStart_1102961 baseEnd_1102961 := by
    simpa [prefixWord, tailWord_1102961, baseEnd_1102961] using wordTrace_append hprefix tailTrace_1102961
  have hstable : (prefixWord ++ tailWord_1102961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102961).length < 2 ^ (prefixWord ++ tailWord_1102961).sum := by decide
  have hdescent : baseEnd_1102961 < baseStart_1102961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102965 : List Nat := [1, 3, 4, 3, 1, 1, 1, 1, 3, 4]
def baseStart_1102965 : Nat := 118140960795 + 1102965 * 2 ^ 59
def prefixEnd_1102965 : Nat := 4983230072969 + 3 ^ 40 * 1102965 * 2
def baseEnd_1102965 : Nat := 377567460057588252043375

theorem tailTrace_1102965 : CollatzResearch.WordTrace tailWord_1102965 prefixEnd_1102965 377567460057588252043375 := by
  unfold tailWord_1102965
  simp only [CollatzResearch.WordTrace]
  refine ⟨40228438449153651270094349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26818958966102434180062899 40228438449153651270094349)
  ·
    refine ⟨15085664418432619226285381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40228438449153651270094349 15085664418432619226285381)
    ·
      refine ⟨2828562078456116104928509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15085664418432619226285381 2828562078456116104928509)
      ·
        refine ⟨1060710779421043539348191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2828562078456116104928509 1060710779421043539348191)
        ·
          refine ⟨1591066169131565309022287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1060710779421043539348191 1591066169131565309022287)
          ·
            refine ⟨2386599253697347963533431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1591066169131565309022287 2386599253697347963533431)
            ·
              refine ⟨3579898880546021945300147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2386599253697347963533431 3579898880546021945300147)
              ·
                refine ⟨5369848320819032917950221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3579898880546021945300147 5369848320819032917950221)
                ·
                  refine ⟨2013693120307137344231333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5369848320819032917950221 2013693120307137344231333)
                  ·
                    refine ⟨377567460057588252043375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2013693120307137344231333 377567460057588252043375)
                    ·
                      rfl

theorem cell22_1102965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_1102965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1102965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1102965 prefixEnd_1102965 := by exact prefixLift 1102965
  have htrace : WordTrace (prefixWord ++ tailWord_1102965) baseStart_1102965 baseEnd_1102965 := by
    simpa [prefixWord, tailWord_1102965, baseEnd_1102965] using wordTrace_append hprefix tailTrace_1102965
  have hstable : (prefixWord ++ tailWord_1102965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102965).length < 2 ^ (prefixWord ++ tailWord_1102965).sum := by decide
  have hdescent : baseEnd_1102965 < baseStart_1102965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102976 : List Nat := [2, 1, 1, 2, 1, 3, 3, 3, 2, 4]
def baseStart_1102976 : Nat := 118140960795 + 1102976 * 2 ^ 59
def prefixEnd_1102976 : Nat := 4983230072969 + 3 ^ 40 * 1102976 * 2
def baseEnd_1102976 : Nat := 377571225582387890018341

theorem tailTrace_1102976 : CollatzResearch.WordTrace tailWord_1102976 prefixEnd_1102976 377571225582387890018341 := by
  unfold tailWord_1102976
  simp only [CollatzResearch.WordTrace]
  refine ⟨20114419826056900074372391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26819226434742533432496521 20114419826056900074372391)
  ·
    refine ⟨30171629739085350111558587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20114419826056900074372391 30171629739085350111558587)
    ·
      refine ⟨45257444608628025167337881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30171629739085350111558587 45257444608628025167337881)
      ·
        refine ⟨33943083456471018875503411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45257444608628025167337881 33943083456471018875503411)
        ·
          refine ⟨50914625184706528313255117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33943083456471018875503411 50914625184706528313255117)
          ·
            refine ⟨19092984444264948117470669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50914625184706528313255117 19092984444264948117470669)
            ·
              refine ⟨7159869166599355544051501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19092984444264948117470669 7159869166599355544051501)
              ·
                refine ⟨2684950937474758329019313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7159869166599355544051501 2684950937474758329019313)
                ·
                  refine ⟨2013713203106068746764485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2684950937474758329019313 2013713203106068746764485)
                  ·
                    refine ⟨377571225582387890018341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2013713203106068746764485 377571225582387890018341)
                    ·
                      rfl

theorem cell22_1102976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 3, 2, 4].length) (baseStart_1102976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1102976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1102976 prefixEnd_1102976 := by exact prefixLift 1102976
  have htrace : WordTrace (prefixWord ++ tailWord_1102976) baseStart_1102976 baseEnd_1102976 := by
    simpa [prefixWord, tailWord_1102976, baseEnd_1102976] using wordTrace_append hprefix tailTrace_1102976
  have hstable : (prefixWord ++ tailWord_1102976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102976).length < 2 ^ (prefixWord ++ tailWord_1102976).sum := by decide
  have hdescent : baseEnd_1102976 < baseStart_1102976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103083 : List Nat := [1, 1, 1, 1, 2, 6, 1, 4, 1, 4]
def baseStart_1103083 : Nat := 118140960795 + 1103083 * 2 ^ 59
def prefixEnd_1103083 : Nat := 4983230072969 + 3 ^ 40 * 1103083 * 2
def baseEnd_1103083 : Nat := 377607853869075277593013

theorem tailTrace_1103083 : CollatzResearch.WordTrace tailWord_1103083 prefixEnd_1103083 377607853869075277593013 := by
  unfold tailWord_1103083
  simp only [CollatzResearch.WordTrace]
  refine ⟨40232742262726157422889903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26821828175150771615259935 40232742262726157422889903)
  ·
    refine ⟨60349113394089236134334855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40232742262726157422889903 60349113394089236134334855)
    ·
      refine ⟨90523670091133854201502283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60349113394089236134334855 90523670091133854201502283)
      ·
        refine ⟨135785505136700781302253425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90523670091133854201502283 135785505136700781302253425)
        ·
          refine ⟨101839128852525585976690069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135785505136700781302253425 101839128852525585976690069)
          ·
            refine ⟨4773709164962136842657347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 101839128852525585976690069 4773709164962136842657347)
            ·
              refine ⟨7160563747443205263986021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4773709164962136842657347 7160563747443205263986021)
              ·
                refine ⟨1342605702645600986997379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7160563747443205263986021 1342605702645600986997379)
                ·
                  refine ⟨2013908553968401480496069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1342605702645600986997379 2013908553968401480496069)
                  ·
                    refine ⟨377607853869075277593013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2013908553968401480496069 377607853869075277593013)
                    ·
                      rfl

theorem cell22_1103083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 4, 1, 4].length) (baseStart_1103083 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1103083 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1103083 prefixEnd_1103083 := by exact prefixLift 1103083
  have htrace : WordTrace (prefixWord ++ tailWord_1103083) baseStart_1103083 baseEnd_1103083 := by
    simpa [prefixWord, tailWord_1103083, baseEnd_1103083] using wordTrace_append hprefix tailTrace_1103083
  have hstable : (prefixWord ++ tailWord_1103083).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103083).length < 2 ^ (prefixWord ++ tailWord_1103083).sum := by decide
  have hdescent : baseEnd_1103083 < baseStart_1103083 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103113 : List Nat := [1, 2, 1, 1, 3, 3, 1, 3, 4, 3]
def baseStart_1103113 : Nat := 118140960795 + 1103113 * 2 ^ 59
def prefixEnd_1103113 : Nat := 4983230072969 + 3 ^ 40 * 1103113 * 2
def baseEnd_1103113 : Nat := 377618123482165199342921

theorem tailTrace_1103113 : CollatzResearch.WordTrace tailWord_1103113 prefixEnd_1103113 377618123482165199342921 := by
  unfold tailWord_1103113
  simp only [CollatzResearch.WordTrace]
  refine ⟨40233836452617472546481993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26822557635078315030987995 40233836452617472546481993)
  ·
    refine ⟨30175377339463104409861495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40233836452617472546481993 30175377339463104409861495)
    ·
      refine ⟨45263066009194656614792243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30175377339463104409861495 45263066009194656614792243)
      ·
        refine ⟨67894599013791984922188365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45263066009194656614792243 67894599013791984922188365)
        ·
          refine ⟨25460474630171994345820637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67894599013791984922188365 25460474630171994345820637)
          ·
            refine ⟨9547677986314497879682739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25460474630171994345820637 9547677986314497879682739)
            ·
              refine ⟨14321516979471746819524109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9547677986314497879682739 14321516979471746819524109)
              ·
                refine ⟨5370568867301905057321541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14321516979471746819524109 5370568867301905057321541)
                ·
                  refine ⟨1006981662619107198247789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5370568867301905057321541 1006981662619107198247789)
                  ·
                    refine ⟨377618123482165199342921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1006981662619107198247789 377618123482165199342921)
                    ·
                      rfl

theorem cell22_1103113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 3, 4, 3].length) (baseStart_1103113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1103113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1103113 prefixEnd_1103113 := by exact prefixLift 1103113
  have htrace : WordTrace (prefixWord ++ tailWord_1103113) baseStart_1103113 baseEnd_1103113 := by
    simpa [prefixWord, tailWord_1103113, baseEnd_1103113] using wordTrace_append hprefix tailTrace_1103113
  have hstable : (prefixWord ++ tailWord_1103113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103113).length < 2 ^ (prefixWord ++ tailWord_1103113).sum := by decide
  have hdescent : baseEnd_1103113 < baseStart_1103113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103252 : List Nat := [2, 4, 2, 1, 2, 1, 1, 4, 1, 4]
def baseStart_1103252 : Nat := 118140960795 + 1103252 * 2 ^ 59
def prefixEnd_1103252 : Nat := 4983230072969 + 3 ^ 40 * 1103252 * 2
def baseEnd_1103252 : Nat := 377665706022815170117495

theorem tailTrace_1103252 : CollatzResearch.WordTrace tailWord_1103252 prefixEnd_1103252 377665706022815170117495 := by
  unfold tailWord_1103252
  simp only [CollatzResearch.WordTrace]
  refine ⟨20119453099556949642896005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26825937466075932857194673 20119453099556949642896005)
  ·
    refine ⟨3772397456166928058043001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20119453099556949642896005 3772397456166928058043001)
    ·
      refine ⟨2829298092125196043532251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3772397456166928058043001 2829298092125196043532251)
      ·
        refine ⟨4243947138187794065298377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2829298092125196043532251 4243947138187794065298377)
        ·
          refine ⟨3182960353640845548973783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4243947138187794065298377 3182960353640845548973783)
          ·
            refine ⟨4774440530461268323460675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3182960353640845548973783 4774440530461268323460675)
            ·
              refine ⟨7161660795691902485191013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4774440530461268323460675 7161660795691902485191013)
              ·
                refine ⟨1342811399192231715973315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7161660795691902485191013 1342811399192231715973315)
                ·
                  refine ⟨2014217098788347573959973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1342811399192231715973315 2014217098788347573959973)
                  ·
                    refine ⟨377665706022815170117495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2014217098788347573959973 377665706022815170117495)
                    ·
                      rfl

theorem cell22_1103252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_1103252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1103252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1103252 prefixEnd_1103252 := by exact prefixLift 1103252
  have htrace : WordTrace (prefixWord ++ tailWord_1103252) baseStart_1103252 baseEnd_1103252 := by
    simpa [prefixWord, tailWord_1103252, baseEnd_1103252] using wordTrace_append hprefix tailTrace_1103252
  have hstable : (prefixWord ++ tailWord_1103252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103252).length < 2 ^ (prefixWord ++ tailWord_1103252).sum := by decide
  have hdescent : baseEnd_1103252 < baseStart_1103252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103344 : List Nat := [2, 1, 1, 1, 3, 5, 1, 4, 1, 3]
def baseStart_1103344 : Nat := 118140960795 + 1103344 * 2 ^ 59
def prefixEnd_1103344 : Nat := 4983230072969 + 3 ^ 40 * 1103344 * 2
def baseEnd_1103344 : Nat := 377697199502957596817213

theorem tailTrace_1103344 : CollatzResearch.WordTrace tailWord_1103344 prefixEnd_1103344 377697199502957596817213 := by
  unfold tailWord_1103344
  simp only [CollatzResearch.WordTrace]
  refine ⟨20121130857390299499070543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26828174476520399332094057 20121130857390299499070543)
  ·
    refine ⟨30181696286085449248605815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20121130857390299499070543 30181696286085449248605815)
    ·
      refine ⟨45272544429128173872908723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30181696286085449248605815 45272544429128173872908723)
      ·
        refine ⟨67908816643692260809363085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45272544429128173872908723 67908816643692260809363085)
        ·
          refine ⟨25465806241384597803511157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67908816643692260809363085 25465806241384597803511157)
          ·
            refine ⟨2387419335129806044079171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25465806241384597803511157 2387419335129806044079171)
            ·
              refine ⟨3581129002694709066118757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2387419335129806044079171 3581129002694709066118757)
              ·
                refine ⟨671461688005257949897267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3581129002694709066118757 671461688005257949897267)
                ·
                  refine ⟨1007192532007886924845901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 671461688005257949897267 1007192532007886924845901)
                  ·
                    refine ⟨377697199502957596817213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1007192532007886924845901 377697199502957596817213)
                    ·
                      rfl

theorem cell22_1103344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 4, 1, 3].length) (baseStart_1103344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1103344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1103344 prefixEnd_1103344 := by exact prefixLift 1103344
  have htrace : WordTrace (prefixWord ++ tailWord_1103344) baseStart_1103344 baseEnd_1103344 := by
    simpa [prefixWord, tailWord_1103344, baseEnd_1103344] using wordTrace_append hprefix tailTrace_1103344
  have hstable : (prefixWord ++ tailWord_1103344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103344).length < 2 ^ (prefixWord ++ tailWord_1103344).sum := by decide
  have hdescent : baseEnd_1103344 < baseStart_1103344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103402 : List Nat := [3, 1, 4, 1, 1, 1, 4, 1, 6]
def baseStart_1103402 : Nat := 118140960795 + 1103402 * 2 ^ 59
def prefixEnd_1103402 : Nat := 4983230072969 + 3 ^ 40 * 1103402 * 2
def baseEnd_1103402 : Nat := 125905684696088259622345

theorem tailTrace_1103402 : CollatzResearch.WordTrace tailWord_1103402 prefixEnd_1103402 125905684696088259622345 := by
  unfold tailWord_1103402
  simp only [CollatzResearch.WordTrace]
  refine ⟨10061094287142618725938115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26829584765713649935834973 10061094287142618725938115)
  ·
    refine ⟨15091641430713928088907173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10061094287142618725938115 15091641430713928088907173)
    ·
      refine ⟨2829682768258861516670095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15091641430713928088907173 2829682768258861516670095)
      ·
        refine ⟨4244524152388292275005143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2829682768258861516670095 4244524152388292275005143)
        ·
          refine ⟨6366786228582438412507715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4244524152388292275005143 6366786228582438412507715)
          ·
            refine ⟨9550179342873657618761573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6366786228582438412507715 9550179342873657618761573)
            ·
              refine ⟨1790658626788810803517795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9550179342873657618761573 1790658626788810803517795)
              ·
                refine ⟨2685987940183216205276693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1790658626788810803517795 2685987940183216205276693)
                ·
                  refine ⟨125905684696088259622345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2685987940183216205276693 125905684696088259622345)
                  ·
                    rfl

theorem cell22_1103402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 1, 6].length) (baseStart_1103402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1103402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1103402 prefixEnd_1103402 := by exact prefixLift 1103402
  have htrace : WordTrace (prefixWord ++ tailWord_1103402) baseStart_1103402 baseEnd_1103402 := by
    simpa [prefixWord, tailWord_1103402, baseEnd_1103402] using wordTrace_append hprefix tailTrace_1103402
  have hstable : (prefixWord ++ tailWord_1103402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103402).length < 2 ^ (prefixWord ++ tailWord_1103402).sum := by decide
  have hdescent : baseEnd_1103402 < baseStart_1103402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103415 : List Nat := [1, 1, 3, 1, 2, 4, 1, 2, 1, 6]
def baseStart_1103415 : Nat := 118140960795 + 1103415 * 2 ^ 59
def prefixEnd_1103415 : Nat := 4983230072969 + 3 ^ 40 * 1103415 * 2
def baseEnd_1103415 : Nat := 377721504253937078291995

theorem tailTrace_1103415 : CollatzResearch.WordTrace tailWord_1103415 prefixEnd_1103415 377721504253937078291995 := by
  unfold tailWord_1103415
  simp only [CollatzResearch.WordTrace]
  refine ⟨40244851297523378123975699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26829900865015585415983799 40244851297523378123975699)
  ·
    refine ⟨60367276946285067185963549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40244851297523378123975699 60367276946285067185963549)
    ·
      refine ⟨22637728854856900194736331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60367276946285067185963549 22637728854856900194736331)
      ·
        refine ⟨33956593282285350292104497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22637728854856900194736331 33956593282285350292104497)
        ·
          refine ⟨25467444961714012719078373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33956593282285350292104497 25467444961714012719078373)
          ·
            refine ⟨4775145930321377384827195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25467444961714012719078373 4775145930321377384827195)
            ·
              refine ⟨7162718895482066077240793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4775145930321377384827195 7162718895482066077240793)
              ·
                refine ⟨5372039171611549557930595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7162718895482066077240793 5372039171611549557930595)
                ·
                  refine ⟨8058058757417324336895893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5372039171611549557930595 8058058757417324336895893)
                  ·
                    refine ⟨377721504253937078291995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8058058757417324336895893 377721504253937078291995)
                    ·
                      rfl

theorem cell22_1103415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 2, 1, 6].length) (baseStart_1103415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1103415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1103415 prefixEnd_1103415 := by exact prefixLift 1103415
  have htrace : WordTrace (prefixWord ++ tailWord_1103415) baseStart_1103415 baseEnd_1103415 := by
    simpa [prefixWord, tailWord_1103415, baseEnd_1103415] using wordTrace_append hprefix tailTrace_1103415
  have hstable : (prefixWord ++ tailWord_1103415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103415).length < 2 ^ (prefixWord ++ tailWord_1103415).sum := by decide
  have hdescent : baseEnd_1103415 < baseStart_1103415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103417 : List Nat := [1, 2, 1, 5, 1, 2, 3, 1, 1, 5]
def baseStart_1103417 : Nat := 118140960795 + 1103417 * 2 ^ 59
def prefixEnd_1103417 : Nat := 4983230072969 + 3 ^ 40 * 1103417 * 2
def baseEnd_1103417 : Nat := 377722188894809739741989

theorem tailTrace_1103417 : CollatzResearch.WordTrace tailWord_1103417 prefixEnd_1103417 377722188894809739741989 := by
  unfold tailWord_1103417
  simp only [CollatzResearch.WordTrace]
  refine ⟨40244924243516132465548505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26829949495677421643699003 40244924243516132465548505)
  ·
    refine ⟨30183693182637099349161379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40244924243516132465548505 30183693182637099349161379)
    ·
      refine ⟨45275539773955649023742069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30183693182637099349161379 45275539773955649023742069)
      ·
        refine ⟨4244581853808342095975819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45275539773955649023742069 4244581853808342095975819)
        ·
          refine ⟨6366872780712513143963729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4244581853808342095975819 6366872780712513143963729)
          ·
            refine ⟨4775154585534384857972797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6366872780712513143963729 4775154585534384857972797)
            ·
              refine ⟨1790682969575394321739799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4775154585534384857972797 1790682969575394321739799)
              ·
                refine ⟨2686024454363091482609699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1790682969575394321739799 2686024454363091482609699)
                ·
                  refine ⟨4029036681544637223914549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2686024454363091482609699 4029036681544637223914549)
                  ·
                    refine ⟨377722188894809739741989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4029036681544637223914549 377722188894809739741989)
                    ·
                      rfl

theorem cell22_1103417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 1, 1, 5].length) (baseStart_1103417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1103417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1103417 prefixEnd_1103417 := by exact prefixLift 1103417
  have htrace : WordTrace (prefixWord ++ tailWord_1103417) baseStart_1103417 baseEnd_1103417 := by
    simpa [prefixWord, tailWord_1103417, baseEnd_1103417] using wordTrace_append hprefix tailTrace_1103417
  have hstable : (prefixWord ++ tailWord_1103417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103417).length < 2 ^ (prefixWord ++ tailWord_1103417).sum := by decide
  have hdescent : baseEnd_1103417 < baseStart_1103417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103453 : List Nat := [1, 4, 4, 2, 2, 1, 1, 1, 6]
def baseStart_1103453 : Nat := 118140960795 + 1103453 * 2 ^ 59
def prefixEnd_1103453 : Nat := 4983230072969 + 3 ^ 40 * 1103453 * 2
def baseEnd_1103453 : Nat := 125911504143505881947293

theorem tailTrace_1103453 : CollatzResearch.WordTrace tailWord_1103453 prefixEnd_1103453 125911504143505881947293 := by
  unfold tailWord_1103453
  simp only [CollatzResearch.WordTrace]
  refine ⟨40246237271385710613859013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26830824847590473742572675 40246237271385710613859013)
  ·
    refine ⟨7546169488384820740098565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40246237271385710613859013 7546169488384820740098565)
    ·
      refine ⟨1414906779072153888768481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7546169488384820740098565 1414906779072153888768481)
      ·
        refine ⟨1061180084304115416576361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1414906779072153888768481 1061180084304115416576361)
        ·
          refine ⟨795885063228086562432271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1061180084304115416576361 795885063228086562432271)
          ·
            refine ⟨1193827594842129843648407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 795885063228086562432271 1193827594842129843648407)
            ·
              refine ⟨1790741392263194765472611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1193827594842129843648407 1790741392263194765472611)
              ·
                refine ⟨2686112088394792148208917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1790741392263194765472611 2686112088394792148208917)
                ·
                  refine ⟨125911504143505881947293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2686112088394792148208917 125911504143505881947293)
                  ·
                    rfl

theorem cell22_1103453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 1, 6].length) (baseStart_1103453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1103453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1103453 prefixEnd_1103453 := by exact prefixLift 1103453
  have htrace : WordTrace (prefixWord ++ tailWord_1103453) baseStart_1103453 baseEnd_1103453 := by
    simpa [prefixWord, tailWord_1103453, baseEnd_1103453] using wordTrace_append hprefix tailTrace_1103453
  have hstable : (prefixWord ++ tailWord_1103453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103453).length < 2 ^ (prefixWord ++ tailWord_1103453).sum := by decide
  have hdescent : baseEnd_1103453 < baseStart_1103453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103552 : List Nat := [2, 1, 1, 2, 4, 1, 1, 4, 1, 5]
def baseStart_1103552 : Nat := 118140960795 + 1103552 * 2 ^ 59
def prefixEnd_1103552 : Nat := 4983230072969 + 3 ^ 40 * 1103552 * 2
def baseEnd_1103552 : Nat := 377768402153714387616575

theorem tailTrace_1103552 : CollatzResearch.WordTrace tailWord_1103552 prefixEnd_1103552 377768402153714387616575 := by
  unfold tailWord_1103552
  simp only [CollatzResearch.WordTrace]
  refine ⟨20124924049013525260856455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26833232065351367014475273 20124924049013525260856455)
  ·
    refine ⟨30187386073520287891284683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20124924049013525260856455 30187386073520287891284683)
    ·
      refine ⟨45281079110280431836927025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30187386073520287891284683 45281079110280431836927025)
      ·
        refine ⟨33960809332710323877695269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45281079110280431836927025 33960809332710323877695269)
        ·
          refine ⟨6367651749883185727067863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33960809332710323877695269 6367651749883185727067863)
          ·
            refine ⟨9551477624824778590601795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6367651749883185727067863 9551477624824778590601795)
            ·
              refine ⟨14327216437237167885902693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9551477624824778590601795 14327216437237167885902693)
              ·
                refine ⟨2686353081981968978606755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14327216437237167885902693 2686353081981968978606755)
                ·
                  refine ⟨4029529622972953467910133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2686353081981968978606755 4029529622972953467910133)
                  ·
                    refine ⟨377768402153714387616575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4029529622972953467910133 377768402153714387616575)
                    ·
                      rfl

theorem cell22_1103552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 4, 1, 5].length) (baseStart_1103552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1103552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1103552 prefixEnd_1103552 := by exact prefixLift 1103552
  have htrace : WordTrace (prefixWord ++ tailWord_1103552) baseStart_1103552 baseEnd_1103552 := by
    simpa [prefixWord, tailWord_1103552, baseEnd_1103552] using wordTrace_append hprefix tailTrace_1103552
  have hstable : (prefixWord ++ tailWord_1103552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103552).length < 2 ^ (prefixWord ++ tailWord_1103552).sum := by decide
  have hdescent : baseEnd_1103552 < baseStart_1103552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103567 : List Nat := [1, 1, 2, 1, 1, 3, 1, 6, 2, 4]
def baseStart_1103567 : Nat := 118140960795 + 1103567 * 2 ^ 59
def prefixEnd_1103567 : Nat := 4983230072969 + 3 ^ 40 * 1103567 * 2
def baseEnd_1103567 : Nat := 377773536960259348491529

theorem tailTrace_1103567 : CollatzResearch.WordTrace tailWord_1103567 prefixEnd_1103567 377773536960259348491529 := by
  unfold tailWord_1103567
  simp only [CollatzResearch.WordTrace]
  refine ⟨40250395192972708083508955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26833596795315138722339303 40250395192972708083508955)
  ·
    refine ⟨60375592789459062125263433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40250395192972708083508955 60375592789459062125263433)
    ·
      refine ⟨45281694592094296593947575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60375592789459062125263433 45281694592094296593947575)
      ·
        refine ⟨67922541888141444890921363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45281694592094296593947575 67922541888141444890921363)
        ·
          refine ⟨101883812832212167336382045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67922541888141444890921363 101883812832212167336382045)
          ·
            refine ⟨38206429812079562751143267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101883812832212167336382045 38206429812079562751143267)
            ·
              refine ⟨57309644718119344126714901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38206429812079562751143267 57309644718119344126714901)
              ·
                refine ⟨2686389596161844255939761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 57309644718119344126714901 2686389596161844255939761)
                ·
                  refine ⟨2014792197121383191954821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2686389596161844255939761 2014792197121383191954821)
                  ·
                    refine ⟨377773536960259348491529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2014792197121383191954821 377773536960259348491529)
                    ·
                      rfl

theorem cell22_1103567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 6, 2, 4].length) (baseStart_1103567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1103567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1103567 prefixEnd_1103567 := by exact prefixLift 1103567
  have htrace : WordTrace (prefixWord ++ tailWord_1103567) baseStart_1103567 baseEnd_1103567 := by
    simpa [prefixWord, tailWord_1103567, baseEnd_1103567] using wordTrace_append hprefix tailTrace_1103567
  have hstable : (prefixWord ++ tailWord_1103567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103567).length < 2 ^ (prefixWord ++ tailWord_1103567).sum := by decide
  have hdescent : baseEnd_1103567 < baseStart_1103567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103569 : List Nat := [1, 2, 2, 1, 2, 5, 1, 1, 4, 3]
def baseStart_1103569 : Nat := 118140960795 + 1103569 * 2 ^ 59
def prefixEnd_1103569 : Nat := 4983230072969 + 3 ^ 40 * 1103569 * 2
def baseEnd_1103569 : Nat := 377774221601132009941523

theorem tailTrace_1103569 : CollatzResearch.WordTrace tailWord_1103569 prefixEnd_1103569 377774221601132009941523 := by
  unfold tailWord_1103569
  simp only [CollatzResearch.WordTrace]
  refine ⟨40250468138965462425081761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26833645425976974950054507 40250468138965462425081761)
  ·
    refine ⟨30187851104224096818811321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40250468138965462425081761 30187851104224096818811321)
    ·
      refine ⟨22640888328168072614108491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30187851104224096818811321 22640888328168072614108491)
      ·
        refine ⟨33961332492252108921162737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22640888328168072614108491 33961332492252108921162737)
        ·
          refine ⟨25470999369189081690872053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33961332492252108921162737 25470999369189081690872053)
          ·
            refine ⟨2387906190861476408519255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25470999369189081690872053 2387906190861476408519255)
            ·
              refine ⟨3581859286292214612778883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2387906190861476408519255 3581859286292214612778883)
              ·
                refine ⟨5372788929438321919168325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3581859286292214612778883 5372788929438321919168325)
                ·
                  refine ⟨1007397924269685359844061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5372788929438321919168325 1007397924269685359844061)
                  ·
                    refine ⟨377774221601132009941523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1007397924269685359844061 377774221601132009941523)
                    ·
                      rfl

theorem cell22_1103569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 1, 4, 3].length) (baseStart_1103569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1103569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1103569 prefixEnd_1103569 := by exact prefixLift 1103569
  have htrace : WordTrace (prefixWord ++ tailWord_1103569) baseStart_1103569 baseEnd_1103569 := by
    simpa [prefixWord, tailWord_1103569, baseEnd_1103569] using wordTrace_append hprefix tailTrace_1103569
  have hstable : (prefixWord ++ tailWord_1103569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103569).length < 2 ^ (prefixWord ++ tailWord_1103569).sum := by decide
  have hdescent : baseEnd_1103569 < baseStart_1103569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103627 : List Nat := [1, 1, 1, 1, 5, 1, 4, 1, 7]
def baseStart_1103627 : Nat := 118140960795 + 1103627 * 2 ^ 59
def prefixEnd_1103627 : Nat := 4983230072969 + 3 ^ 40 * 1103627 * 2
def baseEnd_1103627 : Nat := 125931358728813063997115

theorem tailTrace_1103627 : CollatzResearch.WordTrace tailWord_1103627 prefixEnd_1103627 125931358728813063997115 := by
  unfold tailWord_1103627
  simp only [CollatzResearch.WordTrace]
  refine ⟨40252583572755338330693135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26835055715170225553795423 40252583572755338330693135)
  ·
    refine ⟨60378875359133007496039703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40252583572755338330693135 60378875359133007496039703)
    ·
      refine ⟨90568313038699511244059555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60378875359133007496039703 90568313038699511244059555)
      ·
        refine ⟨135852469558049266866089333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90568313038699511244059555 135852469558049266866089333)
        ·
          refine ⟨12736169021067118768695875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 135852469558049266866089333 12736169021067118768695875)
          ·
            refine ⟨19104253531600678153043813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12736169021067118768695875 19104253531600678153043813)
            ·
              refine ⟨3582047537175127153695715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19104253531600678153043813 3582047537175127153695715)
              ·
                refine ⟨5373071305762690730543573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3582047537175127153695715 5373071305762690730543573)
                ·
                  refine ⟨125931358728813063997115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5373071305762690730543573 125931358728813063997115)
                  ·
                    rfl

theorem cell22_1103627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 1, 7].length) (baseStart_1103627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1103627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1103627 prefixEnd_1103627 := by exact prefixLift 1103627
  have htrace : WordTrace (prefixWord ++ tailWord_1103627) baseStart_1103627 baseEnd_1103627 := by
    simpa [prefixWord, tailWord_1103627, baseEnd_1103627] using wordTrace_append hprefix tailTrace_1103627
  have hstable : (prefixWord ++ tailWord_1103627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103627).length < 2 ^ (prefixWord ++ tailWord_1103627).sum := by decide
  have hdescent : baseEnd_1103627 < baseStart_1103627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103644 : List Nat := [2, 2, 3, 1, 1, 2, 3, 3, 5]
def baseStart_1103644 : Nat := 118140960795 + 1103644 * 2 ^ 59
def prefixEnd_1103644 : Nat := 4983230072969 + 3 ^ 40 * 1103644 * 2
def baseEnd_1103644 : Nat := 125933298544618938105431

theorem tailTrace_1103644 : CollatzResearch.WordTrace tailWord_1103644 prefixEnd_1103644 125933298544618938105431 := by
  unfold tailWord_1103644
  simp only [CollatzResearch.WordTrace]
  refine ⟨20126601806846875117030993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26835469075795833489374657 20126601806846875117030993)
  ·
    refine ⟨15094951355135156337773245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20126601806846875117030993 15094951355135156337773245)
    ·
      refine ⟨5660606758175683626664967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15094951355135156337773245 5660606758175683626664967)
      ·
        refine ⟨8490910137263525439997451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5660606758175683626664967 8490910137263525439997451)
        ·
          refine ⟨12736365205895288159996177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8490910137263525439997451 12736365205895288159996177)
          ·
            refine ⟨9552273904421466119997133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12736365205895288159996177 9552273904421466119997133)
            ·
              refine ⟨3582102714158049794998925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9552273904421466119997133 3582102714158049794998925)
              ·
                refine ⟨1343288517809268673124597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3582102714158049794998925 1343288517809268673124597)
                ·
                  refine ⟨125933298544618938105431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1343288517809268673124597 125933298544618938105431)
                  ·
                    rfl

theorem cell22_1103644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 3, 5].length) (baseStart_1103644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1103644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1103644 prefixEnd_1103644 := by exact prefixLift 1103644
  have htrace : WordTrace (prefixWord ++ tailWord_1103644) baseStart_1103644 baseEnd_1103644 := by
    simpa [prefixWord, tailWord_1103644, baseEnd_1103644] using wordTrace_append hprefix tailTrace_1103644
  have hstable : (prefixWord ++ tailWord_1103644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103644).length < 2 ^ (prefixWord ++ tailWord_1103644).sum := by decide
  have hdescent : baseEnd_1103644 < baseStart_1103644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103704 : List Nat := [2, 1, 2, 2, 1, 1, 1, 1, 8, 3]
def baseStart_1103704 : Nat := 118140960795 + 1103704 * 2 ^ 59
def prefixEnd_1103704 : Nat := 4983230072969 + 3 ^ 40 * 1103704 * 2
def baseEnd_1103704 : Nat := 377820434860036657816109

theorem tailTrace_1103704 : CollatzResearch.WordTrace tailWord_1103704 prefixEnd_1103704 377820434860036657816109 := by
  unfold tailWord_1103704
  simp only [CollatzResearch.WordTrace]
  refine ⟨20127695996738190240623083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26836927995650920320830777 20127695996738190240623083)
  ·
    refine ⟨30191543995107285360934625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20127695996738190240623083 30191543995107285360934625)
    ·
      refine ⟨22643657996330464020700969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30191543995107285360934625 22643657996330464020700969)
      ·
        refine ⟨16982743497247848015525727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22643657996330464020700969 16982743497247848015525727)
        ·
          refine ⟨25474115245871772023288591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16982743497247848015525727 25474115245871772023288591)
          ·
            refine ⟨38211172868807658034932887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25474115245871772023288591 38211172868807658034932887)
            ·
              refine ⟨57316759303211487052399331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38211172868807658034932887 57316759303211487052399331)
              ·
                refine ⟨85975138954817230578598997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57316759303211487052399331 85975138954817230578598997)
                ·
                  refine ⟨1007521159626764420842957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 85975138954817230578598997 1007521159626764420842957)
                  ·
                    refine ⟨377820434860036657816109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1007521159626764420842957 377820434860036657816109)
                    ·
                      rfl

theorem cell22_1103704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 8, 3].length) (baseStart_1103704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1103704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1103704 prefixEnd_1103704 := by exact prefixLift 1103704
  have htrace : WordTrace (prefixWord ++ tailWord_1103704) baseStart_1103704 baseEnd_1103704 := by
    simpa [prefixWord, tailWord_1103704, baseEnd_1103704] using wordTrace_append hprefix tailTrace_1103704
  have hstable : (prefixWord ++ tailWord_1103704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103704).length < 2 ^ (prefixWord ++ tailWord_1103704).sum := by decide
  have hdescent : baseEnd_1103704 < baseStart_1103704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103719 : List Nat := [1, 1, 5, 1, 2, 1, 3, 1, 1, 6]
def baseStart_1103719 : Nat := 118140960795 + 1103719 * 2 ^ 59
def prefixEnd_1103719 : Nat := 4983230072969 + 3 ^ 40 * 1103719 * 2
def baseEnd_1103719 : Nat := 377825569666581618691063

theorem tailTrace_1103719 : CollatzResearch.WordTrace tailWord_1103719 prefixEnd_1103719 377825569666581618691063 := by
  unfold tailWord_1103719
  simp only [CollatzResearch.WordTrace]
  refine ⟨40255939088422038043042211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26837292725614692028694807 40255939088422038043042211)
  ·
    refine ⟨60383908632633057064563317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40255939088422038043042211 60383908632633057064563317)
    ·
      refine ⟨5660991434309349099802811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 60383908632633057064563317 5660991434309349099802811)
      ·
        refine ⟨8491487151464023649704217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5660991434309349099802811 8491487151464023649704217)
        ·
          refine ⟨6368615363598017737278163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8491487151464023649704217 6368615363598017737278163)
          ·
            refine ⟨9552923045397026605917245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6368615363598017737278163 9552923045397026605917245)
            ·
              refine ⟨3582346142023884977218967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9552923045397026605917245 3582346142023884977218967)
              ·
                refine ⟨5373519213035827465828451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3582346142023884977218967 5373519213035827465828451)
                ·
                  refine ⟨8060278819553741198742677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5373519213035827465828451 8060278819553741198742677)
                  ·
                    refine ⟨377825569666581618691063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8060278819553741198742677 377825569666581618691063)
                    ·
                      rfl

theorem cell22_1103719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_1103719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1103719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1103719 prefixEnd_1103719 := by exact prefixLift 1103719
  have htrace : WordTrace (prefixWord ++ tailWord_1103719) baseStart_1103719 baseEnd_1103719 := by
    simpa [prefixWord, tailWord_1103719, baseEnd_1103719] using wordTrace_append hprefix tailTrace_1103719
  have hstable : (prefixWord ++ tailWord_1103719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103719).length < 2 ^ (prefixWord ++ tailWord_1103719).sum := by decide
  have hdescent : baseEnd_1103719 < baseStart_1103719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103774 : List Nat := [4, 3, 1, 3, 2, 1, 1, 3, 4]
def baseStart_1103774 : Nat := 118140960795 + 1103774 * 2 ^ 59
def prefixEnd_1103774 : Nat := 4983230072969 + 3 ^ 40 * 1103774 * 2
def baseEnd_1103774 : Nat := 125948132430193269521965

theorem tailTrace_1103774 : CollatzResearch.WordTrace tailWord_1103774 prefixEnd_1103774 125948132430193269521965 := by
  unfold tailWord_1103774
  simp only [CollatzResearch.WordTrace]
  refine ⟨5032243137902847804536797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26838630068815188290862917 5032243137902847804536797)
  ·
    refine ⟨1887091176713567926701299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5032243137902847804536797 1887091176713567926701299)
    ·
      refine ⟨2830636765070351890051949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1887091176713567926701299 2830636765070351890051949)
      ·
        refine ⟨1061488786901381958769481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2830636765070351890051949 1061488786901381958769481)
        ·
          refine ⟨796116590176036469077111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1061488786901381958769481 796116590176036469077111)
          ·
            refine ⟨1194174885264054703615667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 796116590176036469077111 1194174885264054703615667)
            ·
              refine ⟨1791262327896082055423501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1194174885264054703615667 1791262327896082055423501)
              ·
                refine ⟨671723372961030770783813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1791262327896082055423501 671723372961030770783813)
                ·
                  refine ⟨125948132430193269521965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 671723372961030770783813 125948132430193269521965)
                  ·
                    rfl

theorem cell22_1103774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_1103774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1103774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1103774 prefixEnd_1103774 := by exact prefixLift 1103774
  have htrace : WordTrace (prefixWord ++ tailWord_1103774) baseStart_1103774 baseEnd_1103774 := by
    simpa [prefixWord, tailWord_1103774, baseEnd_1103774] using wordTrace_append hprefix tailTrace_1103774
  have hstable : (prefixWord ++ tailWord_1103774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103774).length < 2 ^ (prefixWord ++ tailWord_1103774).sum := by decide
  have hdescent : baseEnd_1103774 < baseStart_1103774 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103794 : List Nat := [3, 2, 1, 1, 1, 1, 1, 3, 4, 5]
def baseStart_1103794 : Nat := 118140960795 + 1103794 * 2 ^ 59
def prefixEnd_1103794 : Nat := 4983230072969 + 3 ^ 40 * 1103794 * 2
def baseEnd_1103794 : Nat := 377851243699306423065833

theorem tailTrace_1103794 : CollatzResearch.WordTrace tailWord_1103794 prefixEnd_1103794 377851243699306423065833 := by
  unfold tailWord_1103794
  simp only [CollatzResearch.WordTrace]
  refine ⟨10064668640787581463005609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26839116375433550568014957 10064668640787581463005609)
  ·
    refine ⟨7548501480590686097254207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10064668640787581463005609 7548501480590686097254207)
    ·
      refine ⟨11322752220886029145881311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7548501480590686097254207 11322752220886029145881311)
      ·
        refine ⟨16984128331329043718821967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11322752220886029145881311 16984128331329043718821967)
        ·
          refine ⟨25476192496993565578232951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16984128331329043718821967 25476192496993565578232951)
          ·
            refine ⟨38214288745490348367349427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25476192496993565578232951 38214288745490348367349427)
            ·
              refine ⟨57321433118235522551024141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38214288745490348367349427 57321433118235522551024141)
              ·
                refine ⟨21495537419338320956634053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57321433118235522551024141 21495537419338320956634053)
                ·
                  refine ⟨4030413266125935179368885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21495537419338320956634053 4030413266125935179368885)
                  ·
                    refine ⟨377851243699306423065833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4030413266125935179368885 377851243699306423065833)
                    ·
                      rfl

theorem cell22_1103794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 4, 5].length) (baseStart_1103794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1103794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1103794 prefixEnd_1103794 := by exact prefixLift 1103794
  have htrace : WordTrace (prefixWord ++ tailWord_1103794) baseStart_1103794 baseEnd_1103794 := by
    simpa [prefixWord, tailWord_1103794, baseEnd_1103794] using wordTrace_append hprefix tailTrace_1103794
  have hstable : (prefixWord ++ tailWord_1103794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103794).length < 2 ^ (prefixWord ++ tailWord_1103794).sum := by decide
  have hdescent : baseEnd_1103794 < baseStart_1103794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103800 : List Nat := [2, 1, 2, 1, 2, 3, 5, 2, 1, 3]
def baseStart_1103800 : Nat := 118140960795 + 1103800 * 2 ^ 59
def prefixEnd_1103800 : Nat := 4983230072969 + 3 ^ 40 * 1103800 * 2
def baseEnd_1103800 : Nat := 377853297621924407415815

theorem tailTrace_1103800 : CollatzResearch.WordTrace tailWord_1103800 prefixEnd_1103800 377853297621924407415815 := by
  unfold tailWord_1103800
  simp only [CollatzResearch.WordTrace]
  refine ⟨20129446700564294438370427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26839262267419059251160569 20129446700564294438370427)
  ·
    refine ⟨30194170050846441657555641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20129446700564294438370427 30194170050846441657555641)
    ·
      refine ⟨22645627538134831243166731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30194170050846441657555641 22645627538134831243166731)
      ·
        refine ⟨33968441307202246864750097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22645627538134831243166731 33968441307202246864750097)
        ·
          refine ⟨25476330980401685148562573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33968441307202246864750097 25476330980401685148562573)
          ·
            refine ⟨9553624117650631930710965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25476330980401685148562573 9553624117650631930710965)
            ·
              refine ⟨895652261029746743504153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9553624117650631930710965 895652261029746743504153)
              ·
                refine ⟨671739195772310057628115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 895652261029746743504153 671739195772310057628115)
                ·
                  refine ⟨1007608793658465086442173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 671739195772310057628115 1007608793658465086442173)
                  ·
                    refine ⟨377853297621924407415815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1007608793658465086442173 377853297621924407415815)
                    ·
                      rfl

theorem cell22_1103800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 5, 2, 1, 3].length) (baseStart_1103800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1103800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1103800 prefixEnd_1103800 := by exact prefixLift 1103800
  have htrace : WordTrace (prefixWord ++ tailWord_1103800) baseStart_1103800 baseEnd_1103800 := by
    simpa [prefixWord, tailWord_1103800, baseEnd_1103800] using wordTrace_append hprefix tailTrace_1103800
  have hstable : (prefixWord ++ tailWord_1103800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103800).length < 2 ^ (prefixWord ++ tailWord_1103800).sum := by decide
  have hdescent : baseEnd_1103800 < baseStart_1103800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103824 : List Nat := [2, 1, 1, 1, 1, 2, 4, 4, 6]
def baseStart_1103824 : Nat := 118140960795 + 1103824 * 2 ^ 59
def prefixEnd_1103824 : Nat := 4983230072969 + 3 ^ 40 * 1103824 * 2
def baseEnd_1103824 : Nat := 125953837770798781605247

theorem tailTrace_1103824 : CollatzResearch.WordTrace tailWord_1103824 prefixEnd_1103824 125953837770798781605247 := by
  unfold tailWord_1103824
  simp only [CollatzResearch.WordTrace]
  refine ⟨20129884376520820487807263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26839845835361093983743017 20129884376520820487807263)
  ·
    refine ⟨30194826564781230731710895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20129884376520820487807263 30194826564781230731710895)
    ·
      refine ⟨45292239847171846097566343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30194826564781230731710895 45292239847171846097566343)
      ·
        refine ⟨67938359770757769146349515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45292239847171846097566343 67938359770757769146349515)
        ·
          refine ⟨101907539656136653719524273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67938359770757769146349515 101907539656136653719524273)
          ·
            refine ⟨76430654742102490289643205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101907539656136653719524273 76430654742102490289643205)
            ·
              refine ⟨14330747764144216929308101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 76430654742102490289643205 14330747764144216929308101)
              ·
                refine ⟨2687015205777040674245269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14330747764144216929308101 2687015205777040674245269)
                ·
                  refine ⟨125953837770798781605247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2687015205777040674245269 125953837770798781605247)
                  ·
                    rfl

theorem cell22_1103824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 4, 6].length) (baseStart_1103824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1103824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1103824 prefixEnd_1103824 := by exact prefixLift 1103824
  have htrace : WordTrace (prefixWord ++ tailWord_1103824) baseStart_1103824 baseEnd_1103824 := by
    simpa [prefixWord, tailWord_1103824, baseEnd_1103824] using wordTrace_append hprefix tailTrace_1103824
  have hstable : (prefixWord ++ tailWord_1103824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103824).length < 2 ^ (prefixWord ++ tailWord_1103824).sum := by decide
  have hdescent : baseEnd_1103824 < baseStart_1103824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103856 : List Nat := [2, 1, 1, 1, 3, 2, 2, 3, 4, 3]
def baseStart_1103856 : Nat := 118140960795 + 1103856 * 2 ^ 59
def prefixEnd_1103856 : Nat := 4983230072969 + 3 ^ 40 * 1103856 * 2
def baseEnd_1103856 : Nat := 377872467566358928015643

theorem tailTrace_1103856 : CollatzResearch.WordTrace tailWord_1103856 prefixEnd_1103856 377872467566358928015643 := by
  unfold tailWord_1103856
  simp only [CollatzResearch.WordTrace]
  refine ⟨20130467944462855220389711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26840623925950473627186281 20130467944462855220389711)
  ·
    refine ⟨30195701916694282830584567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20130467944462855220389711 30195701916694282830584567)
    ·
      refine ⟨45293552875041424245876851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30195701916694282830584567 45293552875041424245876851)
      ·
        refine ⟨67940329312562136368815277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45293552875041424245876851 67940329312562136368815277)
        ·
          refine ⟨25477623492210801138305729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67940329312562136368815277 25477623492210801138305729)
          ·
            refine ⟨19108217619158100853729297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25477623492210801138305729 19108217619158100853729297)
            ·
              refine ⟨14331163214368575640296973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19108217619158100853729297 14331163214368575640296973)
              ·
                refine ⟨5374186205388215865111365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14331163214368575640296973 5374186205388215865111365)
                ·
                  refine ⟨1007659913510290474708381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5374186205388215865111365 1007659913510290474708381)
                  ·
                    refine ⟨377872467566358928015643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1007659913510290474708381 377872467566358928015643)
                    ·
                      rfl

theorem cell22_1103856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 3, 4, 3].length) (baseStart_1103856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1103856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1103856 prefixEnd_1103856 := by exact prefixLift 1103856
  have htrace : WordTrace (prefixWord ++ tailWord_1103856) baseStart_1103856 baseEnd_1103856 := by
    simpa [prefixWord, tailWord_1103856, baseEnd_1103856] using wordTrace_append hprefix tailTrace_1103856
  have hstable : (prefixWord ++ tailWord_1103856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103856).length < 2 ^ (prefixWord ++ tailWord_1103856).sum := by decide
  have hdescent : baseEnd_1103856 < baseStart_1103856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103873 : List Nat := [1, 2, 4, 1, 2, 1, 1, 5, 2, 3]
def baseStart_1103873 : Nat := 118140960795 + 1103873 * 2 ^ 59
def prefixEnd_1103873 : Nat := 4983230072969 + 3 ^ 40 * 1103873 * 2
def baseEnd_1103873 : Nat := 377878287013776550340591

theorem tailTrace_1103873 : CollatzResearch.WordTrace tailWord_1103873 prefixEnd_1103873 377878287013776550340591 := by
  unfold tailWord_1103873
  simp only [CollatzResearch.WordTrace]
  refine ⟨40261555929864122344148273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26841037286576081562765515 40261555929864122344148273)
  ·
    refine ⟨30196166947398091758111205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40261555929864122344148273 30196166947398091758111205)
    ·
      refine ⟨5661781302637142204645851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30196166947398091758111205 5661781302637142204645851)
      ·
        refine ⟨8492671953955713306968777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5661781302637142204645851 8492671953955713306968777)
        ·
          refine ⟨6369503965466784980226583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8492671953955713306968777 6369503965466784980226583)
          ·
            refine ⟨9554255948200177470339875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6369503965466784980226583 9554255948200177470339875)
            ·
              refine ⟨14331383922300266205509813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9554255948200177470339875 14331383922300266205509813)
              ·
                refine ⟨1343567242715649956766545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14331383922300266205509813 1343567242715649956766545)
                ·
                  refine ⟨1007675432036737467574909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1343567242715649956766545 1007675432036737467574909)
                  ·
                    refine ⟨377878287013776550340591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1007675432036737467574909 377878287013776550340591)
                    ·
                      rfl

theorem cell22_1103873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 5, 2, 3].length) (baseStart_1103873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1103873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1103873 prefixEnd_1103873 := by exact prefixLift 1103873
  have htrace : WordTrace (prefixWord ++ tailWord_1103873) baseStart_1103873 baseEnd_1103873 := by
    simpa [prefixWord, tailWord_1103873, baseEnd_1103873] using wordTrace_append hprefix tailTrace_1103873
  have hstable : (prefixWord ++ tailWord_1103873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103873).length < 2 ^ (prefixWord ++ tailWord_1103873).sum := by decide
  have hdescent : baseEnd_1103873 < baseStart_1103873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103899 : List Nat := [1, 1, 1, 1, 1, 1, 3, 4, 1, 8]
def baseStart_1103899 : Nat := 118140960795 + 1103899 * 2 ^ 59
def prefixEnd_1103899 : Nat := 4983230072969 + 3 ^ 40 * 1103899 * 2
def baseEnd_1103899 : Nat := 377887187345121149190511

theorem tailTrace_1103899 : CollatzResearch.WordTrace tailWord_1103899 prefixEnd_1103899 377887187345121149190511 := by
  unfold tailWord_1103899
  simp only [CollatzResearch.WordTrace]
  refine ⟨40262504227769928784594751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26841669485179952523063167 40262504227769928784594751)
  ·
    refine ⟨60393756341654893176892127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40262504227769928784594751 60393756341654893176892127)
    ·
      refine ⟨90590634512482339765338191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60393756341654893176892127 90590634512482339765338191)
      ·
        refine ⟨135885951768723509648007287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90590634512482339765338191 135885951768723509648007287)
        ·
          refine ⟨203828927653085264472010931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135885951768723509648007287 203828927653085264472010931)
          ·
            refine ⟨305743391479627896708016397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203828927653085264472010931 305743391479627896708016397)
            ·
              refine ⟨114653771804860461265506149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 305743391479627896708016397 114653771804860461265506149)
              ·
                refine ⟨21497582213411336487282403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 114653771804860461265506149 21497582213411336487282403)
                ·
                  refine ⟨32246373320117004730923605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21497582213411336487282403 32246373320117004730923605)
                  ·
                    refine ⟨377887187345121149190511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 32246373320117004730923605 377887187345121149190511)
                    ·
                      rfl

theorem cell22_1103899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 8].length) (baseStart_1103899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1103899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1103899 prefixEnd_1103899 := by exact prefixLift 1103899
  have htrace : WordTrace (prefixWord ++ tailWord_1103899) baseStart_1103899 baseEnd_1103899 := by
    simpa [prefixWord, tailWord_1103899, baseEnd_1103899] using wordTrace_append hprefix tailTrace_1103899
  have hstable : (prefixWord ++ tailWord_1103899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103899).length < 2 ^ (prefixWord ++ tailWord_1103899).sum := by decide
  have hdescent : baseEnd_1103899 < baseStart_1103899 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103924 : List Nat := [2, 5, 1, 2, 2, 1, 3, 1, 2, 3]
def baseStart_1103924 : Nat := 118140960795 + 1103924 * 2 ^ 59
def prefixEnd_1103924 : Nat := 4983230072969 + 3 ^ 40 * 1103924 * 2
def baseEnd_1103924 : Nat := 377895745356029417315435

theorem tailTrace_1103924 : CollatzResearch.WordTrace tailWord_1103924 prefixEnd_1103924 377895745356029417315435 := by
  unfold tailWord_1103924
  simp only [CollatzResearch.WordTrace]
  refine ⟨20131708026339679027127413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26842277368452905369503217 20131708026339679027127413)
  ·
    refine ⟨1887347627469344908793195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20131708026339679027127413 1887347627469344908793195)
    ·
      refine ⟨2831021441204017363189793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1887347627469344908793195 2831021441204017363189793)
      ·
        refine ⟨2123266080903013022392345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2831021441204017363189793 2123266080903013022392345)
        ·
          refine ⟨1592449560677259766794259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2123266080903013022392345 1592449560677259766794259)
          ·
            refine ⟨2388674341015889650191389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1592449560677259766794259 2388674341015889650191389)
            ·
              refine ⟨895752877880958618821771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2388674341015889650191389 895752877880958618821771)
              ·
                refine ⟨1343629316821437928232657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 895752877880958618821771 1343629316821437928232657)
                ·
                  refine ⟨1007721987616078446174493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1343629316821437928232657 1007721987616078446174493)
                  ·
                    refine ⟨377895745356029417315435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1007721987616078446174493 377895745356029417315435)
                    ·
                      rfl

theorem cell22_1103924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_1103924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1103924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1103924 prefixEnd_1103924 := by exact prefixLift 1103924
  have htrace : WordTrace (prefixWord ++ tailWord_1103924) baseStart_1103924 baseEnd_1103924 := by
    simpa [prefixWord, tailWord_1103924, baseEnd_1103924] using wordTrace_append hprefix tailTrace_1103924
  have hstable : (prefixWord ++ tailWord_1103924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103924).length < 2 ^ (prefixWord ++ tailWord_1103924).sum := by decide
  have hdescent : baseEnd_1103924 < baseStart_1103924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104008 : List Nat := [2, 1, 3, 4, 1, 1, 1, 1, 3, 5]
def baseStart_1104008 : Nat := 118140960795 + 1104008 * 2 ^ 59
def prefixEnd_1104008 : Nat := 4983230072969 + 3 ^ 40 * 1104008 * 2
def baseEnd_1104008 : Nat := 377924500272681198215177

theorem tailTrace_1104008 : CollatzResearch.WordTrace tailWord_1104008 prefixEnd_1104008 377924500272681198215177 := by
  unfold tailWord_1104008
  simp only [CollatzResearch.WordTrace]
  refine ⟨20133239892187520200156339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26844319856250026933541785 20133239892187520200156339)
  ·
    refine ⟨30199859838281280300234509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20133239892187520200156339 30199859838281280300234509)
    ·
      refine ⟨11324947439355480112587941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30199859838281280300234509 11324947439355480112587941)
      ·
        refine ⟨2123427644879152521110239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11324947439355480112587941 2123427644879152521110239)
        ·
          refine ⟨3185141467318728781665359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2123427644879152521110239 3185141467318728781665359)
          ·
            refine ⟨4777712200978093172498039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3185141467318728781665359 4777712200978093172498039)
            ·
              refine ⟨7166568301467139758747059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4777712200978093172498039 7166568301467139758747059)
              ·
                refine ⟨10749852452200709638120589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7166568301467139758747059 10749852452200709638120589)
                ·
                  refine ⟨4031194669575266114295221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10749852452200709638120589 4031194669575266114295221)
                  ·
                    refine ⟨377924500272681198215177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4031194669575266114295221 377924500272681198215177)
                    ·
                      rfl

theorem cell22_1104008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 3, 5].length) (baseStart_1104008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1104008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1104008 prefixEnd_1104008 := by exact prefixLift 1104008
  have htrace : WordTrace (prefixWord ++ tailWord_1104008) baseStart_1104008 baseEnd_1104008 := by
    simpa [prefixWord, tailWord_1104008, baseEnd_1104008] using wordTrace_append hprefix tailTrace_1104008
  have hstable : (prefixWord ++ tailWord_1104008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104008).length < 2 ^ (prefixWord ++ tailWord_1104008).sum := by decide
  have hdescent : baseEnd_1104008 < baseStart_1104008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104042 : List Nat := [3, 1, 5, 1, 2, 1, 2, 1, 1, 5]
def baseStart_1104042 : Nat := 118140960795 + 1104042 * 2 ^ 59
def prefixEnd_1104042 : Nat := 4983230072969 + 3 ^ 40 * 1104042 * 2
def baseEnd_1104042 : Nat := 377936139167516442865073

theorem tailTrace_1104042 : CollatzResearch.WordTrace tailWord_1104042 prefixEnd_1104042 377936139167516442865073 := by
  unfold tailWord_1104042
  simp only [CollatzResearch.WordTrace]
  refine ⟨10066929966562966051762595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26845146577501242804700253 10066929966562966051762595)
  ·
    refine ⟨15100394949844449077643893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10066929966562966051762595 15100394949844449077643893)
    ·
      refine ⟨1415662026547917101029115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15100394949844449077643893 1415662026547917101029115)
      ·
        refine ⟨2123493039821875651543673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1415662026547917101029115 2123493039821875651543673)
        ·
          refine ⟨1592619779866406738657755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2123493039821875651543673 1592619779866406738657755)
          ·
            refine ⟨2388929669799610107986633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1592619779866406738657755 2388929669799610107986633)
            ·
              refine ⟨1791697252349707580989975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2388929669799610107986633 1791697252349707580989975)
              ·
                refine ⟨2687545878524561371484963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1791697252349707580989975 2687545878524561371484963)
                ·
                  refine ⟨4031318817786842057227445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2687545878524561371484963 4031318817786842057227445)
                  ·
                    refine ⟨377936139167516442865073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4031318817786842057227445 377936139167516442865073)
                    ·
                      rfl

theorem cell22_1104042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_1104042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1104042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1104042 prefixEnd_1104042 := by exact prefixLift 1104042
  have htrace : WordTrace (prefixWord ++ tailWord_1104042) baseStart_1104042 baseEnd_1104042 := by
    simpa [prefixWord, tailWord_1104042, baseEnd_1104042] using wordTrace_append hprefix tailTrace_1104042
  have hstable : (prefixWord ++ tailWord_1104042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104042).length < 2 ^ (prefixWord ++ tailWord_1104042).sum := by decide
  have hdescent : baseEnd_1104042 < baseStart_1104042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104051 : List Nat := [1, 1, 1, 2, 3, 2, 1, 1, 4, 6]
def baseStart_1104051 : Nat := 118140960795 + 1104051 * 2 ^ 59
def prefixEnd_1104051 : Nat := 4983230072969 + 3 ^ 40 * 1104051 * 2
def baseEnd_1104051 : Nat := 377939220051443419390045

theorem tailTrace_1104051 : CollatzResearch.WordTrace tailWord_1104051 prefixEnd_1104051 377939220051443419390045 := by
  unfold tailWord_1104051
  simp only [CollatzResearch.WordTrace]
  refine ⟨40268048123219258744128007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26845365415479505829418671 40268048123219258744128007)
  ·
    refine ⟨60402072184828888116192011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40268048123219258744128007 60402072184828888116192011)
    ·
      refine ⟨90603108277243332174288017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60402072184828888116192011 90603108277243332174288017)
      ·
        refine ⟨67952331207932499130716013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90603108277243332174288017 67952331207932499130716013)
        ·
          refine ⟨25482124202974687174018505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67952331207932499130716013 25482124202974687174018505)
          ·
            refine ⟨19111593152231015380513879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25482124202974687174018505 19111593152231015380513879)
            ·
              refine ⟨28667389728346523070770819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19111593152231015380513879 28667389728346523070770819)
              ·
                refine ⟨43001084592519784606156229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28667389728346523070770819 43001084592519784606156229)
                ·
                  refine ⟨8062703361097459613654293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43001084592519784606156229 8062703361097459613654293)
                  ·
                    refine ⟨377939220051443419390045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8062703361097459613654293 377939220051443419390045)
                    ·
                      rfl

theorem cell22_1104051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 4, 6].length) (baseStart_1104051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1104051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1104051 prefixEnd_1104051 := by exact prefixLift 1104051
  have htrace : WordTrace (prefixWord ++ tailWord_1104051) baseStart_1104051 baseEnd_1104051 := by
    simpa [prefixWord, tailWord_1104051, baseEnd_1104051] using wordTrace_append hprefix tailTrace_1104051
  have hstable : (prefixWord ++ tailWord_1104051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104051).length < 2 ^ (prefixWord ++ tailWord_1104051).sum := by decide
  have hdescent : baseEnd_1104051 < baseStart_1104051 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104076 : List Nat := [2, 2, 1, 6, 2, 1, 1, 2, 2, 3]
def baseStart_1104076 : Nat := 118140960795 + 1104076 * 2 ^ 59
def prefixEnd_1104076 : Nat := 4983230072969 + 3 ^ 40 * 1104076 * 2
def baseEnd_1104076 : Nat := 377947778062351687514969

theorem tailTrace_1104076 : CollatzResearch.WordTrace tailWord_1104076 prefixEnd_1104076 377947778062351687514969 := by
  unfold tailWord_1104076
  simp only [CollatzResearch.WordTrace]
  refine ⟨20134479974064344006894041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26845973298752458675858721 20134479974064344006894041)
  ·
    refine ⟨15100859980548258005170531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20134479974064344006894041 15100859980548258005170531)
    ·
      refine ⟨22651289970822387007755797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15100859980548258005170531 22651289970822387007755797)
      ·
        refine ⟨1061779217382299390988553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 22651289970822387007755797 1061779217382299390988553)
        ·
          refine ⟨796334413036724543241415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1061779217382299390988553 796334413036724543241415)
          ·
            refine ⟨1194501619555086814862123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 796334413036724543241415 1194501619555086814862123)
            ·
              refine ⟨1791752429332630222293185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1194501619555086814862123 1791752429332630222293185)
              ·
                refine ⟨1343814321999472666719889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1791752429332630222293185 1343814321999472666719889)
                ·
                  refine ⟨1007860741499604500039917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1343814321999472666719889 1007860741499604500039917)
                  ·
                    refine ⟨377947778062351687514969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1007860741499604500039917 377947778062351687514969)
                    ·
                      rfl

theorem cell22_1104076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 2, 2, 3].length) (baseStart_1104076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1104076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1104076 prefixEnd_1104076 := by exact prefixLift 1104076
  have htrace : WordTrace (prefixWord ++ tailWord_1104076) baseStart_1104076 baseEnd_1104076 := by
    simpa [prefixWord, tailWord_1104076, baseEnd_1104076] using wordTrace_append hprefix tailTrace_1104076
  have hstable : (prefixWord ++ tailWord_1104076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104076).length < 2 ^ (prefixWord ++ tailWord_1104076).sum := by decide
  have hdescent : baseEnd_1104076 < baseStart_1104076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104113 : List Nat := [1, 2, 2, 2, 2, 1, 2, 3, 3, 4]
def baseStart_1104113 : Nat := 118140960795 + 1104113 * 2 ^ 59
def prefixEnd_1104113 : Nat := 4983230072969 + 3 ^ 40 * 1104113 * 2
def baseEnd_1104113 : Nat := 377960443918495924339855

theorem tailTrace_1104113 : CollatzResearch.WordTrace tailWord_1104113 prefixEnd_1104113 377960443918495924339855 := by
  unfold tailWord_1104113
  simp only [CollatzResearch.WordTrace]
  refine ⟨40270309448994643332884993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26846872965996428888589995 40270309448994643332884993)
  ·
    refine ⟨30202732086745982499663745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40270309448994643332884993 30202732086745982499663745)
    ·
      refine ⟨22652049065059486874747809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30202732086745982499663745 22652049065059486874747809)
      ·
        refine ⟨16989036798794615156060857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22652049065059486874747809 16989036798794615156060857)
        ·
          refine ⟨12741777599095961367045643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16989036798794615156060857 12741777599095961367045643)
          ·
            refine ⟨19112666398643942050568465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12741777599095961367045643 19112666398643942050568465)
            ·
              refine ⟨14334499798982956537926349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19112666398643942050568465 14334499798982956537926349)
              ·
                refine ⟨5375437424618608701722381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14334499798982956537926349 5375437424618608701722381)
                ·
                  refine ⟨2015789034231978263145893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5375437424618608701722381 2015789034231978263145893)
                  ·
                    refine ⟨377960443918495924339855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2015789034231978263145893 377960443918495924339855)
                    ·
                      rfl

theorem cell22_1104113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 3, 3, 4].length) (baseStart_1104113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1104113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1104113 prefixEnd_1104113 := by exact prefixLift 1104113
  have htrace : WordTrace (prefixWord ++ tailWord_1104113) baseStart_1104113 baseEnd_1104113 := by
    simpa [prefixWord, tailWord_1104113, baseEnd_1104113] using wordTrace_append hprefix tailTrace_1104113
  have hstable : (prefixWord ++ tailWord_1104113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104113).length < 2 ^ (prefixWord ++ tailWord_1104113).sum := by decide
  have hdescent : baseEnd_1104113 < baseStart_1104113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104145 : List Nat := [1, 2, 2, 1, 1, 7, 1, 1, 6]
def baseStart_1104145 : Nat := 118140960795 + 1104145 * 2 ^ 59
def prefixEnd_1104145 : Nat := 4983230072969 + 3 ^ 40 * 1104145 * 2
def baseEnd_1104145 : Nat := 125990466057486169179919

theorem tailTrace_1104145 : CollatzResearch.WordTrace tailWord_1104145 prefixEnd_1104145 125990466057486169179919 := by
  unfold tailWord_1104145
  simp only [CollatzResearch.WordTrace]
  refine ⟨40271476584878712798049889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26847651056585808532033259 40271476584878712798049889)
  ·
    refine ⟨30203607438659034598537417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40271476584878712798049889 30203607438659034598537417)
    ·
      refine ⟨22652705578994275948903063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30203607438659034598537417 22652705578994275948903063)
      ·
        refine ⟨33979058368491413923354595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22652705578994275948903063 33979058368491413923354595)
        ·
          refine ⟨50968587552737120885031893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33979058368491413923354595 50968587552737120885031893)
          ·
            refine ⟨1194576270767276270742935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 50968587552737120885031893 1194576270767276270742935)
            ·
              refine ⟨1791864406150914406114403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1194576270767276270742935 1791864406150914406114403)
              ·
                refine ⟨2687796609226371609171605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1791864406150914406114403 2687796609226371609171605)
                ·
                  refine ⟨125990466057486169179919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2687796609226371609171605 125990466057486169179919)
                  ·
                    rfl

theorem cell22_1104145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 1, 6].length) (baseStart_1104145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1104145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1104145 prefixEnd_1104145 := by exact prefixLift 1104145
  have htrace : WordTrace (prefixWord ++ tailWord_1104145) baseStart_1104145 baseEnd_1104145 := by
    simpa [prefixWord, tailWord_1104145, baseEnd_1104145] using wordTrace_append hprefix tailTrace_1104145
  have hstable : (prefixWord ++ tailWord_1104145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104145).length < 2 ^ (prefixWord ++ tailWord_1104145).sum := by decide
  have hdescent : baseEnd_1104145 < baseStart_1104145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104218 : List Nat := [3, 1, 1, 2, 1, 2, 1, 2, 9]
def baseStart_1104218 : Nat := 118140960795 + 1104218 * 2 ^ 59
def prefixEnd_1104218 : Nat := 4983230072969 + 3 ^ 40 * 1104218 * 2
def baseEnd_1104218 : Nat := 125998795854770216821511

theorem tailTrace_1104218 : CollatzResearch.WordTrace tailWord_1104218 prefixEnd_1104218 125998795854770216821511 := by
  unfold tailWord_1104218
  simp only [CollatzResearch.WordTrace]
  refine ⟨10068534778403561566364327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26849426075742830843638205 10068534778403561566364327)
  ·
    refine ⟨15102802167605342349546491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10068534778403561566364327 15102802167605342349546491)
    ·
      refine ⟨22654203251408013524319737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15102802167605342349546491 22654203251408013524319737)
      ·
        refine ⟨16990652438556010143239803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22654203251408013524319737 16990652438556010143239803)
        ·
          refine ⟨25485978657834015214859705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16990652438556010143239803 25485978657834015214859705)
          ·
            refine ⟨19114483993375511411144779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25485978657834015214859705 19114483993375511411144779)
            ·
              refine ⟨28671725990063267116717169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19114483993375511411144779 28671725990063267116717169)
              ·
                refine ⟨21503794492547450337537877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28671725990063267116717169 21503794492547450337537877)
                ·
                  refine ⟨125998795854770216821511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 21503794492547450337537877 125998795854770216821511)
                  ·
                    rfl

theorem cell22_1104218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 9].length) (baseStart_1104218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1104218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1104218 prefixEnd_1104218 := by exact prefixLift 1104218
  have htrace : WordTrace (prefixWord ++ tailWord_1104218) baseStart_1104218 baseEnd_1104218 := by
    simpa [prefixWord, tailWord_1104218, baseEnd_1104218] using wordTrace_append hprefix tailTrace_1104218
  have hstable : (prefixWord ++ tailWord_1104218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104218).length < 2 ^ (prefixWord ++ tailWord_1104218).sum := by decide
  have hdescent : baseEnd_1104218 < baseStart_1104218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104233 : List Nat := [1, 2, 1, 1, 1, 3, 3, 2, 1, 7]
def baseStart_1104233 : Nat := 118140960795 + 1104233 * 2 ^ 59
def prefixEnd_1104233 : Nat := 4983230072969 + 3 ^ 40 * 1104233 * 2
def baseEnd_1104233 : Nat := 378001522370855611339487

theorem tailTrace_1104233 : CollatzResearch.WordTrace tailWord_1104233 prefixEnd_1104233 378001522370855611339487 := by
  unfold tailWord_1104233
  simp only [CollatzResearch.WordTrace]
  refine ⟨40274686208559903827253353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26849790805706602551502235 40274686208559903827253353)
  ·
    refine ⟨30206014656419927870440015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40274686208559903827253353 30206014656419927870440015)
    ·
      refine ⟨45309021984629891805660023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30206014656419927870440015 45309021984629891805660023)
      ·
        refine ⟨67963532976944837708490035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45309021984629891805660023 67963532976944837708490035)
        ·
          refine ⟨101945299465417256562735053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67963532976944837708490035 101945299465417256562735053)
          ·
            refine ⟨38229487299531471211025645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101945299465417256562735053 38229487299531471211025645)
            ·
              refine ⟨14336057737324301704134617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38229487299531471211025645 14336057737324301704134617)
              ·
                refine ⟨10752043302993226278100963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14336057737324301704134617 10752043302993226278100963)
                ·
                  refine ⟨16128064954489839417151445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10752043302993226278100963 16128064954489839417151445)
                  ·
                    refine ⟨378001522370855611339487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16128064954489839417151445 378001522370855611339487)
                    ·
                      rfl

theorem cell22_1104233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 7].length) (baseStart_1104233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1104233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1104233 prefixEnd_1104233 := by exact prefixLift 1104233
  have htrace : WordTrace (prefixWord ++ tailWord_1104233) baseStart_1104233 baseEnd_1104233 := by
    simpa [prefixWord, tailWord_1104233, baseEnd_1104233] using wordTrace_append hprefix tailTrace_1104233
  have hstable : (prefixWord ++ tailWord_1104233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104233).length < 2 ^ (prefixWord ++ tailWord_1104233).sum := by decide
  have hdescent : baseEnd_1104233 < baseStart_1104233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104282 : List Nat := [3, 1, 1, 4, 1, 2, 1, 4, 1, 4]
def baseStart_1104282 : Nat := 118140960795 + 1104282 * 2 ^ 59
def prefixEnd_1104282 : Nat := 4983230072969 + 3 ^ 40 * 1104282 * 2
def baseEnd_1104282 : Nat := 378018296072235816864337

theorem tailTrace_1104282 : CollatzResearch.WordTrace tailWord_1104282 prefixEnd_1104282 378018296072235816864337 := by
  unfold tailWord_1104282
  simp only [CollatzResearch.WordTrace]
  refine ⟨10069118346345596298946775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26850982256921590130524733 10069118346345596298946775)
  ·
    refine ⟨15103677519518394448420163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10069118346345596298946775 15103677519518394448420163)
    ·
      refine ⟨22655516279277591672630245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15103677519518394448420163 22655516279277591672630245)
      ·
        refine ⟨4247909302364548438618171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22655516279277591672630245 4247909302364548438618171)
        ·
          refine ⟨6371863953546822657927257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4247909302364548438618171 6371863953546822657927257)
          ·
            refine ⟨4778897965160116993445443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6371863953546822657927257 4778897965160116993445443)
            ·
              refine ⟨7168346947740175490168165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4778897965160116993445443 7168346947740175490168165)
              ·
                refine ⟨1344065052701282904406531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7168346947740175490168165 1344065052701282904406531)
                ·
                  refine ⟨2016097579051924356609797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1344065052701282904406531 2016097579051924356609797)
                  ·
                    refine ⟨378018296072235816864337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2016097579051924356609797 378018296072235816864337)
                    ·
                      rfl

theorem cell22_1104282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 4, 1, 4].length) (baseStart_1104282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1104282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1104282 prefixEnd_1104282 := by exact prefixLift 1104282
  have htrace : WordTrace (prefixWord ++ tailWord_1104282) baseStart_1104282 baseEnd_1104282 := by
    simpa [prefixWord, tailWord_1104282, baseEnd_1104282] using wordTrace_append hprefix tailTrace_1104282
  have hstable : (prefixWord ++ tailWord_1104282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104282).length < 2 ^ (prefixWord ++ tailWord_1104282).sum := by decide
  have hdescent : baseEnd_1104282 < baseStart_1104282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104312 : List Nat := [2, 1, 2, 1, 2, 2, 1, 6, 2, 3]
def baseStart_1104312 : Nat := 118140960795 + 1104312 * 2 ^ 59
def prefixEnd_1104312 : Nat := 4983230072969 + 3 ^ 40 * 1104312 * 2
def baseEnd_1104312 : Nat := 378028565685325738614245

theorem tailTrace_1104312 : CollatzResearch.WordTrace tailWord_1104312 prefixEnd_1104312 378028565685325738614245 := by
  unfold tailWord_1104312
  simp only [CollatzResearch.WordTrace]
  refine ⟨20138783787636850159689595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26851711716849133546252793 20138783787636850159689595)
  ·
    refine ⟨30208175681455275239534393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20138783787636850159689595 30208175681455275239534393)
    ·
      refine ⟨22656131761091456429650795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30208175681455275239534393 22656131761091456429650795)
      ·
        refine ⟨33984197641637184644476193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22656131761091456429650795 33984197641637184644476193)
        ·
          refine ⟨25488148231227888483357145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33984197641637184644476193 25488148231227888483357145)
          ·
            refine ⟨19116111173420916362517859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25488148231227888483357145 19116111173420916362517859)
            ·
              refine ⟨28674166760131374543776789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19116111173420916362517859 28674166760131374543776789)
              ·
                refine ⟨1344101566881158181739537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 28674166760131374543776789 1344101566881158181739537)
                ·
                  refine ⟨1008076175160868636304653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1344101566881158181739537 1008076175160868636304653)
                  ·
                    refine ⟨378028565685325738614245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1008076175160868636304653 378028565685325738614245)
                    ·
                      rfl

theorem cell22_1104312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 6, 2, 3].length) (baseStart_1104312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1104312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1104312 prefixEnd_1104312 := by exact prefixLift 1104312
  have htrace : WordTrace (prefixWord ++ tailWord_1104312) baseStart_1104312 baseEnd_1104312 := by
    simpa [prefixWord, tailWord_1104312, baseEnd_1104312] using wordTrace_append hprefix tailTrace_1104312
  have hstable : (prefixWord ++ tailWord_1104312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104312).length < 2 ^ (prefixWord ++ tailWord_1104312).sum := by decide
  have hdescent : baseEnd_1104312 < baseStart_1104312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104329 : List Nat := [1, 2, 1, 1, 2, 1, 8, 1, 2, 3]
def baseStart_1104329 : Nat := 118140960795 + 1104329 * 2 ^ 59
def prefixEnd_1104329 : Nat := 4983230072969 + 3 ^ 40 * 1104329 * 2
def baseEnd_1104329 : Nat := 378034385132743360939193

theorem tailTrace_1104329 : CollatzResearch.WordTrace tailWord_1104329 prefixEnd_1104329 378034385132743360939193 := by
  unfold tailWord_1104329
  simp only [CollatzResearch.WordTrace]
  refine ⟨40278187616212112222748041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26852125077474741481832027 40278187616212112222748041)
  ·
    refine ⟨30208640712159084167061031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40278187616212112222748041 30208640712159084167061031)
    ·
      refine ⟨45312961068238626250591547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30208640712159084167061031 45312961068238626250591547)
      ·
        refine ⟨67969441602357939375887321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45312961068238626250591547 67969441602357939375887321)
        ·
          refine ⟨50977081201768454531915491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67969441602357939375887321 50977081201768454531915491)
          ·
            refine ⟨76465621802652681797873237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50977081201768454531915491 76465621802652681797873237)
            ·
              refine ⟨896081505499836114818827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 76465621802652681797873237 896081505499836114818827)
              ·
                refine ⟨1344122258249754172228241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 896081505499836114818827 1344122258249754172228241)
                ·
                  refine ⟨1008091693687315629171181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1344122258249754172228241 1008091693687315629171181)
                  ·
                    refine ⟨378034385132743360939193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1008091693687315629171181 378034385132743360939193)
                    ·
                      rfl

theorem cell22_1104329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 8, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 8, 1, 2, 3].length) (baseStart_1104329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1104329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1104329 prefixEnd_1104329 := by exact prefixLift 1104329
  have htrace : WordTrace (prefixWord ++ tailWord_1104329) baseStart_1104329 baseEnd_1104329 := by
    simpa [prefixWord, tailWord_1104329, baseEnd_1104329] using wordTrace_append hprefix tailTrace_1104329
  have hstable : (prefixWord ++ tailWord_1104329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104329).length < 2 ^ (prefixWord ++ tailWord_1104329).sum := by decide
  have hdescent : baseEnd_1104329 < baseStart_1104329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104342 : List Nat := [5, 2, 1, 1, 1, 1, 1, 10]
def baseStart_1104342 : Nat := 118140960795 + 1104342 * 2 ^ 59
def prefixEnd_1104342 : Nat := 4983230072969 + 3 ^ 40 * 1104342 * 2
def baseEnd_1104342 : Nat := 42004315033157295596017

theorem tailTrace_1104342 : CollatzResearch.WordTrace tailWord_1104342 prefixEnd_1104342 42004315033157295596017 := by
  unfold tailWord_1104342
  simp only [CollatzResearch.WordTrace]
  refine ⟨2517416360322813465185705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26852441176776676961980853 2517416360322813465185705)
  ·
    refine ⟨1888062270242110098889279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2517416360322813465185705 1888062270242110098889279)
    ·
      refine ⟨2832093405363165148333919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1888062270242110098889279 2832093405363165148333919)
      ·
        refine ⟨4248140108044747722500879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2832093405363165148333919 4248140108044747722500879)
        ·
          refine ⟨6372210162067121583751319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4248140108044747722500879 6372210162067121583751319)
          ·
            refine ⟨9558315243100682375626979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6372210162067121583751319 9558315243100682375626979)
            ·
              refine ⟨14337472864651023563440469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9558315243100682375626979 14337472864651023563440469)
              ·
                refine ⟨42004315033157295596017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 14337472864651023563440469 42004315033157295596017)
                ·
                  rfl

theorem cell22_1104342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 10].length) (baseStart_1104342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1104342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1104342 prefixEnd_1104342 := by exact prefixLift 1104342
  have htrace : WordTrace (prefixWord ++ tailWord_1104342) baseStart_1104342 baseEnd_1104342 := by
    simpa [prefixWord, tailWord_1104342, baseEnd_1104342] using wordTrace_append hprefix tailTrace_1104342
  have hstable : (prefixWord ++ tailWord_1104342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104342).length < 2 ^ (prefixWord ++ tailWord_1104342).sum := by decide
  have hdescent : baseEnd_1104342 < baseStart_1104342 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104374 : List Nat := [5, 1, 1, 1, 2, 1, 2, 3, 3, 3]
def baseStart_1104374 : Nat := 118140960795 + 1104374 * 2 ^ 59
def prefixEnd_1104374 : Nat := 4983230072969 + 3 ^ 40 * 1104374 * 2
def baseEnd_1104374 : Nat := 378049789552378243564055

theorem tailTrace_1104374 : CollatzResearch.WordTrace tailWord_1104374 prefixEnd_1104374 378049789552378243564055 := by
  unfold tailWord_1104374
  simp only [CollatzResearch.WordTrace]
  refine ⟨2517489306315567806758511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26853219267366056605424117 2517489306315567806758511)
  ·
    refine ⟨3776233959473351710137767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2517489306315567806758511 3776233959473351710137767)
    ·
      refine ⟨5664350939210027565206651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3776233959473351710137767 5664350939210027565206651)
      ·
        refine ⟨8496526408815041347809977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5664350939210027565206651 8496526408815041347809977)
        ·
          refine ⟨6372394806611281010857483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8496526408815041347809977 6372394806611281010857483)
          ·
            refine ⟨9558592209916921516286225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6372394806611281010857483 9558592209916921516286225)
            ·
              refine ⟨7168944157437691137214669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9558592209916921516286225 7168944157437691137214669)
              ·
                refine ⟨2688354059039134176455501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7168944157437691137214669 2688354059039134176455501)
                ·
                  refine ⟨1008132772139675316170813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2688354059039134176455501 1008132772139675316170813)
                  ·
                    refine ⟨378049789552378243564055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1008132772139675316170813 378049789552378243564055)
                    ·
                      rfl

theorem cell22_1104374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 3, 3, 3].length) (baseStart_1104374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1104374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1104374 prefixEnd_1104374 := by exact prefixLift 1104374
  have htrace : WordTrace (prefixWord ++ tailWord_1104374) baseStart_1104374 baseEnd_1104374 := by
    simpa [prefixWord, tailWord_1104374, baseEnd_1104374] using wordTrace_append hprefix tailTrace_1104374
  have hstable : (prefixWord ++ tailWord_1104374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104374).length < 2 ^ (prefixWord ++ tailWord_1104374).sum := by decide
  have hdescent : baseEnd_1104374 < baseStart_1104374 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104415 : List Nat := [1, 1, 2, 4, 1, 1, 1, 1, 10]
def baseStart_1104415 : Nat := 118140960795 + 1104415 * 2 ^ 59
def prefixEnd_1104415 : Nat := 4983230072969 + 3 ^ 40 * 1104415 * 2
def baseEnd_1104415 : Nat := 126021274896755934429643

theorem tailTrace_1104415 : CollatzResearch.WordTrace tailWord_1104415 prefixEnd_1104415 126021274896755934429643 := by
  unfold tailWord_1104415
  simp only [CollatzResearch.WordTrace]
  refine ⟨40281324293900548910378699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26854216195933699273585799 40281324293900548910378699)
  ·
    refine ⟨60421986440850823365568049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40281324293900548910378699 60421986440850823365568049)
    ·
      refine ⟨45316489830638117524176037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60421986440850823365568049 45316489830638117524176037)
      ·
        refine ⟨8496841843244647035783007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45316489830638117524176037 8496841843244647035783007)
        ·
          refine ⟨12745262764866970553674511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8496841843244647035783007 12745262764866970553674511)
          ·
            refine ⟨19117894147300455830511767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12745262764866970553674511 19117894147300455830511767)
            ·
              refine ⟨28676841220950683745767651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19117894147300455830511767 28676841220950683745767651)
              ·
                refine ⟨43015261831426025618651477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28676841220950683745767651 43015261831426025618651477)
                ·
                  refine ⟨126021274896755934429643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 43015261831426025618651477 126021274896755934429643)
                  ·
                    rfl

theorem cell22_1104415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 10].length) (baseStart_1104415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1104415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1104415 prefixEnd_1104415 := by exact prefixLift 1104415
  have htrace : WordTrace (prefixWord ++ tailWord_1104415) baseStart_1104415 baseEnd_1104415 := by
    simpa [prefixWord, tailWord_1104415, baseEnd_1104415] using wordTrace_append hprefix tailTrace_1104415
  have hstable : (prefixWord ++ tailWord_1104415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104415).length < 2 ^ (prefixWord ++ tailWord_1104415).sum := by decide
  have hdescent : baseEnd_1104415 < baseStart_1104415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104462 : List Nat := [4, 1, 1, 1, 1, 2, 4, 1, 1, 6]
def baseStart_1104462 : Nat := 118140960795 + 1104462 * 2 ^ 59
def prefixEnd_1104462 : Nat := 4983230072969 + 3 ^ 40 * 1104462 * 2
def baseEnd_1104462 : Nat := 378079913750775347363785

theorem tailTrace_1104462 : CollatzResearch.WordTrace tailWord_1104462 prefixEnd_1104462 378079913750775347363785 := by
  unfold tailWord_1104462
  simp only [CollatzResearch.WordTrace]
  refine ⟨5035379815591284492167455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26855359016486850624893093 5035379815591284492167455)
  ·
    refine ⟨7553069723386926738251183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5035379815591284492167455 7553069723386926738251183)
    ·
      refine ⟨11329604585080390107376775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7553069723386926738251183 11329604585080390107376775)
      ·
        refine ⟨16994406877620585161065163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11329604585080390107376775 16994406877620585161065163)
        ·
          refine ⟨25491610316430877741597745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16994406877620585161065163 25491610316430877741597745)
          ·
            refine ⟨19118707737323158306198309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25491610316430877741597745 19118707737323158306198309)
            ·
              refine ⟨3584757700748092182412183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19118707737323158306198309 3584757700748092182412183)
              ·
                refine ⟨5377136551122138273618275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3584757700748092182412183 5377136551122138273618275)
                ·
                  refine ⟨8065704826683207410427413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5377136551122138273618275 8065704826683207410427413)
                  ·
                    refine ⟨378079913750775347363785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8065704826683207410427413 378079913750775347363785)
                    ·
                      rfl

theorem cell22_1104462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 1, 1, 6].length) (baseStart_1104462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1104462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1104462 prefixEnd_1104462 := by exact prefixLift 1104462
  have htrace : WordTrace (prefixWord ++ tailWord_1104462) baseStart_1104462 baseEnd_1104462 := by
    simpa [prefixWord, tailWord_1104462, baseEnd_1104462] using wordTrace_append hprefix tailTrace_1104462
  have hstable : (prefixWord ++ tailWord_1104462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104462).length < 2 ^ (prefixWord ++ tailWord_1104462).sum := by decide
  have hdescent : baseEnd_1104462 < baseStart_1104462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104494 : List Nat := [4, 1, 2, 2, 2, 2, 2, 7]
def baseStart_1104494 : Nat := 118140960795 + 1104494 * 2 ^ 59
def prefixEnd_1104494 : Nat := 4983230072969 + 3 ^ 40 * 1104494 * 2
def baseEnd_1104494 : Nat := 42010096444970881173743

theorem tailTrace_1104494 : CollatzResearch.WordTrace tailWord_1104494 prefixEnd_1104494 42010096444970881173743 := by
  unfold tailWord_1104494
  simp only [CollatzResearch.WordTrace]
  refine ⟨5035525707576793175313067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26856137107076230268336357 5035525707576793175313067)
  ·
    refine ⟨7553288561365189762969601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5035525707576793175313067 7553288561365189762969601)
    ·
      refine ⟨5664966421023892322227201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7553288561365189762969601 5664966421023892322227201)
      ·
        refine ⟨4248724815767919241670401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5664966421023892322227201 4248724815767919241670401)
        ·
          refine ⟨3186543611825939431252801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4248724815767919241670401 3186543611825939431252801)
          ·
            refine ⟨2389907708869454573439601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3186543611825939431252801 2389907708869454573439601)
            ·
              refine ⟨1792430781652090930079701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2389907708869454573439601 1792430781652090930079701)
              ·
                refine ⟨42010096444970881173743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1792430781652090930079701 42010096444970881173743)
                ·
                  rfl

theorem cell22_1104494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 7].length) (baseStart_1104494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1104494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1104494 prefixEnd_1104494 := by exact prefixLift 1104494
  have htrace : WordTrace (prefixWord ++ tailWord_1104494) baseStart_1104494 baseEnd_1104494 := by
    simpa [prefixWord, tailWord_1104494, baseEnd_1104494] using wordTrace_append hprefix tailTrace_1104494
  have hstable : (prefixWord ++ tailWord_1104494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104494).length < 2 ^ (prefixWord ++ tailWord_1104494).sum := by decide
  have hdescent : baseEnd_1104494 < baseStart_1104494 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104537 : List Nat := [1, 2, 1, 2, 1, 2, 4, 2, 2, 5]
def baseStart_1104537 : Nat := 118140960795 + 1104537 * 2 ^ 59
def prefixEnd_1104537 : Nat := 4983230072969 + 3 ^ 40 * 1104537 * 2
def baseEnd_1104537 : Nat := 378105587783500151738555

theorem tailTrace_1104537 : CollatzResearch.WordTrace tailWord_1104537 prefixEnd_1104537 378105587783500151738555 := by
  unfold tailWord_1104537
  simp only [CollatzResearch.WordTrace]
  refine ⟨40285773999458563746319865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26857182666305709164213243 40285773999458563746319865)
  ·
    refine ⟨30214330499593922809739899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40285773999458563746319865 30214330499593922809739899)
    ·
      refine ⟨45321495749390884214609849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30214330499593922809739899 45321495749390884214609849)
      ·
        refine ⟨33991121812043163160957387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45321495749390884214609849 33991121812043163160957387)
        ·
          refine ⟨50986682718064744741436081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33991121812043163160957387 50986682718064744741436081)
          ·
            refine ⟨38240012038548558556077061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50986682718064744741436081 38240012038548558556077061)
            ·
              refine ⟨7170002257227854729264449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38240012038548558556077061 7170002257227854729264449)
              ·
                refine ⟨5377501692920891046948337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7170002257227854729264449 5377501692920891046948337)
                ·
                  refine ⟨4033126269690668285211253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5377501692920891046948337 4033126269690668285211253)
                  ·
                    refine ⟨378105587783500151738555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4033126269690668285211253 378105587783500151738555)
                    ·
                      rfl

theorem cell22_1104537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 2, 2, 5].length) (baseStart_1104537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1104537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1104537 prefixEnd_1104537 := by exact prefixLift 1104537
  have htrace : WordTrace (prefixWord ++ tailWord_1104537) baseStart_1104537 baseEnd_1104537 := by
    simpa [prefixWord, tailWord_1104537, baseEnd_1104537] using wordTrace_append hprefix tailTrace_1104537
  have hstable : (prefixWord ++ tailWord_1104537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104537).length < 2 ^ (prefixWord ++ tailWord_1104537).sum := by decide
  have hdescent : baseEnd_1104537 < baseStart_1104537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104569 : List Nat := [1, 2, 1, 4, 1, 1, 1, 6, 1, 4]
def baseStart_1104569 : Nat := 118140960795 + 1104569 * 2 ^ 59
def prefixEnd_1104569 : Nat := 4983230072969 + 3 ^ 40 * 1104569 * 2
def baseEnd_1104569 : Nat := 378116542037462734938457

theorem tailTrace_1104569 : CollatzResearch.WordTrace tailWord_1104569 prefixEnd_1104569 378116542037462734938457 := by
  unfold tailWord_1104569
  simp only [CollatzResearch.WordTrace]
  refine ⟨40286941135342633211484761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26857960756895088807656507 40286941135342633211484761)
  ·
    refine ⟨30215205851506974908613571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40286941135342633211484761 30215205851506974908613571)
    ·
      refine ⟨45322808777260462362920357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30215205851506974908613571 45322808777260462362920357)
      ·
        refine ⟨8498026645736336693047567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45322808777260462362920357 8498026645736336693047567)
        ·
          refine ⟨12747039968604505039571351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8498026645736336693047567 12747039968604505039571351)
          ·
            refine ⟨19120559952906757559357027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12747039968604505039571351 19120559952906757559357027)
            ·
              refine ⟨28680839929360136339035541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19120559952906757559357027 28680839929360136339035541)
              ·
                refine ⟨1344414371688756390892291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 28680839929360136339035541 1344414371688756390892291)
                ·
                  refine ⟨2016621557533134586338437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1344414371688756390892291 2016621557533134586338437)
                  ·
                    refine ⟨378116542037462734938457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2016621557533134586338437 378116542037462734938457)
                    ·
                      rfl

theorem cell22_1104569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 6, 1, 4].length) (baseStart_1104569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1104569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1104569 prefixEnd_1104569 := by exact prefixLift 1104569
  have htrace : WordTrace (prefixWord ++ tailWord_1104569) baseStart_1104569 baseEnd_1104569 := by
    simpa [prefixWord, tailWord_1104569, baseEnd_1104569] using wordTrace_append hprefix tailTrace_1104569
  have hstable : (prefixWord ++ tailWord_1104569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104569).length < 2 ^ (prefixWord ++ tailWord_1104569).sum := by decide
  have hdescent : baseEnd_1104569 < baseStart_1104569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104577 : List Nat := [1, 2, 6, 2, 1, 1, 2, 3, 1, 3]
def baseStart_1104577 : Nat := 118140960795 + 1104577 * 2 ^ 59
def prefixEnd_1104577 : Nat := 4983230072969 + 3 ^ 40 * 1104577 * 2
def baseEnd_1104577 : Nat := 378119280600953380738433

theorem tailTrace_1104577 : CollatzResearch.WordTrace tailWord_1104577 prefixEnd_1104577 378119280600953380738433 := by
  unfold tailWord_1104577
  simp only [CollatzResearch.WordTrace]
  refine ⟨40287232919313650577775985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26858155279542433718517323 40287232919313650577775985)
  ·
    refine ⟨30215424689485237933331989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40287232919313650577775985 30215424689485237933331989)
    ·
      refine ⟨1416348032319620528124937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 30215424689485237933331989 1416348032319620528124937)
      ·
        refine ⟨1062261024239715396093703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1416348032319620528124937 1062261024239715396093703)
        ·
          refine ⟨1593391536359573094140555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1062261024239715396093703 1593391536359573094140555)
          ·
            refine ⟨2390087304539359641210833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1593391536359573094140555 2390087304539359641210833)
            ·
              refine ⟨1792565478404519730908125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2390087304539359641210833 1792565478404519730908125)
              ·
                refine ⟨672212054401694899090547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1792565478404519730908125 672212054401694899090547)
                ·
                  refine ⟨1008318081602542348635821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 672212054401694899090547 1008318081602542348635821)
                  ·
                    refine ⟨378119280600953380738433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1008318081602542348635821 378119280600953380738433)
                    ·
                      rfl

theorem cell22_1104577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_1104577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1104577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1104577 prefixEnd_1104577 := by exact prefixLift 1104577
  have htrace : WordTrace (prefixWord ++ tailWord_1104577) baseStart_1104577 baseEnd_1104577 := by
    simpa [prefixWord, tailWord_1104577, baseEnd_1104577] using wordTrace_append hprefix tailTrace_1104577
  have hstable : (prefixWord ++ tailWord_1104577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104577).length < 2 ^ (prefixWord ++ tailWord_1104577).sum := by decide
  have hdescent : baseEnd_1104577 < baseStart_1104577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104586 : List Nat := [3, 1, 2, 1, 4, 2, 1, 3, 1, 4]
def baseStart_1104586 : Nat := 118140960795 + 1104586 * 2 ^ 59
def prefixEnd_1104586 : Nat := 4983230072969 + 3 ^ 40 * 1104586 * 2
def baseEnd_1104586 : Nat := 378122361484880357263405

theorem tailTrace_1104586 : CollatzResearch.WordTrace tailWord_1104586 prefixEnd_1104586 378122361484880357263405 := by
  unfold tailWord_1104586
  simp only [CollatzResearch.WordTrace]
  refine ⟨10071890294070261278713403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26858374117520696743235741 10071890294070261278713403)
  ·
    refine ⟨15107835441105391918070105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10071890294070261278713403 15107835441105391918070105)
    ·
      refine ⟨11330876580829043938552579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15107835441105391918070105 11330876580829043938552579)
      ·
        refine ⟨16996314871243565907828869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11330876580829043938552579 16996314871243565907828869)
        ·
          refine ⟨3186809038358168607717913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16996314871243565907828869 3186809038358168607717913)
          ·
            refine ⟨2390106778768626455788435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3186809038358168607717913 2390106778768626455788435)
            ·
              refine ⟨3585160168152939683682653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2390106778768626455788435 3585160168152939683682653)
              ·
                refine ⟨1344435063057352381380995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3585160168152939683682653 1344435063057352381380995)
                ·
                  refine ⟨2016652594586028572071493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1344435063057352381380995 2016652594586028572071493)
                  ·
                    refine ⟨378122361484880357263405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2016652594586028572071493 378122361484880357263405)
                    ·
                      rfl

theorem cell22_1104586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 3, 1, 4].length) (baseStart_1104586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1104586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1104586 prefixEnd_1104586 := by exact prefixLift 1104586
  have htrace : WordTrace (prefixWord ++ tailWord_1104586) baseStart_1104586 baseEnd_1104586 := by
    simpa [prefixWord, tailWord_1104586, baseEnd_1104586] using wordTrace_append hprefix tailTrace_1104586
  have hstable : (prefixWord ++ tailWord_1104586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104586).length < 2 ^ (prefixWord ++ tailWord_1104586).sum := by decide
  have hdescent : baseEnd_1104586 < baseStart_1104586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104627 : List Nat := [1, 1, 1, 2, 2, 3, 1, 1, 1, 9]
def baseStart_1104627 : Nat := 118140960795 + 1104627 * 2 ^ 59
def prefixEnd_1104627 : Nat := 4983230072969 + 3 ^ 40 * 1104627 * 2
def baseEnd_1104627 : Nat := 378136396622769916988279

theorem tailTrace_1104627 : CollatzResearch.WordTrace tailWord_1104627 prefixEnd_1104627 378136396622769916988279 := by
  unfold tailWord_1104627
  simp only [CollatzResearch.WordTrace]
  refine ⟨40289056569132509117096135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26859371046088339411397423 40289056569132509117096135)
  ·
    refine ⟨60433584853698763675644203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40289056569132509117096135 60433584853698763675644203)
    ·
      refine ⟨90650377280548145513466305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60433584853698763675644203 90650377280548145513466305)
      ·
        refine ⟨67987782960411109135099729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90650377280548145513466305 67987782960411109135099729)
        ·
          refine ⟨50990837220308331851324797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67987782960411109135099729 50990837220308331851324797)
          ·
            refine ⟨19121563957615624444246799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50990837220308331851324797 19121563957615624444246799)
            ·
              refine ⟨28682345936423436666370199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19121563957615624444246799 28682345936423436666370199)
              ·
                refine ⟨43023518904635154999555299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28682345936423436666370199 43023518904635154999555299)
                ·
                  refine ⟨64535278356952732499332949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43023518904635154999555299 64535278356952732499332949)
                  ·
                    refine ⟨378136396622769916988279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 64535278356952732499332949 378136396622769916988279)
                    ·
                      rfl

theorem cell22_1104627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 9].length) (baseStart_1104627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1104627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1104627 prefixEnd_1104627 := by exact prefixLift 1104627
  have htrace : WordTrace (prefixWord ++ tailWord_1104627) baseStart_1104627 baseEnd_1104627 := by
    simpa [prefixWord, tailWord_1104627, baseEnd_1104627] using wordTrace_append hprefix tailTrace_1104627
  have hstable : (prefixWord ++ tailWord_1104627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104627).length < 2 ^ (prefixWord ++ tailWord_1104627).sum := by decide
  have hdescent : baseEnd_1104627 < baseStart_1104627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104753 : List Nat := [1, 2, 2, 2, 1, 5, 2, 3, 4]
def baseStart_1104753 : Nat := 118140960795 + 1104753 * 2 ^ 59
def prefixEnd_1104753 : Nat := 4983230072969 + 3 ^ 40 * 1104753 * 2
def baseEnd_1104753 : Nat := 126059842999249196112631

theorem tailTrace_1104753 : CollatzResearch.WordTrace tailWord_1104753 prefixEnd_1104753 126059842999249196112631 := by
  unfold tailWord_1104753
  simp only [CollatzResearch.WordTrace]
  refine ⟨40293652166676032636182913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26862434777784021757455275 40293652166676032636182913)
  ·
    refine ⟨30220239125007024477137185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40293652166676032636182913 30220239125007024477137185)
    ·
      refine ⟨22665179343755268357852889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30220239125007024477137185 22665179343755268357852889)
      ·
        refine ⟨16998884507816451268389667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22665179343755268357852889 16998884507816451268389667)
        ·
          refine ⟨25498326761724676902584501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16998884507816451268389667 25498326761724676902584501)
          ·
            refine ⟨2390468133911688459617297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25498326761724676902584501 2390468133911688459617297)
            ·
              refine ⟨1792851100433766344712973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2390468133911688459617297 1792851100433766344712973)
              ·
                refine ⟨672319162662662379267365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1792851100433766344712973 672319162662662379267365)
                ·
                  refine ⟨126059842999249196112631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 672319162662662379267365 126059842999249196112631)
                  ·
                    rfl

theorem cell22_1104753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 3, 4].length) (baseStart_1104753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1104753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1104753 prefixEnd_1104753 := by exact prefixLift 1104753
  have htrace : WordTrace (prefixWord ++ tailWord_1104753) baseStart_1104753 baseEnd_1104753 := by
    simpa [prefixWord, tailWord_1104753, baseEnd_1104753] using wordTrace_append hprefix tailTrace_1104753
  have hstable : (prefixWord ++ tailWord_1104753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104753).length < 2 ^ (prefixWord ++ tailWord_1104753).sum := by decide
  have hdescent : baseEnd_1104753 < baseStart_1104753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104809 : List Nat := [1, 2, 1, 1, 1, 1, 5, 1, 9]
def baseStart_1104809 : Nat := 118140960795 + 1104809 * 2 ^ 59
def prefixEnd_1104809 : Nat := 4983230072969 + 3 ^ 40 * 1104809 * 2
def baseEnd_1104809 : Nat := 126066232980727369645907

theorem tailTrace_1104809 : CollatzResearch.WordTrace tailWord_1104809 prefixEnd_1104809 126066232980727369645907 := by
  unfold tailWord_1104809
  simp only [CollatzResearch.WordTrace]
  refine ⟨40295694654473154200221481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26863796436315436133480987 40295694654473154200221481)
  ·
    refine ⟨30221770990854865650166111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40295694654473154200221481 30221770990854865650166111)
    ·
      refine ⟨45332656486282298475249167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30221770990854865650166111 45332656486282298475249167)
      ·
        refine ⟨67998984729423447712873751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45332656486282298475249167 67998984729423447712873751)
        ·
          refine ⟨101998477094135171569310627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67998984729423447712873751 101998477094135171569310627)
          ·
            refine ⟨152997715641202757353965941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101998477094135171569310627 152997715641202757353965941)
            ·
              refine ⟨14343535841362758501934307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 152997715641202757353965941 14343535841362758501934307)
              ·
                refine ⟨21515303762044137752901461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14343535841362758501934307 21515303762044137752901461)
                ·
                  refine ⟨126066232980727369645907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 21515303762044137752901461 126066232980727369645907)
                  ·
                    rfl

theorem cell22_1104809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 9].length) (baseStart_1104809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1104809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1104809 prefixEnd_1104809 := by exact prefixLift 1104809
  have htrace : WordTrace (prefixWord ++ tailWord_1104809) baseStart_1104809 baseEnd_1104809 := by
    simpa [prefixWord, tailWord_1104809, baseEnd_1104809] using wordTrace_append hprefix tailTrace_1104809
  have hstable : (prefixWord ++ tailWord_1104809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104809).length < 2 ^ (prefixWord ++ tailWord_1104809).sum := by decide
  have hdescent : baseEnd_1104809 < baseStart_1104809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104826 : List Nat := [3, 1, 1, 1, 2, 1, 4, 4, 5]
def baseStart_1104826 : Nat := 118140960795 + 1104826 * 2 ^ 59
def prefixEnd_1104826 : Nat := 4983230072969 + 3 ^ 40 * 1104826 * 2
def baseEnd_1104826 : Nat := 126068172796533243754223

theorem tailTrace_1104826 : CollatzResearch.WordTrace tailWord_1104826 prefixEnd_1104826 126068172796533243754223 := by
  unfold tailWord_1104826
  simp only [CollatzResearch.WordTrace]
  refine ⟨10074078673852891525897583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26864209796941044069060221 10074078673852891525897583)
  ·
    refine ⟨15111118010779337288846375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10074078673852891525897583 15111118010779337288846375)
    ·
      refine ⟨22666677016169005933269563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15111118010779337288846375 22666677016169005933269563)
      ·
        refine ⟨34000015524253508899904345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22666677016169005933269563 34000015524253508899904345)
        ·
          refine ⟨25500011643190131674928259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34000015524253508899904345 25500011643190131674928259)
          ·
            refine ⟨38250017464785197512392389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25500011643190131674928259 38250017464785197512392389)
            ·
              refine ⟨7171878274647224533573573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38250017464785197512392389 7171878274647224533573573)
              ·
                refine ⟨1344727176496354600045045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7171878274647224533573573 1344727176496354600045045)
                ·
                  refine ⟨126068172796533243754223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1344727176496354600045045 126068172796533243754223)
                  ·
                    rfl

theorem cell22_1104826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 4, 5].length) (baseStart_1104826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1104826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1104826 prefixEnd_1104826 := by exact prefixLift 1104826
  have htrace : WordTrace (prefixWord ++ tailWord_1104826) baseStart_1104826 baseEnd_1104826 := by
    simpa [prefixWord, tailWord_1104826, baseEnd_1104826] using wordTrace_append hprefix tailTrace_1104826
  have hstable : (prefixWord ++ tailWord_1104826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104826).length < 2 ^ (prefixWord ++ tailWord_1104826).sum := by decide
  have hdescent : baseEnd_1104826 < baseStart_1104826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104836 : List Nat := [2, 3, 3, 3, 2, 1, 2, 1, 2, 3]
def baseStart_1104836 : Nat := 118140960795 + 1104836 * 2 ^ 59
def prefixEnd_1104836 : Nat := 4983230072969 + 3 ^ 40 * 1104836 * 2
def baseEnd_1104836 : Nat := 378207941593963038512639

theorem tailTrace_1104836 : CollatzResearch.WordTrace tailWord_1104836 prefixEnd_1104836 378207941593963038512639 := by
  unfold tailWord_1104836
  simp only [CollatzResearch.WordTrace]
  refine ⟨20148339712687668905727181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26864452950250225207636241 20148339712687668905727181)
  ·
    refine ⟨7555627392257875839647693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20148339712687668905727181 7555627392257875839647693)
    ·
      refine ⟨2833360272096703439867885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7555627392257875839647693 2833360272096703439867885)
      ·
        refine ⟨1062510102036263789950457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2833360272096703439867885 1062510102036263789950457)
        ·
          refine ⟨796882576527197842462843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1062510102036263789950457 796882576527197842462843)
          ·
            refine ⟨1195323864790796763694265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 796882576527197842462843 1195323864790796763694265)
            ·
              refine ⟨896492898593097572770699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1195323864790796763694265 896492898593097572770699)
              ·
                refine ⟨1344739347889646359156049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 896492898593097572770699 1344739347889646359156049)
                ·
                  refine ⟨1008554510917234769367037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1344739347889646359156049 1008554510917234769367037)
                  ·
                    refine ⟨378207941593963038512639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1008554510917234769367037 378207941593963038512639)
                    ·
                      rfl

theorem cell22_1104836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_1104836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1104836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1104836 prefixEnd_1104836 := by exact prefixLift 1104836
  have htrace : WordTrace (prefixWord ++ tailWord_1104836) baseStart_1104836 baseEnd_1104836 := by
    simpa [prefixWord, tailWord_1104836, baseEnd_1104836] using wordTrace_append hprefix tailTrace_1104836
  have hstable : (prefixWord ++ tailWord_1104836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104836).length < 2 ^ (prefixWord ++ tailWord_1104836).sum := by decide
  have hdescent : baseEnd_1104836 < baseStart_1104836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104843 : List Nat := [1, 1, 1, 1, 3, 5, 4, 1, 5]
def baseStart_1104843 : Nat := 118140960795 + 1104843 * 2 ^ 59
def prefixEnd_1104843 : Nat := 4983230072969 + 3 ^ 40 * 1104843 * 2
def baseEnd_1104843 : Nat := 126070112612339117862539

theorem tailTrace_1104843 : CollatzResearch.WordTrace tailWord_1104843 prefixEnd_1104843 126070112612339117862539 := by
  unfold tailWord_1104843
  simp only [CollatzResearch.WordTrace]
  refine ⟨40296934736349978006959183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26864623157566652004639455 40296934736349978006959183)
  ·
    refine ⟨60445402104524967010438775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40296934736349978006959183 60445402104524967010438775)
    ·
      refine ⟨90668103156787450515658163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60445402104524967010438775 90668103156787450515658163)
      ·
        refine ⟨136002154735181175773487245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90668103156787450515658163 136002154735181175773487245)
        ·
          refine ⟨51000808025692940915057717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 136002154735181175773487245 51000808025692940915057717)
          ·
            refine ⟨4781325752408713210786661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 51000808025692940915057717 4781325752408713210786661)
            ·
              refine ⟨896498578576633727022499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4781325752408713210786661 896498578576633727022499)
              ·
                refine ⟨1344747867864950590533749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 896498578576633727022499 1344747867864950590533749)
                ·
                  refine ⟨126070112612339117862539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1344747867864950590533749 126070112612339117862539)
                  ·
                    rfl

theorem cell22_1104843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 4, 1, 5].length) (baseStart_1104843 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1104843 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1104843 prefixEnd_1104843 := by exact prefixLift 1104843
  have htrace : WordTrace (prefixWord ++ tailWord_1104843) baseStart_1104843 baseEnd_1104843 := by
    simpa [prefixWord, tailWord_1104843, baseEnd_1104843] using wordTrace_append hprefix tailTrace_1104843
  have hstable : (prefixWord ++ tailWord_1104843).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104843).length < 2 ^ (prefixWord ++ tailWord_1104843).sum := by decide
  have hdescent : baseEnd_1104843 < baseStart_1104843 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104901 : List Nat := [1, 3, 1, 1, 2, 3, 2, 2, 1, 6]
def baseStart_1104901 : Nat := 118140960795 + 1104901 * 2 ^ 59
def prefixEnd_1104901 : Nat := 4983230072969 + 3 ^ 40 * 1104901 * 2
def baseEnd_1104901 : Nat := 378230192422324535637439

theorem tailTrace_1104901 : CollatzResearch.WordTrace tailWord_1104901 prefixEnd_1104901 378230192422324535637439 := by
  unfold tailWord_1104901
  simp only [CollatzResearch.WordTrace]
  refine ⟨40299050170139853912570557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26866033446759902608380371 40299050170139853912570557)
  ·
    refine ⟨15112143813802445217213959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40299050170139853912570557 15112143813802445217213959)
    ·
      refine ⟨22668215720703667825820939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15112143813802445217213959 22668215720703667825820939)
      ·
        refine ⟨34002323581055501738731409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22668215720703667825820939 34002323581055501738731409)
        ·
          refine ⟨25501742685791626304048557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34002323581055501738731409 25501742685791626304048557)
          ·
            refine ⟨9563153507171859864018209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25501742685791626304048557 9563153507171859864018209)
            ·
              refine ⟨7172365130378894898013657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9563153507171859864018209 7172365130378894898013657)
              ·
                refine ⟨5379273847784171173510243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7172365130378894898013657 5379273847784171173510243)
                ·
                  refine ⟨8068910771676256760265365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5379273847784171173510243 8068910771676256760265365)
                  ·
                    refine ⟨378230192422324535637439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8068910771676256760265365 378230192422324535637439)
                    ·
                      rfl

theorem cell22_1104901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 2, 1, 6].length) (baseStart_1104901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1104901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1104901 prefixEnd_1104901 := by exact prefixLift 1104901
  have htrace : WordTrace (prefixWord ++ tailWord_1104901) baseStart_1104901 baseEnd_1104901 := by
    simpa [prefixWord, tailWord_1104901, baseEnd_1104901] using wordTrace_append hprefix tailTrace_1104901
  have hstable : (prefixWord ++ tailWord_1104901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104901).length < 2 ^ (prefixWord ++ tailWord_1104901).sum := by decide
  have hdescent : baseEnd_1104901 < baseStart_1104901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104903 : List Nat := [1, 1, 4, 3, 1, 1, 4, 1, 1, 5]
def baseStart_1104903 : Nat := 118140960795 + 1104903 * 2 ^ 59
def prefixEnd_1104903 : Nat := 4983230072969 + 3 ^ 40 * 1104903 * 2
def baseEnd_1104903 : Nat := 378230877063197197087433

theorem tailTrace_1104903 : CollatzResearch.WordTrace tailWord_1104903 prefixEnd_1104903 378230877063197197087433 := by
  unfold tailWord_1104903
  simp only [CollatzResearch.WordTrace]
  refine ⟨40299123116132608254143363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26866082077421738836095575 40299123116132608254143363)
  ·
    refine ⟨60448684674198912381215045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40299123116132608254143363 60448684674198912381215045)
    ·
      refine ⟨11334128376412296071477821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60448684674198912381215045 11334128376412296071477821)
      ·
        refine ⟨4250298141154611026804183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11334128376412296071477821 4250298141154611026804183)
        ·
          refine ⟨6375447211731916540206275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4250298141154611026804183 6375447211731916540206275)
          ·
            refine ⟨9563170817597874810309413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6375447211731916540206275 9563170817597874810309413)
            ·
              refine ⟨1793094528299601526933015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9563170817597874810309413 1793094528299601526933015)
              ·
                refine ⟨2689641792449402290399523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1793094528299601526933015 2689641792449402290399523)
                ·
                  refine ⟨4034462688674103435599285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2689641792449402290399523 4034462688674103435599285)
                  ·
                    refine ⟨378230877063197197087433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4034462688674103435599285 378230877063197197087433)
                    ·
                      rfl

theorem cell22_1104903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 1, 1, 5].length) (baseStart_1104903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1104903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1104903 prefixEnd_1104903 := by exact prefixLift 1104903
  have htrace : WordTrace (prefixWord ++ tailWord_1104903) baseStart_1104903 baseEnd_1104903 := by
    simpa [prefixWord, tailWord_1104903, baseEnd_1104903] using wordTrace_append hprefix tailTrace_1104903
  have hstable : (prefixWord ++ tailWord_1104903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104903).length < 2 ^ (prefixWord ++ tailWord_1104903).sum := by decide
  have hdescent : baseEnd_1104903 < baseStart_1104903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104924 : List Nat := [2, 2, 3, 1, 5, 1, 2, 1, 1, 4]
def baseStart_1104924 : Nat := 118140960795 + 1104924 * 2 ^ 59
def prefixEnd_1104924 : Nat := 4983230072969 + 3 ^ 40 * 1104924 * 2
def baseEnd_1104924 : Nat := 378238065792360142312369

theorem tailTrace_1104924 : CollatzResearch.WordTrace tailWord_1104924 prefixEnd_1104924 378238065792360142312369 := by
  unfold tailWord_1104924
  simp only [CollatzResearch.WordTrace]
  refine ⟨20149944524528264420328913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26866592699371019227105217 20149944524528264420328913)
  ·
    refine ⟨15112458393396198315246685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20149944524528264420328913 15112458393396198315246685)
    ·
      refine ⟨5667171897523574368217507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15112458393396198315246685 5667171897523574368217507)
      ·
        refine ⟨8500757846285361552326261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5667171897523574368217507 8500757846285361552326261)
        ·
          refine ⟨796946048089252645530587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8500757846285361552326261 796946048089252645530587)
          ·
            refine ⟨1195419072133878968295881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 796946048089252645530587 1195419072133878968295881)
            ·
              refine ⟨896564304100409226221911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1195419072133878968295881 896564304100409226221911)
              ·
                refine ⟨1344846456150613839332867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 896564304100409226221911 1344846456150613839332867)
                ·
                  refine ⟨2017269684225920758999301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1344846456150613839332867 2017269684225920758999301)
                  ·
                    refine ⟨378238065792360142312369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2017269684225920758999301 378238065792360142312369)
                    ·
                      rfl

theorem cell22_1104924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 2, 1, 1, 4].length) (baseStart_1104924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1104924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1104924 prefixEnd_1104924 := by exact prefixLift 1104924
  have htrace : WordTrace (prefixWord ++ tailWord_1104924) baseStart_1104924 baseEnd_1104924 := by
    simpa [prefixWord, tailWord_1104924, baseEnd_1104924] using wordTrace_append hprefix tailTrace_1104924
  have hstable : (prefixWord ++ tailWord_1104924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104924).length < 2 ^ (prefixWord ++ tailWord_1104924).sum := by decide
  have hdescent : baseEnd_1104924 < baseStart_1104924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104976 : List Nat := [2, 1, 1, 1, 1, 3, 1, 4, 1, 7]
def baseStart_1104976 : Nat := 118140960795 + 1104976 * 2 ^ 59
def prefixEnd_1104976 : Nat := 4983230072969 + 3 ^ 40 * 1104976 * 2
def baseEnd_1104976 : Nat := 378255866455049340012209

theorem tailTrace_1104976 : CollatzResearch.WordTrace tailWord_1104976 prefixEnd_1104976 378255866455049340012209 := by
  unfold tailWord_1104976
  simp only [CollatzResearch.WordTrace]
  refine ⟨20150892822434070860775391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26867857096578761147700521 20150892822434070860775391)
  ·
    refine ⟨30226339233651106291163087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20150892822434070860775391 30226339233651106291163087)
    ·
      refine ⟨45339508850476659436744631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30226339233651106291163087 45339508850476659436744631)
      ·
        refine ⟨68009263275714989155116947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45339508850476659436744631 68009263275714989155116947)
        ·
          refine ⟨102013894913572483732675421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68009263275714989155116947 102013894913572483732675421)
          ·
            refine ⟨38255210592589681399753283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102013894913572483732675421 38255210592589681399753283)
            ·
              refine ⟨57382815888884522099629925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38255210592589681399753283 57382815888884522099629925)
              ·
                refine ⟨10759277979165847893680611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57382815888884522099629925 10759277979165847893680611)
                ·
                  refine ⟨16138916968748771840520917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10759277979165847893680611 16138916968748771840520917)
                  ·
                    refine ⟨378255866455049340012209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16138916968748771840520917 378255866455049340012209)
                    ·
                      rfl

theorem cell22_1104976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 1, 7].length) (baseStart_1104976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1104976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1104976 prefixEnd_1104976 := by exact prefixLift 1104976
  have htrace : WordTrace (prefixWord ++ tailWord_1104976) baseStart_1104976 baseEnd_1104976 := by
    simpa [prefixWord, tailWord_1104976, baseEnd_1104976] using wordTrace_append hprefix tailTrace_1104976
  have hstable : (prefixWord ++ tailWord_1104976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104976).length < 2 ^ (prefixWord ++ tailWord_1104976).sum := by decide
  have hdescent : baseEnd_1104976 < baseStart_1104976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104978 : List Nat := [3, 2, 2, 1, 3, 1, 1, 2, 7]
def baseStart_1104978 : Nat := 118140960795 + 1104978 * 2 ^ 59
def prefixEnd_1104978 : Nat := 4983230072969 + 3 ^ 40 * 1104978 * 2
def baseEnd_1104978 : Nat := 126085517031974000487401

theorem tailTrace_1104978 : CollatzResearch.WordTrace tailWord_1104978 prefixEnd_1104978 126085517031974000487401 := by
  unfold tailWord_1104978
  simp only [CollatzResearch.WordTrace]
  refine ⟨10075464647715224015780897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26867905727240597375415725 10075464647715224015780897)
  ·
    refine ⟨7556598485786418011835673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10075464647715224015780897 7556598485786418011835673)
    ·
      refine ⟨5667448864339813508876755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7556598485786418011835673 5667448864339813508876755)
      ·
        refine ⟨8501173296509720263315133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5667448864339813508876755 8501173296509720263315133)
        ·
          refine ⟨3187939986191145098743175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8501173296509720263315133 3187939986191145098743175)
          ·
            refine ⟨4781909979286717648114763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3187939986191145098743175 4781909979286717648114763)
            ·
              refine ⟨7172864968930076472172145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4781909979286717648114763 7172864968930076472172145)
              ·
                refine ⟨5379648726697557354129109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7172864968930076472172145 5379648726697557354129109)
                ·
                  refine ⟨126085517031974000487401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5379648726697557354129109 126085517031974000487401)
                  ·
                    rfl

theorem cell22_1104978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 2, 7].length) (baseStart_1104978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1104978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1104978 prefixEnd_1104978 := by exact prefixLift 1104978
  have htrace : WordTrace (prefixWord ++ tailWord_1104978) baseStart_1104978 baseEnd_1104978 := by
    simpa [prefixWord, tailWord_1104978, baseEnd_1104978] using wordTrace_append hprefix tailTrace_1104978
  have hstable : (prefixWord ++ tailWord_1104978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104978).length < 2 ^ (prefixWord ++ tailWord_1104978).sum := by decide
  have hdescent : baseEnd_1104978 < baseStart_1104978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104999 : List Nat := [1, 1, 5, 1, 1, 4, 3, 2, 1, 3]
def baseStart_1104999 : Nat := 118140960795 + 1104999 * 2 ^ 59
def prefixEnd_1104999 : Nat := 4983230072969 + 3 ^ 40 * 1104999 * 2
def baseEnd_1104999 : Nat := 378263739825084946687139

theorem tailTrace_1104999 : CollatzResearch.WordTrace tailWord_1104999 prefixEnd_1104999 378263739825084946687139 := by
  unfold tailWord_1104999
  simp only [CollatzResearch.WordTrace]
  refine ⟨40302624523784816649638051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26868416349189877766425367 40302624523784816649638051)
  ·
    refine ⟨60453936785677224974457077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40302624523784816649638051 60453936785677224974457077)
    ·
      refine ⟨5667556573657239841355351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 60453936785677224974457077 5667556573657239841355351)
      ·
        refine ⟨8501334860485859762033027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5667556573657239841355351 8501334860485859762033027)
        ·
          refine ⟨12752002290728789643049541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8501334860485859762033027 12752002290728789643049541)
          ·
            refine ⟨2391000429511648058071789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12752002290728789643049541 2391000429511648058071789)
            ·
              refine ⟨896625161066868021776921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2391000429511648058071789 896625161066868021776921)
              ·
                refine ⟨672468870800151016332691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 896625161066868021776921 672468870800151016332691)
                ·
                  refine ⟨1008703306200226524499037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 672468870800151016332691 1008703306200226524499037)
                  ·
                    refine ⟨378263739825084946687139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1008703306200226524499037 378263739825084946687139)
                    ·
                      rfl

theorem cell22_1104999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 3, 2, 1, 3].length) (baseStart_1104999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1104999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1104999 prefixEnd_1104999 := by exact prefixLift 1104999
  have htrace : WordTrace (prefixWord ++ tailWord_1104999) baseStart_1104999 baseEnd_1104999 := by
    simpa [prefixWord, tailWord_1104999, baseEnd_1104999] using wordTrace_append hprefix tailTrace_1104999
  have hstable : (prefixWord ++ tailWord_1104999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104999).length < 2 ^ (prefixWord ++ tailWord_1104999).sum := by decide
  have hdescent : baseEnd_1104999 < baseStart_1104999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105008 : List Nat := [2, 1, 1, 1, 5, 1, 2, 2, 3, 4]
def baseStart_1105008 : Nat := 118140960795 + 1105008 * 2 ^ 59
def prefixEnd_1105008 : Nat := 4983230072969 + 3 ^ 40 * 1105008 * 2
def baseEnd_1105008 : Nat := 378266820709011923212111

theorem tailTrace_1105008 : CollatzResearch.WordTrace tailWord_1105008 prefixEnd_1105008 378266820709011923212111 := by
  unfold tailWord_1105008
  simp only [CollatzResearch.WordTrace]
  refine ⟨20151476390376105593357839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26868635187168140791143785 20151476390376105593357839)
  ·
    refine ⟨30227214585564158390036759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20151476390376105593357839 30227214585564158390036759)
    ·
      refine ⟨45340821878346237585055139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30227214585564158390036759 45340821878346237585055139)
      ·
        refine ⟨68011232817519356377582709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45340821878346237585055139 68011232817519356377582709)
        ·
          refine ⟨6376053076642439660398379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 68011232817519356377582709 6376053076642439660398379)
          ·
            refine ⟨9564079614963659490597569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6376053076642439660398379 9564079614963659490597569)
            ·
              refine ⟨7173059711222744617948177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9564079614963659490597569 7173059711222744617948177)
              ·
                refine ⟨5379794783417058463461133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7173059711222744617948177 5379794783417058463461133)
                ·
                  refine ⟨2017423043781396923797925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5379794783417058463461133 2017423043781396923797925)
                  ·
                    refine ⟨378266820709011923212111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2017423043781396923797925 378266820709011923212111)
                    ·
                      rfl

theorem cell22_1105008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 2, 3, 4].length) (baseStart_1105008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1105008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1105008 prefixEnd_1105008 := by exact prefixLift 1105008
  have htrace : WordTrace (prefixWord ++ tailWord_1105008) baseStart_1105008 baseEnd_1105008 := by
    simpa [prefixWord, tailWord_1105008, baseEnd_1105008] using wordTrace_append hprefix tailTrace_1105008
  have hstable : (prefixWord ++ tailWord_1105008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105008).length < 2 ^ (prefixWord ++ tailWord_1105008).sum := by decide
  have hdescent : baseEnd_1105008 < baseStart_1105008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105025 : List Nat := [1, 2, 4, 2, 2, 2, 1, 1, 3, 4]
def baseStart_1105025 : Nat := 118140960795 + 1105025 * 2 ^ 59
def prefixEnd_1105025 : Nat := 4983230072969 + 3 ^ 40 * 1105025 * 2
def baseEnd_1105025 : Nat := 378272640156429545537059

theorem tailTrace_1105025 : CollatzResearch.WordTrace tailWord_1105025 prefixEnd_1105025 378272640156429545537059 := by
  unfold tailWord_1105025
  simp only [CollatzResearch.WordTrace]
  refine ⟨40303572821690623090084529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26869048547793748726723019 40303572821690623090084529)
  ·
    refine ⟨30227679616267967317563397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40303572821690623090084529 30227679616267967317563397)
    ·
      refine ⟨5667689928050243872043137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30227679616267967317563397 5667689928050243872043137)
      ·
        refine ⟨4250767446037682904032353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5667689928050243872043137 4250767446037682904032353)
        ·
          refine ⟨3188075584528262178024265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4250767446037682904032353 3188075584528262178024265)
          ·
            refine ⟨2391056688396196633518199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3188075584528262178024265 2391056688396196633518199)
            ·
              refine ⟨3586585032594294950277299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2391056688396196633518199 3586585032594294950277299)
              ·
                refine ⟨5379877548891442425415949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3586585032594294950277299 5379877548891442425415949)
                ·
                  refine ⟨2017454080834290909530981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5379877548891442425415949 2017454080834290909530981)
                  ·
                    refine ⟨378272640156429545537059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2017454080834290909530981 378272640156429545537059)
                    ·
                      rfl

theorem cell22_1105025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_1105025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1105025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1105025 prefixEnd_1105025 := by exact prefixLift 1105025
  have htrace : WordTrace (prefixWord ++ tailWord_1105025) baseStart_1105025 baseEnd_1105025 := by
    simpa [prefixWord, tailWord_1105025, baseEnd_1105025] using wordTrace_append hprefix tailTrace_1105025
  have hstable : (prefixWord ++ tailWord_1105025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105025).length < 2 ^ (prefixWord ++ tailWord_1105025).sum := by decide
  have hdescent : baseEnd_1105025 < baseStart_1105025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105194 : List Nat := [3, 1, 4, 2, 1, 1, 3, 2, 1, 4]
def baseStart_1105194 : Nat := 118140960795 + 1105194 * 2 ^ 59
def prefixEnd_1105194 : Nat := 4983230072969 + 3 ^ 40 * 1105194 * 2
def baseEnd_1105194 : Nat := 378330492310169438061541

theorem tailTrace_1105194 : CollatzResearch.WordTrace tailWord_1105194 prefixEnd_1105194 378330492310169438061541 := by
  unfold tailWord_1105194
  simp only [CollatzResearch.WordTrace]
  refine ⟨10077434189519591238246659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26873157838718909968657757 10077434189519591238246659)
  ·
    refine ⟨15116151284279386857369989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10077434189519591238246659 15116151284279386857369989)
    ·
      refine ⟨2834278365802385035756873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15116151284279386857369989 2834278365802385035756873)
      ·
        refine ⟨2125708774351788776817655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2834278365802385035756873 2125708774351788776817655)
        ·
          refine ⟨3188563161527683165226483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2125708774351788776817655 3188563161527683165226483)
          ·
            refine ⟨4782844742291524747839725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3188563161527683165226483 4782844742291524747839725)
            ·
              refine ⟨1793566778359321780439897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4782844742291524747839725 1793566778359321780439897)
              ·
                refine ⟨1345175083769491335329923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1793566778359321780439897 1345175083769491335329923)
                ·
                  refine ⟨2017762625654237002994885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1345175083769491335329923 2017762625654237002994885)
                  ·
                    refine ⟨378330492310169438061541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2017762625654237002994885 378330492310169438061541)
                    ·
                      rfl

theorem cell22_1105194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_1105194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1105194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1105194 prefixEnd_1105194 := by exact prefixLift 1105194
  have htrace : WordTrace (prefixWord ++ tailWord_1105194) baseStart_1105194 baseEnd_1105194 := by
    simpa [prefixWord, tailWord_1105194, baseEnd_1105194] using wordTrace_append hprefix tailTrace_1105194
  have hstable : (prefixWord ++ tailWord_1105194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105194).length < 2 ^ (prefixWord ++ tailWord_1105194).sum := by decide
  have hdescent : baseEnd_1105194 < baseStart_1105194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105237 : List Nat := [1, 3, 2, 2, 3, 3, 1, 7]
def baseStart_1105237 : Nat := 118140960795 + 1105237 * 2 ^ 59
def prefixEnd_1105237 : Nat := 4983230072969 + 3 ^ 40 * 1105237 * 2
def baseEnd_1105237 : Nat := 42038356898770184359601

theorem tailTrace_1105237 : CollatzResearch.WordTrace tailWord_1105237 prefixEnd_1105237 42038356898770184359601 := by
  unfold tailWord_1105237
  simp only [CollatzResearch.WordTrace]
  refine ⟨40311305096922583296801965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26874203397948388864534643 40311305096922583296801965)
  ·
    refine ⟨15116739411345968736300737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40311305096922583296801965 15116739411345968736300737)
    ·
      refine ⟨11337554558509476552225553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15116739411345968736300737 11337554558509476552225553)
      ·
        refine ⟨8503165918882107414169165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11337554558509476552225553 8503165918882107414169165)
        ·
          refine ⟨3188687219580790280313437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8503165918882107414169165 3188687219580790280313437)
          ·
            refine ⟨1195757707342796355117539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3188687219580790280313437 1195757707342796355117539)
            ·
              refine ⟨1793636561014194532676309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1195757707342796355117539 1793636561014194532676309)
              ·
                refine ⟨42038356898770184359601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1793636561014194532676309 42038356898770184359601)
                ·
                  rfl

theorem cell22_1105237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 7].length) (baseStart_1105237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1105237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1105237 prefixEnd_1105237 := by exact prefixLift 1105237
  have htrace : WordTrace (prefixWord ++ tailWord_1105237) baseStart_1105237 baseEnd_1105237 := by
    simpa [prefixWord, tailWord_1105237, baseEnd_1105237] using wordTrace_append hprefix tailTrace_1105237
  have hstable : (prefixWord ++ tailWord_1105237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105237).length < 2 ^ (prefixWord ++ tailWord_1105237).sum := by decide
  have hdescent : baseEnd_1105237 < baseStart_1105237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105252 : List Nat := [2, 3, 1, 1, 3, 2, 1, 1, 5, 3]
def baseStart_1105252 : Nat := 118140960795 + 1105252 * 2 ^ 59
def prefixEnd_1105252 : Nat := 4983230072969 + 3 ^ 40 * 1105252 * 2
def baseEnd_1105252 : Nat := 378350346895476620111363

theorem tailTrace_1105252 : CollatzResearch.WordTrace tailWord_1105252 prefixEnd_1105252 378350346895476620111363 := by
  unfold tailWord_1105252
  simp only [CollatzResearch.WordTrace]
  refine ⟨20155926095934120429299005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26874568127912160572398673 20155926095934120429299005)
  ·
    refine ⟨7558472285975295160987127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20155926095934120429299005 7558472285975295160987127)
    ·
      refine ⟨11337708428962942741480691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7558472285975295160987127 11337708428962942741480691)
      ·
        refine ⟨17006562643444414112221037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11337708428962942741480691 17006562643444414112221037)
        ·
          refine ⟨6377460991291655292082889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17006562643444414112221037 6377460991291655292082889)
          ·
            refine ⟨4783095743468741469062167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6377460991291655292082889 4783095743468741469062167)
            ·
              refine ⟨7174643615203112203593251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4783095743468741469062167 7174643615203112203593251)
              ·
                refine ⟨10761965422804668305389877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7174643615203112203593251 10761965422804668305389877)
                ·
                  refine ⟨1008934258387937653630301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10761965422804668305389877 1008934258387937653630301)
                  ·
                    refine ⟨378350346895476620111363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1008934258387937653630301 378350346895476620111363)
                    ·
                      rfl

theorem cell22_1105252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 5, 3].length) (baseStart_1105252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1105252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1105252 prefixEnd_1105252 := by exact prefixLift 1105252
  have htrace : WordTrace (prefixWord ++ tailWord_1105252) baseStart_1105252 baseEnd_1105252 := by
    simpa [prefixWord, tailWord_1105252, baseEnd_1105252] using wordTrace_append hprefix tailTrace_1105252
  have hstable : (prefixWord ++ tailWord_1105252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105252).length < 2 ^ (prefixWord ++ tailWord_1105252).sum := by decide
  have hdescent : baseEnd_1105252 < baseStart_1105252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105256 : List Nat := [2, 1, 4, 2, 4, 1, 1, 1, 2, 4]
def baseStart_1105256 : Nat := 118140960795 + 1105256 * 2 ^ 59
def prefixEnd_1105256 : Nat := 4983230072969 + 3 ^ 40 * 1105256 * 2
def baseEnd_1105256 : Nat := 378351716177221943011351

theorem tailTrace_1105256 : CollatzResearch.WordTrace tailWord_1105256 prefixEnd_1105256 378351716177221943011351 := by
  unfold tailWord_1105256
  simp only [CollatzResearch.WordTrace]
  refine ⟨20155999041926874770871811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26874665389235833027829081 20155999041926874770871811)
  ·
    refine ⟨30233998562890312156307717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20155999041926874770871811 30233998562890312156307717)
    ·
      refine ⟨5668874730541933529307697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30233998562890312156307717 5668874730541933529307697)
      ·
        refine ⟨4251656047906450146980773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5668874730541933529307697 4251656047906450146980773)
        ·
          refine ⟨797185508982459402558895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4251656047906450146980773 797185508982459402558895)
          ·
            refine ⟨1195778263473689103838343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 797185508982459402558895 1195778263473689103838343)
            ·
              refine ⟨1793667395210533655757515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1195778263473689103838343 1793667395210533655757515)
              ·
                refine ⟨2690501092815800483636273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1793667395210533655757515 2690501092815800483636273)
                ·
                  refine ⟨2017875819611850362727205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2690501092815800483636273 2017875819611850362727205)
                  ·
                    refine ⟨378351716177221943011351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2017875819611850362727205 378351716177221943011351)
                    ·
                      rfl

theorem cell22_1105256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 1, 2, 4].length) (baseStart_1105256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1105256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1105256 prefixEnd_1105256 := by exact prefixLift 1105256
  have htrace : WordTrace (prefixWord ++ tailWord_1105256) baseStart_1105256 baseEnd_1105256 := by
    simpa [prefixWord, tailWord_1105256, baseEnd_1105256] using wordTrace_append hprefix tailTrace_1105256
  have hstable : (prefixWord ++ tailWord_1105256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105256).length < 2 ^ (prefixWord ++ tailWord_1105256).sum := by decide
  have hdescent : baseEnd_1105256 < baseStart_1105256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105320 : List Nat := [2, 1, 6, 1, 2, 2, 1, 3, 1, 3]
def baseStart_1105320 : Nat := 118140960795 + 1105320 * 2 ^ 59
def prefixEnd_1105320 : Nat := 4983230072969 + 3 ^ 40 * 1105320 * 2
def baseEnd_1105320 : Nat := 378373624685147109411155

theorem tailTrace_1105320 : CollatzResearch.WordTrace tailWord_1105320 prefixEnd_1105320 378373624685147109411155 := by
  unfold tailWord_1105320
  simp only [CollatzResearch.WordTrace]
  refine ⟨20157166177810944236036707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26876221570414592314715609 20157166177810944236036707)
  ·
    refine ⟨30235749266716416354055061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20157166177810944236036707 30235749266716416354055061)
    ·
      refine ⟨1417300746877332016596331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 30235749266716416354055061 1417300746877332016596331)
      ·
        refine ⟨2125951120315998024894497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1417300746877332016596331 2125951120315998024894497)
        ·
          refine ⟨1594463340236998518670873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2125951120315998024894497 1594463340236998518670873)
          ·
            refine ⟨1195847505177748889003155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1594463340236998518670873 1195847505177748889003155)
            ·
              refine ⟨1793771257766623333504733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1195847505177748889003155 1793771257766623333504733)
              ·
                refine ⟨672664221662483750064275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1793771257766623333504733 672664221662483750064275)
                ·
                  refine ⟨1008996332493725625096413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 672664221662483750064275 1008996332493725625096413)
                  ·
                    refine ⟨378373624685147109411155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1008996332493725625096413 378373624685147109411155)
                    ·
                      rfl

theorem cell22_1105320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_1105320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1105320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1105320 prefixEnd_1105320 := by exact prefixLift 1105320
  have htrace : WordTrace (prefixWord ++ tailWord_1105320) baseStart_1105320 baseEnd_1105320 := by
    simpa [prefixWord, tailWord_1105320, baseEnd_1105320] using wordTrace_append hprefix tailTrace_1105320
  have hstable : (prefixWord ++ tailWord_1105320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105320).length < 2 ^ (prefixWord ++ tailWord_1105320).sum := by decide
  have hdescent : baseEnd_1105320 < baseStart_1105320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105355 : List Nat := [1, 1, 1, 1, 3, 3, 3, 9]
def baseStart_1105355 : Nat := 118140960795 + 1105355 * 2 ^ 59
def prefixEnd_1105355 : Nat := 4983230072969 + 3 ^ 40 * 1105355 * 2
def baseEnd_1105355 : Nat := 42042845100046520531783

theorem tailTrace_1105355 : CollatzResearch.WordTrace tailWord_1105355 prefixEnd_1105355 42042845100046520531783 := by
  unfold tailWord_1105355
  simp only [CollatzResearch.WordTrace]
  refine ⟨40315608910495089449597519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26877072606996726299731679 40315608910495089449597519)
  ·
    refine ⟨60473413365742634174396279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40315608910495089449597519 60473413365742634174396279)
    ·
      refine ⟨90710120048613951261594419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60473413365742634174396279 90710120048613951261594419)
      ·
        refine ⟨136065180072920926892391629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90710120048613951261594419 136065180072920926892391629)
        ·
          refine ⟨51024442527345347584646861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 136065180072920926892391629 51024442527345347584646861)
          ·
            refine ⟨19134165947754505344242573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51024442527345347584646861 19134165947754505344242573)
            ·
              refine ⟨7175312230407939504090965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19134165947754505344242573 7175312230407939504090965)
              ·
                refine ⟨42042845100046520531783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7175312230407939504090965 42042845100046520531783)
                ·
                  rfl

theorem cell22_1105355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 9].length) (baseStart_1105355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1105355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1105355 prefixEnd_1105355 := by exact prefixLift 1105355
  have htrace : WordTrace (prefixWord ++ tailWord_1105355) baseStart_1105355 baseEnd_1105355 := by
    simpa [prefixWord, tailWord_1105355, baseEnd_1105355] using wordTrace_append hprefix tailTrace_1105355
  have hstable : (prefixWord ++ tailWord_1105355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105355).length < 2 ^ (prefixWord ++ tailWord_1105355).sum := by decide
  have hdescent : baseEnd_1105355 < baseStart_1105355 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105387 : List Nat := [1, 1, 1, 1, 2, 3, 2, 1, 7, 3]
def baseStart_1105387 : Nat := 118140960795 + 1105387 * 2 ^ 59
def prefixEnd_1105387 : Nat := 4983230072969 + 3 ^ 40 * 1105387 * 2
def baseEnd_1105387 : Nat := 378396560154381267985949

theorem tailTrace_1105387 : CollatzResearch.WordTrace tailWord_1105387 prefixEnd_1105387 378396560154381267985949 := by
  unfold tailWord_1105387
  simp only [CollatzResearch.WordTrace]
  refine ⟨40316776046379158914762415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26877850697586105943174943 40316776046379158914762415)
  ·
    refine ⟨60475164069568738372143623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40316776046379158914762415 60475164069568738372143623)
    ·
      refine ⟨90712746104353107558215435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60475164069568738372143623 90712746104353107558215435)
      ·
        refine ⟨136069119156529661337323153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90712746104353107558215435 136069119156529661337323153)
        ·
          refine ⟨102051839367397246002992365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136069119156529661337323153 102051839367397246002992365)
          ·
            refine ⟨38269439762773967251122137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102051839367397246002992365 38269439762773967251122137)
            ·
              refine ⟨28702079822080475438341603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38269439762773967251122137 28702079822080475438341603)
              ·
                refine ⟨43053119733120713157512405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28702079822080475438341603 43053119733120713157512405)
                ·
                  refine ⟨1009057493745016714629197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 43053119733120713157512405 1009057493745016714629197)
                  ·
                    refine ⟨378396560154381267985949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1009057493745016714629197 378396560154381267985949)
                    ·
                      rfl

theorem cell22_1105387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 7, 3].length) (baseStart_1105387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1105387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1105387 prefixEnd_1105387 := by exact prefixLift 1105387
  have htrace : WordTrace (prefixWord ++ tailWord_1105387) baseStart_1105387 baseEnd_1105387 := by
    simpa [prefixWord, tailWord_1105387, baseEnd_1105387] using wordTrace_append hprefix tailTrace_1105387
  have hstable : (prefixWord ++ tailWord_1105387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105387).length < 2 ^ (prefixWord ++ tailWord_1105387).sum := by decide
  have hdescent : baseEnd_1105387 < baseStart_1105387 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105389 : List Nat := [1, 5, 1, 3, 3, 9]
def baseStart_1105389 : Nat := 118140960795 + 1105389 * 2 ^ 59
def prefixEnd_1105389 : Nat := 4983230072969 + 3 ^ 40 * 1105389 * 2
def baseEnd_1105389 : Nat := 4671570923398196659703

theorem tailTrace_1105389 : CollatzResearch.WordTrace tailWord_1105389 prefixEnd_1105389 4671570923398196659703 := by
  unfold tailWord_1105389
  simp only [CollatzResearch.WordTrace]
  refine ⟨40316848992371913256335221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26877899328247942170890147 40316848992371913256335221)
  ·
    refine ⟨3779704593034866867781427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40316848992371913256335221 3779704593034866867781427)
    ·
      refine ⟨5669556889552300301672141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3779704593034866867781427 5669556889552300301672141)
      ·
        refine ⟨2126083833582112613127053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5669556889552300301672141 2126083833582112613127053)
        ·
          refine ⟨797281437593292229922645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2126083833582112613127053 797281437593292229922645)
          ·
            refine ⟨4671570923398196659703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 797281437593292229922645 4671570923398196659703)
            ·
              rfl

theorem cell22_1105389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 9].length) (baseStart_1105389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1105389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1105389 prefixEnd_1105389 := by exact prefixLift 1105389
  have htrace : WordTrace (prefixWord ++ tailWord_1105389) baseStart_1105389 baseEnd_1105389 := by
    simpa [prefixWord, tailWord_1105389, baseEnd_1105389] using wordTrace_append hprefix tailTrace_1105389
  have hstable : (prefixWord ++ tailWord_1105389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105389).length < 2 ^ (prefixWord ++ tailWord_1105389).sum := by decide
  have hdescent : baseEnd_1105389 < baseStart_1105389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105417 : List Nat := [1, 2, 1, 1, 3, 1, 3, 5, 5]
def baseStart_1105417 : Nat := 118140960795 + 1105417 * 2 ^ 59
def prefixEnd_1105417 : Nat := 4983230072969 + 3 ^ 40 * 1105417 * 2
def baseEnd_1105417 : Nat := 126135609922490396578619

theorem tailTrace_1105417 : CollatzResearch.WordTrace tailWord_1105417 prefixEnd_1105417 126135609922490396578619 := by
  unfold tailWord_1105417
  simp only [CollatzResearch.WordTrace]
  refine ⟨40317870236270474038354505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26878580157513649358903003 40317870236270474038354505)
  ·
    refine ⟨30238402677202855528765879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40317870236270474038354505 30238402677202855528765879)
    ·
      refine ⟨45357604015804283293148819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30238402677202855528765879 45357604015804283293148819)
      ·
        refine ⟨68036406023706424939723229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45357604015804283293148819 68036406023706424939723229)
        ·
          refine ⟨25513652258889909352396211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68036406023706424939723229 25513652258889909352396211)
          ·
            refine ⟨38270478388334864028594317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25513652258889909352396211 38270478388334864028594317)
            ·
              refine ⟨14351429395625574010722869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38270478388334864028594317 14351429395625574010722869)
              ·
                refine ⟨1345446505839897563505269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14351429395625574010722869 1345446505839897563505269)
                ·
                  refine ⟨126135609922490396578619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1345446505839897563505269 126135609922490396578619)
                  ·
                    rfl

theorem cell22_1105417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 5, 5].length) (baseStart_1105417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1105417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1105417 prefixEnd_1105417 := by exact prefixLift 1105417
  have htrace : WordTrace (prefixWord ++ tailWord_1105417) baseStart_1105417 baseEnd_1105417 := by
    simpa [prefixWord, tailWord_1105417, baseEnd_1105417] using wordTrace_append hprefix tailTrace_1105417
  have hstable : (prefixWord ++ tailWord_1105417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105417).length < 2 ^ (prefixWord ++ tailWord_1105417).sum := by decide
  have hdescent : baseEnd_1105417 < baseStart_1105417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105507 : List Nat := [1, 1, 1, 5, 1, 3, 10]
def baseStart_1105507 : Nat := 118140960795 + 1105507 * 2 ^ 59
def prefixEnd_1105507 : Nat := 4983230072969 + 3 ^ 40 * 1105507 * 2
def baseEnd_1105507 : Nat := 14016208837286702036503

theorem tailTrace_1105507 : CollatzResearch.WordTrace tailWord_1105507 prefixEnd_1105507 14016208837286702036503 := by
  unfold tailWord_1105507
  simp only [CollatzResearch.WordTrace]
  refine ⟨40321152805944419409130775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26880768537296279606087183 40321152805944419409130775)
  ·
    refine ⟨60481729208916629113696163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40321152805944419409130775 60481729208916629113696163)
    ·
      refine ⟨90722593813374943670544245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60481729208916629113696163 90722593813374943670544245)
      ·
        refine ⟨8505243170003900969113523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 90722593813374943670544245 8505243170003900969113523)
        ·
          refine ⟨12757864755005851453670285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8505243170003900969113523 12757864755005851453670285)
          ·
            refine ⟨4784199283127194295126357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12757864755005851453670285 4784199283127194295126357)
            ·
              refine ⟨14016208837286702036503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4784199283127194295126357 14016208837286702036503)
              ·
                rfl

theorem cell22_1105507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 10].length) (baseStart_1105507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1105507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1105507 prefixEnd_1105507 := by exact prefixLift 1105507
  have htrace : WordTrace (prefixWord ++ tailWord_1105507) baseStart_1105507 baseEnd_1105507 := by
    simpa [prefixWord, tailWord_1105507, baseEnd_1105507] using wordTrace_append hprefix tailTrace_1105507
  have hstable : (prefixWord ++ tailWord_1105507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105507).length < 2 ^ (prefixWord ++ tailWord_1105507).sum := by decide
  have hdescent : baseEnd_1105507 < baseStart_1105507 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105509 : List Nat := [1, 3, 1, 3, 3, 1, 1, 1, 4, 4]
def baseStart_1105509 : Nat := 118140960795 + 1105509 * 2 ^ 59
def prefixEnd_1105509 : Nat := 4983230072969 + 3 ^ 40 * 1105509 * 2
def baseEnd_1105509 : Nat := 378438323247613616435575

theorem tailTrace_1105509 : CollatzResearch.WordTrace tailWord_1105509 prefixEnd_1105509 378438323247613616435575 := by
  unfold tailWord_1105509
  simp only [CollatzResearch.WordTrace]
  refine ⟨40321225751937173750703581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26880817167958115833802387 40321225751937173750703581)
  ·
    refine ⟨15120459656976440156513843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40321225751937173750703581 15120459656976440156513843)
    ·
      refine ⟨22680689485464660234770765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15120459656976440156513843 22680689485464660234770765)
      ·
        refine ⟨8505258557049247588039037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22680689485464660234770765 8505258557049247588039037)
        ·
          refine ⟨3189471958893467845514639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8505258557049247588039037 3189471958893467845514639)
          ·
            refine ⟨4784207938340201768271959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3189471958893467845514639 4784207938340201768271959)
            ·
              refine ⟨7176311907510302652407939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4784207938340201768271959 7176311907510302652407939)
              ·
                refine ⟨10764467861265453978611909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7176311907510302652407939 10764467861265453978611909)
                ·
                  refine ⟨2018337723987272620989733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10764467861265453978611909 2018337723987272620989733)
                  ·
                    refine ⟨378438323247613616435575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2018337723987272620989733 378438323247613616435575)
                    ·
                      rfl

theorem cell22_1105509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 4, 4].length) (baseStart_1105509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1105509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1105509 prefixEnd_1105509 := by exact prefixLift 1105509
  have htrace : WordTrace (prefixWord ++ tailWord_1105509) baseStart_1105509 baseEnd_1105509 := by
    simpa [prefixWord, tailWord_1105509, baseEnd_1105509] using wordTrace_append hprefix tailTrace_1105509
  have hstable : (prefixWord ++ tailWord_1105509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105509).length < 2 ^ (prefixWord ++ tailWord_1105509).sum := by decide
  have hdescent : baseEnd_1105509 < baseStart_1105509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105539 : List Nat := [1, 1, 1, 3, 3, 1, 1, 3, 5, 3]
def baseStart_1105539 : Nat := 118140960795 + 1105539 * 2 ^ 59
def prefixEnd_1105539 : Nat := 4983230072969 + 3 ^ 40 * 1105539 * 2
def baseEnd_1105539 : Nat := 378448592860703538185483

theorem tailTrace_1105539 : CollatzResearch.WordTrace tailWord_1105539 prefixEnd_1105539 378448592860703538185483 := by
  unfold tailWord_1105539
  simp only [CollatzResearch.WordTrace]
  refine ⟨40322319941828488874295671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26881546627885659249530447 40322319941828488874295671)
  ·
    refine ⟨60483479912742733311443507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40322319941828488874295671 60483479912742733311443507)
    ·
      refine ⟨90725219869114099967165261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60483479912742733311443507 90725219869114099967165261)
      ·
        refine ⟨34021957450917787487686973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90725219869114099967165261 34021957450917787487686973)
        ·
          refine ⟨12758234044094170307882615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34021957450917787487686973 12758234044094170307882615)
          ·
            refine ⟨19137351066141255461823923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12758234044094170307882615 19137351066141255461823923)
            ·
              refine ⟨28706026599211883192735885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19137351066141255461823923 28706026599211883192735885)
              ·
                refine ⟨10764759974704456197275957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28706026599211883192735885 10764759974704456197275957)
                ·
                  refine ⟨1009196247628542768494621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10764759974704456197275957 1009196247628542768494621)
                  ·
                    refine ⟨378448592860703538185483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1009196247628542768494621 378448592860703538185483)
                    ·
                      rfl

theorem cell22_1105539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 5, 3].length) (baseStart_1105539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1105539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1105539 prefixEnd_1105539 := by exact prefixLift 1105539
  have htrace : WordTrace (prefixWord ++ tailWord_1105539) baseStart_1105539 baseEnd_1105539 := by
    simpa [prefixWord, tailWord_1105539, baseEnd_1105539] using wordTrace_append hprefix tailTrace_1105539
  have hstable : (prefixWord ++ tailWord_1105539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105539).length < 2 ^ (prefixWord ++ tailWord_1105539).sum := by decide
  have hdescent : baseEnd_1105539 < baseStart_1105539 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105552 : List Nat := [2, 1, 1, 1, 1, 1, 3, 3, 9]
def baseStart_1105552 : Nat := 118140960795 + 1105552 * 2 ^ 59
def prefixEnd_1105552 : Nat := 4983230072969 + 3 ^ 40 * 1105552 * 2
def baseEnd_1105552 : Nat := 126151014342125279203481

theorem tailTrace_1105552 : CollatzResearch.WordTrace tailWord_1105552 prefixEnd_1105552 126151014342125279203481 := by
  unfold tailWord_1105552
  simp only [CollatzResearch.WordTrace]
  refine ⟨20161397045390696047259455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26881862727187594729679273 20161397045390696047259455)
  ·
    refine ⟨30242095568086044070889183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20161397045390696047259455 30242095568086044070889183)
    ·
      refine ⟨45363143352129066106333775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30242095568086044070889183 45363143352129066106333775)
      ·
        refine ⟨68044715028193599159500663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45363143352129066106333775 68044715028193599159500663)
        ·
          refine ⟨102067072542290398739250995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68044715028193599159500663 102067072542290398739250995)
          ·
            refine ⟨153100608813435598108876493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102067072542290398739250995 153100608813435598108876493)
            ·
              refine ⟨57412728305038349290828685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 153100608813435598108876493 57412728305038349290828685)
              ·
                refine ⟨21529773114389380984060757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57412728305038349290828685 21529773114389380984060757)
                ·
                  refine ⟨126151014342125279203481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 21529773114389380984060757 126151014342125279203481)
                  ·
                    rfl

theorem cell22_1105552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 9].length) (baseStart_1105552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1105552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1105552 prefixEnd_1105552 := by exact prefixLift 1105552
  have htrace : WordTrace (prefixWord ++ tailWord_1105552) baseStart_1105552 baseEnd_1105552 := by
    simpa [prefixWord, tailWord_1105552, baseEnd_1105552] using wordTrace_append hprefix tailTrace_1105552
  have hstable : (prefixWord ++ tailWord_1105552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105552).length < 2 ^ (prefixWord ++ tailWord_1105552).sum := by decide
  have hdescent : baseEnd_1105552 < baseStart_1105552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105590 : List Nat := [5, 1, 3, 1, 1, 2, 1, 2, 3, 3]
def baseStart_1105590 : Nat := 118140960795 + 1105590 * 2 ^ 59
def prefixEnd_1105590 : Nat := 4983230072969 + 3 ^ 40 * 1105590 * 2
def baseEnd_1105590 : Nat := 378466051202956405160327

theorem tailTrace_1105590 : CollatzResearch.WordTrace tailWord_1105590 prefixEnd_1105590 378466051202956405160327 := by
  unfold tailWord_1105590
  simp only [CollatzResearch.WordTrace]
  refine ⟨2520261254040232786525139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26882786709762483056268149 2520261254040232786525139)
  ·
    refine ⟨3780391881060349179787709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2520261254040232786525139 3780391881060349179787709)
    ·
      refine ⟨1417646955397630942420391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3780391881060349179787709 1417646955397630942420391)
      ·
        refine ⟨2126470433096446413630587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1417646955397630942420391 2126470433096446413630587)
        ·
          refine ⟨3189705649644669620445881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2126470433096446413630587 3189705649644669620445881)
          ·
            refine ⟨2392279237233502215334411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3189705649644669620445881 2392279237233502215334411)
            ·
              refine ⟨3588418855850253323001617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2392279237233502215334411 3588418855850253323001617)
              ·
                refine ⟨2691314141887689992251213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3588418855850253323001617 2691314141887689992251213)
                ·
                  refine ⟨1009242803207883747094205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2691314141887689992251213 1009242803207883747094205)
                  ·
                    refine ⟨378466051202956405160327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1009242803207883747094205 378466051202956405160327)
                    ·
                      rfl

theorem cell22_1105590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_1105590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1105590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1105590 prefixEnd_1105590 := by exact prefixLift 1105590
  have htrace : WordTrace (prefixWord ++ tailWord_1105590) baseStart_1105590 baseEnd_1105590 := by
    simpa [prefixWord, tailWord_1105590, baseEnd_1105590] using wordTrace_append hprefix tailTrace_1105590
  have hstable : (prefixWord ++ tailWord_1105590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105590).length < 2 ^ (prefixWord ++ tailWord_1105590).sum := by decide
  have hdescent : baseEnd_1105590 < baseStart_1105590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105599 : List Nat := [1, 1, 2, 2, 2, 3, 1, 3, 3, 4]
def baseStart_1105599 : Nat := 118140960795 + 1105599 * 2 ^ 59
def prefixEnd_1105599 : Nat := 4983230072969 + 3 ^ 40 * 1105599 * 2
def baseEnd_1105599 : Nat := 378469132086883381685299

theorem tailTrace_1105599 : CollatzResearch.WordTrace tailWord_1105599 prefixEnd_1105599 378469132086883381685299 := by
  unfold tailWord_1105599
  simp only [CollatzResearch.WordTrace]
  refine ⟨40324508321611119121479851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26883005547740746080986567 40324508321611119121479851)
  ·
    refine ⟨60486762482416678682219777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40324508321611119121479851 60486762482416678682219777)
    ·
      refine ⟨45365071861812509011664833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60486762482416678682219777 45365071861812509011664833)
      ·
        refine ⟨34023803896359381758748625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45365071861812509011664833 34023803896359381758748625)
        ·
          refine ⟨25517852922269536319061469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34023803896359381758748625 25517852922269536319061469)
          ·
            refine ⟨9569194845851076119648051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25517852922269536319061469 9569194845851076119648051)
            ·
              refine ⟨14353792268776614179472077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9569194845851076119648051 14353792268776614179472077)
              ·
                refine ⟨5382672100791230317302029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14353792268776614179472077 5382672100791230317302029)
                ·
                  refine ⟨2018502037796711368988261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5382672100791230317302029 2018502037796711368988261)
                  ·
                    refine ⟨378469132086883381685299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2018502037796711368988261 378469132086883381685299)
                    ·
                      rfl

theorem cell22_1105599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 3, 3, 4].length) (baseStart_1105599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1105599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1105599 prefixEnd_1105599 := by exact prefixLift 1105599
  have htrace : WordTrace (prefixWord ++ tailWord_1105599) baseStart_1105599 baseEnd_1105599 := by
    simpa [prefixWord, tailWord_1105599, baseEnd_1105599] using wordTrace_append hprefix tailTrace_1105599
  have hstable : (prefixWord ++ tailWord_1105599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105599).length < 2 ^ (prefixWord ++ tailWord_1105599).sum := by decide
  have hdescent : baseEnd_1105599 < baseStart_1105599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105614 : List Nat := [4, 1, 1, 1, 3, 1, 1, 2, 8]
def baseStart_1105614 : Nat := 118140960795 + 1105614 * 2 ^ 59
def prefixEnd_1105614 : Nat := 4983230072969 + 3 ^ 40 * 1105614 * 2
def baseEnd_1105614 : Nat := 126158088964476114186751

theorem tailTrace_1105614 : CollatzResearch.WordTrace tailWord_1105614 prefixEnd_1105614 126158088964476114186751 := by
  unfold tailWord_1105614
  simp only [CollatzResearch.WordTrace]
  refine ⟨5040631927069597085409487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26883370277704517788850597 5040631927069597085409487)
  ·
    refine ⟨7560947890604395628114231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5040631927069597085409487 7560947890604395628114231)
    ·
      refine ⟨11341421835906593442171347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7560947890604395628114231 11341421835906593442171347)
      ·
        refine ⟨17012132753859890163257021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11341421835906593442171347 17012132753859890163257021)
        ·
          refine ⟨6379549782697458811221383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17012132753859890163257021 6379549782697458811221383)
          ·
            refine ⟨9569324674046188216832075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6379549782697458811221383 9569324674046188216832075)
            ·
              refine ⟨14353987011069282325248113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9569324674046188216832075 14353987011069282325248113)
              ·
                refine ⟨10765490258301961743936085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14353987011069282325248113 10765490258301961743936085)
                ·
                  refine ⟨126158088964476114186751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10765490258301961743936085 126158088964476114186751)
                  ·
                    rfl

theorem cell22_1105614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 8].length) (baseStart_1105614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1105614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1105614 prefixEnd_1105614 := by exact prefixLift 1105614
  have htrace : WordTrace (prefixWord ++ tailWord_1105614) baseStart_1105614 baseEnd_1105614 := by
    simpa [prefixWord, tailWord_1105614, baseEnd_1105614] using wordTrace_append hprefix tailTrace_1105614
  have hstable : (prefixWord ++ tailWord_1105614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105614).length < 2 ^ (prefixWord ++ tailWord_1105614).sum := by decide
  have hdescent : baseEnd_1105614 < baseStart_1105614 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105631 : List Nat := [1, 1, 2, 3, 2, 2, 1, 6, 4]
def baseStart_1105631 : Nat := 118140960795 + 1105631 * 2 ^ 59
def prefixEnd_1105631 : Nat := 4983230072969 + 3 ^ 40 * 1105631 * 2
def baseEnd_1105631 : Nat := 126160028780281988295067

theorem tailTrace_1105631 : CollatzResearch.WordTrace tailWord_1105631 prefixEnd_1105631 126160028780281988295067 := by
  unfold tailWord_1105631
  simp only [CollatzResearch.WordTrace]
  refine ⟨40325675457495188586644747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26883783638330125724429831 40325675457495188586644747)
  ·
    refine ⟨60488513186242782879967121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40325675457495188586644747 60488513186242782879967121)
    ·
      refine ⟨45366384889682087159975341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60488513186242782879967121 45366384889682087159975341)
      ·
        refine ⟨17012394333630782684990753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45366384889682087159975341 17012394333630782684990753)
        ·
          refine ⟨12759295750223087013743065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17012394333630782684990753 12759295750223087013743065)
          ·
            refine ⟨9569471812667315260307299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12759295750223087013743065 9569471812667315260307299)
            ·
              refine ⟨14354207719000972890460949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9569471812667315260307299 14354207719000972890460949)
              ·
                refine ⟨672853486828170604240357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14354207719000972890460949 672853486828170604240357)
                ·
                  refine ⟨126160028780281988295067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 672853486828170604240357 126160028780281988295067)
                  ·
                    rfl

theorem cell22_1105631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 6, 4].length) (baseStart_1105631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1105631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1105631 prefixEnd_1105631 := by exact prefixLift 1105631
  have htrace : WordTrace (prefixWord ++ tailWord_1105631) baseStart_1105631 baseEnd_1105631 := by
    simpa [prefixWord, tailWord_1105631, baseEnd_1105631] using wordTrace_append hprefix tailTrace_1105631
  have hstable : (prefixWord ++ tailWord_1105631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105631).length < 2 ^ (prefixWord ++ tailWord_1105631).sum := by decide
  have hdescent : baseEnd_1105631 < baseStart_1105631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105644 : List Nat := [2, 2, 1, 1, 2, 2, 3, 2, 1, 6]
def baseStart_1105644 : Nat := 118140960795 + 1105644 * 2 ^ 59
def prefixEnd_1105644 : Nat := 4983230072969 + 3 ^ 40 * 1105644 * 2
def baseEnd_1105644 : Nat := 378484536506518264310161

theorem tailTrace_1105644 : CollatzResearch.WordTrace tailWord_1105644 prefixEnd_1105644 378484536506518264310161 := by
  unfold tailWord_1105644
  simp only [CollatzResearch.WordTrace]
  refine ⟨20163074803224045903433993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26884099737632061204578657 20163074803224045903433993)
  ·
    refine ⟨15122306102418034427575495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20163074803224045903433993 15122306102418034427575495)
    ·
      refine ⟨22683459153627051641363243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15122306102418034427575495 22683459153627051641363243)
      ·
        refine ⟨34025188730440577462044865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22683459153627051641363243 34025188730440577462044865)
        ·
          refine ⟨25518891547830433096533649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34025188730440577462044865 25518891547830433096533649)
          ·
            refine ⟨19139168660872824822400237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25518891547830433096533649 19139168660872824822400237)
            ·
              refine ⟨7177188247827309308400089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19139168660872824822400237 7177188247827309308400089)
              ·
                refine ⟨5382891185870481981300067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7177188247827309308400089 5382891185870481981300067)
                ·
                  refine ⟨8074336778805722971950101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5382891185870481981300067 8074336778805722971950101)
                  ·
                    refine ⟨378484536506518264310161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8074336778805722971950101 378484536506518264310161)
                    ·
                      rfl

theorem cell22_1105644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 6].length) (baseStart_1105644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1105644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1105644 prefixEnd_1105644 := by exact prefixLift 1105644
  have htrace : WordTrace (prefixWord ++ tailWord_1105644) baseStart_1105644 baseEnd_1105644 := by
    simpa [prefixWord, tailWord_1105644, baseEnd_1105644] using wordTrace_append hprefix tailTrace_1105644
  have hstable : (prefixWord ++ tailWord_1105644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105644).length < 2 ^ (prefixWord ++ tailWord_1105644).sum := by decide
  have hdescent : baseEnd_1105644 < baseStart_1105644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105682 : List Nat := [3, 2, 4, 1, 1, 2, 3, 2, 4]
def baseStart_1105682 : Nat := 118140960795 + 1105682 * 2 ^ 59
def prefixEnd_1105682 : Nat := 4983230072969 + 3 ^ 40 * 1105682 * 2
def baseEnd_1105682 : Nat := 126165848227699610620015

theorem tailTrace_1105682 : CollatzResearch.WordTrace tailWord_1105682 prefixEnd_1105682 126165848227699610620015 := by
  unfold tailWord_1105682
  simp only [CollatzResearch.WordTrace]
  refine ⟨10081883895077606074187825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26885023720206949531167533 10081883895077606074187825)
  ·
    refine ⟨7561412921308204555640869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10081883895077606074187825 7561412921308204555640869)
    ·
      refine ⟨1417764922745288354182663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7561412921308204555640869 1417764922745288354182663)
      ·
        refine ⟨2126647384117932531273995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1417764922745288354182663 2126647384117932531273995)
        ·
          refine ⟨3189971076176898796910993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2126647384117932531273995 3189971076176898796910993)
          ·
            refine ⟨2392478307132674097683245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3189971076176898796910993 2392478307132674097683245)
            ·
              refine ⟨897179365174752786631217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2392478307132674097683245 897179365174752786631217)
              ·
                refine ⟨672884523881064589973413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 897179365174752786631217 672884523881064589973413)
                ·
                  refine ⟨126165848227699610620015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 672884523881064589973413 126165848227699610620015)
                  ·
                    rfl

theorem cell22_1105682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 3, 2, 4].length) (baseStart_1105682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1105682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1105682 prefixEnd_1105682 := by exact prefixLift 1105682
  have htrace : WordTrace (prefixWord ++ tailWord_1105682) baseStart_1105682 baseEnd_1105682 := by
    simpa [prefixWord, tailWord_1105682, baseEnd_1105682] using wordTrace_append hprefix tailTrace_1105682
  have hstable : (prefixWord ++ tailWord_1105682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105682).length < 2 ^ (prefixWord ++ tailWord_1105682).sum := by decide
  have hdescent : baseEnd_1105682 < baseStart_1105682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105719 : List Nat := [1, 1, 3, 1, 2, 1, 2, 1, 3, 7]
def baseStart_1105719 : Nat := 118140960795 + 1105719 * 2 ^ 59
def prefixEnd_1105719 : Nat := 4983230072969 + 3 ^ 40 * 1105719 * 2
def baseEnd_1105719 : Nat := 378510210539243068684931

theorem tailTrace_1105719 : CollatzResearch.WordTrace tailWord_1105719 prefixEnd_1105719 378510210539243068684931 := by
  unfold tailWord_1105719
  simp only [CollatzResearch.WordTrace]
  refine ⟨40328885081176379615848211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26885923387450919743898807 40328885081176379615848211)
  ·
    refine ⟨60493327621764569423772317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40328885081176379615848211 60493327621764569423772317)
    ·
      refine ⟨22684997858161713533914619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60493327621764569423772317 22684997858161713533914619)
      ·
        refine ⟨34027496787242570300871929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22684997858161713533914619 34027496787242570300871929)
        ·
          refine ⟨25520622590431927725653947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34027496787242570300871929 25520622590431927725653947)
          ·
            refine ⟨38280933885647891588480921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25520622590431927725653947 38280933885647891588480921)
            ·
              refine ⟨28710700414235918691360691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38280933885647891588480921 28710700414235918691360691)
              ·
                refine ⟨43066050621353878037041037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28710700414235918691360691 43066050621353878037041037)
                ·
                  refine ⟨16149768983007704263890389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43066050621353878037041037 16149768983007704263890389)
                  ·
                    refine ⟨378510210539243068684931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16149768983007704263890389 378510210539243068684931)
                    ·
                      rfl

theorem cell22_1105719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 7].length) (baseStart_1105719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1105719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1105719 prefixEnd_1105719 := by exact prefixLift 1105719
  have htrace : WordTrace (prefixWord ++ tailWord_1105719) baseStart_1105719 baseEnd_1105719 := by
    simpa [prefixWord, tailWord_1105719, baseEnd_1105719] using wordTrace_append hprefix tailTrace_1105719
  have hstable : (prefixWord ++ tailWord_1105719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105719).length < 2 ^ (prefixWord ++ tailWord_1105719).sum := by decide
  have hdescent : baseEnd_1105719 < baseStart_1105719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105768 : List Nat := [2, 1, 4, 2, 1, 1, 2, 4, 1, 4]
def baseStart_1105768 : Nat := 118140960795 + 1105768 * 2 ^ 59
def prefixEnd_1105768 : Nat := 4983230072969 + 3 ^ 40 * 1105768 * 2
def baseEnd_1105768 : Nat := 378526984240623274209781

theorem tailTrace_1105768 : CollatzResearch.WordTrace tailWord_1105768 prefixEnd_1105768 378526984240623274209781 := by
  unfold tailWord_1105768
  simp only [CollatzResearch.WordTrace]
  refine ⟨20165336128999430492190979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26887114838665907322921305 20165336128999430492190979)
  ·
    refine ⟨30248004193499145738286469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20165336128999430492190979 30248004193499145738286469)
    ·
      refine ⟨5671500786281089825928713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30248004193499145738286469 5671500786281089825928713)
      ·
        refine ⟨4253625589710817369446535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5671500786281089825928713 4253625589710817369446535)
        ·
          refine ⟨6380438384566226054169803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4253625589710817369446535 6380438384566226054169803)
          ·
            refine ⟨9570657576849339081254705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6380438384566226054169803 9570657576849339081254705)
            ·
              refine ⟨7177993182637004310941029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9570657576849339081254705 7177993182637004310941029)
              ·
                refine ⟨1345873721744438308301443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7177993182637004310941029 1345873721744438308301443)
                ·
                  refine ⟨2018810582616657462452165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1345873721744438308301443 2018810582616657462452165)
                  ·
                    refine ⟨378526984240623274209781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2018810582616657462452165 378526984240623274209781)
                    ·
                      rfl

theorem cell22_1105768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_1105768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1105768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1105768 prefixEnd_1105768 := by exact prefixLift 1105768
  have htrace : WordTrace (prefixWord ++ tailWord_1105768) baseStart_1105768 baseEnd_1105768 := by
    simpa [prefixWord, tailWord_1105768, baseEnd_1105768] using wordTrace_append hprefix tailTrace_1105768
  have hstable : (prefixWord ++ tailWord_1105768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105768).length < 2 ^ (prefixWord ++ tailWord_1105768).sum := by decide
  have hdescent : baseEnd_1105768 < baseStart_1105768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105828 : List Nat := [2, 3, 1, 2, 1, 3, 4, 6]
def baseStart_1105828 : Nat := 118140960795 + 1105828 * 2 ^ 59
def prefixEnd_1105828 : Nat := 4983230072969 + 3 ^ 40 * 1105828 * 2
def baseEnd_1105828 : Nat := 42060835940755901967733

theorem tailTrace_1105828 : CollatzResearch.WordTrace tailWord_1105828 prefixEnd_1105828 42060835940755901967733 := by
  unfold tailWord_1105828
  simp only [CollatzResearch.WordTrace]
  refine ⟨20166430318890745615783069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26888573758520994154377425 20166430318890745615783069)
  ·
    refine ⟨7562411369584029605918651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20166430318890745615783069 7562411369584029605918651)
    ·
      refine ⟨11343617054376044408877977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7562411369584029605918651 11343617054376044408877977)
      ·
        refine ⟨8507712790782033306658483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11343617054376044408877977 8507712790782033306658483)
        ·
          refine ⟨12761569186173049959987725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8507712790782033306658483 12761569186173049959987725)
          ·
            refine ⟨4785588444814893734995397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12761569186173049959987725 4785588444814893734995397)
            ·
              refine ⟨897297833402792575311637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4785588444814893734995397 897297833402792575311637)
              ·
                refine ⟨42060835940755901967733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 897297833402792575311637 42060835940755901967733)
                ·
                  rfl

theorem cell22_1105828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 4, 6].length) (baseStart_1105828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1105828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1105828 prefixEnd_1105828 := by exact prefixLift 1105828
  have htrace : WordTrace (prefixWord ++ tailWord_1105828) baseStart_1105828 baseEnd_1105828 := by
    simpa [prefixWord, tailWord_1105828, baseEnd_1105828] using wordTrace_append hprefix tailTrace_1105828
  have hstable : (prefixWord ++ tailWord_1105828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105828).length < 2 ^ (prefixWord ++ tailWord_1105828).sum := by decide
  have hdescent : baseEnd_1105828 < baseStart_1105828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105856 : List Nat := [2, 1, 1, 2, 3, 2, 1, 3, 7]
def baseStart_1105856 : Nat := 118140960795 + 1105856 * 2 ^ 59
def prefixEnd_1105856 : Nat := 4983230072969 + 3 ^ 40 * 1105856 * 2
def baseEnd_1105856 : Nat := 126185702813006792669837

theorem tailTrace_1105856 : CollatzResearch.WordTrace tailWord_1105856 prefixEnd_1105856 126185702813006792669837 := by
  unfold tailWord_1105856
  simp only [CollatzResearch.WordTrace]
  refine ⟨20166940940840026006792711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26889254587786701342390281 20166940940840026006792711)
  ·
    refine ⟨30250411411260039010189067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20166940940840026006792711 30250411411260039010189067)
    ·
      refine ⟨45375617116890058515283601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30250411411260039010189067 45375617116890058515283601)
      ·
        refine ⟨34031712837667543886462701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45375617116890058515283601 34031712837667543886462701)
        ·
          refine ⟨12761892314125328957423513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34031712837667543886462701 12761892314125328957423513)
          ·
            refine ⟨9571419235593996718067635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12761892314125328957423513 9571419235593996718067635)
            ·
              refine ⟨14357128853390995077101453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9571419235593996718067635 14357128853390995077101453)
              ·
                refine ⟨5383923320021623153913045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14357128853390995077101453 5383923320021623153913045)
                ·
                  refine ⟨126185702813006792669837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5383923320021623153913045 126185702813006792669837)
                  ·
                    rfl

theorem cell22_1105856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 3, 7].length) (baseStart_1105856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1105856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1105856 prefixEnd_1105856 := by exact prefixLift 1105856
  have htrace : WordTrace (prefixWord ++ tailWord_1105856) baseStart_1105856 baseEnd_1105856 := by
    simpa [prefixWord, tailWord_1105856, baseEnd_1105856] using wordTrace_append hprefix tailTrace_1105856
  have hstable : (prefixWord ++ tailWord_1105856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105856).length < 2 ^ (prefixWord ++ tailWord_1105856).sum := by decide
  have hdescent : baseEnd_1105856 < baseStart_1105856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105871 : List Nat := [1, 1, 2, 1, 1, 5, 2, 1, 1, 7]
def baseStart_1105871 : Nat := 118140960795 + 1105871 * 2 ^ 59
def prefixEnd_1105871 : Nat := 4983230072969 + 3 ^ 40 * 1105871 * 2
def baseEnd_1105871 : Nat := 378562243245565338884465

theorem tailTrace_1105871 : CollatzResearch.WordTrace tailWord_1105871 prefixEnd_1105871 378562243245565338884465 := by
  unfold tailWord_1105871
  simp only [CollatzResearch.WordTrace]
  refine ⟨40334428976625709575381467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26889619317750473050254311 40334428976625709575381467)
  ·
    refine ⟨60501643464938564363072201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40334428976625709575381467 60501643464938564363072201)
    ·
      refine ⟨45376232598703923272304151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60501643464938564363072201 45376232598703923272304151)
      ·
        refine ⟨68064348898055884908456227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45376232598703923272304151 68064348898055884908456227)
        ·
          refine ⟨102096523347083827362684341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68064348898055884908456227 102096523347083827362684341)
          ·
            refine ⟨9571549063789108815251657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 102096523347083827362684341 9571549063789108815251657)
            ·
              refine ⟨7178661797841831611438743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9571549063789108815251657 7178661797841831611438743)
              ·
                refine ⟨10767992696762747417158115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7178661797841831611438743 10767992696762747417158115)
                ·
                  refine ⟨16151989045144121125737173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10767992696762747417158115 16151989045144121125737173)
                  ·
                    refine ⟨378562243245565338884465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16151989045144121125737173 378562243245565338884465)
                    ·
                      rfl

theorem cell22_1105871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 7].length) (baseStart_1105871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1105871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1105871 prefixEnd_1105871 := by exact prefixLift 1105871
  have htrace : WordTrace (prefixWord ++ tailWord_1105871) baseStart_1105871 baseEnd_1105871 := by
    simpa [prefixWord, tailWord_1105871, baseEnd_1105871] using wordTrace_append hprefix tailTrace_1105871
  have hstable : (prefixWord ++ tailWord_1105871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105871).length < 2 ^ (prefixWord ++ tailWord_1105871).sum := by decide
  have hdescent : baseEnd_1105871 < baseStart_1105871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106008 : List Nat := [2, 1, 2, 2, 1, 4, 1, 2, 7]
def baseStart_1106008 : Nat := 118140960795 + 1106008 * 2 ^ 59
def prefixEnd_1106008 : Nat := 4983230072969 + 3 ^ 40 * 1106008 * 2
def baseEnd_1106008 : Nat := 126203047048447549403015

theorem tailTrace_1106008 : CollatzResearch.WordTrace tailWord_1106008 prefixEnd_1106008 126203047048447549403015 := by
  unfold tailWord_1106008
  simp only [CollatzResearch.WordTrace]
  refine ⟨20169712888564690986559339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26892950518086254648745785 20169712888564690986559339)
  ·
    refine ⟨30254569332847036479839009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20169712888564690986559339 30254569332847036479839009)
    ·
      refine ⟨22690926999635277359879257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30254569332847036479839009 22690926999635277359879257)
      ·
        refine ⟨17018195249726458019909443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22690926999635277359879257 17018195249726458019909443)
        ·
          refine ⟨25527292874589687029864165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17018195249726458019909443 25527292874589687029864165)
          ·
            refine ⟨4786367413985566318099531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25527292874589687029864165 4786367413985566318099531)
            ·
              refine ⟨7179551120978349477149297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4786367413985566318099531 7179551120978349477149297)
              ·
                refine ⟨5384663340733762107861973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7179551120978349477149297 5384663340733762107861973)
                ·
                  refine ⟨126203047048447549403015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5384663340733762107861973 126203047048447549403015)
                  ·
                    rfl

theorem cell22_1106008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 2, 7].length) (baseStart_1106008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1106008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1106008 prefixEnd_1106008 := by exact prefixLift 1106008
  have htrace : WordTrace (prefixWord ++ tailWord_1106008) baseStart_1106008 baseEnd_1106008 := by
    simpa [prefixWord, tailWord_1106008, baseEnd_1106008] using wordTrace_append hprefix tailTrace_1106008
  have hstable : (prefixWord ++ tailWord_1106008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106008).length < 2 ^ (prefixWord ++ tailWord_1106008).sum := by decide
  have hdescent : baseEnd_1106008 < baseStart_1106008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106014 : List Nat := [4, 4, 1, 1, 2, 2, 8]
def baseStart_1106014 : Nat := 118140960795 + 1106014 * 2 ^ 59
def prefixEnd_1106014 : Nat := 4983230072969 + 3 ^ 40 * 1106014 * 2
def baseEnd_1106014 : Nat := 14022636854368912317001

theorem tailTrace_1106014 : CollatzResearch.WordTrace tailWord_1106014 prefixEnd_1106014 14022636854368912317001 := by
  unfold tailWord_1106014
  simp only [CollatzResearch.WordTrace]
  refine ⟨5042455576888455624729637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26893096410071763331891397 5042455576888455624729637)
  ·
    refine ⟨945460420666585429636807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5042455576888455624729637 945460420666585429636807)
    ·
      refine ⟨1418190630999878144455211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 945460420666585429636807 1418190630999878144455211)
      ·
        refine ⟨2127285946499817216682817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1418190630999878144455211 2127285946499817216682817)
        ·
          refine ⟨1595464459874862912512113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2127285946499817216682817 1595464459874862912512113)
          ·
            refine ⟨1196598344906147184384085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1595464459874862912512113 1196598344906147184384085)
            ·
              refine ⟨14022636854368912317001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1196598344906147184384085 14022636854368912317001)
              ·
                rfl

theorem cell22_1106014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 8].length) (baseStart_1106014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1106014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1106014 prefixEnd_1106014 := by exact prefixLift 1106014
  have htrace : WordTrace (prefixWord ++ tailWord_1106014) baseStart_1106014 baseEnd_1106014 := by
    simpa [prefixWord, tailWord_1106014, baseEnd_1106014] using wordTrace_append hprefix tailTrace_1106014
  have hstable : (prefixWord ++ tailWord_1106014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106014).length < 2 ^ (prefixWord ++ tailWord_1106014).sum := by decide
  have hdescent : baseEnd_1106014 < baseStart_1106014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106083 : List Nat := [1, 1, 1, 4, 1, 1, 1, 1, 5, 6]
def baseStart_1106083 : Nat := 118140960795 + 1106083 * 2 ^ 59
def prefixEnd_1106083 : Nat := 4983230072969 + 3 ^ 40 * 1106083 * 2
def baseEnd_1106083 : Nat := 378634815178067452583815

theorem tailTrace_1106083 : CollatzResearch.WordTrace tailWord_1106083 prefixEnd_1106083 378634815178067452583815 := by
  unfold tailWord_1106083
  simp only [CollatzResearch.WordTrace]
  refine ⟨40342161251857669782098903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26894774167905113188065935 40342161251857669782098903)
  ·
    refine ⟨60513241877786504673148355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40342161251857669782098903 60513241877786504673148355)
    ·
      refine ⟨90769862816679757009722533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60513241877786504673148355 90769862816679757009722533)
      ·
        refine ⟨17019349278127454439322975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 90769862816679757009722533 17019349278127454439322975)
        ·
          refine ⟨25529023917191181658984463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17019349278127454439322975 25529023917191181658984463)
          ·
            refine ⟨38293535875786772488476695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25529023917191181658984463 38293535875786772488476695)
            ·
              refine ⟨57440303813680158732715043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38293535875786772488476695 57440303813680158732715043)
              ·
                refine ⟨86160455720520238099072565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57440303813680158732715043 86160455720520238099072565)
                ·
                  refine ⟨8077542723798772321788053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 86160455720520238099072565 8077542723798772321788053)
                  ·
                    refine ⟨378634815178067452583815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8077542723798772321788053 378634815178067452583815)
                    ·
                      rfl

theorem cell22_1106083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 5, 6].length) (baseStart_1106083 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1106083 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1106083 prefixEnd_1106083 := by exact prefixLift 1106083
  have htrace : WordTrace (prefixWord ++ tailWord_1106083) baseStart_1106083 baseEnd_1106083 := by
    simpa [prefixWord, tailWord_1106083, baseEnd_1106083] using wordTrace_append hprefix tailTrace_1106083
  have hstable : (prefixWord ++ tailWord_1106083).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106083).length < 2 ^ (prefixWord ++ tailWord_1106083).sum := by decide
  have hdescent : baseEnd_1106083 < baseStart_1106083 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106160 : List Nat := [2, 1, 1, 1, 3, 1, 1, 7, 5]
def baseStart_1106160 : Nat := 118140960795 + 1106160 * 2 ^ 59
def prefixEnd_1106160 : Nat := 4983230072969 + 3 ^ 40 * 1106160 * 2
def baseEnd_1106160 : Nat := 126220391283888306136193

theorem tailTrace_1106160 : CollatzResearch.WordTrace tailWord_1106160 prefixEnd_1106160 126220391283888306136193 := by
  unfold tailWord_1106160
  simp only [CollatzResearch.WordTrace]
  refine ⟨20172484836289355966325967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26896646448385807955101289 20172484836289355966325967)
  ·
    refine ⟨30258727254434033949488951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20172484836289355966325967 30258727254434033949488951)
    ·
      refine ⟨45388090881651050924233427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30258727254434033949488951 45388090881651050924233427)
      ·
        refine ⟨68082136322476576386350141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45388090881651050924233427 68082136322476576386350141)
        ·
          refine ⟨25530801120928716144881303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68082136322476576386350141 25530801120928716144881303)
          ·
            refine ⟨38296201681393074217321955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25530801120928716144881303 38296201681393074217321955)
            ·
              refine ⟨57444302522089611325982933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38296201681393074217321955 57444302522089611325982933)
              ·
                refine ⟨1346350840361475265452725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 57444302522089611325982933 1346350840361475265452725)
                ·
                  refine ⟨126220391283888306136193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1346350840361475265452725 126220391283888306136193)
                  ·
                    rfl

theorem cell22_1106160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 7, 5].length) (baseStart_1106160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1106160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1106160 prefixEnd_1106160 := by exact prefixLift 1106160
  have htrace : WordTrace (prefixWord ++ tailWord_1106160) baseStart_1106160 baseEnd_1106160 := by
    simpa [prefixWord, tailWord_1106160, baseEnd_1106160] using wordTrace_append hprefix tailTrace_1106160
  have hstable : (prefixWord ++ tailWord_1106160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106160).length < 2 ^ (prefixWord ++ tailWord_1106160).sum := by decide
  have hdescent : baseEnd_1106160 < baseStart_1106160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106252 : List Nat := [2, 2, 1, 3, 2, 1, 1, 4, 2, 4]
def baseStart_1106252 : Nat := 118140960795 + 1106252 * 2 ^ 59
def prefixEnd_1106252 : Nat := 4983230072969 + 3 ^ 40 * 1106252 * 2
def baseEnd_1106252 : Nat := 378692667331807345108297

theorem tailTrace_1106252 : CollatzResearch.WordTrace tailWord_1106252 prefixEnd_1106252 378692667331807345108297 := by
  unfold tailWord_1106252
  simp only [CollatzResearch.WordTrace]
  refine ⟨20174162594122705822500505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26898883458830274430000673 20174162594122705822500505)
  ·
    refine ⟨15130621945592029366875379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20174162594122705822500505 15130621945592029366875379)
    ·
      refine ⟨22695932918388044050313069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15130621945592029366875379 22695932918388044050313069)
      ·
        refine ⟨8510974844395516518867401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22695932918388044050313069 8510974844395516518867401)
        ·
          refine ⟨6383231133296637389150551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8510974844395516518867401 6383231133296637389150551)
          ·
            refine ⟨9574846699944956083725827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6383231133296637389150551 9574846699944956083725827)
            ·
              refine ⟨14362270049917434125588741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9574846699944956083725827 14362270049917434125588741)
              ·
                refine ⟨2692925634359518898547889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14362270049917434125588741 2692925634359518898547889)
                ·
                  refine ⟨2019694225769639173910917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2692925634359518898547889 2019694225769639173910917)
                  ·
                    refine ⟨378692667331807345108297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2019694225769639173910917 378692667331807345108297)
                    ·
                      rfl

theorem cell22_1106252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 4, 2, 4].length) (baseStart_1106252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1106252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1106252 prefixEnd_1106252 := by exact prefixLift 1106252
  have htrace : WordTrace (prefixWord ++ tailWord_1106252) baseStart_1106252 baseEnd_1106252 := by
    simpa [prefixWord, tailWord_1106252, baseEnd_1106252] using wordTrace_append hprefix tailTrace_1106252
  have hstable : (prefixWord ++ tailWord_1106252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106252).length < 2 ^ (prefixWord ++ tailWord_1106252).sum := by decide
  have hdescent : baseEnd_1106252 < baseStart_1106252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106256 : List Nat := [2, 1, 1, 1, 1, 8, 2, 2, 4]
def baseStart_1106256 : Nat := 118140960795 + 1106256 * 2 ^ 59
def prefixEnd_1106256 : Nat := 4983230072969 + 3 ^ 40 * 1106256 * 2
def baseEnd_1106256 : Nat := 126231345537850889336095

theorem tailTrace_1106256 : CollatzResearch.WordTrace tailWord_1106256 prefixEnd_1106256 126231345537850889336095 := by
  unfold tailWord_1106256
  simp only [CollatzResearch.WordTrace]
  refine ⟨20174235540115460164073311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26898980720153946885431081 20174235540115460164073311)
  ·
    refine ⟨30261353310173190246109967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20174235540115460164073311 30261353310173190246109967)
    ·
      refine ⟨45392029965259785369164951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30261353310173190246109967 45392029965259785369164951)
      ·
        refine ⟨68088044947889678053747427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45392029965259785369164951 68088044947889678053747427)
        ·
          refine ⟨102132067421834517080621141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68088044947889678053747427 102132067421834517080621141)
          ·
            refine ⟨1196860165099623247038529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 102132067421834517080621141 1196860165099623247038529)
            ·
              refine ⟨897645123824717435278897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1196860165099623247038529 897645123824717435278897)
              ·
                refine ⟨673233842868538076459173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 897645123824717435278897 673233842868538076459173)
                ·
                  refine ⟨126231345537850889336095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 673233842868538076459173 126231345537850889336095)
                  ·
                    rfl

theorem cell22_1106256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 2, 2, 4].length) (baseStart_1106256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1106256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1106256 prefixEnd_1106256 := by exact prefixLift 1106256
  have htrace : WordTrace (prefixWord ++ tailWord_1106256) baseStart_1106256 baseEnd_1106256 := by
    simpa [prefixWord, tailWord_1106256, baseEnd_1106256] using wordTrace_append hprefix tailTrace_1106256
  have hstable : (prefixWord ++ tailWord_1106256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106256).length < 2 ^ (prefixWord ++ tailWord_1106256).sum := by decide
  have hdescent : baseEnd_1106256 < baseStart_1106256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106265 : List Nat := [1, 2, 1, 2, 2, 2, 1, 2, 2, 7]
def baseStart_1106265 : Nat := 118140960795 + 1106265 * 2 ^ 59
def prefixEnd_1106265 : Nat := 4983230072969 + 3 ^ 40 * 1106265 * 2
def baseEnd_1106265 : Nat := 378697117497479644533257

theorem tailTrace_1106265 : CollatzResearch.WordTrace tailWord_1106265 prefixEnd_1106265 378697117497479644533257 := by
  unfold tailWord_1106265
  simp only [CollatzResearch.WordTrace]
  refine ⟨40348799337198314865224249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26899199558132209910149499 40348799337198314865224249)
  ·
    refine ⟨30261599502898736148918187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40348799337198314865224249 30261599502898736148918187)
    ·
      refine ⟨45392399254348104223377281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30261599502898736148918187 45392399254348104223377281)
      ·
        refine ⟨34044299440761078167532961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45392399254348104223377281 34044299440761078167532961)
        ·
          refine ⟨25533224580570808625649721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34044299440761078167532961 25533224580570808625649721)
          ·
            refine ⟨19149918435428106469237291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25533224580570808625649721 19149918435428106469237291)
            ·
              refine ⟨28724877653142159703855937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19149918435428106469237291 28724877653142159703855937)
              ·
                refine ⟨21543658239856619777891953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28724877653142159703855937 21543658239856619777891953)
                ·
                  refine ⟨16157743679892464833418965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21543658239856619777891953 16157743679892464833418965)
                  ·
                    refine ⟨378697117497479644533257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16157743679892464833418965 378697117497479644533257)
                    ·
                      rfl

theorem cell22_1106265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 7].length) (baseStart_1106265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1106265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1106265 prefixEnd_1106265 := by exact prefixLift 1106265
  have htrace : WordTrace (prefixWord ++ tailWord_1106265) baseStart_1106265 baseEnd_1106265 := by
    simpa [prefixWord, tailWord_1106265, baseEnd_1106265] using wordTrace_append hprefix tailTrace_1106265
  have hstable : (prefixWord ++ tailWord_1106265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106265).length < 2 ^ (prefixWord ++ tailWord_1106265).sum := by decide
  have hdescent : baseEnd_1106265 < baseStart_1106265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106284 : List Nat := [2, 2, 1, 1, 6, 1, 3, 6]
def baseStart_1106284 : Nat := 118140960795 + 1106284 * 2 ^ 59
def prefixEnd_1106284 : Nat := 4983230072969 + 3 ^ 40 * 1106284 * 2
def baseEnd_1106284 : Nat := 42078180176196658700911

theorem tailTrace_1106284 : CollatzResearch.WordTrace tailWord_1106284 prefixEnd_1106284 42078180176196658700911 := by
  unfold tailWord_1106284
  simp only [CollatzResearch.WordTrace]
  refine ⟨20174746162064740555082953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26899661549419654073443937 20174746162064740555082953)
  ·
    refine ⟨15131059621548555416312215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20174746162064740555082953 15131059621548555416312215)
    ·
      refine ⟨22696589432322833124468323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15131059621548555416312215 22696589432322833124468323)
      ·
        refine ⟨34044884148484249686702485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22696589432322833124468323 34044884148484249686702485)
        ·
          refine ⟨1595853944460199204064179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 34044884148484249686702485 1595853944460199204064179)
          ·
            refine ⟨2393780916690298806096269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1595853944460199204064179 2393780916690298806096269)
            ·
              refine ⟨897667843758862052286101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2393780916690298806096269 897667843758862052286101)
              ·
                refine ⟨42078180176196658700911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 897667843758862052286101 42078180176196658700911)
                ·
                  rfl

theorem cell22_1106284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 3, 6].length) (baseStart_1106284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1106284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1106284 prefixEnd_1106284 := by exact prefixLift 1106284
  have htrace : WordTrace (prefixWord ++ tailWord_1106284) baseStart_1106284 baseEnd_1106284 := by
    simpa [prefixWord, tailWord_1106284, baseEnd_1106284] using wordTrace_append hprefix tailTrace_1106284
  have hstable : (prefixWord ++ tailWord_1106284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106284).length < 2 ^ (prefixWord ++ tailWord_1106284).sum := by decide
  have hdescent : baseEnd_1106284 < baseStart_1106284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106312 : List Nat := [2, 1, 3, 3, 1, 1, 3, 1, 7]
def baseStart_1106312 : Nat := 118140960795 + 1106312 * 2 ^ 59
def prefixEnd_1106312 : Nat := 4983230072969 + 3 ^ 40 * 1106312 * 2
def baseEnd_1106312 : Nat := 126237735519329062869371

theorem tailTrace_1106312 : CollatzResearch.WordTrace tailWord_1106312 prefixEnd_1106312 126237735519329062869371 := by
  unfold tailWord_1106312
  simp only [CollatzResearch.WordTrace]
  refine ⟨20175256784014020946092595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26900342378685361261456793 20175256784014020946092595)
  ·
    refine ⟨30262885176021031419138893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20175256784014020946092595 30262885176021031419138893)
    ·
      refine ⟨11348581941007886782177085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30262885176021031419138893 11348581941007886782177085)
      ·
        refine ⟨4255718227877957543316407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11348581941007886782177085 4255718227877957543316407)
        ·
          refine ⟨6383577341816936314974611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4255718227877957543316407 6383577341816936314974611)
          ·
            refine ⟨9575366012725404472461917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6383577341816936314974611 9575366012725404472461917)
            ·
              refine ⟨3590762254772026677173219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9575366012725404472461917 3590762254772026677173219)
              ·
                refine ⟨5386143382158040015759829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3590762254772026677173219 5386143382158040015759829)
                ·
                  refine ⟨126237735519329062869371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5386143382158040015759829 126237735519329062869371)
                  ·
                    rfl

theorem cell22_1106312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 1, 7].length) (baseStart_1106312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1106312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1106312 prefixEnd_1106312 := by exact prefixLift 1106312
  have htrace : WordTrace (prefixWord ++ tailWord_1106312) baseStart_1106312 baseEnd_1106312 := by
    simpa [prefixWord, tailWord_1106312, baseEnd_1106312] using wordTrace_append hprefix tailTrace_1106312
  have hstable : (prefixWord ++ tailWord_1106312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106312).length < 2 ^ (prefixWord ++ tailWord_1106312).sum := by decide
  have hdescent : baseEnd_1106312 < baseStart_1106312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106316 : List Nat := [2, 2, 1, 2, 1, 4, 2, 4, 1, 3]
def baseStart_1106316 : Nat := 118140960795 + 1106316 * 2 ^ 59
def prefixEnd_1106316 : Nat := 4983230072969 + 3 ^ 40 * 1106316 * 2
def baseEnd_1106316 : Nat := 378714575839732511508101

theorem tailTrace_1106316 : CollatzResearch.WordTrace tailWord_1106316 prefixEnd_1106316 378714575839732511508101 := by
  unfold tailWord_1106316
  simp only [CollatzResearch.WordTrace]
  refine ⟨20175329730006775287665401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26900439640009033716887201 20175329730006775287665401)
  ·
    refine ⟨15131497297505081465749051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20175329730006775287665401 15131497297505081465749051)
    ·
      refine ⟨22697245946257622198623577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15131497297505081465749051 22697245946257622198623577)
      ·
        refine ⟨17022934459693216648967683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22697245946257622198623577 17022934459693216648967683)
        ·
          refine ⟨25534401689539824973451525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17022934459693216648967683 25534401689539824973451525)
          ·
            refine ⟨4787700316788717182522161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25534401689539824973451525 4787700316788717182522161)
            ·
              refine ⟨3590775237591537886891621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4787700316788717182522161 3590775237591537886891621)
              ·
                refine ⟨673270357048413353792179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3590775237591537886891621 673270357048413353792179)
                ·
                  refine ⟨1009905535572620030688269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 673270357048413353792179 1009905535572620030688269)
                  ·
                    refine ⟨378714575839732511508101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1009905535572620030688269 378714575839732511508101)
                    ·
                      rfl

theorem cell22_1106316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 4, 1, 3].length) (baseStart_1106316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1106316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1106316 prefixEnd_1106316 := by exact prefixLift 1106316
  have htrace : WordTrace (prefixWord ++ tailWord_1106316) baseStart_1106316 baseEnd_1106316 := by
    simpa [prefixWord, tailWord_1106316, baseEnd_1106316] using wordTrace_append hprefix tailTrace_1106316
  have hstable : (prefixWord ++ tailWord_1106316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106316).length < 2 ^ (prefixWord ++ tailWord_1106316).sum := by decide
  have hdescent : baseEnd_1106316 < baseStart_1106316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106327 : List Nat := [1, 1, 3, 3, 1, 1, 4, 1, 2, 5]
def baseStart_1106327 : Nat := 118140960795 + 1106327 * 2 ^ 59
def prefixEnd_1106327 : Nat := 4983230072969 + 3 ^ 40 * 1106327 * 2
def baseEnd_1106327 : Nat := 378718341364532149483067

theorem tailTrace_1106327 : CollatzResearch.WordTrace tailWord_1106327 prefixEnd_1106327 378718341364532149483067 := by
  unfold tailWord_1106327
  simp only [CollatzResearch.WordTrace]
  refine ⟨40351060662973699453981235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26900707108649132969320823 40351060662973699453981235)
  ·
    refine ⟨60526590994460549180971853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40351060662973699453981235 60526590994460549180971853)
    ·
      refine ⟨22697471622922705942864445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60526590994460549180971853 22697471622922705942864445)
      ·
        refine ⟨8511551858596014728574167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22697471622922705942864445 8511551858596014728574167)
        ·
          refine ⟨12767327787894022092861251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8511551858596014728574167 12767327787894022092861251)
          ·
            refine ⟨19150991681841033139291877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12767327787894022092861251 19150991681841033139291877)
            ·
              refine ⟨3590810940345193713617227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19150991681841033139291877 3590810940345193713617227)
              ·
                refine ⟨5386216410517790570425841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3590810940345193713617227 5386216410517790570425841)
                ·
                  refine ⟨4039662307888342927819381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5386216410517790570425841 4039662307888342927819381)
                  ·
                    refine ⟨378718341364532149483067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4039662307888342927819381 378718341364532149483067)
                    ·
                      rfl

theorem cell22_1106327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 1, 2, 5].length) (baseStart_1106327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1106327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1106327 prefixEnd_1106327 := by exact prefixLift 1106327
  have htrace : WordTrace (prefixWord ++ tailWord_1106327) baseStart_1106327 baseEnd_1106327 := by
    simpa [prefixWord, tailWord_1106327, baseEnd_1106327] using wordTrace_append hprefix tailTrace_1106327
  have hstable : (prefixWord ++ tailWord_1106327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106327).length < 2 ^ (prefixWord ++ tailWord_1106327).sum := by decide
  have hdescent : baseEnd_1106327 < baseStart_1106327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106329 : List Nat := [1, 2, 1, 2, 1, 4, 5, 1, 5]
def baseStart_1106329 : Nat := 118140960795 + 1106329 * 2 ^ 59
def prefixEnd_1106329 : Nat := 4983230072969 + 3 ^ 40 * 1106329 * 2
def baseEnd_1106329 : Nat := 126239675335134936977687

theorem tailTrace_1106329 : CollatzResearch.WordTrace tailWord_1106329 prefixEnd_1106329 126239675335134936977687 := by
  unfold tailWord_1106329
  simp only [CollatzResearch.WordTrace]
  refine ⟨40351133608966453795554041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26900755739310969197036027 40351133608966453795554041)
  ·
    refine ⟨30263350206724840346665531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40351133608966453795554041 30263350206724840346665531)
    ·
      refine ⟨45395025310087260519998297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30263350206724840346665531 45395025310087260519998297)
      ·
        refine ⟨34046268982565445389998723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45395025310087260519998297 34046268982565445389998723)
        ·
          refine ⟨51069403473848168084998085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34046268982565445389998723 51069403473848168084998085)
          ·
            refine ⟨9575513151346531515937141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51069403473848168084998085 9575513151346531515937141)
            ·
              refine ⟨897704357938737329619107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9575513151346531515937141 897704357938737329619107)
              ·
                refine ⟨1346556536908105994428661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 897704357938737329619107 1346556536908105994428661)
                ·
                  refine ⟨126239675335134936977687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1346556536908105994428661 126239675335134936977687)
                  ·
                    rfl

theorem cell22_1106329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 5, 1, 5].length) (baseStart_1106329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1106329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1106329 prefixEnd_1106329 := by exact prefixLift 1106329
  have htrace : WordTrace (prefixWord ++ tailWord_1106329) baseStart_1106329 baseEnd_1106329 := by
    simpa [prefixWord, tailWord_1106329, baseEnd_1106329] using wordTrace_append hprefix tailTrace_1106329
  have hstable : (prefixWord ++ tailWord_1106329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106329).length < 2 ^ (prefixWord ++ tailWord_1106329).sum := by decide
  have hdescent : baseEnd_1106329 < baseStart_1106329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106359 : List Nat := [1, 1, 3, 1, 3, 3, 2, 3, 1, 4]
def baseStart_1106359 : Nat := 118140960795 + 1106359 * 2 ^ 59
def prefixEnd_1106359 : Nat := 4983230072969 + 3 ^ 40 * 1106359 * 2
def baseEnd_1106359 : Nat := 378729295618494732682969

theorem tailTrace_1106359 : CollatzResearch.WordTrace tailWord_1106359 prefixEnd_1106359 378729295618494732682969 := by
  unfold tailWord_1106359
  simp only [CollatzResearch.WordTrace]
  refine ⟨40352227798857768919146131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26901485199238512612764087 40352227798857768919146131)
  ·
    refine ⟨60528341698286653378719197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40352227798857768919146131 60528341698286653378719197)
    ·
      refine ⟨22698128136857495017019699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60528341698286653378719197 22698128136857495017019699)
      ·
        refine ⟨34047192205286242525529549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22698128136857495017019699 34047192205286242525529549)
        ·
          refine ⟨12767697076982340947073581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34047192205286242525529549 12767697076982340947073581)
          ·
            refine ⟨4787886403868377855152593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12767697076982340947073581 4787886403868377855152593)
            ·
              refine ⟨3590914802901283391364445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4787886403868377855152593 3590914802901283391364445)
              ·
                refine ⟨1346593051087981271761667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3590914802901283391364445 1346593051087981271761667)
                ·
                  refine ⟨2019889576631971907642501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1346593051087981271761667 2019889576631971907642501)
                  ·
                    refine ⟨378729295618494732682969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2019889576631971907642501 378729295618494732682969)
                    ·
                      rfl

theorem cell22_1106359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 3, 1, 4].length) (baseStart_1106359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1106359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1106359 prefixEnd_1106359 := by exact prefixLift 1106359
  have htrace : WordTrace (prefixWord ++ tailWord_1106359) baseStart_1106359 baseEnd_1106359 := by
    simpa [prefixWord, tailWord_1106359, baseEnd_1106359] using wordTrace_append hprefix tailTrace_1106359
  have hstable : (prefixWord ++ tailWord_1106359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106359).length < 2 ^ (prefixWord ++ tailWord_1106359).sum := by decide
  have hdescent : baseEnd_1106359 < baseStart_1106359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106436 : List Nat := [2, 3, 2, 3, 1, 3, 1, 7]
def baseStart_1106436 : Nat := 118140960795 + 1106436 * 2 ^ 59
def prefixEnd_1106436 : Nat := 4983230072969 + 3 ^ 40 * 1106436 * 2
def baseEnd_1106436 : Nat := 42083961588010244278637

theorem tailTrace_1106436 : CollatzResearch.WordTrace tailWord_1106436 prefixEnd_1106436 42083961588010244278637 := by
  unfold tailWord_1106436
  simp only [CollatzResearch.WordTrace]
  refine ⟨20177518109789405534849581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26903357479719207379799441 20177518109789405534849581)
  ·
    refine ⟨7566569291171027075568593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20177518109789405534849581 7566569291171027075568593)
    ·
      refine ⟨5674926968378270306676445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7566569291171027075568593 5674926968378270306676445)
      ·
        refine ⟨2128097613141851365003667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5674926968378270306676445 2128097613141851365003667)
        ·
          refine ⟨3192146419712777047505501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2128097613141851365003667 3192146419712777047505501)
          ·
            refine ⟨1197054907392291392814563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3192146419712777047505501 1197054907392291392814563)
            ·
              refine ⟨1795582361088437089221845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1197054907392291392814563 1795582361088437089221845)
              ·
                refine ⟨42083961588010244278637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1795582361088437089221845 42083961588010244278637)
                ·
                  rfl

theorem cell22_1106436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 7].length) (baseStart_1106436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1106436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1106436 prefixEnd_1106436 := by exact prefixLift 1106436
  have htrace : WordTrace (prefixWord ++ tailWord_1106436) baseStart_1106436 baseEnd_1106436 := by
    simpa [prefixWord, tailWord_1106436, baseEnd_1106436] using wordTrace_append hprefix tailTrace_1106436
  have hstable : (prefixWord ++ tailWord_1106436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106436).length < 2 ^ (prefixWord ++ tailWord_1106436).sum := by decide
  have hdescent : baseEnd_1106436 < baseStart_1106436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106455 : List Nat := [1, 1, 3, 6, 2, 1, 1, 1, 2, 4]
def baseStart_1106455 : Nat := 118140960795 + 1106455 * 2 ^ 59
def prefixEnd_1106455 : Nat := 4983230072969 + 3 ^ 40 * 1106455 * 2
def baseEnd_1106455 : Nat := 378762158380382482282675

theorem tailTrace_1106455 : CollatzResearch.WordTrace tailWord_1106455 prefixEnd_1106455 378762158380382482282675 := by
  unfold tailWord_1106455
  simp only [CollatzResearch.WordTrace]
  refine ⟨40355729206509977314640819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26903819471006651543093879 40355729206509977314640819)
  ·
    refine ⟨60533593809764965971961229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40355729206509977314640819 60533593809764965971961229)
    ·
      refine ⟨22700097678661862239485461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60533593809764965971961229 22700097678661862239485461)
      ·
        refine ⟨1064067078687274792475881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 22700097678661862239485461 1064067078687274792475881)
        ·
          refine ⟨798050309015456094356911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1064067078687274792475881 798050309015456094356911)
          ·
            refine ⟨1197075463523184141535367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 798050309015456094356911 1197075463523184141535367)
            ·
              refine ⟨1795613195284776212303051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1197075463523184141535367 1795613195284776212303051)
              ·
                refine ⟨2693419792927164318454577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1795613195284776212303051 2693419792927164318454577)
                ·
                  refine ⟨2020064844695373238840933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2693419792927164318454577 2020064844695373238840933)
                  ·
                    refine ⟨378762158380382482282675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2020064844695373238840933 378762158380382482282675)
                    ·
                      rfl

theorem cell22_1106455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 1, 2, 4].length) (baseStart_1106455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1106455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1106455 prefixEnd_1106455 := by exact prefixLift 1106455
  have htrace : WordTrace (prefixWord ++ tailWord_1106455) baseStart_1106455 baseEnd_1106455 := by
    simpa [prefixWord, tailWord_1106455, baseEnd_1106455] using wordTrace_append hprefix tailTrace_1106455
  have hstable : (prefixWord ++ tailWord_1106455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106455).length < 2 ^ (prefixWord ++ tailWord_1106455).sum := by decide
  have hdescent : baseEnd_1106455 < baseStart_1106455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106562 : List Nat := [3, 4, 3, 1, 1, 1, 1, 1, 3, 4]
def baseStart_1106562 : Nat := 118140960795 + 1106562 * 2 ^ 59
def prefixEnd_1106562 : Nat := 4983230072969 + 3 ^ 40 * 1106562 * 2
def baseEnd_1106562 : Nat := 378798786667069869857347

theorem tailTrace_1106562 : CollatzResearch.WordTrace tailWord_1106562 prefixEnd_1106562 378798786667069869857347 := by
  unfold tailWord_1106562
  simp only [CollatzResearch.WordTrace]
  refine ⟨10089907954280583647196485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26906421211414889725857293 10089907954280583647196485)
  ·
    refine ⟨1891857741427609433849341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10089907954280583647196485 1891857741427609433849341)
    ·
      refine ⟨709446653035353537693503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1891857741427609433849341 709446653035353537693503)
      ·
        refine ⟨1064169979553030306540255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 709446653035353537693503 1064169979553030306540255)
        ·
          refine ⟨1596254969329545459810383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1064169979553030306540255 1596254969329545459810383)
          ·
            refine ⟨2394382453994318189715575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1596254969329545459810383 2394382453994318189715575)
            ·
              refine ⟨3591573680991477284573363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2394382453994318189715575 3591573680991477284573363)
              ·
                refine ⟨5387360521487215926860045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3591573680991477284573363 5387360521487215926860045)
                ·
                  refine ⟨2020260195557705972572517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5387360521487215926860045 2020260195557705972572517)
                  ·
                    refine ⟨378798786667069869857347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2020260195557705972572517 378798786667069869857347)
                    ·
                      rfl

theorem cell22_1106562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_1106562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1106562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1106562 prefixEnd_1106562 := by exact prefixLift 1106562
  have htrace : WordTrace (prefixWord ++ tailWord_1106562) baseStart_1106562 baseEnd_1106562 := by
    simpa [prefixWord, tailWord_1106562, baseEnd_1106562] using wordTrace_append hprefix tailTrace_1106562
  have hstable : (prefixWord ++ tailWord_1106562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106562).length < 2 ^ (prefixWord ++ tailWord_1106562).sum := by decide
  have hdescent : baseEnd_1106562 < baseStart_1106562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106661 : List Nat := [1, 3, 1, 4, 1, 2, 1, 3, 6]
def baseStart_1106661 : Nat := 118140960795 + 1106661 * 2 ^ 59
def prefixEnd_1106661 : Nat := 4983230072969 + 3 ^ 40 * 1106661 * 2
def baseEnd_1106661 : Nat := 126277558796755537210681

theorem tailTrace_1106661 : CollatzResearch.WordTrace tailWord_1106661 prefixEnd_1106661 126277558796755537210681 := by
  unfold tailWord_1106661
  simp only [CollatzResearch.WordTrace]
  refine ⟨40363242643763674496639837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26908828429175782997759891 40363242643763674496639837)
  ·
    refine ⟨15136215991411377936239939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40363242643763674496639837 15136215991411377936239939)
    ·
      refine ⟨22704323987117066904359909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15136215991411377936239939 22704323987117066904359909)
      ·
        refine ⟨4257060747584450044567483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22704323987117066904359909 4257060747584450044567483)
        ·
          refine ⟨6385591121376675066851225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4257060747584450044567483 6385591121376675066851225)
          ·
            refine ⟨4789193341032506300138419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6385591121376675066851225 4789193341032506300138419)
            ·
              refine ⟨7183790011548759450207629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4789193341032506300138419 7183790011548759450207629)
              ·
                refine ⟨2693921254330784793827861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7183790011548759450207629 2693921254330784793827861)
                ·
                  refine ⟨126277558796755537210681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2693921254330784793827861 126277558796755537210681)
                  ·
                    rfl

theorem cell22_1106661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 3, 6].length) (baseStart_1106661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1106661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1106661 prefixEnd_1106661 := by exact prefixLift 1106661
  have htrace : WordTrace (prefixWord ++ tailWord_1106661) baseStart_1106661 baseEnd_1106661 := by
    simpa [prefixWord, tailWord_1106661, baseEnd_1106661] using wordTrace_append hprefix tailTrace_1106661
  have hstable : (prefixWord ++ tailWord_1106661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106661).length < 2 ^ (prefixWord ++ tailWord_1106661).sum := by decide
  have hdescent : baseEnd_1106661 < baseStart_1106661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106691 : List Nat := [1, 1, 1, 3, 2, 2, 1, 5, 2, 4]
def baseStart_1106691 : Nat := 118140960795 + 1106691 * 2 ^ 59
def prefixEnd_1106691 : Nat := 4983230072969 + 3 ^ 40 * 1106691 * 2
def baseEnd_1106691 : Nat := 378842946003356533381951

theorem tailTrace_1106691 : CollatzResearch.WordTrace tailWord_1106691 prefixEnd_1106691 378842946003356533381951 := by
  unfold tailWord_1106691
  simp only [CollatzResearch.WordTrace]
  refine ⟨40364336833654989620231927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26909557889103326413487951 40364336833654989620231927)
  ·
    refine ⟨60546505250482484430347891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40364336833654989620231927 60546505250482484430347891)
    ·
      refine ⟨90819757875723726645521837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60546505250482484430347891 90819757875723726645521837)
      ·
        refine ⟨34057409203396397492070689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90819757875723726645521837 34057409203396397492070689)
        ·
          refine ⟨25543056902547298119053017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34057409203396397492070689 25543056902547298119053017)
          ·
            refine ⟨19157292676910473589289763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25543056902547298119053017 19157292676910473589289763)
            ·
              refine ⟨28735939015365710383934645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19157292676910473589289763 28735939015365710383934645)
              ·
                refine ⟨2693994282690535348493873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28735939015365710383934645 2693994282690535348493873)
                ·
                  refine ⟨2020495712017901511370405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2693994282690535348493873 2020495712017901511370405)
                  ·
                    refine ⟨378842946003356533381951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2020495712017901511370405 378842946003356533381951)
                    ·
                      rfl

theorem cell22_1106691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 5, 2, 4].length) (baseStart_1106691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1106691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1106691 prefixEnd_1106691 := by exact prefixLift 1106691
  have htrace : WordTrace (prefixWord ++ tailWord_1106691) baseStart_1106691 baseEnd_1106691 := by
    simpa [prefixWord, tailWord_1106691, baseEnd_1106691] using wordTrace_append hprefix tailTrace_1106691
  have hstable : (prefixWord ++ tailWord_1106691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106691).length < 2 ^ (prefixWord ++ tailWord_1106691).sum := by decide
  have hdescent : baseEnd_1106691 < baseStart_1106691 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106695 : List Nat := [1, 1, 4, 4, 1, 1, 3, 3, 4]
def baseStart_1106695 : Nat := 118140960795 + 1106695 * 2 ^ 59
def prefixEnd_1106695 : Nat := 4983230072969 + 3 ^ 40 * 1106695 * 2
def baseEnd_1106695 : Nat := 126281438428367285427313

theorem tailTrace_1106695 : CollatzResearch.WordTrace tailWord_1106695 prefixEnd_1106695 126281438428367285427313 := by
  unfold tailWord_1106695
  simp only [CollatzResearch.WordTrace]
  refine ⟨40364482725640498303377539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26909655150426998868918359 40364482725640498303377539)
  ·
    refine ⟨60546724088460747455066309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40364482725640498303377539 60546724088460747455066309)
    ·
      refine ⟨11352510766586390147824933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60546724088460747455066309 11352510766586390147824933)
      ·
        refine ⟨2128595768734948152717175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11352510766586390147824933 2128595768734948152717175)
        ·
          refine ⟨3192893653102422229075763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2128595768734948152717175 3192893653102422229075763)
          ·
            refine ⟨4789340479653633343613645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3192893653102422229075763 4789340479653633343613645)
            ·
              refine ⟨1796002679870112503855117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4789340479653633343613645 1796002679870112503855117)
              ·
                refine ⟨673501004951292188945669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1796002679870112503855117 673501004951292188945669)
                ·
                  refine ⟨126281438428367285427313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 673501004951292188945669 126281438428367285427313)
                  ·
                    rfl

theorem cell22_1106695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 3, 4].length) (baseStart_1106695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1106695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1106695 prefixEnd_1106695 := by exact prefixLift 1106695
  have htrace : WordTrace (prefixWord ++ tailWord_1106695) baseStart_1106695 baseEnd_1106695 := by
    simpa [prefixWord, tailWord_1106695, baseEnd_1106695] using wordTrace_append hprefix tailTrace_1106695
  have hstable : (prefixWord ++ tailWord_1106695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106695).length < 2 ^ (prefixWord ++ tailWord_1106695).sum := by decide
  have hdescent : baseEnd_1106695 < baseStart_1106695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106738 : List Nat := [3, 2, 1, 1, 3, 1, 2, 1, 5, 3]
def baseStart_1106738 : Nat := 118140960795 + 1106738 * 2 ^ 59
def prefixEnd_1106738 : Nat := 4983230072969 + 3 ^ 40 * 1106738 * 2
def baseEnd_1106738 : Nat := 378859035063864077456807

theorem tailTrace_1106738 : CollatzResearch.WordTrace tailWord_1106738 prefixEnd_1106738 378859035063864077456807 := by
  unfold tailWord_1106738
  simp only [CollatzResearch.WordTrace]
  refine ⟨10091512766121179161798217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26910700709656477764795245 10091512766121179161798217)
  ·
    refine ⟨7568634574590884371348663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10091512766121179161798217 7568634574590884371348663)
    ·
      refine ⟨11352951861886326557022995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7568634574590884371348663 11352951861886326557022995)
      ·
        refine ⟨17029427792829489835534493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11352951861886326557022995 17029427792829489835534493)
        ·
          refine ⟨6386035422311058688325435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17029427792829489835534493 6386035422311058688325435)
          ·
            refine ⟨9579053133466588032488153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6386035422311058688325435 9579053133466588032488153)
            ·
              refine ⟨7184289850099941024366115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9579053133466588032488153 7184289850099941024366115)
              ·
                refine ⟨10776434775149911536549173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7184289850099941024366115 10776434775149911536549173)
                ·
                  refine ⟨1010290760170304206551485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10776434775149911536549173 1010290760170304206551485)
                  ·
                    refine ⟨378859035063864077456807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1010290760170304206551485 378859035063864077456807)
                    ·
                      rfl

theorem cell22_1106738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 5, 3].length) (baseStart_1106738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1106738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1106738 prefixEnd_1106738 := by exact prefixLift 1106738
  have htrace : WordTrace (prefixWord ++ tailWord_1106738) baseStart_1106738 baseEnd_1106738 := by
    simpa [prefixWord, tailWord_1106738, baseEnd_1106738] using wordTrace_append hprefix tailTrace_1106738
  have hstable : (prefixWord ++ tailWord_1106738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106738).length < 2 ^ (prefixWord ++ tailWord_1106738).sum := by decide
  have hdescent : baseEnd_1106738 < baseStart_1106738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106742 : List Nat := [5, 1, 2, 2, 2, 1, 2, 1, 2, 4]
def baseStart_1106742 : Nat := 118140960795 + 1106742 * 2 ^ 59
def prefixEnd_1106742 : Nat := 4983230072969 + 3 ^ 40 * 1106742 * 2
def baseEnd_1106742 : Nat := 378860404345609400356795

theorem tailTrace_1106742 : CollatzResearch.WordTrace tailWord_1106742 prefixEnd_1106742 378860404345609400356795 := by
  unfold tailWord_1106742
  simp only [CollatzResearch.WordTrace]
  refine ⟨2522887309779389083146155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26910797970980150220225653 2522887309779389083146155)
  ·
    refine ⟨3784330964669083624719233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2522887309779389083146155 3784330964669083624719233)
    ·
      refine ⟨2838248223501812718539425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3784330964669083624719233 2838248223501812718539425)
      ·
        refine ⟨2128686167626359538904569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2838248223501812718539425 2128686167626359538904569)
        ·
          refine ⟨1596514625719769654178427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2128686167626359538904569 1596514625719769654178427)
          ·
            refine ⟨2394771938579654481267641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1596514625719769654178427 2394771938579654481267641)
            ·
              refine ⟨1796078953934740860950731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2394771938579654481267641 1796078953934740860950731)
              ·
                refine ⟨2694118430902111291426097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1796078953934740860950731 2694118430902111291426097)
                ·
                  refine ⟨2020588823176583468569573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2694118430902111291426097 2020588823176583468569573)
                  ·
                    refine ⟨378860404345609400356795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2020588823176583468569573 378860404345609400356795)
                    ·
                      rfl

theorem cell22_1106742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_1106742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1106742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1106742 prefixEnd_1106742 := by exact prefixLift 1106742
  have htrace : WordTrace (prefixWord ++ tailWord_1106742) baseStart_1106742 baseEnd_1106742 := by
    simpa [prefixWord, tailWord_1106742, baseEnd_1106742] using wordTrace_append hprefix tailTrace_1106742
  have hstable : (prefixWord ++ tailWord_1106742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106742).length < 2 ^ (prefixWord ++ tailWord_1106742).sum := by decide
  have hdescent : baseEnd_1106742 < baseStart_1106742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106755 : List Nat := [1, 1, 1, 3, 1, 4, 2, 5, 1, 3]
def baseStart_1106755 : Nat := 118140960795 + 1106755 * 2 ^ 59
def prefixEnd_1106755 : Nat := 4983230072969 + 3 ^ 40 * 1106755 * 2
def baseEnd_1106755 : Nat := 378864854511281699781755

theorem tailTrace_1106755 : CollatzResearch.WordTrace tailWord_1106755 prefixEnd_1106755 378864854511281699781755 := by
  unfold tailWord_1106755
  simp only [CollatzResearch.WordTrace]
  refine ⟨40366671105423128550561719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26911114070282085700374479 40366671105423128550561719)
  ·
    refine ⟨60550006658134692825842579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40366671105423128550561719 60550006658134692825842579)
    ·
      refine ⟨90825009987202039238763869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60550006658134692825842579 90825009987202039238763869)
      ·
        refine ⟨34059378745200764714536451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90825009987202039238763869 34059378745200764714536451)
        ·
          refine ⟨51089068117801147071804677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34059378745200764714536451 51089068117801147071804677)
          ·
            refine ⟨9579200272087715075963377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51089068117801147071804677 9579200272087715075963377)
            ·
              refine ⟨7184400204065786306972533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9579200272087715075963377 7184400204065786306972533)
              ·
                refine ⟨673537519131167466278675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7184400204065786306972533 673537519131167466278675)
                ·
                  refine ⟨1010306278696751199418013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 673537519131167466278675 1010306278696751199418013)
                  ·
                    refine ⟨378864854511281699781755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1010306278696751199418013 378864854511281699781755)
                    ·
                      rfl

theorem cell22_1106755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 5, 1, 3].length) (baseStart_1106755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1106755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1106755 prefixEnd_1106755 := by exact prefixLift 1106755
  have htrace : WordTrace (prefixWord ++ tailWord_1106755) baseStart_1106755 baseEnd_1106755 := by
    simpa [prefixWord, tailWord_1106755, baseEnd_1106755] using wordTrace_append hprefix tailTrace_1106755
  have hstable : (prefixWord ++ tailWord_1106755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106755).length < 2 ^ (prefixWord ++ tailWord_1106755).sum := by decide
  have hdescent : baseEnd_1106755 < baseStart_1106755 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106766 : List Nat := [4, 1, 1, 1, 1, 1, 1, 2, 3, 7]
def baseStart_1106766 : Nat := 118140960795 + 1106766 * 2 ^ 59
def prefixEnd_1106766 : Nat := 4983230072969 + 3 ^ 40 * 1106766 * 2
def baseEnd_1106766 : Nat := 378868620036081337756721

theorem tailTrace_1106766 : CollatzResearch.WordTrace tailWord_1106766 prefixEnd_1106766 378868620036081337756721 := by
  unfold tailWord_1106766
  simp only [CollatzResearch.WordTrace]
  refine ⟨5045884038547909678651519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26911381538922184952808101 5045884038547909678651519)
  ·
    refine ⟨7568826057821864517977279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5045884038547909678651519 7568826057821864517977279)
    ·
      refine ⟨11353239086732796776965919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7568826057821864517977279 11353239086732796776965919)
      ·
        refine ⟨17029858630099195165448879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11353239086732796776965919 17029858630099195165448879)
        ·
          refine ⟨25544787945148792748173319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17029858630099195165448879 25544787945148792748173319)
          ·
            refine ⟨38317181917723189122259979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25544787945148792748173319 38317181917723189122259979)
            ·
              refine ⟨57475772876584783683389969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38317181917723189122259979 57475772876584783683389969)
              ·
                refine ⟨43106829657438587762542477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57475772876584783683389969 43106829657438587762542477)
                ·
                  refine ⟨16165061121539470410953429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43106829657438587762542477 16165061121539470410953429)
                  ·
                    refine ⟨378868620036081337756721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16165061121539470410953429 378868620036081337756721)
                    ·
                      rfl

theorem cell22_1106766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 3, 7].length) (baseStart_1106766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1106766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1106766 prefixEnd_1106766 := by exact prefixLift 1106766
  have htrace : WordTrace (prefixWord ++ tailWord_1106766) baseStart_1106766 baseEnd_1106766 := by
    simpa [prefixWord, tailWord_1106766, baseEnd_1106766] using wordTrace_append hprefix tailTrace_1106766
  have hstable : (prefixWord ++ tailWord_1106766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106766).length < 2 ^ (prefixWord ++ tailWord_1106766).sum := by decide
  have hdescent : baseEnd_1106766 < baseStart_1106766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106815 : List Nat := [1, 1, 2, 2, 1, 1, 8, 1, 1, 4]
def baseStart_1106815 : Nat := 118140960795 + 1106815 * 2 ^ 59
def prefixEnd_1106815 : Nat := 4983230072969 + 3 ^ 40 * 1106815 * 2
def baseEnd_1106815 : Nat := 378885393737461543281571

theorem tailTrace_1106815 : CollatzResearch.WordTrace tailWord_1106815 prefixEnd_1106815 378885393737461543281571 := by
  unfold tailWord_1106815
  simp only [CollatzResearch.WordTrace]
  refine ⟨40368859485205758797745899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26912572990137172531830599 40368859485205758797745899)
  ·
    refine ⟨60553289227808638196618849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40368859485205758797745899 60553289227808638196618849)
    ·
      refine ⟨45414966920856478647464137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60553289227808638196618849 45414966920856478647464137)
      ·
        refine ⟨34061225190642358985598103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45414966920856478647464137 34061225190642358985598103)
        ·
          refine ⟨51091837785963538478397155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34061225190642358985598103 51091837785963538478397155)
          ·
            refine ⟨76637756678945307717595733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51091837785963538478397155 76637756678945307717595733)
            ·
              refine ⟨898098711081390324815575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 76637756678945307717595733 898098711081390324815575)
              ·
                refine ⟨1347148066622085487223363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 898098711081390324815575 1347148066622085487223363)
                ·
                  refine ⟨2020722099933128230835045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1347148066622085487223363 2020722099933128230835045)
                  ·
                    refine ⟨378885393737461543281571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2020722099933128230835045 378885393737461543281571)
                    ·
                      rfl

theorem cell22_1106815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 8, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 8, 1, 1, 4].length) (baseStart_1106815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1106815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1106815 prefixEnd_1106815 := by exact prefixLift 1106815
  have htrace : WordTrace (prefixWord ++ tailWord_1106815) baseStart_1106815 baseEnd_1106815 := by
    simpa [prefixWord, tailWord_1106815, baseEnd_1106815] using wordTrace_append hprefix tailTrace_1106815
  have hstable : (prefixWord ++ tailWord_1106815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106815).length < 2 ^ (prefixWord ++ tailWord_1106815).sum := by decide
  have hdescent : baseEnd_1106815 < baseStart_1106815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106841 : List Nat := [1, 2, 1, 2, 1, 3, 1, 11]
def baseStart_1106841 : Nat := 118140960795 + 1106841 * 2 ^ 59
def prefixEnd_1106841 : Nat := 4983230072969 + 3 ^ 40 * 1106841 * 2
def baseEnd_1106841 : Nat := 42099366007645126903499

theorem tailTrace_1106841 : CollatzResearch.WordTrace tailWord_1106841 prefixEnd_1106841 42099366007645126903499 := by
  unfold tailWord_1106841
  simp only [CollatzResearch.WordTrace]
  refine ⟨40369807783111565238192377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26913205188741043492128251 40369807783111565238192377)
  ·
    refine ⟨30277355837333673928644283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40369807783111565238192377 30277355837333673928644283)
    ·
      refine ⟨45416033756000510892966425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30277355837333673928644283 45416033756000510892966425)
      ·
        refine ⟨34062025317000383169724819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45416033756000510892966425 34062025317000383169724819)
        ·
          refine ⟨51093037975500574754587229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34062025317000383169724819 51093037975500574754587229)
          ·
            refine ⟨19159889240812715532970211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51093037975500574754587229 19159889240812715532970211)
            ·
              refine ⟨28739833861219073299455317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19159889240812715532970211 28739833861219073299455317)
              ·
                refine ⟨42099366007645126903499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 28739833861219073299455317 42099366007645126903499)
                ·
                  rfl

theorem cell22_1106841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 11].length) (baseStart_1106841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1106841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1106841 prefixEnd_1106841 := by exact prefixLift 1106841
  have htrace : WordTrace (prefixWord ++ tailWord_1106841) baseStart_1106841 baseEnd_1106841 := by
    simpa [prefixWord, tailWord_1106841, baseEnd_1106841] using wordTrace_append hprefix tailTrace_1106841
  have hstable : (prefixWord ++ tailWord_1106841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106841).length < 2 ^ (prefixWord ++ tailWord_1106841).sum := by decide
  have hdescent : baseEnd_1106841 < baseStart_1106841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106932 : List Nat := [2, 6, 2, 1, 2, 1, 2, 2, 4]
def baseStart_1106932 : Nat := 118140960795 + 1106932 * 2 ^ 59
def prefixEnd_1106932 : Nat := 4983230072969 + 3 ^ 40 * 1106932 * 2
def baseEnd_1106932 : Nat := 126308481742837412702071

theorem tailTrace_1106932 : CollatzResearch.WordTrace tailWord_1106932 prefixEnd_1106932 126308481742837412702071 := by
  unfold tailWord_1106932
  simp only [CollatzResearch.WordTrace]
  refine ⟨20186563412890943889877525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26915417883854591853170033 20186563412890943889877525)
  ·
    refine ⟨946245159979262994838009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 20186563412890943889877525 946245159979262994838009)
    ·
      refine ⟨709683869984447246128507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 946245159979262994838009 709683869984447246128507)
      ·
        refine ⟨1064525804976670869192761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 709683869984447246128507 1064525804976670869192761)
        ·
          refine ⟨798394353732503151894571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1064525804976670869192761 798394353732503151894571)
          ·
            refine ⟨1197591530598754727841857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 798394353732503151894571 1197591530598754727841857)
            ·
              refine ⟨898193647949066045881393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1197591530598754727841857 898193647949066045881393)
              ·
                refine ⟨673645235961799534411045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 898193647949066045881393 673645235961799534411045)
                ·
                  refine ⟨126308481742837412702071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 673645235961799534411045 126308481742837412702071)
                  ·
                    rfl

theorem cell22_1106932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_1106932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1106932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1106932 prefixEnd_1106932 := by exact prefixLift 1106932
  have htrace : WordTrace (prefixWord ++ tailWord_1106932) baseStart_1106932 baseEnd_1106932 := by
    simpa [prefixWord, tailWord_1106932, baseEnd_1106932] using wordTrace_append hprefix tailTrace_1106932
  have hstable : (prefixWord ++ tailWord_1106932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106932).length < 2 ^ (prefixWord ++ tailWord_1106932).sum := by decide
  have hdescent : baseEnd_1106932 < baseStart_1106932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106965 : List Nat := [1, 3, 2, 1, 4, 2, 1, 2, 6]
def baseStart_1106965 : Nat := 118140960795 + 1106965 * 2 ^ 59
def prefixEnd_1106965 : Nat := 4983230072969 + 3 ^ 40 * 1106965 * 2
def baseEnd_1106965 : Nat := 126312247267637050677037

theorem tailTrace_1106965 : CollatzResearch.WordTrace tailWord_1106965 prefixEnd_1106965 126312247267637050677037 := by
  unfold tailWord_1106965
  simp only [CollatzResearch.WordTrace]
  refine ⟨40374330434662334415706349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26916220289774889610470899 40374330434662334415706349)
  ·
    refine ⟨15140373912998375405889881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40374330434662334415706349 15140373912998375405889881)
    ·
      refine ⟨11355280434748781554417411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15140373912998375405889881 11355280434748781554417411)
      ·
        refine ⟨17032920652123172331626117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11355280434748781554417411 17032920652123172331626117)
        ·
          refine ⟨3193672622273094812179897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17032920652123172331626117 3193672622273094812179897)
          ·
            refine ⟨2395254466704821109134923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3193672622273094812179897 2395254466704821109134923)
            ·
              refine ⟨3592881700057231663702385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2395254466704821109134923 3592881700057231663702385)
              ·
                refine ⟨2694661275042923747776789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3592881700057231663702385 2694661275042923747776789)
                ·
                  refine ⟨126312247267637050677037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2694661275042923747776789 126312247267637050677037)
                  ·
                    rfl

theorem cell22_1106965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 2, 6].length) (baseStart_1106965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1106965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1106965 prefixEnd_1106965 := by exact prefixLift 1106965
  have htrace : WordTrace (prefixWord ++ tailWord_1106965) baseStart_1106965 baseEnd_1106965 := by
    simpa [prefixWord, tailWord_1106965, baseEnd_1106965] using wordTrace_append hprefix tailTrace_1106965
  have hstable : (prefixWord ++ tailWord_1106965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106965).length < 2 ^ (prefixWord ++ tailWord_1106965).sum := by decide
  have hdescent : baseEnd_1106965 < baseStart_1106965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106993 : List Nat := [1, 2, 2, 3, 1, 2, 11]
def baseStart_1106993 : Nat := 118140960795 + 1106993 * 2 ^ 59
def prefixEnd_1106993 : Nat := 4983230072969 + 3 ^ 40 * 1106993 * 2
def baseEnd_1106993 : Nat := 14035049139819570827075

theorem tailTrace_1106993 : CollatzResearch.WordTrace tailWord_1106993 prefixEnd_1106993 14035049139819570827075 := by
  unfold tailWord_1106993
  simp only [CollatzResearch.WordTrace]
  refine ⟨40375351678560895197725633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26916901119040596798483755 40375351678560895197725633)
  ·
    refine ⟨30281513758920671398294225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40375351678560895197725633 30281513758920671398294225)
    ·
      refine ⟨22711135319190503548720669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30281513758920671398294225 22711135319190503548720669)
      ·
        refine ⟨8516675744696438830770251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22711135319190503548720669 8516675744696438830770251)
        ·
          refine ⟨12775013617044658246155377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8516675744696438830770251 12775013617044658246155377)
          ·
            refine ⟨9581260212783493684616533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12775013617044658246155377 9581260212783493684616533)
            ·
              refine ⟨14035049139819570827075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 9581260212783493684616533 14035049139819570827075)
              ·
                rfl

theorem cell22_1106993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 11].length) (baseStart_1106993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1106993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1106993 prefixEnd_1106993 := by exact prefixLift 1106993
  have htrace : WordTrace (prefixWord ++ tailWord_1106993) baseStart_1106993 baseEnd_1106993 := by
    simpa [prefixWord, tailWord_1106993, baseEnd_1106993] using wordTrace_append hprefix tailTrace_1106993
  have hstable : (prefixWord ++ tailWord_1106993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106993).length < 2 ^ (prefixWord ++ tailWord_1106993).sum := by decide
  have hdescent : baseEnd_1106993 < baseStart_1106993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107014 : List Nat := [6, 1, 1, 1, 1, 2, 3, 1, 1, 5]
def baseStart_1107014 : Nat := 118140960795 + 1107014 * 2 ^ 59
def prefixEnd_1107014 : Nat := 4983230072969 + 3 ^ 40 * 1107014 * 2
def baseEnd_1107014 : Nat := 378953515504291357555961

theorem tailTrace_1107014 : CollatzResearch.WordTrace tailWord_1107014 prefixEnd_1107014 378953515504291357555961 := by
  unfold tailWord_1107014
  simp only [CollatzResearch.WordTrace]
  refine ⟨1261753675358900493257503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 26917411740989877189493397 1261753675358900493257503)
  ·
    refine ⟨1892630513038350739886255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1261753675358900493257503 1892630513038350739886255)
    ·
      refine ⟨2838945769557526109829383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1892630513038350739886255 2838945769557526109829383)
      ·
        refine ⟨4258418654336289164744075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2838945769557526109829383 4258418654336289164744075)
        ·
          refine ⟨6387627981504433747116113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4258418654336289164744075 6387627981504433747116113)
          ·
            refine ⟨4790720986128325310337085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6387627981504433747116113 4790720986128325310337085)
            ·
              refine ⟨1796520369798121991376407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4790720986128325310337085 1796520369798121991376407)
              ·
                refine ⟨2694780554697182987064611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1796520369798121991376407 2694780554697182987064611)
                ·
                  refine ⟨4042170832045774480596917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2694780554697182987064611 4042170832045774480596917)
                  ·
                    refine ⟨378953515504291357555961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4042170832045774480596917 378953515504291357555961)
                    ·
                      rfl

theorem cell22_1107014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_1107014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1107014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1107014 prefixEnd_1107014 := by exact prefixLift 1107014
  have htrace : WordTrace (prefixWord ++ tailWord_1107014) baseStart_1107014 baseEnd_1107014 := by
    simpa [prefixWord, tailWord_1107014, baseEnd_1107014] using wordTrace_append hprefix tailTrace_1107014
  have hstable : (prefixWord ++ tailWord_1107014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107014).length < 2 ^ (prefixWord ++ tailWord_1107014).sum := by decide
  have hdescent : baseEnd_1107014 < baseStart_1107014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107055 : List Nat := [1, 1, 2, 1, 3, 3, 2, 4, 5]
def baseStart_1107055 : Nat := 118140960795 + 1107055 * 2 ^ 59
def prefixEnd_1107055 : Nat := 4983230072969 + 3 ^ 40 * 1107055 * 2
def baseEnd_1107055 : Nat := 126322516880726972426945

theorem tailTrace_1107055 : CollatzResearch.WordTrace tailWord_1107055 prefixEnd_1107055 126322516880726972426945 := by
  unfold tailWord_1107055
  simp only [CollatzResearch.WordTrace]
  refine ⟨40377613004336279786482619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26918408669557519857655079 40377613004336279786482619)
  ·
    refine ⟨60566419506504419679723929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40377613004336279786482619 60566419506504419679723929)
    ·
      refine ⟨45424814629878314759792947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60566419506504419679723929 45424814629878314759792947)
      ·
        refine ⟨68137221944817472139689421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45424814629878314759792947 68137221944817472139689421)
        ·
          refine ⟨25551458229306552052383533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68137221944817472139689421 25551458229306552052383533)
          ·
            refine ⟨9581796835989957019643825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25551458229306552052383533 9581796835989957019643825)
            ·
              refine ⟨7186347626992467764732869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9581796835989957019643825 7186347626992467764732869)
              ·
                refine ⟨1347440180061087705887413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7186347626992467764732869 1347440180061087705887413)
                ·
                  refine ⟨126322516880726972426945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1347440180061087705887413 126322516880726972426945)
                  ·
                    rfl

theorem cell22_1107055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 4, 5].length) (baseStart_1107055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1107055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1107055 prefixEnd_1107055 := by exact prefixLift 1107055
  have htrace : WordTrace (prefixWord ++ tailWord_1107055) baseStart_1107055 baseEnd_1107055 := by
    simpa [prefixWord, tailWord_1107055, baseEnd_1107055] using wordTrace_append hprefix tailTrace_1107055
  have hstable : (prefixWord ++ tailWord_1107055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107055).length < 2 ^ (prefixWord ++ tailWord_1107055).sum := by decide
  have hdescent : baseEnd_1107055 < baseStart_1107055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107072 : List Nat := [2, 1, 1, 2, 1, 3, 6, 1, 5]
def baseStart_1107072 : Nat := 118140960795 + 1107072 * 2 ^ 59
def prefixEnd_1107072 : Nat := 4983230072969 + 3 ^ 40 * 1107072 * 2
def baseEnd_1107072 : Nat := 126324456696532846535261

theorem tailTrace_1107072 : CollatzResearch.WordTrace tailWord_1107072 prefixEnd_1107072 126324456696532846535261 := by
  unfold tailWord_1107072
  simp only [CollatzResearch.WordTrace]
  refine ⟨20189116522637345844925735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26918822030183127793234313 20189116522637345844925735)
  ·
    refine ⟨30283674783956018767388603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20189116522637345844925735 30283674783956018767388603)
    ·
      refine ⟨45425512175934028151082905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30283674783956018767388603 45425512175934028151082905)
      ·
        refine ⟨34069134131950521113312179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45425512175934028151082905 34069134131950521113312179)
        ·
          refine ⟨51103701197925781669968269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34069134131950521113312179 51103701197925781669968269)
          ·
            refine ⟨19163887949222168126238101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51103701197925781669968269 19163887949222168126238101)
            ·
              refine ⟨898307247619789130917411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 19163887949222168126238101 898307247619789130917411)
              ·
                refine ⟨1347460871429683696376117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 898307247619789130917411 1347460871429683696376117)
                ·
                  refine ⟨126324456696532846535261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1347460871429683696376117 126324456696532846535261)
                  ·
                    rfl

theorem cell22_1107072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 6, 1, 5].length) (baseStart_1107072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1107072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1107072 prefixEnd_1107072 := by exact prefixLift 1107072
  have htrace : WordTrace (prefixWord ++ tailWord_1107072) baseStart_1107072 baseEnd_1107072 := by
    simpa [prefixWord, tailWord_1107072, baseEnd_1107072] using wordTrace_append hprefix tailTrace_1107072
  have hstable : (prefixWord ++ tailWord_1107072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107072).length < 2 ^ (prefixWord ++ tailWord_1107072).sum := by decide
  have hdescent : baseEnd_1107072 < baseStart_1107072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107130 : List Nat := [3, 1, 1, 1, 2, 2, 1, 4, 1, 6]
def baseStart_1107130 : Nat := 118140960795 + 1107130 * 2 ^ 59
def prefixEnd_1107130 : Nat := 4983230072969 + 3 ^ 40 * 1107130 * 2
def baseEnd_1107130 : Nat := 378993224674905721655605

theorem tailTrace_1107130 : CollatzResearch.WordTrace tailWord_1107130 prefixEnd_1107130 378993224674905721655605 := by
  unfold tailWord_1107130
  simp only [CollatzResearch.WordTrace]
  refine ⟨10095087119766141898865711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26920232319376378396975229 10095087119766141898865711)
  ·
    refine ⟨15142630679649212848298567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10095087119766141898865711 15142630679649212848298567)
    ·
      refine ⟨22713946019473819272447851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15142630679649212848298567 22713946019473819272447851)
      ·
        refine ⟨34070919029210728908671777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22713946019473819272447851 34070919029210728908671777)
        ·
          refine ⟨25553189271908046681503833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34070919029210728908671777 25553189271908046681503833)
          ·
            refine ⟨19164891953931035011127875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25553189271908046681503833 19164891953931035011127875)
            ·
              refine ⟨28747337930896552516691813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19164891953931035011127875 28747337930896552516691813)
              ·
                refine ⟨5390125862043103596879715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28747337930896552516691813 5390125862043103596879715)
                ·
                  refine ⟨8085188793064655395319573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5390125862043103596879715 8085188793064655395319573)
                  ·
                    refine ⟨378993224674905721655605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8085188793064655395319573 378993224674905721655605)
                    ·
                      rfl

theorem cell22_1107130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 4, 1, 6].length) (baseStart_1107130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1107130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1107130 prefixEnd_1107130 := by exact prefixLift 1107130
  have htrace : WordTrace (prefixWord ++ tailWord_1107130) baseStart_1107130 baseEnd_1107130 := by
    simpa [prefixWord, tailWord_1107130, baseEnd_1107130] using wordTrace_append hprefix tailTrace_1107130
  have hstable : (prefixWord ++ tailWord_1107130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107130).length < 2 ^ (prefixWord ++ tailWord_1107130).sum := by decide
  have hdescent : baseEnd_1107130 < baseStart_1107130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107132 : List Nat := [2, 2, 2, 3, 2, 1, 1, 3, 1, 5]
def baseStart_1107132 : Nat := 118140960795 + 1107132 * 2 ^ 59
def prefixEnd_1107132 : Nat := 4983230072969 + 3 ^ 40 * 1107132 * 2
def baseEnd_1107132 : Nat := 378993909315778383105599

theorem tailTrace_1107132 : CollatzResearch.WordTrace tailWord_1107132 prefixEnd_1107132 378993909315778383105599 := by
  unfold tailWord_1107132
  simp only [CollatzResearch.WordTrace]
  refine ⟨20190210712528660968517825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26920280950038214624690433 20190210712528660968517825)
  ·
    refine ⟨15142658034396495726388369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20190210712528660968517825 15142658034396495726388369)
    ·
      refine ⟨11356993525797371794791277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15142658034396495726388369 11356993525797371794791277)
      ·
        refine ⟨4258872572174014423046729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11356993525797371794791277 4258872572174014423046729)
        ·
          refine ⟨3194154429130510817285047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4258872572174014423046729 3194154429130510817285047)
          ·
            refine ⟨4791231643695766225927571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3194154429130510817285047 4791231643695766225927571)
            ·
              refine ⟨7186847465543649338891357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4791231643695766225927571 7186847465543649338891357)
              ·
                refine ⟨2695067799578868502084259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7186847465543649338891357 2695067799578868502084259)
                ·
                  refine ⟨4042601699368302753126389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2695067799578868502084259 4042601699368302753126389)
                  ·
                    refine ⟨378993909315778383105599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4042601699368302753126389 378993909315778383105599)
                    ·
                      rfl

theorem cell22_1107132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 3, 1, 5].length) (baseStart_1107132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1107132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1107132 prefixEnd_1107132 := by exact prefixLift 1107132
  have htrace : WordTrace (prefixWord ++ tailWord_1107132) baseStart_1107132 baseEnd_1107132 := by
    simpa [prefixWord, tailWord_1107132, baseEnd_1107132] using wordTrace_append hprefix tailTrace_1107132
  have hstable : (prefixWord ++ tailWord_1107132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107132).length < 2 ^ (prefixWord ++ tailWord_1107132).sum := by decide
  have hdescent : baseEnd_1107132 < baseStart_1107132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107196 : List Nat := [2, 2, 2, 1, 6, 1, 2, 6]
def baseStart_1107196 : Nat := 118140960795 + 1107196 * 2 ^ 59
def prefixEnd_1107196 : Nat := 4983230072969 + 3 ^ 40 * 1107196 * 2
def baseEnd_1107196 : Nat := 42112868647078172167267

theorem tailTrace_1107196 : CollatzResearch.WordTrace tailWord_1107196 prefixEnd_1107196 42112868647078172167267 := by
  unfold tailWord_1107196
  simp only [CollatzResearch.WordTrace]
  refine ⟨20191377848412730433682721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26921837131216973911576961 20191377848412730433682721)
  ·
    refine ⟨15143533386309547825262041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20191377848412730433682721 15143533386309547825262041)
    ·
      refine ⟨11357650039732160868946531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15143533386309547825262041 11357650039732160868946531)
      ·
        refine ⟨17036475059598241303419797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11357650039732160868946531 17036475059598241303419797)
        ·
          refine ⟨798584768418667561097803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 17036475059598241303419797 798584768418667561097803)
          ·
            refine ⟨1197877152628001341646705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 798584768418667561097803 1197877152628001341646705)
            ·
              refine ⟨898407864471001006235029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1197877152628001341646705 898407864471001006235029)
              ·
                refine ⟨42112868647078172167267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 898407864471001006235029 42112868647078172167267)
                ·
                  rfl

theorem cell22_1107196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 2, 6].length) (baseStart_1107196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1107196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1107196 prefixEnd_1107196 := by exact prefixLift 1107196
  have htrace : WordTrace (prefixWord ++ tailWord_1107196) baseStart_1107196 baseEnd_1107196 := by
    simpa [prefixWord, tailWord_1107196, baseEnd_1107196] using wordTrace_append hprefix tailTrace_1107196
  have hstable : (prefixWord ++ tailWord_1107196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107196).length < 2 ^ (prefixWord ++ tailWord_1107196).sum := by decide
  have hdescent : baseEnd_1107196 < baseStart_1107196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107211 : List Nat := [1, 1, 1, 1, 5, 3, 3, 3, 1, 3]
def baseStart_1107211 : Nat := 118140960795 + 1107211 * 2 ^ 59
def prefixEnd_1107211 : Nat := 4983230072969 + 3 ^ 40 * 1107211 * 2
def baseEnd_1107211 : Nat := 379020952630248510380357

theorem tailTrace_1107211 : CollatzResearch.WordTrace tailWord_1107211 prefixEnd_1107211 379020952630248510380357 := by
  unfold tailWord_1107211
  simp only [CollatzResearch.WordTrace]
  refine ⟨40383302791771118429161487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26922201861180745619440991 40383302791771118429161487)
  ·
    refine ⟨60574954187656677643742231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40383302791771118429161487 60574954187656677643742231)
    ·
      refine ⟨90862431281485016465613347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60574954187656677643742231 90862431281485016465613347)
      ·
        refine ⟨136293646922227524698420021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90862431281485016465613347 136293646922227524698420021)
        ·
          refine ⟨12777529398958830440476877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 136293646922227524698420021 12777529398958830440476877)
          ·
            refine ⟨4791573524609561415178829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12777529398958830440476877 4791573524609561415178829)
            ·
              refine ⟨1796840071728585530692061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4791573524609561415178829 1796840071728585530692061)
              ·
                refine ⟨673815026898219574009523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1796840071728585530692061 673815026898219574009523)
                ·
                  refine ⟨1010722540347329361014285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 673815026898219574009523 1010722540347329361014285)
                  ·
                    refine ⟨379020952630248510380357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1010722540347329361014285 379020952630248510380357)
                    ·
                      rfl

theorem cell22_1107211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 3, 1, 3].length) (baseStart_1107211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1107211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1107211 prefixEnd_1107211 := by exact prefixLift 1107211
  have htrace : WordTrace (prefixWord ++ tailWord_1107211) baseStart_1107211 baseEnd_1107211 := by
    simpa [prefixWord, tailWord_1107211, baseEnd_1107211] using wordTrace_append hprefix tailTrace_1107211
  have hstable : (prefixWord ++ tailWord_1107211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107211).length < 2 ^ (prefixWord ++ tailWord_1107211).sum := by decide
  have hdescent : baseEnd_1107211 < baseStart_1107211 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107271 : List Nat := [1, 1, 4, 1, 2, 4, 3, 1, 1, 4]
def baseStart_1107271 : Nat := 118140960795 + 1107271 * 2 ^ 59
def prefixEnd_1107271 : Nat := 4983230072969 + 3 ^ 40 * 1107271 * 2
def baseEnd_1107271 : Nat := 379041491856428353880173

theorem tailTrace_1107271 : CollatzResearch.WordTrace tailWord_1107271 prefixEnd_1107271 379041491856428353880173 := by
  unfold tailWord_1107271
  simp only [CollatzResearch.WordTrace]
  refine ⟨40385491171553748676345667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26923660781035832450897111 40385491171553748676345667)
  ·
    refine ⟨60578236757330623014518501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40385491171553748676345667 60578236757330623014518501)
    ·
      refine ⟨11358419391999491815222219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60578236757330623014518501 11358419391999491815222219)
      ·
        refine ⟨17037629087999237722833329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11358419391999491815222219 17037629087999237722833329)
        ·
          refine ⟨12778221815999428292124997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17037629087999237722833329 12778221815999428292124997)
          ·
            refine ⟨2395916590499892804773437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12778221815999428292124997 2395916590499892804773437)
            ·
              refine ⟨898468721437459801790039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2395916590499892804773437 898468721437459801790039)
              ·
                refine ⟨1347703082156189702685059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 898468721437459801790039 1347703082156189702685059)
                ·
                  refine ⟨2021554623234284554027589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1347703082156189702685059 2021554623234284554027589)
                  ·
                    refine ⟨379041491856428353880173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2021554623234284554027589 379041491856428353880173)
                    ·
                      rfl

theorem cell22_1107271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 3, 1, 1, 4].length) (baseStart_1107271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1107271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1107271 prefixEnd_1107271 := by exact prefixLift 1107271
  have htrace : WordTrace (prefixWord ++ tailWord_1107271) baseStart_1107271 baseEnd_1107271 := by
    simpa [prefixWord, tailWord_1107271, baseEnd_1107271] using wordTrace_append hprefix tailTrace_1107271
  have hstable : (prefixWord ++ tailWord_1107271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107271).length < 2 ^ (prefixWord ++ tailWord_1107271).sum := by decide
  have hdescent : baseEnd_1107271 < baseStart_1107271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107282 : List Nat := [3, 2, 2, 1, 1, 1, 1, 2, 3, 6]
def baseStart_1107282 : Nat := 118140960795 + 1107282 * 2 ^ 59
def prefixEnd_1107282 : Nat := 4983230072969 + 3 ^ 40 * 1107282 * 2
def baseEnd_1107282 : Nat := 379045257381227991855139

theorem tailTrace_1107282 : CollatzResearch.WordTrace tailWord_1107282 prefixEnd_1107282 379045257381227991855139 := by
  unfold tailWord_1107282
  simp only [CollatzResearch.WordTrace]
  refine ⟨10096473093628474388749025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26923928249675931703330733 10096473093628474388749025)
  ·
    refine ⟨7572354820221355791561769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10096473093628474388749025 7572354820221355791561769)
    ·
      refine ⟨5679266115166016843671327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7572354820221355791561769 5679266115166016843671327)
      ·
        refine ⟨8518899172749025265506991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5679266115166016843671327 8518899172749025265506991)
        ·
          refine ⟨12778348759123537898260487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8518899172749025265506991 12778348759123537898260487)
          ·
            refine ⟨19167523138685306847390731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12778348759123537898260487 19167523138685306847390731)
            ·
              refine ⟨28751284708027960271086097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19167523138685306847390731 28751284708027960271086097)
              ·
                refine ⟨21563463531020970203314573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28751284708027960271086097 21563463531020970203314573)
                ·
                  refine ⟨8086298824132863826242965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21563463531020970203314573 8086298824132863826242965)
                  ·
                    refine ⟨379045257381227991855139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8086298824132863826242965 379045257381227991855139)
                    ·
                      rfl

theorem cell22_1107282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_1107282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1107282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1107282 prefixEnd_1107282 := by exact prefixLift 1107282
  have htrace : WordTrace (prefixWord ++ tailWord_1107282) baseStart_1107282 baseEnd_1107282 := by
    simpa [prefixWord, tailWord_1107282, baseEnd_1107282] using wordTrace_append hprefix tailTrace_1107282
  have hstable : (prefixWord ++ tailWord_1107282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107282).length < 2 ^ (prefixWord ++ tailWord_1107282).sum := by decide
  have hdescent : baseEnd_1107282 < baseStart_1107282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107314 : List Nat := [3, 2, 1, 2, 1, 2, 5, 6]
def baseStart_1107314 : Nat := 118140960795 + 1107314 * 2 ^ 59
def prefixEnd_1107314 : Nat := 4983230072969 + 3 ^ 40 * 1107314 * 2
def baseEnd_1107314 : Nat := 42117356848354508339449

theorem tailTrace_1107314 : CollatzResearch.WordTrace tailWord_1107314 prefixEnd_1107314 42117356848354508339449 := by
  unfold tailWord_1107314
  simp only [CollatzResearch.WordTrace]
  refine ⟨10096764877599491755040249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26924706340265311346773997 10096764877599491755040249)
  ·
    refine ⟨7572573658199618816280187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10096764877599491755040249 7572573658199618816280187)
    ·
      refine ⟨11358860487299428224420281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7572573658199618816280187 11358860487299428224420281)
      ·
        refine ⟨8519145365474571168315211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11358860487299428224420281 8519145365474571168315211)
        ·
          refine ⟨12778718048211856752472817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8519145365474571168315211 12778718048211856752472817)
          ·
            refine ⟨9584038536158892564354613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12778718048211856752472817 9584038536158892564354613)
            ·
              refine ⟨898503612764896177908245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9584038536158892564354613 898503612764896177908245)
              ·
                refine ⟨42117356848354508339449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 898503612764896177908245 42117356848354508339449)
                ·
                  rfl

theorem cell22_1107314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 5, 6].length) (baseStart_1107314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1107314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1107314 prefixEnd_1107314 := by exact prefixLift 1107314
  have htrace : WordTrace (prefixWord ++ tailWord_1107314) baseStart_1107314 baseEnd_1107314 := by
    simpa [prefixWord, tailWord_1107314, baseEnd_1107314] using wordTrace_append hprefix tailTrace_1107314
  have hstable : (prefixWord ++ tailWord_1107314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107314).length < 2 ^ (prefixWord ++ tailWord_1107314).sum := by decide
  have hdescent : baseEnd_1107314 < baseStart_1107314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107453 : List Nat := [1, 4, 1, 1, 1, 5, 2, 2, 2, 3]
def baseStart_1107453 : Nat := 118140960795 + 1107453 * 2 ^ 59
def prefixEnd_1107453 : Nat := 4983230072969 + 3 ^ 40 * 1107453 * 2
def baseEnd_1107453 : Nat := 379103794175840545829615

theorem tailTrace_1107453 : CollatzResearch.WordTrace tailWord_1107453 prefixEnd_1107453 379103794175840545829615 := by
  unfold tailWord_1107453
  simp only [CollatzResearch.WordTrace]
  refine ⟨40392129256894393759471013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26928086171262929172980675 40392129256894393759471013)
  ·
    refine ⟨7573524235667698829900815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40392129256894393759471013 7573524235667698829900815)
    ·
      refine ⟨11360286353501548244851223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7573524235667698829900815 11360286353501548244851223)
      ·
        refine ⟨17040429530252322367276835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11360286353501548244851223 17040429530252322367276835)
        ·
          refine ⟨25560644295378483550915253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17040429530252322367276835 25560644295378483550915253)
          ·
            refine ⟨2396310402691732832898305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25560644295378483550915253 2396310402691732832898305)
            ·
              refine ⟨1797232802018799624673729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2396310402691732832898305 1797232802018799624673729)
              ·
                refine ⟨1347924601514099718505297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1797232802018799624673729 1347924601514099718505297)
                ·
                  refine ⟨1010943451135574788878973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1347924601514099718505297 1010943451135574788878973)
                  ·
                    refine ⟨379103794175840545829615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1010943451135574788878973 379103794175840545829615)
                    ·
                      rfl

theorem cell22_1107453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 2, 2, 3].length) (baseStart_1107453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1107453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1107453 prefixEnd_1107453 := by exact prefixLift 1107453
  have htrace : WordTrace (prefixWord ++ tailWord_1107453) baseStart_1107453 baseEnd_1107453 := by
    simpa [prefixWord, tailWord_1107453, baseEnd_1107453] using wordTrace_append hprefix tailTrace_1107453
  have hstable : (prefixWord ++ tailWord_1107453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107453).length < 2 ^ (prefixWord ++ tailWord_1107453).sum := by decide
  have hdescent : baseEnd_1107453 < baseStart_1107453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107466 : List Nat := [3, 1, 2, 2, 2, 4, 1, 7]
def baseStart_1107466 : Nat := 118140960795 + 1107466 * 2 ^ 59
def prefixEnd_1107466 : Nat := 4983230072969 + 3 ^ 40 * 1107466 * 2
def baseEnd_1107466 : Nat := 42123138260168093917175

theorem tailTrace_1107466 : CollatzResearch.WordTrace tailWord_1107466 prefixEnd_1107466 42123138260168093917175 := by
  unfold tailWord_1107466
  simp only [CollatzResearch.WordTrace]
  refine ⟨10098150851461824244923563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26928402270564864653129501 10098150851461824244923563)
  ·
    refine ⟨15147226277192736367385345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10098150851461824244923563 15147226277192736367385345)
    ·
      refine ⟨11360419707894552275539009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15147226277192736367385345 11360419707894552275539009)
      ·
        refine ⟨8520314780920914206654257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11360419707894552275539009 8520314780920914206654257)
        ·
          refine ⟨6390236085690685654990693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8520314780920914206654257 6390236085690685654990693)
          ·
            refine ⟨1198169266067003560310755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6390236085690685654990693 1198169266067003560310755)
            ·
              refine ⟨1797253899100505340466133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1198169266067003560310755 1797253899100505340466133)
              ·
                refine ⟨42123138260168093917175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1797253899100505340466133 42123138260168093917175)
                ·
                  rfl

theorem cell22_1107466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 7].length) (baseStart_1107466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1107466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1107466 prefixEnd_1107466 := by exact prefixLift 1107466
  have htrace : WordTrace (prefixWord ++ tailWord_1107466) baseStart_1107466 baseEnd_1107466 := by
    simpa [prefixWord, tailWord_1107466, baseEnd_1107466] using wordTrace_append hprefix tailTrace_1107466
  have hstable : (prefixWord ++ tailWord_1107466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107466).length < 2 ^ (prefixWord ++ tailWord_1107466).sum := by decide
  have hdescent : baseEnd_1107466 < baseStart_1107466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107511 : List Nat := [1, 1, 3, 1, 2, 4, 3, 2, 5]
def baseStart_1107511 : Nat := 118140960795 + 1107511 * 2 ^ 59
def prefixEnd_1107511 : Nat := 4983230072969 + 3 ^ 40 * 1107511 * 2
def baseEnd_1107511 : Nat := 126374549587049242626479

theorem tailTrace_1107511 : CollatzResearch.WordTrace tailWord_1107511 prefixEnd_1107511 126374549587049242626479 := by
  unfold tailWord_1107511
  simp only [CollatzResearch.WordTrace]
  refine ⟨40394244690684269665082387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26929496460456179776721591 40394244690684269665082387)
  ·
    refine ⟨60591367036026404497623581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40394244690684269665082387 60591367036026404497623581)
    ·
      refine ⟨22721762638509901686608843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60591367036026404497623581 22721762638509901686608843)
      ·
        refine ⟨34082643957764852529913265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22721762638509901686608843 34082643957764852529913265)
        ·
          refine ⟨25561982968323639397434949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34082643957764852529913265 25561982968323639397434949)
          ·
            refine ⟨4792871806560682387019053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25561982968323639397434949 4792871806560682387019053)
            ·
              refine ⟨1797326927460255895132145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4792871806560682387019053 1797326927460255895132145)
              ·
                refine ⟨1347995195595191921349109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1797326927460255895132145 1347995195595191921349109)
                ·
                  refine ⟨126374549587049242626479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1347995195595191921349109 126374549587049242626479)
                  ·
                    rfl

theorem cell22_1107511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 2, 5].length) (baseStart_1107511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1107511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1107511 prefixEnd_1107511 := by exact prefixLift 1107511
  have htrace : WordTrace (prefixWord ++ tailWord_1107511) baseStart_1107511 baseEnd_1107511 := by
    simpa [prefixWord, tailWord_1107511, baseEnd_1107511] using wordTrace_append hprefix tailTrace_1107511
  have hstable : (prefixWord ++ tailWord_1107511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107511).length < 2 ^ (prefixWord ++ tailWord_1107511).sum := by decide
  have hdescent : baseEnd_1107511 < baseStart_1107511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107573 : List Nat := [1, 3, 4, 2, 1, 1, 3, 1, 6]
def baseStart_1107573 : Nat := 118140960795 + 1107573 * 2 ^ 59
def prefixEnd_1107573 : Nat := 4983230072969 + 3 ^ 40 * 1107573 * 2
def baseEnd_1107573 : Nat := 126381624209400077609749

theorem tailTrace_1107573 : CollatzResearch.WordTrace tailWord_1107573 prefixEnd_1107573 126381624209400077609749 := by
  unfold tailWord_1107573
  simp only [CollatzResearch.WordTrace]
  refine ⟨40396506016459654253839373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26931004010973102835892915 40396506016459654253839373)
  ·
    refine ⟨15148689756172370345189765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40396506016459654253839373 15148689756172370345189765)
    ·
      refine ⟨2840379329282319439723081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15148689756172370345189765 2840379329282319439723081)
      ·
        refine ⟨2130284496961739579792311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2840379329282319439723081 2130284496961739579792311)
        ·
          refine ⟨3195426745442609369688467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2130284496961739579792311 3195426745442609369688467)
          ·
            refine ⟨4793140118163914054532701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3195426745442609369688467 4793140118163914054532701)
            ·
              refine ⟨1797427544311467770449763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4793140118163914054532701 1797427544311467770449763)
              ·
                refine ⟨2696141316467201655674645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1797427544311467770449763 2696141316467201655674645)
                ·
                  refine ⟨126381624209400077609749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2696141316467201655674645 126381624209400077609749)
                  ·
                    rfl

theorem cell22_1107573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 1, 6].length) (baseStart_1107573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1107573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1107573 prefixEnd_1107573 := by exact prefixLift 1107573
  have htrace : WordTrace (prefixWord ++ tailWord_1107573) baseStart_1107573 baseEnd_1107573 := by
    simpa [prefixWord, tailWord_1107573, baseEnd_1107573] using wordTrace_append hprefix tailTrace_1107573
  have hstable : (prefixWord ++ tailWord_1107573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107573).length < 2 ^ (prefixWord ++ tailWord_1107573).sum := by decide
  have hdescent : baseEnd_1107573 < baseStart_1107573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107592 : List Nat := [2, 1, 3, 5, 1, 2, 1, 2, 1, 4]
def baseStart_1107592 : Nat := 118140960795 + 1107592 * 2 ^ 59
def prefixEnd_1107592 : Nat := 4983230072969 + 3 ^ 40 * 1107592 * 2
def baseEnd_1107592 : Nat := 379151376716490516604189

theorem tailTrace_1107592 : CollatzResearch.WordTrace tailWord_1107592 prefixEnd_1107592 379151376716490516604189 := by
  unfold tailWord_1107592
  simp only [CollatzResearch.WordTrace]
  refine ⟨20198599501695410249390515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26931466002260546999187353 20198599501695410249390515)
  ·
    refine ⟨30297899252543115374085773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20198599501695410249390515 30297899252543115374085773)
    ·
      refine ⟨11361712219703668265282165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30297899252543115374085773 11361712219703668265282165)
      ·
        refine ⟨1065160520597218899870203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11361712219703668265282165 1065160520597218899870203)
        ·
          refine ⟨1597740780895828349805305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1065160520597218899870203 1597740780895828349805305)
          ·
            refine ⟨1198305585671871262353979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1597740780895828349805305 1198305585671871262353979)
            ·
              refine ⟨1797458378507806893530969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1198305585671871262353979 1797458378507806893530969)
              ·
                refine ⟨1348093783880855170148227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1797458378507806893530969 1348093783880855170148227)
                ·
                  refine ⟨2022140675821282755222341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1348093783880855170148227 2022140675821282755222341)
                  ·
                    refine ⟨379151376716490516604189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2022140675821282755222341 379151376716490516604189)
                    ·
                      rfl

theorem cell22_1107592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 2, 1, 4].length) (baseStart_1107592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1107592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1107592 prefixEnd_1107592 := by exact prefixLift 1107592
  have htrace : WordTrace (prefixWord ++ tailWord_1107592) baseStart_1107592 baseEnd_1107592 := by
    simpa [prefixWord, tailWord_1107592, baseEnd_1107592] using wordTrace_append hprefix tailTrace_1107592
  have hstable : (prefixWord ++ tailWord_1107592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107592).length < 2 ^ (prefixWord ++ tailWord_1107592).sum := by decide
  have hdescent : baseEnd_1107592 < baseStart_1107592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107618 : List Nat := [3, 3, 1, 4, 1, 10]
def baseStart_1107618 : Nat := 118140960795 + 1107618 * 2 ^ 59
def prefixEnd_1107618 : Nat := 4983230072969 + 3 ^ 40 * 1107618 * 2
def baseEnd_1107618 : Nat := 4680991074664631054989

theorem tailTrace_1107618 : CollatzResearch.WordTrace tailWord_1107618 prefixEnd_1107618 4680991074664631054989 := by
  unfold tailWord_1107618
  simp only [CollatzResearch.WordTrace]
  refine ⟨10099536825324156734806877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26932098200864417959485005 10099536825324156734806877)
  ·
    refine ⟨3787326309496558775552579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10099536825324156734806877 3787326309496558775552579)
    ·
      refine ⟨5680989464244838163328869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3787326309496558775552579 5680989464244838163328869)
      ·
        refine ⟨1065185524545907155624163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5680989464244838163328869 1065185524545907155624163)
        ·
          refine ⟨1597778286818860733436245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1065185524545907155624163 1597778286818860733436245)
          ·
            refine ⟨4680991074664631054989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1597778286818860733436245 4680991074664631054989)
            ·
              rfl

theorem cell22_1107618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 10].length) (baseStart_1107618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1107618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1107618 prefixEnd_1107618 := by exact prefixLift 1107618
  have htrace : WordTrace (prefixWord ++ tailWord_1107618) baseStart_1107618 baseEnd_1107618 := by
    simpa [prefixWord, tailWord_1107618, baseEnd_1107618] using wordTrace_append hprefix tailTrace_1107618
  have hstable : (prefixWord ++ tailWord_1107618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107618).length < 2 ^ (prefixWord ++ tailWord_1107618).sum := by decide
  have hdescent : baseEnd_1107618 < baseStart_1107618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107624 : List Nat := [2, 1, 7, 1, 1, 1, 1, 4, 4]
def baseStart_1107624 : Nat := 118140960795 + 1107624 * 2 ^ 59
def prefixEnd_1107624 : Nat := 4983230072969 + 3 ^ 40 * 1107624 * 2
def baseEnd_1107624 : Nat := 126387443656817699934697

theorem tailTrace_1107624 : CollatzResearch.WordTrace tailWord_1107624 prefixEnd_1107624 126387443656817699934697 := by
  unfold tailWord_1107624
  simp only [CollatzResearch.WordTrace]
  refine ⟨20199183069637444981972963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26932244092849926642630617 20199183069637444981972963)
  ·
    refine ⟨30298774604456167472959445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20199183069637444981972963 30298774604456167472959445)
    ·
      refine ⟨710127529791941425147487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 30298774604456167472959445 710127529791941425147487)
      ·
        refine ⟨1065191294687912137721231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 710127529791941425147487 1065191294687912137721231)
        ·
          refine ⟨1597786942031868206581847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1065191294687912137721231 1597786942031868206581847)
          ·
            refine ⟨2396680413047802309872771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1597786942031868206581847 2396680413047802309872771)
            ·
              refine ⟨3595020619571703464809157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2396680413047802309872771 3595020619571703464809157)
              ·
                refine ⟨674066366169694399651717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3595020619571703464809157 674066366169694399651717)
                ·
                  refine ⟨126387443656817699934697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 674066366169694399651717 126387443656817699934697)
                  ·
                    rfl

theorem cell22_1107624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 4, 4].length) (baseStart_1107624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1107624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1107624 prefixEnd_1107624 := by exact prefixLift 1107624
  have htrace : WordTrace (prefixWord ++ tailWord_1107624) baseStart_1107624 baseEnd_1107624 := by
    simpa [prefixWord, tailWord_1107624, baseEnd_1107624] using wordTrace_append hprefix tailTrace_1107624
  have hstable : (prefixWord ++ tailWord_1107624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107624).length < 2 ^ (prefixWord ++ tailWord_1107624).sum := by decide
  have hdescent : baseEnd_1107624 < baseStart_1107624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107654 : List Nat := [6, 1, 2, 1, 1, 3, 1, 1, 2, 4]
def baseStart_1107654 : Nat := 118140960795 + 1107654 * 2 ^ 59
def prefixEnd_1107654 : Nat := 4983230072969 + 3 ^ 40 * 1107654 * 2
def baseEnd_1107654 : Nat := 379172600583543021553999

theorem tailTrace_1107654 : CollatzResearch.WordTrace tailWord_1107654 prefixEnd_1107654 379172600583543021553999 := by
  unfold tailWord_1107654
  simp only [CollatzResearch.WordTrace]
  refine ⟨1262483135286443908985563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 26932973552777470058358677 1262483135286443908985563)
  ·
    refine ⟨1893724702929665863478345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1262483135286443908985563 1893724702929665863478345)
    ·
      refine ⟨1420293527197249397608759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1893724702929665863478345 1420293527197249397608759)
      ·
        refine ⟨2130440290795874096413139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1420293527197249397608759 2130440290795874096413139)
        ·
          refine ⟨3195660436193811144619709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2130440290795874096413139 3195660436193811144619709)
          ·
            refine ⟨1198372663572679179232391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3195660436193811144619709 1198372663572679179232391)
            ·
              refine ⟨1797558995359018768848587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1198372663572679179232391 1797558995359018768848587)
              ·
                refine ⟨2696338493038528153272881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1797558995359018768848587 2696338493038528153272881)
                ·
                  refine ⟨2022253869778896114954661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2696338493038528153272881 2022253869778896114954661)
                  ·
                    refine ⟨379172600583543021553999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2022253869778896114954661 379172600583543021553999)
                    ·
                      rfl

theorem cell22_1107654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_1107654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1107654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1107654 prefixEnd_1107654 := by exact prefixLift 1107654
  have htrace : WordTrace (prefixWord ++ tailWord_1107654) baseStart_1107654 baseEnd_1107654 := by
    simpa [prefixWord, tailWord_1107654, baseEnd_1107654] using wordTrace_append hprefix tailTrace_1107654
  have hstable : (prefixWord ++ tailWord_1107654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107654).length < 2 ^ (prefixWord ++ tailWord_1107654).sum := by decide
  have hdescent : baseEnd_1107654 < baseStart_1107654 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107691 : List Nat := [1, 1, 1, 1, 2, 4, 3, 3, 6]
def baseStart_1107691 : Nat := 118140960795 + 1107691 * 2 ^ 59
def prefixEnd_1107691 : Nat := 4983230072969 + 3 ^ 40 * 1107691 * 2
def baseEnd_1107691 : Nat := 126395088813229086126295

theorem tailTrace_1107691 : CollatzResearch.WordTrace tailWord_1107691 prefixEnd_1107691 126395088813229086126295 := by
  unfold tailWord_1107691
  simp only [CollatzResearch.WordTrace]
  refine ⟨40400809830032160406634927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26933873220021440271089951 40400809830032160406634927)
  ·
    refine ⟨60601214745048240609952391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40400809830032160406634927 60601214745048240609952391)
    ·
      refine ⟨90901822117572360914928587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60601214745048240609952391 90901822117572360914928587)
      ·
        refine ⟨136352733176358541372392881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90901822117572360914928587 136352733176358541372392881)
        ·
          refine ⟨102264549882268906029294661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136352733176358541372392881 102264549882268906029294661)
          ·
            refine ⟨19174603102925419880492749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 102264549882268906029294661 19174603102925419880492749)
            ·
              refine ⟨7190476163597032455184781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19174603102925419880492749 7190476163597032455184781)
              ·
                refine ⟨2696428561348887170694293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7190476163597032455184781 2696428561348887170694293)
                ·
                  refine ⟨126395088813229086126295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2696428561348887170694293 126395088813229086126295)
                  ·
                    rfl

theorem cell22_1107691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 3, 6].length) (baseStart_1107691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1107691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1107691 prefixEnd_1107691 := by exact prefixLift 1107691
  have htrace : WordTrace (prefixWord ++ tailWord_1107691) baseStart_1107691 baseEnd_1107691 := by
    simpa [prefixWord, tailWord_1107691, baseEnd_1107691] using wordTrace_append hprefix tailTrace_1107691
  have hstable : (prefixWord ++ tailWord_1107691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107691).length < 2 ^ (prefixWord ++ tailWord_1107691).sum := by decide
  have hdescent : baseEnd_1107691 < baseStart_1107691 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107723 : List Nat := [1, 1, 1, 1, 5, 1, 3, 2, 4, 3]
def baseStart_1107723 : Nat := 118140960795 + 1107723 * 2 ^ 59
def prefixEnd_1107723 : Nat := 4983230072969 + 3 ^ 40 * 1107723 * 2
def baseEnd_1107723 : Nat := 379196220693649841578787

theorem tailTrace_1107723 : CollatzResearch.WordTrace tailWord_1107723 prefixEnd_1107723 379196220693649841578787 := by
  unfold tailWord_1107723
  simp only [CollatzResearch.WordTrace]
  refine ⟨40401976965916229871799823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26934651310610819914533215 40401976965916229871799823)
  ·
    refine ⟨60602965448874344807699735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40401976965916229871799823 60602965448874344807699735)
    ·
      refine ⟨90904448173311517211549603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60602965448874344807699735 90904448173311517211549603)
      ·
        refine ⟨136356672259967275817324405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90904448173311517211549603 136356672259967275817324405)
        ·
          refine ⟨12783438024371932107874163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 136356672259967275817324405 12783438024371932107874163)
          ·
            refine ⟨19175157036557898161811245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12783438024371932107874163 19175157036557898161811245)
            ·
              refine ⟨7190683888709211810679217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19175157036557898161811245 7190683888709211810679217)
              ·
                refine ⟨5393012916531908858009413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7190683888709211810679217 5393012916531908858009413)
                ·
                  refine ⟨1011189921849732910876765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5393012916531908858009413 1011189921849732910876765)
                  ·
                    refine ⟨379196220693649841578787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1011189921849732910876765 379196220693649841578787)
                    ·
                      rfl

theorem cell22_1107723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 2, 4, 3].length) (baseStart_1107723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1107723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1107723 prefixEnd_1107723 := by exact prefixLift 1107723
  have htrace : WordTrace (prefixWord ++ tailWord_1107723) baseStart_1107723 baseEnd_1107723 := by
    simpa [prefixWord, tailWord_1107723, baseEnd_1107723] using wordTrace_append hprefix tailTrace_1107723
  have hstable : (prefixWord ++ tailWord_1107723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107723).length < 2 ^ (prefixWord ++ tailWord_1107723).sum := by decide
  have hdescent : baseEnd_1107723 < baseStart_1107723 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107736 : List Nat := [2, 1, 2, 3, 1, 1, 12]
def baseStart_1107736 : Nat := 118140960795 + 1107736 * 2 ^ 59
def prefixEnd_1107736 : Nat := 4983230072969 + 3 ^ 40 * 1107736 * 2
def baseEnd_1107736 : Nat := 14044469291086005222361

theorem tailTrace_1107736 : CollatzResearch.WordTrace tailWord_1107736 prefixEnd_1107736 14044469291086005222361 := by
  unfold tailWord_1107736
  simp only [CollatzResearch.WordTrace]
  refine ⟨20201225557434566546011531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26934967409912755394682041 20201225557434566546011531)
  ·
    refine ⟨30301838336151849819017297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20201225557434566546011531 30301838336151849819017297)
    ·
      refine ⟨22726378752113887364262973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30301838336151849819017297 22726378752113887364262973)
      ·
        refine ⟨8522392032042707761598615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22726378752113887364262973 8522392032042707761598615)
        ·
          refine ⟨12783588048064061642397923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8522392032042707761598615 12783588048064061642397923)
          ·
            refine ⟨19175382072096092463596885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12783588048064061642397923 19175382072096092463596885)
            ·
              refine ⟨14044469291086005222361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 19175382072096092463596885 14044469291086005222361)
              ·
                rfl

theorem cell22_1107736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 12].length) (baseStart_1107736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1107736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1107736 prefixEnd_1107736 := by exact prefixLift 1107736
  have htrace : WordTrace (prefixWord ++ tailWord_1107736) baseStart_1107736 baseEnd_1107736 := by
    simpa [prefixWord, tailWord_1107736, baseEnd_1107736] using wordTrace_append hprefix tailTrace_1107736
  have hstable : (prefixWord ++ tailWord_1107736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107736).length < 2 ^ (prefixWord ++ tailWord_1107736).sum := by decide
  have hdescent : baseEnd_1107736 < baseStart_1107736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107738 : List Nat := [3, 1, 1, 3, 2, 2, 1, 1, 4, 4]
def baseStart_1107738 : Nat := 118140960795 + 1107738 * 2 ^ 59
def prefixEnd_1107738 : Nat := 4983230072969 + 3 ^ 40 * 1107738 * 2
def baseEnd_1107738 : Nat := 379201355500194802453741

theorem tailTrace_1107738 : CollatzResearch.WordTrace tailWord_1107738 prefixEnd_1107738 379201355500194802453741 := by
  unfold tailWord_1107738
  simp only [CollatzResearch.WordTrace]
  refine ⟨10100631015215471858398967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26935016040574591622397245 10100631015215471858398967)
  ·
    refine ⟨15150946522823207787598451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10100631015215471858398967 15150946522823207787598451)
    ·
      refine ⟨22726419784234811681397677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15150946522823207787598451 22726419784234811681397677)
      ·
        refine ⟨8522407419088054380524129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22726419784234811681397677 8522407419088054380524129)
        ·
          refine ⟨6391805564316040785393097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8522407419088054380524129 6391805564316040785393097)
          ·
            refine ⟨4793854173237030589044823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6391805564316040785393097 4793854173237030589044823)
            ·
              refine ⟨7190781259855545883567235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4793854173237030589044823 7190781259855545883567235)
              ·
                refine ⟨10786171889783318825350853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7190781259855545883567235 10786171889783318825350853)
                ·
                  refine ⟨2022407229334372279753285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10786171889783318825350853 2022407229334372279753285)
                  ·
                    refine ⟨379201355500194802453741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2022407229334372279753285 379201355500194802453741)
                    ·
                      rfl

theorem cell22_1107738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 4, 4].length) (baseStart_1107738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1107738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1107738 prefixEnd_1107738 := by exact prefixLift 1107738
  have htrace : WordTrace (prefixWord ++ tailWord_1107738) baseStart_1107738 baseEnd_1107738 := by
    simpa [prefixWord, tailWord_1107738, baseEnd_1107738] using wordTrace_append hprefix tailTrace_1107738
  have hstable : (prefixWord ++ tailWord_1107738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107738).length < 2 ^ (prefixWord ++ tailWord_1107738).sum := by decide
  have hdescent : baseEnd_1107738 < baseStart_1107738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107740 : List Nat := [2, 2, 3, 1, 1, 2, 2, 4, 2, 3]
def baseStart_1107740 : Nat := 118140960795 + 1107740 * 2 ^ 59
def prefixEnd_1107740 : Nat := 4983230072969 + 3 ^ 40 * 1107740 * 2
def baseEnd_1107740 : Nat := 379202040141067463903735

theorem tailTrace_1107740 : CollatzResearch.WordTrace tailWord_1107740 prefixEnd_1107740 379202040141067463903735 := by
  unfold tailWord_1107740
  simp only [CollatzResearch.WordTrace]
  refine ⟨20201298503427320887584337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26935064671236427850112449 20201298503427320887584337)
  ·
    refine ⟨15150973877570490665688253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20201298503427320887584337 15150973877570490665688253)
    ·
      refine ⟨5681615204088933999633095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15150973877570490665688253 5681615204088933999633095)
      ·
        refine ⟨8522422806133400999449643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5681615204088933999633095 8522422806133400999449643)
        ·
          refine ⟨12783634209200101499174465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8522422806133400999449643 12783634209200101499174465)
          ·
            refine ⟨9587725656900076124380849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12783634209200101499174465 9587725656900076124380849)
            ·
              refine ⟨7190794242675057093285637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9587725656900076124380849 7190794242675057093285637)
              ·
                refine ⟨1348273920501573204991057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7190794242675057093285637 1348273920501573204991057)
                ·
                  refine ⟨1011205440376179903743293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1348273920501573204991057 1011205440376179903743293)
                  ·
                    refine ⟨379202040141067463903735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1011205440376179903743293 379202040141067463903735)
                    ·
                      rfl

theorem cell22_1107740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 4, 2, 3].length) (baseStart_1107740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1107740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1107740 prefixEnd_1107740 := by exact prefixLift 1107740
  have htrace : WordTrace (prefixWord ++ tailWord_1107740) baseStart_1107740 baseEnd_1107740 := by
    simpa [prefixWord, tailWord_1107740, baseEnd_1107740] using wordTrace_append hprefix tailTrace_1107740
  have hstable : (prefixWord ++ tailWord_1107740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107740).length < 2 ^ (prefixWord ++ tailWord_1107740).sum := by decide
  have hdescent : baseEnd_1107740 < baseStart_1107740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107802 : List Nat := [3, 1, 1, 2, 1, 3, 3, 4, 1, 3]
def baseStart_1107802 : Nat := 118140960795 + 1107802 * 2 ^ 59
def prefixEnd_1107802 : Nat := 4983230072969 + 3 ^ 40 * 1107802 * 2
def baseEnd_1107802 : Nat := 379223264008119968853545

theorem tailTrace_1107802 : CollatzResearch.WordTrace tailWord_1107802 prefixEnd_1107802 379223264008119968853545 := by
  unfold tailWord_1107802
  simp only [CollatzResearch.WordTrace]
  refine ⟨10101214583157506590981415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26936572221753350909283773 10101214583157506590981415)
  ·
    refine ⟨15151821874736259886472123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10101214583157506590981415 15151821874736259886472123)
    ·
      refine ⟨22727732812104389829708185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15151821874736259886472123 22727732812104389829708185)
      ·
        refine ⟨17045799609078292372281139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22727732812104389829708185 17045799609078292372281139)
        ·
          refine ⟨25568699413617438558421709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17045799609078292372281139 25568699413617438558421709)
          ·
            refine ⟨9588262280106539459408141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25568699413617438558421709 9588262280106539459408141)
            ·
              refine ⟨3595598355039952297278053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9588262280106539459408141 3595598355039952297278053)
              ·
                refine ⟨674174691569991055739635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3595598355039952297278053 674174691569991055739635)
                ·
                  refine ⟨1011262037354986583609453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 674174691569991055739635 1011262037354986583609453)
                  ·
                    refine ⟨379223264008119968853545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1011262037354986583609453 379223264008119968853545)
                    ·
                      rfl

theorem cell22_1107802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 4, 1, 3].length) (baseStart_1107802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1107802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1107802 prefixEnd_1107802 := by exact prefixLift 1107802
  have htrace : WordTrace (prefixWord ++ tailWord_1107802) baseStart_1107802 baseEnd_1107802 := by
    simpa [prefixWord, tailWord_1107802, baseEnd_1107802] using wordTrace_append hprefix tailTrace_1107802
  have hstable : (prefixWord ++ tailWord_1107802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107802).length < 2 ^ (prefixWord ++ tailWord_1107802).sum := by decide
  have hdescent : baseEnd_1107802 < baseStart_1107802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107845 : List Nat := [1, 3, 1, 1, 3, 2, 3, 3, 1, 4]
def baseStart_1107845 : Nat := 118140960795 + 1107845 * 2 ^ 59
def prefixEnd_1107845 : Nat := 4983230072969 + 3 ^ 40 * 1107845 * 2
def baseEnd_1107845 : Nat := 379237983786882190028413

theorem tailTrace_1107845 : CollatzResearch.WordTrace tailWord_1107845 prefixEnd_1107845 379237983786882190028413 := by
  unfold tailWord_1107845
  simp only [CollatzResearch.WordTrace]
  refine ⟨40406426671474244707740989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26937617780982829805160659 40406426671474244707740989)
  ·
    refine ⟨15152410001802841765402871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40406426671474244707740989 15152410001802841765402871)
    ·
      refine ⟨22728615002704262648104307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15152410001802841765402871 22728615002704262648104307)
      ·
        refine ⟨34092922504056393972156461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22728615002704262648104307 34092922504056393972156461)
        ·
          refine ⟨12784845939021147739558673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34092922504056393972156461 12784845939021147739558673)
          ·
            refine ⟨9588634454265860804669005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12784845939021147739558673 9588634454265860804669005)
            ·
              refine ⟨3595737920349697801750877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9588634454265860804669005 3595737920349697801750877)
              ·
                refine ⟨1348401720131136675656579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3595737920349697801750877 1348401720131136675656579)
                ·
                  refine ⟨2022602580196705013484869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1348401720131136675656579 2022602580196705013484869)
                  ·
                    refine ⟨379237983786882190028413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2022602580196705013484869 379237983786882190028413)
                    ·
                      rfl

theorem cell22_1107845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 3, 1, 4].length) (baseStart_1107845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1107845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1107845 prefixEnd_1107845 := by exact prefixLift 1107845
  have htrace : WordTrace (prefixWord ++ tailWord_1107845) baseStart_1107845 baseEnd_1107845 := by
    simpa [prefixWord, tailWord_1107845, baseEnd_1107845] using wordTrace_append hprefix tailTrace_1107845
  have hstable : (prefixWord ++ tailWord_1107845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107845).length < 2 ^ (prefixWord ++ tailWord_1107845).sum := by decide
  have hdescent : baseEnd_1107845 < baseStart_1107845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107860 : List Nat := [2, 4, 2, 1, 1, 2, 1, 3, 6]
def baseStart_1107860 : Nat := 118140960795 + 1107860 * 2 ^ 59
def prefixEnd_1107860 : Nat := 4983230072969 + 3 ^ 40 * 1107860 * 2
def baseEnd_1107860 : Nat := 126414372864475716967789

theorem tailTrace_1107860 : CollatzResearch.WordTrace tailWord_1107860 prefixEnd_1107860 126414372864475716967789 := by
  unfold tailWord_1107860
  simp only [CollatzResearch.WordTrace]
  refine ⟨20203486883209951134768517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26937982510946601513024689 20203486883209951134768517)
  ·
    refine ⟨3788153790601865837769097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20203486883209951134768517 3788153790601865837769097)
    ·
      refine ⟨2841115342951399378326823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3788153790601865837769097 2841115342951399378326823)
      ·
        refine ⟨4261673014427099067490235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2841115342951399378326823 4261673014427099067490235)
        ·
          refine ⟨6392509521640648601235353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4261673014427099067490235 6392509521640648601235353)
          ·
            refine ⟨4794382141230486450926515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6392509521640648601235353 4794382141230486450926515)
            ·
              refine ⟨7191573211845729676389773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4794382141230486450926515 7191573211845729676389773)
              ·
                refine ⟨2696839954442148628646165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7191573211845729676389773 2696839954442148628646165)
                ·
                  refine ⟨126414372864475716967789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2696839954442148628646165 126414372864475716967789)
                  ·
                    rfl

theorem cell22_1107860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 3, 6].length) (baseStart_1107860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1107860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1107860 prefixEnd_1107860 := by exact prefixLift 1107860
  have htrace : WordTrace (prefixWord ++ tailWord_1107860) baseStart_1107860 baseEnd_1107860 := by
    simpa [prefixWord, tailWord_1107860, baseEnd_1107860] using wordTrace_append hprefix tailTrace_1107860
  have hstable : (prefixWord ++ tailWord_1107860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107860).length < 2 ^ (prefixWord ++ tailWord_1107860).sum := by decide
  have hdescent : baseEnd_1107860 < baseStart_1107860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107922 : List Nat := [3, 2, 2, 3, 2, 1, 2, 7]
def baseStart_1107922 : Nat := 118140960795 + 1107922 * 2 ^ 59
def prefixEnd_1107922 : Nat := 4983230072969 + 3 ^ 40 * 1107922 * 2
def baseEnd_1107922 : Nat := 42140482495608850650353

theorem tailTrace_1107922 : CollatzResearch.WordTrace tailWord_1107922 prefixEnd_1107922 42140482495608850650353 := by
  unfold tailWord_1107922
  simp only [CollatzResearch.WordTrace]
  refine ⟨10102308773048821714573505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26939490061463524572196013 10102308773048821714573505)
  ·
    refine ⟨7576731579786616285930129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10102308773048821714573505 7576731579786616285930129)
    ·
      refine ⟨5682548684839962214447597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7576731579786616285930129 5682548684839962214447597)
      ·
        refine ⟨2130955756814985830417849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5682548684839962214447597 2130955756814985830417849)
        ·
          refine ⟨1598216817611239372813387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2130955756814985830417849 1598216817611239372813387)
          ·
            refine ⟨2397325226416859059220081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1598216817611239372813387 2397325226416859059220081)
            ·
              refine ⟨1797993919812644294415061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2397325226416859059220081 1797993919812644294415061)
              ·
                refine ⟨42140482495608850650353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1797993919812644294415061 42140482495608850650353)
                ·
                  rfl

theorem cell22_1107922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 7].length) (baseStart_1107922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1107922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1107922 prefixEnd_1107922 := by exact prefixLift 1107922
  have htrace : WordTrace (prefixWord ++ tailWord_1107922) baseStart_1107922 baseEnd_1107922 := by
    simpa [prefixWord, tailWord_1107922, baseEnd_1107922] using wordTrace_append hprefix tailTrace_1107922
  have hstable : (prefixWord ++ tailWord_1107922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107922).length < 2 ^ (prefixWord ++ tailWord_1107922).sum := by decide
  have hdescent : baseEnd_1107922 < baseStart_1107922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107926 : List Nat := [5, 2, 1, 1, 3, 1, 1, 3, 2, 3]
def baseStart_1107926 : Nat := 118140960795 + 1107926 * 2 ^ 59
def prefixEnd_1107926 : Nat := 4983230072969 + 3 ^ 40 * 1107926 * 2
def baseEnd_1107926 : Nat := 379265711742224978753165

theorem tailTrace_1107926 : CollatzResearch.WordTrace tailWord_1107926 prefixEnd_1107926 379265711742224978753165 := by
  unfold tailWord_1107926
  simp only [CollatzResearch.WordTrace]
  refine ⟨2525586311511299721339977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26939587322787197027626421 2525586311511299721339977)
  ·
    refine ⟨1894189733633474791004983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2525586311511299721339977 1894189733633474791004983)
    ·
      refine ⟨2841284600450212186507475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1894189733633474791004983 2841284600450212186507475)
      ·
        refine ⟨4261926900675318279761213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2841284600450212186507475 4261926900675318279761213)
        ·
          refine ⟨1598222587753244354910455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4261926900675318279761213 1598222587753244354910455)
          ·
            refine ⟨2397333881629866532365683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1598222587753244354910455 2397333881629866532365683)
            ·
              refine ⟨3596000822444799798548525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2397333881629866532365683 3596000822444799798548525)
              ·
                refine ⟨1348500308416799924455697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3596000822444799798548525 1348500308416799924455697)
                ·
                  refine ⟨1011375231312599943341773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1348500308416799924455697 1011375231312599943341773)
                  ·
                    refine ⟨379265711742224978753165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1011375231312599943341773 379265711742224978753165)
                    ·
                      rfl

theorem cell22_1107926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_1107926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1107926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1107926 prefixEnd_1107926 := by exact prefixLift 1107926
  have htrace : WordTrace (prefixWord ++ tailWord_1107926) baseStart_1107926 baseEnd_1107926 := by
    simpa [prefixWord, tailWord_1107926, baseEnd_1107926] using wordTrace_append hprefix tailTrace_1107926
  have hstable : (prefixWord ++ tailWord_1107926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107926).length < 2 ^ (prefixWord ++ tailWord_1107926).sum := by decide
  have hdescent : baseEnd_1107926 < baseStart_1107926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107980 : List Nat := [2, 2, 1, 2, 3, 1, 1, 1, 5, 4]
def baseStart_1107980 : Nat := 118140960795 + 1107980 * 2 ^ 59
def prefixEnd_1107980 : Nat := 4983230072969 + 3 ^ 40 * 1107980 * 2
def baseEnd_1107980 : Nat := 379284197045786837902999

theorem tailTrace_1107980 : CollatzResearch.WordTrace tailWord_1107980 prefixEnd_1107980 379284197045786837902999 := by
  unfold tailWord_1107980
  simp only [CollatzResearch.WordTrace]
  refine ⟨20205675262992581381952697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26940900350656775175936929 20205675262992581381952697)
  ·
    refine ⟨15154256447244436036464523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20205675262992581381952697 15154256447244436036464523)
    ·
      refine ⟨22731384670866654054696785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15154256447244436036464523 22731384670866654054696785)
      ·
        refine ⟨17048538503149990541022589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22731384670866654054696785 17048538503149990541022589)
        ·
          refine ⟨6393201938681246452883471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17048538503149990541022589 6393201938681246452883471)
          ·
            refine ⟨9589802908021869679325207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6393201938681246452883471 9589802908021869679325207)
            ·
              refine ⟨14384704362032804518987811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9589802908021869679325207 14384704362032804518987811)
              ·
                refine ⟨21577056543049206778481717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14384704362032804518987811 21577056543049206778481717)
                ·
                  refine ⟨2022849050910863135482661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21577056543049206778481717 2022849050910863135482661)
                  ·
                    refine ⟨379284197045786837902999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2022849050910863135482661 379284197045786837902999)
                    ·
                      rfl

theorem cell22_1107980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 5, 4].length) (baseStart_1107980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1107980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1107980 prefixEnd_1107980 := by exact prefixLift 1107980
  have htrace : WordTrace (prefixWord ++ tailWord_1107980) baseStart_1107980 baseEnd_1107980 := by
    simpa [prefixWord, tailWord_1107980, baseEnd_1107980] using wordTrace_append hprefix tailTrace_1107980
  have hstable : (prefixWord ++ tailWord_1107980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107980).length < 2 ^ (prefixWord ++ tailWord_1107980).sum := by decide
  have hdescent : baseEnd_1107980 < baseStart_1107980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1107997 : List Nat := [1, 4, 2, 2, 2, 1, 2, 1, 3, 4]
def baseStart_1107997 : Nat := 118140960795 + 1107997 * 2 ^ 59
def prefixEnd_1107997 : Nat := 4983230072969 + 3 ^ 40 * 1107997 * 2
def baseEnd_1107997 : Nat := 379290016493204460227947

theorem tailTrace_1107997 : CollatzResearch.WordTrace tailWord_1107997 prefixEnd_1107997 379290016493204460227947 := by
  unfold tailWord_1107997
  simp only [CollatzResearch.WordTrace]
  refine ⟨40411970566923574667274245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26941313711282383111516163 40411970566923574667274245)
  ·
    refine ⟨7577244481298170250113921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40411970566923574667274245 7577244481298170250113921)
    ·
      refine ⟨5682933360973627687585441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7577244481298170250113921 5682933360973627687585441)
      ·
        refine ⟨4262200020730220765689081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5682933360973627687585441 4262200020730220765689081)
        ·
          refine ⟨3196650015547665574266811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4262200020730220765689081 3196650015547665574266811)
          ·
            refine ⟨4794975023321498361400217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3196650015547665574266811 4794975023321498361400217)
            ·
              refine ⟨3596231267491123771050163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4794975023321498361400217 3596231267491123771050163)
              ·
                refine ⟨5394346901236685656575245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3596231267491123771050163 5394346901236685656575245)
                ·
                  refine ⟨2022880087963757121215717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5394346901236685656575245 2022880087963757121215717)
                  ·
                    refine ⟨379290016493204460227947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2022880087963757121215717 379290016493204460227947)
                    ·
                      rfl

theorem cell22_1107997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_1107997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1107997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1107997 prefixEnd_1107997 := by exact prefixLift 1107997
  have htrace : WordTrace (prefixWord ++ tailWord_1107997) baseStart_1107997 baseEnd_1107997 := by
    simpa [prefixWord, tailWord_1107997, baseEnd_1107997] using wordTrace_append hprefix tailTrace_1107997
  have hstable : (prefixWord ++ tailWord_1107997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1107997).length < 2 ^ (prefixWord ++ tailWord_1107997).sum := by decide
  have hdescent : baseEnd_1107997 < baseStart_1107997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1107997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108014 : List Nat := [4, 1, 3, 1, 1, 3, 1, 3, 1, 4]
def baseStart_1108014 : Nat := 118140960795 + 1108014 * 2 ^ 59
def prefixEnd_1108014 : Nat := 4983230072969 + 3 ^ 40 * 1108014 * 2
def baseEnd_1108014 : Nat := 379295835940622082552895

theorem tailTrace_1108014 : CollatzResearch.WordTrace tailWord_1108014 prefixEnd_1108014 379295835940622082552895 := by
  unfold tailWord_1108014
  simp only [CollatzResearch.WordTrace]
  refine ⟨5051573825982748321330387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26941727071907991047095397 5051573825982748321330387)
  ·
    refine ⟨7577360738974122481995581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5051573825982748321330387 7577360738974122481995581)
    ·
      refine ⟨2841510277115295930748343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7577360738974122481995581 2841510277115295930748343)
      ·
        refine ⟨4262265415672943896122515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2841510277115295930748343 4262265415672943896122515)
        ·
          refine ⟨6393398123509415844183773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4262265415672943896122515 6393398123509415844183773)
          ·
            refine ⟨2397524296316030941568915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6393398123509415844183773 2397524296316030941568915)
            ·
              refine ⟨3596286444474046412353373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2397524296316030941568915 3596286444474046412353373)
              ·
                refine ⟨1348607416677767404632515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3596286444474046412353373 1348607416677767404632515)
                ·
                  refine ⟨2022911125016651106948773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1348607416677767404632515 2022911125016651106948773)
                  ·
                    refine ⟨379295835940622082552895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2022911125016651106948773 379295835940622082552895)
                    ·
                      rfl

theorem cell22_1108014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_1108014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1108014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1108014 prefixEnd_1108014 := by exact prefixLift 1108014
  have htrace : WordTrace (prefixWord ++ tailWord_1108014) baseStart_1108014 baseEnd_1108014 := by
    simpa [prefixWord, tailWord_1108014, baseEnd_1108014] using wordTrace_append hprefix tailTrace_1108014
  have hstable : (prefixWord ++ tailWord_1108014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108014).length < 2 ^ (prefixWord ++ tailWord_1108014).sum := by decide
  have hdescent : baseEnd_1108014 < baseStart_1108014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108074 : List Nat := [3, 1, 3, 2, 4, 1, 8]
def baseStart_1108074 : Nat := 118140960795 + 1108074 * 2 ^ 59
def prefixEnd_1108074 : Nat := 4983230072969 + 3 ^ 40 * 1108074 * 2
def baseEnd_1108074 : Nat := 14048754635807478742693

theorem tailTrace_1108074 : CollatzResearch.WordTrace tailWord_1108074 prefixEnd_1108074 14048754635807478742693 := by
  unfold tailWord_1108074
  simp only [CollatzResearch.WordTrace]
  refine ⟨10103694746911154204456819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26943185991763077878551517 10103694746911154204456819)
  ·
    refine ⟨15155542120366731306685229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10103694746911154204456819 15155542120366731306685229)
    ·
      refine ⟨5683328295137524240006961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15155542120366731306685229 5683328295137524240006961)
      ·
        refine ⟨4262496221353143180005221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5683328295137524240006961 4262496221353143180005221)
        ·
          refine ⟨799218041503714346250979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4262496221353143180005221 799218041503714346250979)
          ·
            refine ⟨1198827062255571519376469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 799218041503714346250979 1198827062255571519376469)
            ·
              refine ⟨14048754635807478742693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1198827062255571519376469 14048754635807478742693)
              ·
                rfl

theorem cell22_1108074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 8].length) (baseStart_1108074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1108074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1108074 prefixEnd_1108074 := by exact prefixLift 1108074
  have htrace : WordTrace (prefixWord ++ tailWord_1108074) baseStart_1108074 baseEnd_1108074 := by
    simpa [prefixWord, tailWord_1108074, baseEnd_1108074] using wordTrace_append hprefix tailTrace_1108074
  have hstable : (prefixWord ++ tailWord_1108074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108074).length < 2 ^ (prefixWord ++ tailWord_1108074).sum := by decide
  have hdescent : baseEnd_1108074 < baseStart_1108074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108089 : List Nat := [1, 2, 1, 3, 4, 1, 3, 1, 3, 3]
def baseStart_1108089 : Nat := 118140960795 + 1108089 * 2 ^ 59
def prefixEnd_1108089 : Nat := 4983230072969 + 3 ^ 40 * 1108089 * 2
def baseEnd_1108089 : Nat := 379321509973346886927665

theorem tailTrace_1108089 : CollatzResearch.WordTrace tailWord_1108089 prefixEnd_1108089 379321509973346886927665 := by
  unfold tailWord_1108089
  simp only [CollatzResearch.WordTrace]
  refine ⟨40415326082590274379623321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26943550721726849586415547 40415326082590274379623321)
  ·
    refine ⟨30311494561942705784717491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40415326082590274379623321 30311494561942705784717491)
    ·
      refine ⟨45467241842914058677076237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30311494561942705784717491 45467241842914058677076237)
      ·
        refine ⟨17050215691092772003903589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45467241842914058677076237 17050215691092772003903589)
        ·
          refine ⟨3196915442079894750731923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17050215691092772003903589 3196915442079894750731923)
          ·
            refine ⟨4795373163119842126097885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3196915442079894750731923 4795373163119842126097885)
            ·
              refine ⟨1798264936169940797286707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4795373163119842126097885 1798264936169940797286707)
              ·
                refine ⟨2697397404254911195930061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1798264936169940797286707 2697397404254911195930061)
                ·
                  refine ⟨1011524026595591698473773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2697397404254911195930061 1011524026595591698473773)
                  ·
                    refine ⟨379321509973346886927665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1011524026595591698473773 379321509973346886927665)
                    ·
                      rfl

theorem cell22_1108089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 1, 3, 3].length) (baseStart_1108089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1108089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1108089 prefixEnd_1108089 := by exact prefixLift 1108089
  have htrace : WordTrace (prefixWord ++ tailWord_1108089) baseStart_1108089 baseEnd_1108089 := by
    simpa [prefixWord, tailWord_1108089, baseEnd_1108089] using wordTrace_append hprefix tailTrace_1108089
  have hstable : (prefixWord ++ tailWord_1108089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108089).length < 2 ^ (prefixWord ++ tailWord_1108089).sum := by decide
  have hdescent : baseEnd_1108089 < baseStart_1108089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108164 : List Nat := [2, 3, 3, 1, 2, 2, 1, 2, 6]
def baseStart_1108164 : Nat := 118140960795 + 1108164 * 2 ^ 59
def prefixEnd_1108164 : Nat := 4983230072969 + 3 ^ 40 * 1108164 * 2
def baseEnd_1108164 : Nat := 126449061335357230434145

theorem tailTrace_1108164 : CollatzResearch.WordTrace tailWord_1108164 prefixEnd_1108164 126449061335357230434145 := by
  unfold tailWord_1108164
  simp only [CollatzResearch.WordTrace]
  refine ⟨20209030778659281094301773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26945374371545708125735697 20209030778659281094301773)
  ·
    refine ⟨7578386541997230410363165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20209030778659281094301773 7578386541997230410363165)
    ·
      refine ⟨2841894953248961403886187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7578386541997230410363165 2841894953248961403886187)
      ·
        refine ⟨4262842429873442105829281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2841894953248961403886187 4262842429873442105829281)
        ·
          refine ⟨3197131822405081579371961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4262842429873442105829281 3197131822405081579371961)
          ·
            refine ⟨2397848866803811184528971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3197131822405081579371961 2397848866803811184528971)
            ·
              refine ⟨3596773300205716776793457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2397848866803811184528971 3596773300205716776793457)
              ·
                refine ⟨2697579975154287582595093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3596773300205716776793457 2697579975154287582595093)
                ·
                  refine ⟨126449061335357230434145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2697579975154287582595093 126449061335357230434145)
                  ·
                    rfl

theorem cell22_1108164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 2, 6].length) (baseStart_1108164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1108164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1108164 prefixEnd_1108164 := by exact prefixLift 1108164
  have htrace : WordTrace (prefixWord ++ tailWord_1108164) baseStart_1108164 baseEnd_1108164 := by
    simpa [prefixWord, tailWord_1108164, baseEnd_1108164] using wordTrace_append hprefix tailTrace_1108164
  have hstable : (prefixWord ++ tailWord_1108164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108164).length < 2 ^ (prefixWord ++ tailWord_1108164).sum := by decide
  have hdescent : baseEnd_1108164 < baseStart_1108164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108224 : List Nat := [2, 1, 1, 2, 1, 1, 6, 2, 3, 3]
def baseStart_1108224 : Nat := 118140960795 + 1108224 * 2 ^ 59
def prefixEnd_1108224 : Nat := 4983230072969 + 3 ^ 40 * 1108224 * 2
def baseEnd_1108224 : Nat := 379367723232251534802251

theorem tailTrace_1108224 : CollatzResearch.WordTrace tailWord_1108224 prefixEnd_1108224 379367723232251534802251 := by
  unfold tailWord_1108224
  simp only [CollatzResearch.WordTrace]
  refine ⟨20210124968550596217893863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26946833291400794957191817 20210124968550596217893863)
  ·
    refine ⟨30315187452825894326840795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20210124968550596217893863 30315187452825894326840795)
    ·
      refine ⟨45472781179238841490261193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30315187452825894326840795 45472781179238841490261193)
      ·
        refine ⟨34104585884429131117695895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45472781179238841490261193 34104585884429131117695895)
        ·
          refine ⟨51156878826643696676543843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34104585884429131117695895 51156878826643696676543843)
          ·
            refine ⟨76735318239965545014815765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51156878826643696676543843 76735318239965545014815765)
            ·
              refine ⟨3596968042498384922569489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 76735318239965545014815765 3596968042498384922569489)
              ·
                refine ⟨2697726031873788691927117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3596968042498384922569489 2697726031873788691927117)
                ·
                  refine ⟨1011647261952670759472669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2697726031873788691927117 1011647261952670759472669)
                  ·
                    refine ⟨379367723232251534802251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1011647261952670759472669 379367723232251534802251)
                    ·
                      rfl

theorem cell22_1108224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 2, 3, 3].length) (baseStart_1108224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1108224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1108224 prefixEnd_1108224 := by exact prefixLift 1108224
  have htrace : WordTrace (prefixWord ++ tailWord_1108224) baseStart_1108224 baseEnd_1108224 := by
    simpa [prefixWord, tailWord_1108224, baseEnd_1108224] using wordTrace_append hprefix tailTrace_1108224
  have hstable : (prefixWord ++ tailWord_1108224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108224).length < 2 ^ (prefixWord ++ tailWord_1108224).sum := by decide
  have hdescent : baseEnd_1108224 < baseStart_1108224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108226 : List Nat := [3, 4, 1, 1, 2, 1, 4, 6]
def baseStart_1108226 : Nat := 118140960795 + 1108226 * 2 ^ 59
def prefixEnd_1108226 : Nat := 4983230072969 + 3 ^ 40 * 1108226 * 2
def baseEnd_1108226 : Nat := 42152045319236021805805

theorem tailTrace_1108226 : CollatzResearch.WordTrace tailWord_1108226 prefixEnd_1108226 42152045319236021805805 := by
  unfold tailWord_1108226
  simp only [CollatzResearch.WordTrace]
  refine ⟨10105080720773486694340133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26946881922062631184907021 10105080720773486694340133)
  ·
    refine ⟨1894702635145028755188775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10105080720773486694340133 1894702635145028755188775)
    ·
      refine ⟨2842053952717543132783163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1894702635145028755188775 2842053952717543132783163)
      ·
        refine ⟨4263080929076314699174745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2842053952717543132783163 4263080929076314699174745)
        ·
          refine ⟨3197310696807236024381059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4263080929076314699174745 3197310696807236024381059)
          ·
            refine ⟨4795966045210854036571589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3197310696807236024381059 4795966045210854036571589)
            ·
              refine ⟨899243633477035131857173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4795966045210854036571589 899243633477035131857173)
              ·
                refine ⟨42152045319236021805805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 899243633477035131857173 42152045319236021805805)
                ·
                  rfl

theorem cell22_1108226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 4, 6].length) (baseStart_1108226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1108226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1108226 prefixEnd_1108226 := by exact prefixLift 1108226
  have htrace : WordTrace (prefixWord ++ tailWord_1108226) baseStart_1108226 baseEnd_1108226 := by
    simpa [prefixWord, tailWord_1108226, baseEnd_1108226] using wordTrace_append hprefix tailTrace_1108226
  have hstable : (prefixWord ++ tailWord_1108226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108226).length < 2 ^ (prefixWord ++ tailWord_1108226).sum := by decide
  have hdescent : baseEnd_1108226 < baseStart_1108226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108258 : List Nat := [3, 3, 1, 1, 3, 3, 1, 1, 3, 3]
def baseStart_1108258 : Nat := 118140960795 + 1108258 * 2 ^ 59
def prefixEnd_1108258 : Nat := 4983230072969 + 3 ^ 40 * 1108258 * 2
def baseEnd_1108258 : Nat := 379379362127086779452147

theorem tailTrace_1108258 : CollatzResearch.WordTrace tailWord_1108258 prefixEnd_1108258 379379362127086779452147 := by
  unfold tailWord_1108258
  simp only [CollatzResearch.WordTrace]
  refine ⟨10105372504744504060631357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26947660012652010828350285 10105372504744504060631357)
  ·
    refine ⟨3789514689279189022736759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10105372504744504060631357 3789514689279189022736759)
    ·
      refine ⟨5684272033918783534105139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3789514689279189022736759 5684272033918783534105139)
      ·
        refine ⟨8526408050878175301157709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5684272033918783534105139 8526408050878175301157709)
        ·
          refine ⟨3197403019079315737934141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8526408050878175301157709 3197403019079315737934141)
          ·
            refine ⟨1199026132154743401725303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3197403019079315737934141 1199026132154743401725303)
            ·
              refine ⟨1798539198232115102587955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1199026132154743401725303 1798539198232115102587955)
              ·
                refine ⟨2697808797348172653881933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1798539198232115102587955 2697808797348172653881933)
                ·
                  refine ⟨1011678299005564745205725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2697808797348172653881933 1011678299005564745205725)
                  ·
                    refine ⟨379379362127086779452147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1011678299005564745205725 379379362127086779452147)
                    ·
                      rfl

theorem cell22_1108258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 1, 3, 3].length) (baseStart_1108258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1108258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1108258 prefixEnd_1108258 := by exact prefixLift 1108258
  have htrace : WordTrace (prefixWord ++ tailWord_1108258) baseStart_1108258 baseEnd_1108258 := by
    simpa [prefixWord, tailWord_1108258, baseEnd_1108258] using wordTrace_append hprefix tailTrace_1108258
  have hstable : (prefixWord ++ tailWord_1108258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108258).length < 2 ^ (prefixWord ++ tailWord_1108258).sum := by decide
  have hdescent : baseEnd_1108258 < baseStart_1108258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108284 : List Nat := [2, 2, 2, 2, 1, 2, 3, 1, 3, 4]
def baseStart_1108284 : Nat := 118140960795 + 1108284 * 2 ^ 59
def prefixEnd_1108284 : Nat := 4983230072969 + 3 ^ 40 * 1108284 * 2
def baseEnd_1108284 : Nat := 379388262458431378302067

theorem tailTrace_1108284 : CollatzResearch.WordTrace tailWord_1108284 prefixEnd_1108284 379388262458431378302067 := by
  unfold tailWord_1108284
  simp only [CollatzResearch.WordTrace]
  refine ⟨20211219158441911341485953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26948292211255881788647937 20211219158441911341485953)
  ·
    refine ⟨15158414368831433506114465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20211219158441911341485953 15158414368831433506114465)
    ·
      refine ⟨11368810776623575129585849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15158414368831433506114465 11368810776623575129585849)
      ·
        refine ⟨8526608082467681347189387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11368810776623575129585849 8526608082467681347189387)
        ·
          refine ⟨12789912123701522020784081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8526608082467681347189387 12789912123701522020784081)
          ·
            refine ⟨9592434092776141515588061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12789912123701522020784081 9592434092776141515588061)
            ·
              refine ⟨3597162784791053068345523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9592434092776141515588061 3597162784791053068345523)
              ·
                refine ⟨5395744177186579602518285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3597162784791053068345523 5395744177186579602518285)
                ·
                  refine ⟨2023404066444967350944357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5395744177186579602518285 2023404066444967350944357)
                  ·
                    refine ⟨379388262458431378302067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2023404066444967350944357 379388262458431378302067)
                    ·
                      rfl

theorem cell22_1108284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 1, 3, 4].length) (baseStart_1108284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1108284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1108284 prefixEnd_1108284 := by exact prefixLift 1108284
  have htrace : WordTrace (prefixWord ++ tailWord_1108284) baseStart_1108284 baseEnd_1108284 := by
    simpa [prefixWord, tailWord_1108284, baseEnd_1108284] using wordTrace_append hprefix tailTrace_1108284
  have hstable : (prefixWord ++ tailWord_1108284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108284).length < 2 ^ (prefixWord ++ tailWord_1108284).sum := by decide
  have hdescent : baseEnd_1108284 < baseStart_1108284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108382 : List Nat := [4, 3, 1, 2, 1, 2, 3, 1, 2, 3]
def baseStart_1108382 : Nat := 118140960795 + 1108382 * 2 ^ 59
def prefixEnd_1108382 : Nat := 4983230072969 + 3 ^ 40 * 1108382 * 2
def baseEnd_1108382 : Nat := 379421809861191789351767

theorem tailTrace_1108382 : CollatzResearch.WordTrace tailWord_1108382 prefixEnd_1108382 379421809861191789351767 := by
  unfold tailWord_1108382
  simp only [CollatzResearch.WordTrace]
  refine ⟨5053251583816098177504925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26950675113685856946692933 5053251583816098177504925)
  ·
    refine ⟨1894969343931036816564347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5053251583816098177504925 1894969343931036816564347)
    ·
      refine ⟨2842454015896555224846521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1894969343931036816564347 2842454015896555224846521)
      ·
        refine ⟨2131840511922416418634891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2842454015896555224846521 2131840511922416418634891)
        ·
          refine ⟨3197760767883624627952337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2131840511922416418634891 3197760767883624627952337)
          ·
            refine ⟨2398320575912718470964253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3197760767883624627952337 2398320575912718470964253)
            ·
              refine ⟨899370215967269426611595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2398320575912718470964253 899370215967269426611595)
              ·
                refine ⟨1349055323950904139917393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 899370215967269426611595 1349055323950904139917393)
                ·
                  refine ⟨1011791492963178104938045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1349055323950904139917393 1011791492963178104938045)
                  ·
                    refine ⟨379421809861191789351767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1011791492963178104938045 379421809861191789351767)
                    ·
                      rfl

theorem cell22_1108382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_1108382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1108382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1108382 prefixEnd_1108382 := by exact prefixLift 1108382
  have htrace : WordTrace (prefixWord ++ tailWord_1108382) baseStart_1108382 baseEnd_1108382 := by
    simpa [prefixWord, tailWord_1108382, baseEnd_1108382] using wordTrace_append hprefix tailTrace_1108382
  have hstable : (prefixWord ++ tailWord_1108382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108382).length < 2 ^ (prefixWord ++ tailWord_1108382).sum := by decide
  have hdescent : baseEnd_1108382 < baseStart_1108382 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108419 : List Nat := [1, 1, 1, 3, 1, 1, 3, 2, 5, 4]
def baseStart_1108419 : Nat := 118140960795 + 1108419 * 2 ^ 59
def prefixEnd_1108419 : Nat := 4983230072969 + 3 ^ 40 * 1108419 * 2
def baseEnd_1108419 : Nat := 379434475717336026176653

theorem tailTrace_1108419 : CollatzResearch.WordTrace tailWord_1108419 prefixEnd_1108419 379434475717336026176653 := by
  unfold tailWord_1108419
  simp only [CollatzResearch.WordTrace]
  refine ⟨40427362171394740739136311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26951574780929827159424207 40427362171394740739136311)
  ·
    refine ⟨60641043257092111108704467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40427362171394740739136311 60641043257092111108704467)
    ·
      refine ⟨90961564885638166663056701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60641043257092111108704467 90961564885638166663056701)
      ·
        refine ⟨34110586832114312498646263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90961564885638166663056701 34110586832114312498646263)
        ·
          refine ⟨51165880248171468747969395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34110586832114312498646263 51165880248171468747969395)
          ·
            refine ⟨76748820372257203121954093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51165880248171468747969395 76748820372257203121954093)
            ·
              refine ⟨28780807639596451170732785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76748820372257203121954093 28780807639596451170732785)
              ·
                refine ⟨21585605729697338378049589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28780807639596451170732785 21585605729697338378049589)
                ·
                  refine ⟨2023650537159125472942149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21585605729697338378049589 2023650537159125472942149)
                  ·
                    refine ⟨379434475717336026176653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2023650537159125472942149 379434475717336026176653)
                    ·
                      rfl

theorem cell22_1108419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 5, 4].length) (baseStart_1108419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1108419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1108419 prefixEnd_1108419 := by exact prefixLift 1108419
  have htrace : WordTrace (prefixWord ++ tailWord_1108419) baseStart_1108419 baseEnd_1108419 := by
    simpa [prefixWord, tailWord_1108419, baseEnd_1108419] using wordTrace_append hprefix tailTrace_1108419
  have hstable : (prefixWord ++ tailWord_1108419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108419).length < 2 ^ (prefixWord ++ tailWord_1108419).sum := by decide
  have hdescent : baseEnd_1108419 < baseStart_1108419 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108453 : List Nat := [1, 3, 1, 5, 2, 1, 1, 1, 3, 4]
def baseStart_1108453 : Nat := 118140960795 + 1108453 * 2 ^ 59
def prefixEnd_1108453 : Nat := 4983230072969 + 3 ^ 40 * 1108453 * 2
def baseEnd_1108453 : Nat := 379446114612171270826549

theorem tailTrace_1108453 : CollatzResearch.WordTrace tailWord_1108453 prefixEnd_1108453 379446114612171270826549 := by
  unfold tailWord_1108453
  simp only [CollatzResearch.WordTrace]
  refine ⟨40428602253271564545874013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26952401502181043030582675 40428602253271564545874013)
  ·
    refine ⟨15160725844976836704702755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40428602253271564545874013 15160725844976836704702755)
    ·
      refine ⟨22741088767465255057054133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15160725844976836704702755 22741088767465255057054133)
      ·
        refine ⟨2131977071949867661598825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22741088767465255057054133 2131977071949867661598825)
        ·
          refine ⟨1598982803962400746199119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2131977071949867661598825 1598982803962400746199119)
          ·
            refine ⟨2398474205943601119298679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1598982803962400746199119 2398474205943601119298679)
            ·
              refine ⟨3597711308915401678948019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2398474205943601119298679 3597711308915401678948019)
              ·
                refine ⟨5396566963373102518422029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3597711308915401678948019 5396566963373102518422029)
                ·
                  refine ⟨2023712611264913444408261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5396566963373102518422029 2023712611264913444408261)
                  ·
                    refine ⟨379446114612171270826549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2023712611264913444408261 379446114612171270826549)
                    ·
                      rfl

theorem cell22_1108453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 1, 3, 4].length) (baseStart_1108453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1108453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1108453 prefixEnd_1108453 := by exact prefixLift 1108453
  have htrace : WordTrace (prefixWord ++ tailWord_1108453) baseStart_1108453 baseEnd_1108453 := by
    simpa [prefixWord, tailWord_1108453, baseEnd_1108453] using wordTrace_append hprefix tailTrace_1108453
  have hstable : (prefixWord ++ tailWord_1108453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108453).length < 2 ^ (prefixWord ++ tailWord_1108453).sum := by decide
  have hdescent : baseEnd_1108453 < baseStart_1108453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108470 : List Nat := [5, 1, 1, 1, 2, 1, 5, 1, 1, 4]
def baseStart_1108470 : Nat := 118140960795 + 1108470 * 2 ^ 59
def prefixEnd_1108470 : Nat := 4983230072969 + 3 ^ 40 * 1108470 * 2
def baseEnd_1108470 : Nat := 379451934059588893151497

theorem tailTrace_1108470 : CollatzResearch.WordTrace tailWord_1108470 prefixEnd_1108470 379451934059588893151497 := by
  unfold tailWord_1108470
  simp only [CollatzResearch.WordTrace]
  refine ⟨2526826393388123528077679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26952814862806650966161909 2526826393388123528077679)
  ·
    refine ⟨3790239590082185292116519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2526826393388123528077679 3790239590082185292116519)
    ·
      refine ⟨5685359385123277938174779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3790239590082185292116519 5685359385123277938174779)
      ·
        refine ⟨8528039077684916907262169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5685359385123277938174779 8528039077684916907262169)
        ·
          refine ⟨6396029308263687680446627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8528039077684916907262169 6396029308263687680446627)
          ·
            refine ⟨9594043962395531520669941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6396029308263687680446627 9594043962395531520669941)
            ·
              refine ⟨899441621474581080062807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9594043962395531520669941 899441621474581080062807)
              ·
                refine ⟨1349162432211871620094211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 899441621474581080062807 1349162432211871620094211)
                ·
                  refine ⟨2023743648317807430141317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1349162432211871620094211 2023743648317807430141317)
                  ·
                    refine ⟨379451934059588893151497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2023743648317807430141317 379451934059588893151497)
                    ·
                      rfl

theorem cell22_1108470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 5, 1, 1, 4].length) (baseStart_1108470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1108470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1108470 prefixEnd_1108470 := by exact prefixLift 1108470
  have htrace : WordTrace (prefixWord ++ tailWord_1108470) baseStart_1108470 baseEnd_1108470 := by
    simpa [prefixWord, tailWord_1108470, baseEnd_1108470] using wordTrace_append hprefix tailTrace_1108470
  have hstable : (prefixWord ++ tailWord_1108470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108470).length < 2 ^ (prefixWord ++ tailWord_1108470).sum := by decide
  have hdescent : baseEnd_1108470 < baseStart_1108470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108483 : List Nat := [1, 1, 1, 3, 2, 1, 6, 2, 2, 3]
def baseStart_1108483 : Nat := 118140960795 + 1108483 * 2 ^ 59
def prefixEnd_1108483 : Nat := 4983230072969 + 3 ^ 40 * 1108483 * 2
def baseEnd_1108483 : Nat := 379456384225261192576457

theorem tailTrace_1108483 : CollatzResearch.WordTrace tailWord_1108483 prefixEnd_1108483 379456384225261192576457 := by
  unfold tailWord_1108483
  simp only [CollatzResearch.WordTrace]
  refine ⟨40429696443162879669466103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26953130962108586446310735 40429696443162879669466103)
  ·
    refine ⟨60644544664744319504199155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40429696443162879669466103 60644544664744319504199155)
    ·
      refine ⟨90966816997116479256298733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60644544664744319504199155 90966816997116479256298733)
      ·
        refine ⟨34112556373918679721112025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90966816997116479256298733 34112556373918679721112025)
        ·
          refine ⟨25584417280439009790834019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34112556373918679721112025 25584417280439009790834019)
          ·
            refine ⟨38376625920658514686251029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25584417280439009790834019 38376625920658514686251029)
            ·
              refine ⟨1798904340030867875918017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 38376625920658514686251029 1798904340030867875918017)
              ·
                refine ⟨1349178255023150906938513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1798904340030867875918017 1349178255023150906938513)
                ·
                  refine ⟨1011883691267363180203885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1349178255023150906938513 1011883691267363180203885)
                  ·
                    refine ⟨379456384225261192576457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1011883691267363180203885 379456384225261192576457)
                    ·
                      rfl

theorem cell22_1108483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 2, 2, 3].length) (baseStart_1108483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1108483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1108483 prefixEnd_1108483 := by exact prefixLift 1108483
  have htrace : WordTrace (prefixWord ++ tailWord_1108483) baseStart_1108483 baseEnd_1108483 := by
    simpa [prefixWord, tailWord_1108483, baseEnd_1108483] using wordTrace_append hprefix tailTrace_1108483
  have hstable : (prefixWord ++ tailWord_1108483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108483).length < 2 ^ (prefixWord ++ tailWord_1108483).sum := by decide
  have hdescent : baseEnd_1108483 < baseStart_1108483 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108500 : List Nat := [2, 4, 3, 1, 1, 2, 2, 1, 1, 5]
def baseStart_1108500 : Nat := 118140960795 + 1108500 * 2 ^ 59
def prefixEnd_1108500 : Nat := 4983230072969 + 3 ^ 40 * 1108500 * 2
def baseEnd_1108500 : Nat := 379462203672678814901405

theorem tailTrace_1108500 : CollatzResearch.WordTrace tailWord_1108500 prefixEnd_1108500 379462203672678814901405 := by
  unfold tailWord_1108500
  simp only [CollatzResearch.WordTrace]
  refine ⟨20215158242050645786417477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26953544322734194381889969 20215158242050645786417477)
  ·
    refine ⟨3790342170384496084953277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20215158242050645786417477 3790342170384496084953277)
    ·
      refine ⟨1421378313894186031857479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3790342170384496084953277 1421378313894186031857479)
      ·
        refine ⟨2132067470841279047786219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1421378313894186031857479 2132067470841279047786219)
        ·
          refine ⟨3198101206261918571679329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2132067470841279047786219 3198101206261918571679329)
          ·
            refine ⟨2398575904696438928759497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3198101206261918571679329 2398575904696438928759497)
            ·
              refine ⟨1798931928522329196569623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2398575904696438928759497 1798931928522329196569623)
              ·
                refine ⟨2698397892783493794854435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1798931928522329196569623 2698397892783493794854435)
                ·
                  refine ⟨4047596839175240692281653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2698397892783493794854435 4047596839175240692281653)
                  ·
                    refine ⟨379462203672678814901405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4047596839175240692281653 379462203672678814901405)
                    ·
                      rfl

theorem cell22_1108500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_1108500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1108500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1108500 prefixEnd_1108500 := by exact prefixLift 1108500
  have htrace : WordTrace (prefixWord ++ tailWord_1108500) baseStart_1108500 baseEnd_1108500 := by
    simpa [prefixWord, tailWord_1108500, baseEnd_1108500] using wordTrace_append hprefix tailTrace_1108500
  have hstable : (prefixWord ++ tailWord_1108500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108500).length < 2 ^ (prefixWord ++ tailWord_1108500).sum := by decide
  have hdescent : baseEnd_1108500 < baseStart_1108500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108545 : List Nat := [1, 2, 5, 1, 1, 3, 2, 1, 3, 3]
def baseStart_1108545 : Nat := 118140960795 + 1108545 * 2 ^ 59
def prefixEnd_1108545 : Nat := 4983230072969 + 3 ^ 40 * 1108545 * 2
def baseEnd_1108545 : Nat := 379477608092313697526267

theorem tailTrace_1108545 : CollatzResearch.WordTrace tailWord_1108545 prefixEnd_1108545 379477608092313697526267 := by
  unfold tailWord_1108545
  simp only [CollatzResearch.WordTrace]
  refine ⟨40431957768938264258223089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26954638512625509505482059 40431957768938264258223089)
  ·
    refine ⟨30323968326703698193667317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40431957768938264258223089 30323968326703698193667317)
    ·
      refine ⟨2842872030628471705656311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30323968326703698193667317 2842872030628471705656311)
      ·
        refine ⟨4264308045942707558484467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2842872030628471705656311 4264308045942707558484467)
        ·
          refine ⟨6396462068914061337726701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4264308045942707558484467 6396462068914061337726701)
          ·
            refine ⟨2398673275842773001647513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6396462068914061337726701 2398673275842773001647513)
            ·
              refine ⟨1799004956882079751235635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2398673275842773001647513 1799004956882079751235635)
              ·
                refine ⟨2698507435323119626853453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1799004956882079751235635 2698507435323119626853453)
                ·
                  refine ⟨1011940288246169860070045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2698507435323119626853453 1011940288246169860070045)
                  ·
                    refine ⟨379477608092313697526267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1011940288246169860070045 379477608092313697526267)
                    ·
                      rfl

theorem cell22_1108545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_1108545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1108545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1108545 prefixEnd_1108545 := by exact prefixLift 1108545
  have htrace : WordTrace (prefixWord ++ tailWord_1108545) baseStart_1108545 baseEnd_1108545 := by
    simpa [prefixWord, tailWord_1108545, baseEnd_1108545] using wordTrace_append hprefix tailTrace_1108545
  have hstable : (prefixWord ++ tailWord_1108545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108545).length < 2 ^ (prefixWord ++ tailWord_1108545).sum := by decide
  have hdescent : baseEnd_1108545 < baseStart_1108545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108556 : List Nat := [2, 2, 1, 3, 1, 2, 1, 3, 2, 5]
def baseStart_1108556 : Nat := 118140960795 + 1108556 * 2 ^ 59
def prefixEnd_1108556 : Nat := 4983230072969 + 3 ^ 40 * 1108556 * 2
def baseEnd_1108556 : Nat := 379481373617113335501233

theorem tailTrace_1108556 : CollatzResearch.WordTrace tailWord_1108556 prefixEnd_1108556 379481373617113335501233 := by
  unfold tailWord_1108556
  simp only [CollatzResearch.WordTrace]
  refine ⟨20216179485949206568436761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26954905981265608757915681 20216179485949206568436761)
  ·
    refine ⟨15162134614461904926327571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20216179485949206568436761 15162134614461904926327571)
    ·
      refine ⟨22743201921692857389491357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15162134614461904926327571 22743201921692857389491357)
      ·
        refine ⟨8528700720634821521059259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22743201921692857389491357 8528700720634821521059259)
        ·
          refine ⟨12793051080952232281588889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8528700720634821521059259 12793051080952232281588889)
          ·
            refine ⟨9594788310714174211191667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12793051080952232281588889 9594788310714174211191667)
            ·
              refine ⟨14392182466071261316787501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9594788310714174211191667 14392182466071261316787501)
              ·
                refine ⟨5397068424776722993795313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14392182466071261316787501 5397068424776722993795313)
                ·
                  refine ⟨4047801318582542245346485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5397068424776722993795313 4047801318582542245346485)
                  ·
                    refine ⟨379481373617113335501233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4047801318582542245346485 379481373617113335501233)
                    ·
                      rfl

theorem cell22_1108556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 3, 2, 5].length) (baseStart_1108556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1108556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1108556 prefixEnd_1108556 := by exact prefixLift 1108556
  have htrace : WordTrace (prefixWord ++ tailWord_1108556) baseStart_1108556 baseEnd_1108556 := by
    simpa [prefixWord, tailWord_1108556, baseEnd_1108556] using wordTrace_append hprefix tailTrace_1108556
  have hstable : (prefixWord ++ tailWord_1108556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108556).length < 2 ^ (prefixWord ++ tailWord_1108556).sum := by decide
  have hdescent : baseEnd_1108556 < baseStart_1108556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108588 : List Nat := [2, 2, 1, 1, 3, 1, 4, 3, 1, 4]
def baseStart_1108588 : Nat := 118140960795 + 1108588 * 2 ^ 59
def prefixEnd_1108588 : Nat := 4983230072969 + 3 ^ 40 * 1108588 * 2
def baseEnd_1108588 : Nat := 379492327871075918701135

theorem tailTrace_1108588 : CollatzResearch.WordTrace tailWord_1108588 prefixEnd_1108588 379492327871075918701135 := by
  unfold tailWord_1108588
  simp only [CollatzResearch.WordTrace]
  refine ⟨20216763053891241301019209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26955684071854988401358945 20216763053891241301019209)
  ·
    refine ⟨15162572290418430975764407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20216763053891241301019209 15162572290418430975764407)
    ·
      refine ⟨22743858435627646463646611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15162572290418430975764407 22743858435627646463646611)
      ·
        refine ⟨34115787653441469695469917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22743858435627646463646611 34115787653441469695469917)
        ·
          refine ⟨12793420370040551135801219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34115787653441469695469917 12793420370040551135801219)
          ·
            refine ⟨19190130555060826703701829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12793420370040551135801219 19190130555060826703701829)
            ·
              refine ⟨3598149479073905006944093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19190130555060826703701829 3598149479073905006944093)
              ·
                refine ⟨1349306054652714377604035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3598149479073905006944093 1349306054652714377604035)
                ·
                  refine ⟨2023959081979071566406053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1349306054652714377604035 2023959081979071566406053)
                  ·
                    refine ⟨379492327871075918701135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2023959081979071566406053 379492327871075918701135)
                    ·
                      rfl

theorem cell22_1108588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 4].length) (baseStart_1108588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1108588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1108588 prefixEnd_1108588 := by exact prefixLift 1108588
  have htrace : WordTrace (prefixWord ++ tailWord_1108588) baseStart_1108588 baseEnd_1108588 := by
    simpa [prefixWord, tailWord_1108588, baseEnd_1108588] using wordTrace_append hprefix tailTrace_1108588
  have hstable : (prefixWord ++ tailWord_1108588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108588).length < 2 ^ (prefixWord ++ tailWord_1108588).sum := by decide
  have hdescent : baseEnd_1108588 < baseStart_1108588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108631 : List Nat := [1, 1, 3, 3, 2, 1, 1, 10]
def baseStart_1108631 : Nat := 118140960795 + 1108631 * 2 ^ 59
def prefixEnd_1108631 : Nat := 4983230072969 + 3 ^ 40 * 1108631 * 2
def baseEnd_1108631 : Nat := 42167449738870904430667

theorem tailTrace_1108631 : CollatzResearch.WordTrace tailWord_1108631 prefixEnd_1108631 42167449738870904430667 := by
  unfold tailWord_1108631
  simp only [CollatzResearch.WordTrace]
  refine ⟨40435094446626700945853747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26956729631084467297235831 40435094446626700945853747)
  ·
    refine ⟨60652641669940051418780621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40435094446626700945853747 60652641669940051418780621)
    ·
      refine ⟨22744740626227519282042733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60652641669940051418780621 22744740626227519282042733)
      ·
        refine ⟨8529277734835319730766025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22744740626227519282042733 8529277734835319730766025)
        ·
          refine ⟨6396958301126489798074519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8529277734835319730766025 6396958301126489798074519)
          ·
            refine ⟨9595437451689734697111779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6396958301126489798074519 9595437451689734697111779)
            ·
              refine ⟨14393156177534602045667669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9595437451689734697111779 14393156177534602045667669)
              ·
                refine ⟨42167449738870904430667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 14393156177534602045667669 42167449738870904430667)
                ·
                  rfl

theorem cell22_1108631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 10].length) (baseStart_1108631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1108631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1108631 prefixEnd_1108631 := by exact prefixLift 1108631
  have htrace : WordTrace (prefixWord ++ tailWord_1108631) baseStart_1108631 baseEnd_1108631 := by
    simpa [prefixWord, tailWord_1108631, baseEnd_1108631] using wordTrace_append hprefix tailTrace_1108631
  have hstable : (prefixWord ++ tailWord_1108631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108631).length < 2 ^ (prefixWord ++ tailWord_1108631).sum := by decide
  have hdescent : baseEnd_1108631 < baseStart_1108631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108633 : List Nat := [1, 2, 1, 2, 1, 2, 6, 1, 2, 4]
def baseStart_1108633 : Nat := 118140960795 + 1108633 * 2 ^ 59
def prefixEnd_1108633 : Nat := 4983230072969 + 3 ^ 40 * 1108633 * 2
def baseEnd_1108633 : Nat := 379507732290710801325997

theorem tailTrace_1108633 : CollatzResearch.WordTrace tailWord_1108633 prefixEnd_1108633 379507732290710801325997 := by
  unfold tailWord_1108633
  simp only [CollatzResearch.WordTrace]
  refine ⟨40435167392619455287426553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26956778261746303524951035 40435167392619455287426553)
  ·
    refine ⟨30326375544464591465569915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40435167392619455287426553 30326375544464591465569915)
    ·
      refine ⟨45489563316696887198354873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30326375544464591465569915 45489563316696887198354873)
      ·
        refine ⟨34117172487522665398766155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45489563316696887198354873 34117172487522665398766155)
        ·
          refine ⟨51175758731283998098149233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34117172487522665398766155 51175758731283998098149233)
          ·
            refine ⟨38381819048462998573611925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51175758731283998098149233 38381819048462998573611925)
            ·
              refine ⟨1799147767896703058138059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 38381819048462998573611925 1799147767896703058138059)
              ·
                refine ⟨2698721651845054587207089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1799147767896703058138059 2698721651845054587207089)
                ·
                  refine ⟨2024041238883790940405317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2698721651845054587207089 2024041238883790940405317)
                  ·
                    refine ⟨379507732290710801325997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2024041238883790940405317 379507732290710801325997)
                    ·
                      rfl

theorem cell22_1108633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 1, 2, 4].length) (baseStart_1108633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1108633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1108633 prefixEnd_1108633 := by exact prefixLift 1108633
  have htrace : WordTrace (prefixWord ++ tailWord_1108633) baseStart_1108633 baseEnd_1108633 := by
    simpa [prefixWord, tailWord_1108633, baseEnd_1108633] using wordTrace_append hprefix tailTrace_1108633
  have hstable : (prefixWord ++ tailWord_1108633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108633).length < 2 ^ (prefixWord ++ tailWord_1108633).sum := by decide
  have hdescent : baseEnd_1108633 < baseStart_1108633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108648 : List Nat := [2, 1, 7, 12]
def baseStart_1108648 : Nat := 118140960795 + 1108648 * 2 ^ 59
def prefixEnd_1108648 : Nat := 4983230072969 + 3 ^ 40 * 1108648 * 2
def baseEnd_1108648 : Nat := 520593782026413939919

theorem tailTrace_1108648 : CollatzResearch.WordTrace tailWord_1108648 prefixEnd_1108648 520593782026413939919 := by
  unfold tailWord_1108648
  simp only [CollatzResearch.WordTrace]
  refine ⟨20217857243782556424611299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26957142991710075232815065 20217857243782556424611299)
  ·
    refine ⟨30326785865673834636916949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20217857243782556424611299 30326785865673834636916949)
    ·
      refine ⟨710784043726730499302741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 30326785865673834636916949 710784043726730499302741)
      ·
        refine ⟨520593782026413939919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 710784043726730499302741 520593782026413939919)
        ·
          rfl

theorem cell22_1108648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 12].length) (baseStart_1108648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1108648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1108648 prefixEnd_1108648 := by exact prefixLift 1108648
  have htrace : WordTrace (prefixWord ++ tailWord_1108648) baseStart_1108648 baseEnd_1108648 := by
    simpa [prefixWord, tailWord_1108648, baseEnd_1108648] using wordTrace_append hprefix tailTrace_1108648
  have hstable : (prefixWord ++ tailWord_1108648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108648).length < 2 ^ (prefixWord ++ tailWord_1108648).sum := by decide
  have hdescent : baseEnd_1108648 < baseStart_1108648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108654 : List Nat := [4, 1, 4, 1, 1, 1, 4, 2, 4]
def baseStart_1108654 : Nat := 118140960795 + 1108654 * 2 ^ 59
def prefixEnd_1108654 : Nat := 4983230072969 + 3 ^ 40 * 1108654 * 2
def baseEnd_1108654 : Nat := 126504973673291248850311

theorem tailTrace_1108654 : CollatzResearch.WordTrace tailWord_1108654 prefixEnd_1108654 126504973673291248850311 := by
  unfold tailWord_1108654
  simp only [CollatzResearch.WordTrace]
  refine ⟨5054491665692921984242627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26957288883695583915960677 5054491665692921984242627)
  ·
    refine ⟨7581737498539382976363941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5054491665692921984242627 7581737498539382976363941)
    ·
      refine ⟨1421575780976134308068239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7581737498539382976363941 1421575780976134308068239)
      ·
        refine ⟨2132363671464201462102359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1421575780976134308068239 2132363671464201462102359)
        ·
          refine ⟨3198545507196302193153539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2132363671464201462102359 3198545507196302193153539)
          ·
            refine ⟨4797818260794453289730309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3198545507196302193153539 4797818260794453289730309)
            ·
              refine ⟨899590923898959991824433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4797818260794453289730309 899590923898959991824433)
              ·
                refine ⟨674693192924219993868325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 899590923898959991824433 674693192924219993868325)
                ·
                  refine ⟨126504973673291248850311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 674693192924219993868325 126504973673291248850311)
                  ·
                    rfl

theorem cell22_1108654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 4, 2, 4].length) (baseStart_1108654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1108654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1108654 prefixEnd_1108654 := by exact prefixLift 1108654
  have htrace : WordTrace (prefixWord ++ tailWord_1108654) baseStart_1108654 baseEnd_1108654 := by
    simpa [prefixWord, tailWord_1108654, baseEnd_1108654] using wordTrace_append hprefix tailTrace_1108654
  have hstable : (prefixWord ++ tailWord_1108654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108654).length < 2 ^ (prefixWord ++ tailWord_1108654).sum := by decide
  have hdescent : baseEnd_1108654 < baseStart_1108654 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108680 : List Nat := [2, 1, 3, 1, 2, 4, 1, 2, 3, 3]
def baseStart_1108680 : Nat := 118140960795 + 1108680 * 2 ^ 59
def prefixEnd_1108680 : Nat := 4983230072969 + 3 ^ 40 * 1108680 * 2
def baseEnd_1108680 : Nat := 379523821351218345400853

theorem tailTrace_1108680 : CollatzResearch.WordTrace tailWord_1108680 prefixEnd_1108680 379523821351218345400853 := by
  unfold tailWord_1108680
  simp only [CollatzResearch.WordTrace]
  refine ⟨20218440811724591157193747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26957921082299454876258329 20218440811724591157193747)
  ·
    refine ⟨30327661217586886735790621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20218440811724591157193747 30327661217586886735790621)
    ·
      refine ⟨11372872956595082525921483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30327661217586886735790621 11372872956595082525921483)
      ·
        refine ⟨17059309434892623788882225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11372872956595082525921483 17059309434892623788882225)
        ·
          refine ⟨12794482076169467841661669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17059309434892623788882225 12794482076169467841661669)
          ·
            refine ⟨2398965389281775220311563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12794482076169467841661669 2398965389281775220311563)
            ·
              refine ⟨3598448083922662830467345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2398965389281775220311563 3598448083922662830467345)
              ·
                refine ⟨2698836062941997122850509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3598448083922662830467345 2698836062941997122850509)
                ·
                  refine ⟨1012063523603248921068941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2698836062941997122850509 1012063523603248921068941)
                  ·
                    refine ⟨379523821351218345400853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1012063523603248921068941 379523821351218345400853)
                    ·
                      rfl

theorem cell22_1108680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 2, 3, 3].length) (baseStart_1108680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1108680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1108680 prefixEnd_1108680 := by exact prefixLift 1108680
  have htrace : WordTrace (prefixWord ++ tailWord_1108680) baseStart_1108680 baseEnd_1108680 := by
    simpa [prefixWord, tailWord_1108680, baseEnd_1108680] using wordTrace_append hprefix tailTrace_1108680
  have hstable : (prefixWord ++ tailWord_1108680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108680).length < 2 ^ (prefixWord ++ tailWord_1108680).sum := by decide
  have hdescent : baseEnd_1108680 < baseStart_1108680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108697 : List Nat := [1, 2, 1, 2, 3, 2, 4, 3, 1, 3]
def baseStart_1108697 : Nat := 118140960795 + 1108697 * 2 ^ 59
def prefixEnd_1108697 : Nat := 4983230072969 + 3 ^ 40 * 1108697 * 2
def baseEnd_1108697 : Nat := 379529640798635967725801

theorem tailTrace_1108697 : CollatzResearch.WordTrace tailWord_1108697 prefixEnd_1108697 379529640798635967725801 := by
  unfold tailWord_1108697
  simp only [CollatzResearch.WordTrace]
  refine ⟨40437501664387594217756345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26958334442925062811837563 40437501664387594217756345)
  ·
    refine ⟨30328126248290695663317259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40437501664387594217756345 30328126248290695663317259)
    ·
      refine ⟨45492189372436043494975889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30328126248290695663317259 45492189372436043494975889)
      ·
        refine ⟨34119142029327032621231917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45492189372436043494975889 34119142029327032621231917)
        ·
          refine ⟨12794678260997637232961969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34119142029327032621231917 12794678260997637232961969)
          ·
            refine ⟨9596008695748227924721477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12794678260997637232961969 9596008695748227924721477)
            ·
              refine ⟨1799251630452792735885277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9596008695748227924721477 1799251630452792735885277)
              ·
                refine ⟨674719361419797275956979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1799251630452792735885277 674719361419797275956979)
                ·
                  refine ⟨1012079042129695913935469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 674719361419797275956979 1012079042129695913935469)
                  ·
                    refine ⟨379529640798635967725801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1012079042129695913935469 379529640798635967725801)
                    ·
                      rfl

theorem cell22_1108697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 3, 1, 3].length) (baseStart_1108697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1108697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1108697 prefixEnd_1108697 := by exact prefixLift 1108697
  have htrace : WordTrace (prefixWord ++ tailWord_1108697) baseStart_1108697 baseEnd_1108697 := by
    simpa [prefixWord, tailWord_1108697, baseEnd_1108697] using wordTrace_append hprefix tailTrace_1108697
  have hstable : (prefixWord ++ tailWord_1108697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108697).length < 2 ^ (prefixWord ++ tailWord_1108697).sum := by decide
  have hdescent : baseEnd_1108697 < baseStart_1108697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108708 : List Nat := [2, 3, 1, 1, 1, 4, 1, 2, 2, 5]
def baseStart_1108708 : Nat := 118140960795 + 1108708 * 2 ^ 59
def prefixEnd_1108708 : Nat := 4983230072969 + 3 ^ 40 * 1108708 * 2
def baseEnd_1108708 : Nat := 379533406323435605700767

theorem tailTrace_1108708 : CollatzResearch.WordTrace tailWord_1108708 prefixEnd_1108708 379533406323435605700767 := by
  unfold tailWord_1108708
  simp only [CollatzResearch.WordTrace]
  refine ⟨20218951433673871548203389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26958601911565162064271185 20218951433673871548203389)
  ·
    refine ⟨7582106787627701830576271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20218951433673871548203389 7582106787627701830576271)
    ·
      refine ⟨11373160181441552745864407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7582106787627701830576271 11373160181441552745864407)
      ·
        refine ⟨17059740272162329118796611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11373160181441552745864407 17059740272162329118796611)
        ·
          refine ⟨25589610408243493678194917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17059740272162329118796611 25589610408243493678194917)
          ·
            refine ⟨4798051951545655064661547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25589610408243493678194917 4798051951545655064661547)
            ·
              refine ⟨7197077927318482596992321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4798051951545655064661547 7197077927318482596992321)
              ·
                refine ⟨5397808445488861947744241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7197077927318482596992321 5397808445488861947744241)
                ·
                  refine ⟨4048356334116646460808181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5397808445488861947744241 4048356334116646460808181)
                  ·
                    refine ⟨379533406323435605700767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4048356334116646460808181 379533406323435605700767)
                    ·
                      rfl

theorem cell22_1108708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 2, 2, 5].length) (baseStart_1108708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1108708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1108708 prefixEnd_1108708 := by exact prefixLift 1108708
  have htrace : WordTrace (prefixWord ++ tailWord_1108708) baseStart_1108708 baseEnd_1108708 := by
    simpa [prefixWord, tailWord_1108708, baseEnd_1108708] using wordTrace_append hprefix tailTrace_1108708
  have hstable : (prefixWord ++ tailWord_1108708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108708).length < 2 ^ (prefixWord ++ tailWord_1108708).sum := by decide
  have hdescent : baseEnd_1108708 < baseStart_1108708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108753 : List Nat := [1, 2, 2, 1, 1, 3, 2, 4, 1, 5]
def baseStart_1108753 : Nat := 118140960795 + 1108753 * 2 ^ 59
def prefixEnd_1108753 : Nat := 4983230072969 + 3 ^ 40 * 1108753 * 2
def baseEnd_1108753 : Nat := 379548810743070488325629

theorem tailTrace_1108753 : CollatzResearch.WordTrace tailWord_1108753 prefixEnd_1108753 379548810743070488325629 := by
  unfold tailWord_1108753
  simp only [CollatzResearch.WordTrace]
  refine ⟨40439544152184715781794913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26959696101456477187863275 40439544152184715781794913)
  ·
    refine ⟨30329658114138536836346185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40439544152184715781794913 30329658114138536836346185)
    ·
      refine ⟨22747243585603902627259639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30329658114138536836346185 22747243585603902627259639)
      ·
        refine ⟨34120865378405853940889459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22747243585603902627259639 34120865378405853940889459)
        ·
          refine ⟨51181298067608780911334189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34120865378405853940889459 51181298067608780911334189)
          ·
            refine ⟨19192986775353292841750321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51181298067608780911334189 19192986775353292841750321)
            ·
              refine ⟨14394740081514969631312741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19192986775353292841750321 14394740081514969631312741)
              ·
                refine ⟨2699013765284056805871139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14394740081514969631312741 2699013765284056805871139)
                ·
                  refine ⟨4048520647926085208806709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2699013765284056805871139 4048520647926085208806709)
                  ·
                    refine ⟨379548810743070488325629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4048520647926085208806709 379548810743070488325629)
                    ·
                      rfl

theorem cell22_1108753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 5].length) (baseStart_1108753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1108753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1108753 prefixEnd_1108753 := by exact prefixLift 1108753
  have htrace : WordTrace (prefixWord ++ tailWord_1108753) baseStart_1108753 baseEnd_1108753 := by
    simpa [prefixWord, tailWord_1108753, baseEnd_1108753] using wordTrace_append hprefix tailTrace_1108753
  have hstable : (prefixWord ++ tailWord_1108753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108753).length < 2 ^ (prefixWord ++ tailWord_1108753).sum := by decide
  have hdescent : baseEnd_1108753 < baseStart_1108753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108772 : List Nat := [2, 3, 1, 3, 3, 2, 1, 1, 6]
def baseStart_1108772 : Nat := 118140960795 + 1108772 * 2 ^ 59
def prefixEnd_1108772 : Nat := 4983230072969 + 3 ^ 40 * 1108772 * 2
def baseEnd_1108772 : Nat := 126518438277120257366857

theorem tailTrace_1108772 : CollatzResearch.WordTrace tailWord_1108772 prefixEnd_1108772 126518438277120257366857 := by
  unfold tailWord_1108772
  simp only [CollatzResearch.WordTrace]
  refine ⟨20220118569557941013368285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26960158092743921351157713 20220118569557941013368285)
  ·
    refine ⟨7582544463584227880013107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20220118569557941013368285 7582544463584227880013107)
    ·
      refine ⟨11373816695376341820019661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7582544463584227880013107 11373816695376341820019661)
      ·
        refine ⟨4265181260766128182507373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11373816695376341820019661 4265181260766128182507373)
        ·
          refine ⟨1599442972787298068440265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4265181260766128182507373 1599442972787298068440265)
          ·
            refine ⟨1199582229590473551330199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1599442972787298068440265 1199582229590473551330199)
            ·
              refine ⟨1799373344385710326995299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1199582229590473551330199 1799373344385710326995299)
              ·
                refine ⟨2699060016578565490492949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1799373344385710326995299 2699060016578565490492949)
                ·
                  refine ⟨126518438277120257366857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2699060016578565490492949 126518438277120257366857)
                  ·
                    rfl

theorem cell22_1108772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 1, 6].length) (baseStart_1108772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1108772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1108772 prefixEnd_1108772 := by exact prefixLift 1108772
  have htrace : WordTrace (prefixWord ++ tailWord_1108772) baseStart_1108772 baseEnd_1108772 := by
    simpa [prefixWord, tailWord_1108772, baseEnd_1108772] using wordTrace_append hprefix tailTrace_1108772
  have hstable : (prefixWord ++ tailWord_1108772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108772).length < 2 ^ (prefixWord ++ tailWord_1108772).sum := by decide
  have hdescent : baseEnd_1108772 < baseStart_1108772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108787 : List Nat := [1, 1, 1, 2, 6, 2, 1, 3, 2, 3]
def baseStart_1108787 : Nat := 118140960795 + 1108787 * 2 ^ 59
def prefixEnd_1108787 : Nat := 4983230072969 + 3 ^ 40 * 1108787 * 2
def baseEnd_1108787 : Nat := 379560449637905732975525

theorem tailTrace_1108787 : CollatzResearch.WordTrace tailWord_1108787 prefixEnd_1108787 379560449637905732975525 := by
  unfold tailWord_1108787
  simp only [CollatzResearch.WordTrace]
  refine ⟨40440784234061539588532615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26960522822707693059021743 40440784234061539588532615)
  ·
    refine ⟨60661176351092309382798923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40440784234061539588532615 60661176351092309382798923)
    ·
      refine ⟨90991764526638464074198385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60661176351092309382798923 90991764526638464074198385)
      ·
        refine ⟨68243823394978848055648789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90991764526638464074198385 68243823394978848055648789)
        ·
          refine ⟨3198929221639633502608537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 68243823394978848055648789 3198929221639633502608537)
          ·
            refine ⟨2399196916229725126956403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3198929221639633502608537 2399196916229725126956403)
            ·
              refine ⟨3598795374344587690434605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2399196916229725126956403 3598795374344587690434605)
              ·
                refine ⟨1349548265379220383912977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3598795374344587690434605 1349548265379220383912977)
                ·
                  refine ⟨1012161199034415287934733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1349548265379220383912977 1012161199034415287934733)
                  ·
                    refine ⟨379560449637905732975525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1012161199034415287934733 379560449637905732975525)
                    ·
                      rfl

theorem cell22_1108787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 3, 2, 3].length) (baseStart_1108787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1108787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1108787 prefixEnd_1108787 := by exact prefixLift 1108787
  have htrace : WordTrace (prefixWord ++ tailWord_1108787) baseStart_1108787 baseEnd_1108787 := by
    simpa [prefixWord, tailWord_1108787, baseEnd_1108787] using wordTrace_append hprefix tailTrace_1108787
  have hstable : (prefixWord ++ tailWord_1108787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108787).length < 2 ^ (prefixWord ++ tailWord_1108787).sum := by decide
  have hdescent : baseEnd_1108787 < baseStart_1108787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108804 : List Nat := [2, 3, 4, 2, 1, 1, 1, 2, 1, 5]
def baseStart_1108804 : Nat := 118140960795 + 1108804 * 2 ^ 59
def prefixEnd_1108804 : Nat := 4983230072969 + 3 ^ 40 * 1108804 * 2
def baseEnd_1108804 : Nat := 379566269085323355300473

theorem tailTrace_1108804 : CollatzResearch.WordTrace tailWord_1108804 prefixEnd_1108804 379566269085323355300473 := by
  unfold tailWord_1108804
  simp only [CollatzResearch.WordTrace]
  refine ⟨20220702137499975745950733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26960936183333300994600977 20220702137499975745950733)
  ·
    refine ⟨7582763301562490904731525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20220702137499975745950733 7582763301562490904731525)
    ·
      refine ⟨1421768119042967044637161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7582763301562490904731525 1421768119042967044637161)
      ·
        refine ⟨1066326089282225283477871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1421768119042967044637161 1066326089282225283477871)
        ·
          refine ⟨1599489133923337925216807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1066326089282225283477871 1599489133923337925216807)
          ·
            refine ⟨2399233700885006887825211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1599489133923337925216807 2399233700885006887825211)
            ·
              refine ⟨3598850551327510331737817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2399233700885006887825211 3598850551327510331737817)
              ·
                refine ⟨2699137913495632748803363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3598850551327510331737817 2699137913495632748803363)
                ·
                  refine ⟨4048706870243449123205045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2699137913495632748803363 4048706870243449123205045)
                  ·
                    refine ⟨379566269085323355300473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4048706870243449123205045 379566269085323355300473)
                    ·
                      rfl

theorem cell22_1108804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_1108804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1108804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1108804 prefixEnd_1108804 := by exact prefixLift 1108804
  have htrace : WordTrace (prefixWord ++ tailWord_1108804) baseStart_1108804 baseEnd_1108804 := by
    simpa [prefixWord, tailWord_1108804, baseEnd_1108804] using wordTrace_append hprefix tailTrace_1108804
  have hstable : (prefixWord ++ tailWord_1108804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108804).length < 2 ^ (prefixWord ++ tailWord_1108804).sum := by decide
  have hdescent : baseEnd_1108804 < baseStart_1108804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108834 : List Nat := [3, 3, 2, 1, 4, 1, 1, 7]
def baseStart_1108834 : Nat := 118140960795 + 1108834 * 2 ^ 59
def prefixEnd_1108834 : Nat := 4983230072969 + 3 ^ 40 * 1108834 * 2
def baseEnd_1108834 : Nat := 42175170966490364116709

theorem tailTrace_1108834 : CollatzResearch.WordTrace tailWord_1108834 prefixEnd_1108834 42175170966490364116709 := by
  unfold tailWord_1108834
  simp only [CollatzResearch.WordTrace]
  refine ⟨10110624616222816653873389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26961665643260844410329037 10110624616222816653873389)
  ·
    refine ⟨3791484231083556245202521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10110624616222816653873389 3791484231083556245202521)
    ·
      refine ⟨2843613173312667183901891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3791484231083556245202521 2843613173312667183901891)
      ·
        refine ⟨4265419759969000775852837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2843613173312667183901891 4265419759969000775852837)
        ·
          refine ⟨799766204994187645472407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4265419759969000775852837 799766204994187645472407)
          ·
            refine ⟨1199649307491281468208611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 799766204994187645472407 1199649307491281468208611)
            ·
              refine ⟨1799473961236922202312917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1199649307491281468208611 1799473961236922202312917)
              ·
                refine ⟨42175170966490364116709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1799473961236922202312917 42175170966490364116709)
                ·
                  rfl

theorem cell22_1108834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 7].length) (baseStart_1108834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1108834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1108834 prefixEnd_1108834 := by exact prefixLift 1108834
  have htrace : WordTrace (prefixWord ++ tailWord_1108834) baseStart_1108834 baseEnd_1108834 := by
    simpa [prefixWord, tailWord_1108834, baseEnd_1108834] using wordTrace_append hprefix tailTrace_1108834
  have hstable : (prefixWord ++ tailWord_1108834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108834).length < 2 ^ (prefixWord ++ tailWord_1108834).sum := by decide
  have hdescent : baseEnd_1108834 < baseStart_1108834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108843 : List Nat := [1, 1, 1, 1, 2, 2, 5, 1, 1, 7]
def baseStart_1108843 : Nat := 118140960795 + 1108843 * 2 ^ 59
def prefixEnd_1108843 : Nat := 4983230072969 + 3 ^ 40 * 1108843 * 2
def baseEnd_1108843 : Nat := 379579619582340253575353

theorem tailTrace_1108843 : CollatzResearch.WordTrace tailWord_1108843 prefixEnd_1108843 379579619582340253575353 := by
  unfold tailWord_1108843
  simp only [CollatzResearch.WordTrace]
  refine ⟨40442826721858661152571183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26961884481239107435047455 40442826721858661152571183)
  ·
    refine ⟨60664240082787991728856775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40442826721858661152571183 60664240082787991728856775)
    ·
      refine ⟨90996360124181987593285163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60664240082787991728856775 90996360124181987593285163)
      ·
        refine ⟨136494540186272981389927745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90996360124181987593285163 136494540186272981389927745)
        ·
          refine ⟨102370905139704736042445809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136494540186272981389927745 102370905139704736042445809)
          ·
            refine ⟨76778178854778552031834357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102370905139704736042445809 76778178854778552031834357)
            ·
              refine ⟨7197954267635489252984471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 76778178854778552031834357 7197954267635489252984471)
              ·
                refine ⟨10796931401453233879476707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7197954267635489252984471 10796931401453233879476707)
                ·
                  refine ⟨16195397102179850819215061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10796931401453233879476707 16195397102179850819215061)
                  ·
                    refine ⟨379579619582340253575353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16195397102179850819215061 379579619582340253575353)
                    ·
                      rfl

theorem cell22_1108843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 7].length) (baseStart_1108843 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1108843 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1108843 prefixEnd_1108843 := by exact prefixLift 1108843
  have htrace : WordTrace (prefixWord ++ tailWord_1108843) baseStart_1108843 baseEnd_1108843 := by
    simpa [prefixWord, tailWord_1108843, baseEnd_1108843] using wordTrace_append hprefix tailTrace_1108843
  have hstable : (prefixWord ++ tailWord_1108843).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108843).length < 2 ^ (prefixWord ++ tailWord_1108843).sum := by decide
  have hdescent : baseEnd_1108843 < baseStart_1108843 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108920 : List Nat := [2, 1, 2, 1, 2, 4, 2, 1, 1, 6]
def baseStart_1108920 : Nat := 118140960795 + 1108920 * 2 ^ 59
def prefixEnd_1108920 : Nat := 4983230072969 + 3 ^ 40 * 1108920 * 2
def baseEnd_1108920 : Nat := 379605978255937719400117

theorem tailTrace_1108920 : CollatzResearch.WordTrace tailWord_1108920 prefixEnd_1108920 379605978255937719400117 := by
  unfold tailWord_1108920
  simp only [CollatzResearch.WordTrace]
  refine ⟨20222817571289851651562107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26963756761719802202082809 20222817571289851651562107)
  ·
    refine ⟨30334226356934777477343161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20222817571289851651562107 30334226356934777477343161)
    ·
      refine ⟨22750669767701083108007371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30334226356934777477343161 22750669767701083108007371)
      ·
        refine ⟨34126004651551624662011057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22750669767701083108007371 34126004651551624662011057)
        ·
          refine ⟨25594503488663718496508293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34126004651551624662011057 25594503488663718496508293)
          ·
            refine ⟨4798969404124447218095305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25594503488663718496508293 4798969404124447218095305)
            ·
              refine ⟨3599227053093335413571479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4798969404124447218095305 3599227053093335413571479)
              ·
                refine ⟨5398840579640003120357219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3599227053093335413571479 5398840579640003120357219)
                ·
                  refine ⟨8098260869460004680535829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5398840579640003120357219 8098260869460004680535829)
                  ·
                    refine ⟨379605978255937719400117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8098260869460004680535829 379605978255937719400117)
                    ·
                      rfl

theorem cell22_1108920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 1, 1, 6].length) (baseStart_1108920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1108920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1108920 prefixEnd_1108920 := by exact prefixLift 1108920
  have htrace : WordTrace (prefixWord ++ tailWord_1108920) baseStart_1108920 baseEnd_1108920 := by
    simpa [prefixWord, tailWord_1108920, baseEnd_1108920] using wordTrace_append hprefix tailTrace_1108920
  have hstable : (prefixWord ++ tailWord_1108920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108920).length < 2 ^ (prefixWord ++ tailWord_1108920).sum := by decide
  have hdescent : baseEnd_1108920 < baseStart_1108920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108934 : List Nat := [6, 1, 3, 1, 1, 1, 3, 2, 1, 3]
def baseStart_1108934 : Nat := 118140960795 + 1108934 * 2 ^ 59
def prefixEnd_1108934 : Nat := 4983230072969 + 3 ^ 40 * 1108934 * 2
def baseEnd_1108934 : Nat := 379610770742046349550075

theorem tailTrace_1108934 : CollatzResearch.WordTrace tailWord_1108934 prefixEnd_1108934 379610770742046349550075 := by
  unfold tailWord_1108934
  simp only [CollatzResearch.WordTrace]
  refine ⟨1263942055141530740441683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 26964097176352655796089237 1263942055141530740441683)
  ·
    refine ⟨1895913082712296110662525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1263942055141530740441683 1895913082712296110662525)
    ·
      refine ⟨710967406017111041498447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1895913082712296110662525 710967406017111041498447)
      ·
        refine ⟨1066451109025666562247671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 710967406017111041498447 1066451109025666562247671)
        ·
          refine ⟨1599676663538499843371507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1066451109025666562247671 1599676663538499843371507)
          ·
            refine ⟨2399514995307749765057261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1599676663538499843371507 2399514995307749765057261)
            ·
              refine ⟨899818123240406161896473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2399514995307749765057261 899818123240406161896473)
              ·
                refine ⟨674863592430304621422355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 899818123240406161896473 674863592430304621422355)
                ·
                  refine ⟨1012295388645456932133533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 674863592430304621422355 1012295388645456932133533)
                  ·
                    refine ⟨379610770742046349550075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1012295388645456932133533 379610770742046349550075)
                    ·
                      rfl

theorem cell22_1108934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_1108934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1108934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1108934 prefixEnd_1108934 := by exact prefixLift 1108934
  have htrace : WordTrace (prefixWord ++ tailWord_1108934) baseStart_1108934 baseEnd_1108934 := by
    simpa [prefixWord, tailWord_1108934, baseEnd_1108934] using wordTrace_append hprefix tailTrace_1108934
  have hstable : (prefixWord ++ tailWord_1108934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108934).length < 2 ^ (prefixWord ++ tailWord_1108934).sum := by decide
  have hdescent : baseEnd_1108934 < baseStart_1108934 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108984 : List Nat := [2, 1, 2, 1, 1, 3, 1, 7, 1, 3]
def baseStart_1108984 : Nat := 118140960795 + 1108984 * 2 ^ 59
def prefixEnd_1108984 : Nat := 4983230072969 + 3 ^ 40 * 1108984 * 2
def baseEnd_1108984 : Nat := 379627886763862885799921

theorem tailTrace_1108984 : CollatzResearch.WordTrace tailWord_1108984 prefixEnd_1108984 379627886763862885799921 := by
  unfold tailWord_1108984
  simp only [CollatzResearch.WordTrace]
  refine ⟨20223984707173921116727003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26965312942898561488969337 20223984707173921116727003)
  ·
    refine ⟨30335977060760881675090505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20223984707173921116727003 30335977060760881675090505)
    ·
      refine ⟨22751982795570661256317879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30335977060760881675090505 22751982795570661256317879)
      ·
        refine ⟨34127974193355991884476819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22751982795570661256317879 34127974193355991884476819)
        ·
          refine ⟨51191961290033987826715229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34127974193355991884476819 51191961290033987826715229)
          ·
            refine ⟨19196985483762745435018211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51191961290033987826715229 19196985483762745435018211)
            ·
              refine ⟨28795478225644118152527317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19196985483762745435018211 28795478225644118152527317)
              ·
                refine ⟨674894020913534019199859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 28795478225644118152527317 674894020913534019199859)
                ·
                  refine ⟨1012341031370301028799789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 674894020913534019199859 1012341031370301028799789)
                  ·
                    refine ⟨379627886763862885799921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1012341031370301028799789 379627886763862885799921)
                    ·
                      rfl

theorem cell22_1108984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 7, 1, 3].length) (baseStart_1108984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1108984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1108984 prefixEnd_1108984 := by exact prefixLift 1108984
  have htrace : WordTrace (prefixWord ++ tailWord_1108984) baseStart_1108984 baseEnd_1108984 := by
    simpa [prefixWord, tailWord_1108984, baseEnd_1108984] using wordTrace_append hprefix tailTrace_1108984
  have hstable : (prefixWord ++ tailWord_1108984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108984).length < 2 ^ (prefixWord ++ tailWord_1108984).sum := by decide
  have hdescent : baseEnd_1108984 < baseStart_1108984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1108997 : List Nat := [1, 3, 1, 1, 2, 3, 4, 2, 5]
def baseStart_1108997 : Nat := 118140960795 + 1108997 * 2 ^ 59
def prefixEnd_1108997 : Nat := 4983230072969 + 3 ^ 40 * 1108997 * 2
def baseEnd_1108997 : Nat := 126544112309845061741627

theorem tailTrace_1108997 : CollatzResearch.WordTrace tailWord_1108997 prefixEnd_1108997 126544112309845061741627 := by
  unfold tailWord_1108997
  simp only [CollatzResearch.WordTrace]
  refine ⟨40448443563300745453677245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26965629042200496969118163 40448443563300745453677245)
  ·
    refine ⟨15168166336237779545128967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40448443563300745453677245 15168166336237779545128967)
    ·
      refine ⟨22752249504356669317693451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15168166336237779545128967 22752249504356669317693451)
      ·
        refine ⟨34128374256535003976540177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22752249504356669317693451 34128374256535003976540177)
        ·
          refine ⟨25596280692401252982405133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34128374256535003976540177 25596280692401252982405133)
          ·
            refine ⟨9598605259650469868401925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25596280692401252982405133 9598605259650469868401925)
            ·
              refine ⟨1799738486184463100325361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9598605259650469868401925 1799738486184463100325361)
              ·
                refine ⟨1349803864638347325244021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1799738486184463100325361 1349803864638347325244021)
                ·
                  refine ⟨126544112309845061741627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1349803864638347325244021 126544112309845061741627)
                  ·
                    rfl

theorem cell22_1108997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 2, 5].length) (baseStart_1108997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1108997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1108997 prefixEnd_1108997 := by exact prefixLift 1108997
  have htrace : WordTrace (prefixWord ++ tailWord_1108997) baseStart_1108997 baseEnd_1108997 := by
    simpa [prefixWord, tailWord_1108997, baseEnd_1108997] using wordTrace_append hprefix tailTrace_1108997
  have hstable : (prefixWord ++ tailWord_1108997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1108997).length < 2 ^ (prefixWord ++ tailWord_1108997).sum := by decide
  have hdescent : baseEnd_1108997 < baseStart_1108997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1108997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109027 : List Nat := [1, 1, 1, 4, 3, 2, 2, 1, 3, 4]
def baseStart_1109027 : Nat := 118140960795 + 1109027 * 2 ^ 59
def prefixEnd_1109027 : Nat := 4983230072969 + 3 ^ 40 * 1109027 * 2
def baseEnd_1109027 : Nat := 379642606542625106974789

theorem tailTrace_1109027 : CollatzResearch.WordTrace tailWord_1109027 prefixEnd_1109027 379642606542625106974789 := by
  unfold tailWord_1109027
  simp only [CollatzResearch.WordTrace]
  refine ⟨40449537753192060577269335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26966358502128040384846223 40449537753192060577269335)
  ·
    refine ⟨60674306629788090865904003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40449537753192060577269335 60674306629788090865904003)
    ·
      refine ⟨91011459944682136298856005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60674306629788090865904003 91011459944682136298856005)
      ·
        refine ⟨17064648739627900556035501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 91011459944682136298856005 17064648739627900556035501)
        ·
          refine ⟨6399243277360462708513313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17064648739627900556035501 6399243277360462708513313)
          ·
            refine ⟨4799432458020347031384985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6399243277360462708513313 4799432458020347031384985)
            ·
              refine ⟨3599574343515260273538739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4799432458020347031384985 3599574343515260273538739)
              ·
                refine ⟨5399361515272890410308109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3599574343515260273538739 5399361515272890410308109)
                ·
                  refine ⟨2024760568227333903865541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5399361515272890410308109 2024760568227333903865541)
                  ·
                    refine ⟨379642606542625106974789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2024760568227333903865541 379642606542625106974789)
                    ·
                      rfl

theorem cell22_1109027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 1, 3, 4].length) (baseStart_1109027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1109027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1109027 prefixEnd_1109027 := by exact prefixLift 1109027
  have htrace : WordTrace (prefixWord ++ tailWord_1109027) baseStart_1109027 baseEnd_1109027 := by
    simpa [prefixWord, tailWord_1109027, baseEnd_1109027] using wordTrace_append hprefix tailTrace_1109027
  have hstable : (prefixWord ++ tailWord_1109027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109027).length < 2 ^ (prefixWord ++ tailWord_1109027).sum := by decide
  have hdescent : baseEnd_1109027 < baseStart_1109027 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109074 : List Nat := [3, 2, 2, 1, 3, 1, 3, 1, 1, 5]
def baseStart_1109074 : Nat := 118140960795 + 1109074 * 2 ^ 59
def prefixEnd_1109074 : Nat := 4983230072969 + 3 ^ 40 * 1109074 * 2
def baseEnd_1109074 : Nat := 379658695603132651049645

theorem tailTrace_1109074 : CollatzResearch.WordTrace tailWord_1109074 prefixEnd_1109074 379658695603132651049645 := by
  unfold tailWord_1109074
  simp only [CollatzResearch.WordTrace]
  refine ⟨10112812996005446901057569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26967501322681191736153517 10112812996005446901057569)
  ·
    refine ⟨7584609747004085175793177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10112812996005446901057569 7584609747004085175793177)
    ·
      refine ⟨5688457310253063881844883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7584609747004085175793177 5688457310253063881844883)
      ·
        refine ⟨8532685965379595822767325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5688457310253063881844883 8532685965379595822767325)
        ·
          refine ⟨3199757237017348433537747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8532685965379595822767325 3199757237017348433537747)
          ·
            refine ⟨4799635855526022650306621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3199757237017348433537747 4799635855526022650306621)
            ·
              refine ⟨1799863445822258493864983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4799635855526022650306621 1799863445822258493864983)
              ·
                refine ⟨2699795168733387740797475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1799863445822258493864983 2699795168733387740797475)
                ·
                  refine ⟨4049692753100081611196213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2699795168733387740797475 4049692753100081611196213)
                  ·
                    refine ⟨379658695603132651049645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4049692753100081611196213 379658695603132651049645)
                    ·
                      rfl

theorem cell22_1109074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_1109074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1109074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1109074 prefixEnd_1109074 := by exact prefixLift 1109074
  have htrace : WordTrace (prefixWord ++ tailWord_1109074) baseStart_1109074 baseEnd_1109074 := by
    simpa [prefixWord, tailWord_1109074, baseEnd_1109074] using wordTrace_append hprefix tailTrace_1109074
  have hstable : (prefixWord ++ tailWord_1109074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109074).length < 2 ^ (prefixWord ++ tailWord_1109074).sum := by decide
  have hdescent : baseEnd_1109074 < baseStart_1109074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109117 : List Nat := [1, 4, 1, 1, 3, 1, 2, 1, 2, 6]
def baseStart_1109117 : Nat := 118140960795 + 1109117 * 2 ^ 59
def prefixEnd_1109117 : Nat := 4983230072969 + 3 ^ 40 * 1109117 * 2
def baseEnd_1109117 : Nat := 379673415381894872224513

theorem tailTrace_1109117 : CollatzResearch.WordTrace tailWord_1109117 prefixEnd_1109117 379673415381894872224513 := by
  unfold tailWord_1109117
  simp only [CollatzResearch.WordTrace]
  refine ⟨40452820322866005948045605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26968546881910670632030403 40452820322866005948045605)
  ·
    refine ⟨7584903810537376115258551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40452820322866005948045605 7584903810537376115258551)
    ·
      refine ⟨11377355715806064172887827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7584903810537376115258551 11377355715806064172887827)
      ·
        refine ⟨17066033573709096259331741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11377355715806064172887827 17066033573709096259331741)
        ·
          refine ⟨6399762590140911097249403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17066033573709096259331741 6399762590140911097249403)
          ·
            refine ⟨9599643885211366645874105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6399762590140911097249403 9599643885211366645874105)
            ·
              refine ⟨7199732913908524984405579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9599643885211366645874105 7199732913908524984405579)
              ·
                refine ⟨10799599370862787476608369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7199732913908524984405579 10799599370862787476608369)
                ·
                  refine ⟨8099699528147090607456277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10799599370862787476608369 8099699528147090607456277)
                  ·
                    refine ⟨379673415381894872224513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8099699528147090607456277 379673415381894872224513)
                    ·
                      rfl

theorem cell22_1109117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 2, 6].length) (baseStart_1109117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1109117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1109117 prefixEnd_1109117 := by exact prefixLift 1109117
  have htrace : WordTrace (prefixWord ++ tailWord_1109117) baseStart_1109117 baseEnd_1109117 := by
    simpa [prefixWord, tailWord_1109117, baseEnd_1109117] using wordTrace_append hprefix tailTrace_1109117
  have hstable : (prefixWord ++ tailWord_1109117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109117).length < 2 ^ (prefixWord ++ tailWord_1109117).sum := by decide
  have hdescent : baseEnd_1109117 < baseStart_1109117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109125 : List Nat := [1, 3, 1, 1, 7, 1, 2, 1, 2, 3]
def baseStart_1109125 : Nat := 118140960795 + 1109125 * 2 ^ 59
def prefixEnd_1109125 : Nat := 4983230072969 + 3 ^ 40 * 1109125 * 2
def baseEnd_1109125 : Nat := 379676153945385518024489

theorem tailTrace_1109125 : CollatzResearch.WordTrace tailWord_1109125 prefixEnd_1109125 379676153945385518024489 := by
  unfold tailWord_1109125
  simp only [CollatzResearch.WordTrace]
  refine ⟨40453112106837023314336829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26968741404558015542891219 40453112106837023314336829)
  ·
    refine ⟨15169917040063883742876311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40453112106837023314336829 15169917040063883742876311)
    ·
      refine ⟨22754875560095825614314467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15169917040063883742876311 22754875560095825614314467)
      ·
        refine ⟨34132313340143738421471701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22754875560095825614314467 34132313340143738421471701)
        ·
          refine ⟨799976093909618869253243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 34132313340143738421471701 799976093909618869253243)
          ·
            refine ⟨1199964140864428303879865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 799976093909618869253243 1199964140864428303879865)
            ·
              refine ⟨899973105648321227909899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1199964140864428303879865 899973105648321227909899)
              ·
                refine ⟨1349959658472481841864849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 899973105648321227909899 1349959658472481841864849)
                ·
                  refine ⟨1012469743854361381398637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1349959658472481841864849 1012469743854361381398637)
                  ·
                    refine ⟨379676153945385518024489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1012469743854361381398637 379676153945385518024489)
                    ·
                      rfl

theorem cell22_1109125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 2, 1, 2, 3].length) (baseStart_1109125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1109125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1109125 prefixEnd_1109125 := by exact prefixLift 1109125
  have htrace : WordTrace (prefixWord ++ tailWord_1109125) baseStart_1109125 baseEnd_1109125 := by
    simpa [prefixWord, tailWord_1109125, baseEnd_1109125] using wordTrace_append hprefix tailTrace_1109125
  have hstable : (prefixWord ++ tailWord_1109125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109125).length < 2 ^ (prefixWord ++ tailWord_1109125).sum := by decide
  have hdescent : baseEnd_1109125 < baseStart_1109125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109170 : List Nat := [3, 2, 1, 1, 1, 6, 2, 2, 1, 3]
def baseStart_1109170 : Nat := 118140960795 + 1109170 * 2 ^ 59
def prefixEnd_1109170 : Nat := 4983230072969 + 3 ^ 40 * 1109170 * 2
def baseEnd_1109170 : Nat := 379691558365020400649351

theorem tailTrace_1109170 : CollatzResearch.WordTrace tailWord_1109170 prefixEnd_1109170 379691558365020400649351 := by
  unfold tailWord_1109170
  simp only [CollatzResearch.WordTrace]
  refine ⟨10113688347918498999931241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26969835594449330666483309 10113688347918498999931241)
  ·
    refine ⟨7585266260938874249948431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10113688347918498999931241 7585266260938874249948431)
    ·
      refine ⟨11377899391408311374922647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7585266260938874249948431 11377899391408311374922647)
      ·
        refine ⟨17066849087112467062383971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11377899391408311374922647 17066849087112467062383971)
        ·
          refine ⟨25600273630668700593575957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17066849087112467062383971 25600273630668700593575957)
          ·
            refine ⟨1200012826437595340323873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 25600273630668700593575957 1200012826437595340323873)
            ·
              refine ⟨900009619828196505242905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1200012826437595340323873 900009619828196505242905)
              ·
                refine ⟨675007214871147378932179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 900009619828196505242905 675007214871147378932179)
                ·
                  refine ⟨1012510822306721068398269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 675007214871147378932179 1012510822306721068398269)
                  ·
                    refine ⟨379691558365020400649351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1012510822306721068398269 379691558365020400649351)
                    ·
                      rfl

theorem cell22_1109170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 2, 2, 1, 3].length) (baseStart_1109170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1109170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1109170 prefixEnd_1109170 := by exact prefixLift 1109170
  have htrace : WordTrace (prefixWord ++ tailWord_1109170) baseStart_1109170 baseEnd_1109170 := by
    simpa [prefixWord, tailWord_1109170, baseEnd_1109170] using wordTrace_append hprefix tailTrace_1109170
  have hstable : (prefixWord ++ tailWord_1109170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109170).length < 2 ^ (prefixWord ++ tailWord_1109170).sum := by decide
  have hdescent : baseEnd_1109170 < baseStart_1109170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109194 : List Nat := [3, 1, 2, 1, 3, 3, 1, 2, 6]
def baseStart_1109194 : Nat := 118140960795 + 1109194 * 2 ^ 59
def prefixEnd_1109194 : Nat := 4983230072969 + 3 ^ 40 * 1109194 * 2
def baseEnd_1109194 : Nat := 126566591351830779349759

theorem tailTrace_1109194 : CollatzResearch.WordTrace tailWord_1109194 prefixEnd_1109194 126566591351830779349759 := by
  unfold tailWord_1109194
  simp only [CollatzResearch.WordTrace]
  refine ⟨10113907185896762024649659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26970419162391365399065757 10113907185896762024649659)
  ·
    refine ⟨15170860778845143036974489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10113907185896762024649659 15170860778845143036974489)
    ·
      refine ⟨11378145584133857277730867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15170860778845143036974489 11378145584133857277730867)
      ·
        refine ⟨17067218376200785916596301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11378145584133857277730867 17067218376200785916596301)
        ·
          refine ⟨6400206891075294718723613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17067218376200785916596301 6400206891075294718723613)
          ·
            refine ⟨2400077584153235519521355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6400206891075294718723613 2400077584153235519521355)
            ·
              refine ⟨3600116376229853279282033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2400077584153235519521355 3600116376229853279282033)
              ·
                refine ⟨2700087282172389959461525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3600116376229853279282033 2700087282172389959461525)
                ·
                  refine ⟨126566591351830779349759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2700087282172389959461525 126566591351830779349759)
                  ·
                    rfl

theorem cell22_1109194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 2, 6].length) (baseStart_1109194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1109194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1109194 prefixEnd_1109194 := by exact prefixLift 1109194
  have htrace : WordTrace (prefixWord ++ tailWord_1109194) baseStart_1109194 baseEnd_1109194 := by
    simpa [prefixWord, tailWord_1109194, baseEnd_1109194] using wordTrace_append hprefix tailTrace_1109194
  have hstable : (prefixWord ++ tailWord_1109194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109194).length < 2 ^ (prefixWord ++ tailWord_1109194).sum := by decide
  have hdescent : baseEnd_1109194 < baseStart_1109194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109209 : List Nat := [1, 2, 1, 2, 3, 1, 1, 4, 4, 3]
def baseStart_1109209 : Nat := 118140960795 + 1109209 * 2 ^ 59
def prefixEnd_1109209 : Nat := 4983230072969 + 3 ^ 40 * 1109209 * 2
def baseEnd_1109209 : Nat := 379704908862037298924231

theorem tailTrace_1109209 : CollatzResearch.WordTrace tailWord_1109209 prefixEnd_1109209 379704908862037298924231 := by
  unfold tailWord_1109209
  simp only [CollatzResearch.WordTrace]
  refine ⟨40456175838532705660394681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26970783892355137106929787 40456175838532705660394681)
  ·
    refine ⟨30342131878899529245296011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40456175838532705660394681 30342131878899529245296011)
    ·
      refine ⟨45513197818349293867944017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30342131878899529245296011 45513197818349293867944017)
      ·
        refine ⟨34134898363761970400958013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45513197818349293867944017 34134898363761970400958013)
        ·
          refine ⟨12800586886410738900359255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34134898363761970400958013 12800586886410738900359255)
          ·
            refine ⟨19200880329616108350538883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12800586886410738900359255 19200880329616108350538883)
            ·
              refine ⟨28801320494424162525808325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19200880329616108350538883 28801320494424162525808325)
              ·
                refine ⟨5400247592704530473589061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28801320494424162525808325 5400247592704530473589061)
                ·
                  refine ⟨1012546423632099463797949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5400247592704530473589061 1012546423632099463797949)
                  ·
                    refine ⟨379704908862037298924231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1012546423632099463797949 379704908862037298924231)
                    ·
                      rfl

theorem cell22_1109209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 4, 4, 3].length) (baseStart_1109209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1109209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1109209 prefixEnd_1109209 := by exact prefixLift 1109209
  have htrace : WordTrace (prefixWord ++ tailWord_1109209) baseStart_1109209 baseEnd_1109209 := by
    simpa [prefixWord, tailWord_1109209, baseEnd_1109209] using wordTrace_append hprefix tailTrace_1109209
  have hstable : (prefixWord ++ tailWord_1109209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109209).length < 2 ^ (prefixWord ++ tailWord_1109209).sum := by decide
  have hdescent : baseEnd_1109209 < baseStart_1109209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
