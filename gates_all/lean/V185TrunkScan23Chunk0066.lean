import V185TrunkScan23Chunk0065

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_390884 : List Nat := [2, 3, 1, 1, 1, 3, 2, 2, 2, 1, 5]
def baseStart_390884 : Nat := 118140960795 + 390884 * 2 ^ 59
def prefixEnd_390884 : Nat := 4983230072969 + 3 ^ 40 * 390884 * 2
def baseEnd_390884 : Nat := 200711372152153898252363

theorem tailTrace_390884 : CollatzResearch.WordTrace tailWord_390884 prefixEnd_390884 200711372152153898252363 := by
  unfold tailWord_390884
  simp only [CollatzResearch.WordTrace]
  refine ⟨7128355357950750258729853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9504473810601000344973137 7128355357950750258729853)
  ·
    refine ⟨2673133259231531347023695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7128355357950750258729853 2673133259231531347023695)
    ·
      refine ⟨4009699888847297020535543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2673133259231531347023695 4009699888847297020535543)
      ·
        refine ⟨6014549833270945530803315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4009699888847297020535543 6014549833270945530803315)
        ·
          refine ⟨9021824749906418296204973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6014549833270945530803315 9021824749906418296204973)
          ·
            refine ⟨3383184281214906861076865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9021824749906418296204973 3383184281214906861076865)
            ·
              refine ⟨2537388210911180145807649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3383184281214906861076865 2537388210911180145807649)
              ·
                refine ⟨1903041158183385109355737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2537388210911180145807649 1903041158183385109355737)
                ·
                  refine ⟨1427280868637538832016803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1903041158183385109355737 1427280868637538832016803)
                  ·
                    refine ⟨2140921302956308248025205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1427280868637538832016803 2140921302956308248025205)
                    ·
                      refine ⟨200711372152153898252363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2140921302956308248025205 200711372152153898252363)
                      ·
                        rfl

theorem cell23_390884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 2, 2, 1, 5].length) (baseStart_390884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_390884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_390884 prefixEnd_390884 := by exact prefixLift 390884
  have htrace : WordTrace (prefixWord ++ tailWord_390884) baseStart_390884 baseEnd_390884 := by
    simpa [prefixWord, tailWord_390884, baseEnd_390884] using wordTrace_append hprefix tailTrace_390884
  have hstable : (prefixWord ++ tailWord_390884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390884).length < 2 ^ (prefixWord ++ tailWord_390884).sum := by decide
  have hdescent : baseEnd_390884 < baseStart_390884 := by decide
  rcases family_descends (prefixWord ++ tailWord_390884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390898 : List Nat := [3, 2, 1, 3, 1, 1, 1, 1, 6, 2, 2]
def baseStart_390898 : Nat := 118140960795 + 390898 * 2 ^ 59
def prefixEnd_390898 : Nat := 4983230072969 + 3 ^ 40 * 390898 * 2
def baseEnd_390898 : Nat := 200718560881316843477299

theorem tailTrace_390898 : CollatzResearch.WordTrace tailWord_390898 prefixEnd_390898 200718560881316843477299 := by
  unfold tailWord_390898
  simp only [CollatzResearch.WordTrace]
  refine ⟨3564305334462695227117337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9504814225233853938979565 3564305334462695227117337)
  ·
    refine ⟨2673229000847021420338003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3564305334462695227117337 2673229000847021420338003)
    ·
      refine ⟨4009843501270532130507005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2673229000847021420338003 4009843501270532130507005)
      ·
        refine ⟨1503691312976449548940127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4009843501270532130507005 1503691312976449548940127)
        ·
          refine ⟨2255536969464674323410191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1503691312976449548940127 2255536969464674323410191)
          ·
            refine ⟨3383305454197011485115287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2255536969464674323410191 3383305454197011485115287)
            ·
              refine ⟨5074958181295517227672931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3383305454197011485115287 5074958181295517227672931)
              ·
                refine ⟨7612437271943275841509397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5074958181295517227672931 7612437271943275841509397)
                ·
                  refine ⟨356832997122341055070753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7612437271943275841509397 356832997122341055070753)
                  ·
                    refine ⟨267624747841755791303065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 356832997122341055070753 267624747841755791303065)
                    ·
                      refine ⟨200718560881316843477299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 267624747841755791303065 200718560881316843477299)
                      ·
                        rfl

theorem cell23_390898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 6, 2, 2].length) (baseStart_390898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_390898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_390898 prefixEnd_390898 := by exact prefixLift 390898
  have htrace : WordTrace (prefixWord ++ tailWord_390898) baseStart_390898 baseEnd_390898 := by
    simpa [prefixWord, tailWord_390898, baseEnd_390898] using wordTrace_append hprefix tailTrace_390898
  have hstable : (prefixWord ++ tailWord_390898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390898).length < 2 ^ (prefixWord ++ tailWord_390898).sum := by decide
  have hdescent : baseEnd_390898 < baseStart_390898 := by decide
  rcases family_descends (prefixWord ++ tailWord_390898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390944 : List Nat := [2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 7]
def baseStart_390944 : Nat := 118140960795 + 390944 * 2 ^ 59
def prefixEnd_390944 : Nat := 4983230072969 + 3 ^ 40 * 390944 * 2
def baseEnd_390944 : Nat := 200742180991423663502087

theorem tailTrace_390944 : CollatzResearch.WordTrace tailWord_390944 prefixEnd_390944 200742180991423663502087 := by
  unfold tailWord_390944
  simp only [CollatzResearch.WordTrace]
  refine ⟨7129449547842065382321943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9505932730456087176429257 7129449547842065382321943)
  ·
    refine ⟨10694174321763098073482915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7129449547842065382321943 10694174321763098073482915)
    ·
      refine ⟨16041261482644647110224373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10694174321763098073482915 16041261482644647110224373)
      ·
        refine ⟨1503868263997935666583535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16041261482644647110224373 1503868263997935666583535)
        ·
          refine ⟨2255802395996903499875303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1503868263997935666583535 2255802395996903499875303)
          ·
            refine ⟨3383703593995355249812955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2255802395996903499875303 3383703593995355249812955)
            ·
              refine ⟨5075555390993032874719433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3383703593995355249812955 5075555390993032874719433)
              ·
                refine ⟨3806666543244774656039575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5075555390993032874719433 3806666543244774656039575)
                ·
                  refine ⟨5709999814867161984059363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3806666543244774656039575 5709999814867161984059363)
                  ·
                    refine ⟨8564999722300742976089045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5709999814867161984059363 8564999722300742976089045)
                    ·
                      refine ⟨200742180991423663502087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 8564999722300742976089045 200742180991423663502087)
                      ·
                        rfl

theorem cell23_390944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_390944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_390944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_390944 prefixEnd_390944 := by exact prefixLift 390944
  have htrace : WordTrace (prefixWord ++ tailWord_390944) baseStart_390944 baseEnd_390944 := by
    simpa [prefixWord, tailWord_390944, baseEnd_390944] using wordTrace_append hprefix tailTrace_390944
  have hstable : (prefixWord ++ tailWord_390944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390944).length < 2 ^ (prefixWord ++ tailWord_390944).sum := by decide
  have hdescent : baseEnd_390944 < baseStart_390944 := by decide
  rcases family_descends (prefixWord ++ tailWord_390944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390981 : List Nat := [1, 3, 1, 1, 1, 2, 4, 3, 3, 4]
def baseStart_390981 : Nat := 118140960795 + 390981 * 2 ^ 59
def prefixEnd_390981 : Nat := 4983230072969 + 3 ^ 40 * 390981 * 2
def baseEnd_390981 : Nat := 66920393258546672913139

theorem tailTrace_390981 : CollatzResearch.WordTrace tailWord_390981 prefixEnd_390981 66920393258546672913139 := by
  unfold tailWord_390981
  simp only [CollatzResearch.WordTrace]
  refine ⟨14260248596550086083740797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9506832397700057389160531 14260248596550086083740797)
  ·
    refine ⟨5347593223706282281402799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14260248596550086083740797 5347593223706282281402799)
    ·
      refine ⟨8021389835559423422104199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5347593223706282281402799 8021389835559423422104199)
      ·
        refine ⟨12032084753339135133156299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8021389835559423422104199 12032084753339135133156299)
        ·
          refine ⟨18048127130008702699734449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12032084753339135133156299 18048127130008702699734449)
          ·
            refine ⟨13536095347506527024800837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18048127130008702699734449 13536095347506527024800837)
            ·
              refine ⟨2538017877657473817150157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13536095347506527024800837 2538017877657473817150157)
              ·
                refine ⟨951756704121552681431309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2538017877657473817150157 951756704121552681431309)
                ·
                  refine ⟨356908764045582255536741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 951756704121552681431309 356908764045582255536741)
                  ·
                    refine ⟨66920393258546672913139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 356908764045582255536741 66920393258546672913139)
                    ·
                      rfl

theorem cell23_390981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 3, 3, 4].length) (baseStart_390981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_390981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_390981 prefixEnd_390981 := by exact prefixLift 390981
  have htrace : WordTrace (prefixWord ++ tailWord_390981) baseStart_390981 baseEnd_390981 := by
    simpa [prefixWord, tailWord_390981, baseEnd_390981] using wordTrace_append hprefix tailTrace_390981
  have hstable : (prefixWord ++ tailWord_390981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390981).length < 2 ^ (prefixWord ++ tailWord_390981).sum := by decide
  have hdescent : baseEnd_390981 < baseStart_390981 := by decide
  rcases family_descends (prefixWord ++ tailWord_390981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391008 : List Nat := [2, 1, 1, 3, 3, 2, 3, 1, 2, 2, 3]
def baseStart_391008 : Nat := 118140960795 + 391008 * 2 ^ 59
def prefixEnd_391008 : Nat := 4983230072969 + 3 ^ 40 * 391008 * 2
def baseEnd_391008 : Nat := 200775043753311413101793

theorem tailTrace_391008 : CollatzResearch.WordTrace tailWord_391008 prefixEnd_391008 200775043753311413101793 := by
  unfold tailWord_391008
  simp only [CollatzResearch.WordTrace]
  refine ⟨7130616683726134847486839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9507488911634846463315785 7130616683726134847486839)
  ·
    refine ⟨10695925025589202271230259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7130616683726134847486839 10695925025589202271230259)
    ·
      refine ⟨16043887538383803406845389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10695925025589202271230259 16043887538383803406845389)
      ·
        refine ⟨6016457826893926277567021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16043887538383803406845389 6016457826893926277567021)
        ·
          refine ⟨2256171685085222354087633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6016457826893926277567021 2256171685085222354087633)
          ·
            refine ⟨1692128763813916765565725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2256171685085222354087633 1692128763813916765565725)
            ·
              refine ⟨634548286430218787087147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1692128763813916765565725 634548286430218787087147)
              ·
                refine ⟨951822429645328180630721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 634548286430218787087147 951822429645328180630721)
                ·
                  refine ⟨713866822233996135473041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 951822429645328180630721 713866822233996135473041)
                  ·
                    refine ⟨535400116675497101604781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 713866822233996135473041 535400116675497101604781)
                    ·
                      refine ⟨200775043753311413101793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 535400116675497101604781 200775043753311413101793)
                      ·
                        rfl

theorem cell23_391008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 1, 2, 2, 3].length) (baseStart_391008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_391008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_391008 prefixEnd_391008 := by exact prefixLift 391008
  have htrace : WordTrace (prefixWord ++ tailWord_391008) baseStart_391008 baseEnd_391008 := by
    simpa [prefixWord, tailWord_391008, baseEnd_391008] using wordTrace_append hprefix tailTrace_391008
  have hstable : (prefixWord ++ tailWord_391008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391008).length < 2 ^ (prefixWord ++ tailWord_391008).sum := by decide
  have hdescent : baseEnd_391008 < baseStart_391008 := by decide
  rcases family_descends (prefixWord ++ tailWord_391008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391015 : List Nat := [1, 1, 5, 1, 2, 1, 4, 3, 1, 4]
def baseStart_391015 : Nat := 118140960795 + 391015 * 2 ^ 59
def prefixEnd_391015 : Nat := 4983230072969 + 3 ^ 40 * 391015 * 2
def baseEnd_391015 : Nat := 66926212705964295238087

theorem tailTrace_391015 : CollatzResearch.WordTrace tailWord_391015 prefixEnd_391015 66926212705964295238087 := by
  unfold tailWord_391015
  simp only [CollatzResearch.WordTrace]
  refine ⟨14261488678426909890478499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9507659118951273260318999 14261488678426909890478499)
  ·
    refine ⟨21392233017640364835717749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14261488678426909890478499 21392233017640364835717749)
    ·
      refine ⟨2005521845403784203348539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21392233017640364835717749 2005521845403784203348539)
      ·
        refine ⟨3008282768105676305022809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2005521845403784203348539 3008282768105676305022809)
        ·
          refine ⟨2256212076079257228767107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3008282768105676305022809 2256212076079257228767107)
          ·
            refine ⟨3384318114118885843150661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2256212076079257228767107 3384318114118885843150661)
            ·
              refine ⟨634559646397291095590749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3384318114118885843150661 634559646397291095590749)
              ·
                refine ⟨237959867398984160846531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 634559646397291095590749 237959867398984160846531)
                ·
                  refine ⟨356939801098476241269797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 237959867398984160846531 356939801098476241269797)
                  ·
                    refine ⟨66926212705964295238087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 356939801098476241269797 66926212705964295238087)
                    ·
                      rfl

theorem cell23_391015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 3, 1, 4].length) (baseStart_391015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_391015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_391015 prefixEnd_391015 := by exact prefixLift 391015
  have htrace : WordTrace (prefixWord ++ tailWord_391015) baseStart_391015 baseEnd_391015 := by
    simpa [prefixWord, tailWord_391015, baseEnd_391015] using wordTrace_append hprefix tailTrace_391015
  have hstable : (prefixWord ++ tailWord_391015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391015).length < 2 ^ (prefixWord ++ tailWord_391015).sum := by decide
  have hdescent : baseEnd_391015 < baseStart_391015 := by decide
  rcases family_descends (prefixWord ++ tailWord_391015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391089 : List Nat := [1, 2, 2, 4, 2, 2, 3, 2, 1, 1, 3]
def baseStart_391089 : Nat := 118140960795 + 391089 * 2 ^ 59
def prefixEnd_391089 : Nat := 4983230072969 + 3 ^ 40 * 391089 * 2
def baseEnd_391089 : Nat := 200816635686325596188921

theorem tailTrace_391089 : CollatzResearch.WordTrace tailWord_391089 prefixEnd_391089 200816635686325596188921 := by
  unfold tailWord_391089
  simp only [CollatzResearch.WordTrace]
  refine ⟨14264187680158820528672321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9509458453439213685781547 14264187680158820528672321)
  ·
    refine ⟨10698140760119115396504241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14264187680158820528672321 10698140760119115396504241)
    ·
      refine ⟨8023605570089336547378181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10698140760119115396504241 8023605570089336547378181)
      ·
        refine ⟨1504426044391750602633409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8023605570089336547378181 1504426044391750602633409)
        ·
          refine ⟨1128319533293812951975057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1504426044391750602633409 1128319533293812951975057)
          ·
            refine ⟨846239649970359713981293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1128319533293812951975057 846239649970359713981293)
            ·
              refine ⟨317339868738884892742985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 846239649970359713981293 317339868738884892742985)
              ·
                refine ⟨238004901554163669557239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 317339868738884892742985 238004901554163669557239)
                ·
                  refine ⟨357007352331245504335859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 238004901554163669557239 357007352331245504335859)
                  ·
                    refine ⟨535511028496868256503789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 357007352331245504335859 535511028496868256503789)
                    ·
                      refine ⟨200816635686325596188921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 535511028496868256503789 200816635686325596188921)
                      ·
                        rfl

theorem cell23_391089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 3, 2, 1, 1, 3].length) (baseStart_391089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_391089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_391089 prefixEnd_391089 := by exact prefixLift 391089
  have htrace : WordTrace (prefixWord ++ tailWord_391089) baseStart_391089 baseEnd_391089 := by
    simpa [prefixWord, tailWord_391089, baseEnd_391089] using wordTrace_append hprefix tailTrace_391089
  have hstable : (prefixWord ++ tailWord_391089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391089).length < 2 ^ (prefixWord ++ tailWord_391089).sum := by decide
  have hdescent : baseEnd_391089 < baseStart_391089 := by decide
  rcases family_descends (prefixWord ++ tailWord_391089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391101 : List Nat := [1, 4, 1, 2, 3, 1, 1, 10]
def baseStart_391101 : Nat := 118140960795 + 391101 * 2 ^ 59
def prefixEnd_391101 : Nat := 4983230072969 + 3 ^ 40 * 391101 * 2
def baseEnd_391101 : Nat := 7437881387191835156995

theorem tailTrace_391101 : CollatzResearch.WordTrace tailWord_391101 prefixEnd_391101 7437881387191835156995 := by
  unfold tailWord_391101
  simp only [CollatzResearch.WordTrace]
  refine ⟨14264625356115346578109157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9509750237410231052072771 14264625356115346578109157)
  ·
    refine ⟨2674617254271627483395467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14264625356115346578109157 2674617254271627483395467)
    ·
      refine ⟨4011925881407441225093201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2674617254271627483395467 4011925881407441225093201)
      ·
        refine ⟨3008944411055580918819901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4011925881407441225093201 3008944411055580918819901)
        ·
          refine ⟨1128354154145842844557463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3008944411055580918819901 1128354154145842844557463)
          ·
            refine ⟨1692531231218764266836195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1128354154145842844557463 1692531231218764266836195)
            ·
              refine ⟨2538796846828146400254293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1692531231218764266836195 2538796846828146400254293)
              ·
                refine ⟨7437881387191835156995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 2538796846828146400254293 7437881387191835156995)
                ·
                  rfl

theorem cell23_391101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 10].length) (baseStart_391101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_391101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_391101 prefixEnd_391101 := by exact prefixLift 391101
  have htrace : WordTrace (prefixWord ++ tailWord_391101) baseStart_391101 baseEnd_391101 := by
    simpa [prefixWord, tailWord_391101, baseEnd_391101] using wordTrace_append hprefix tailTrace_391101
  have hstable : (prefixWord ++ tailWord_391101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391101).length < 2 ^ (prefixWord ++ tailWord_391101).sum := by decide
  have hdescent : baseEnd_391101 < baseStart_391101 := by decide
  rcases family_descends (prefixWord ++ tailWord_391101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391128 : List Nat := [2, 1, 2, 2, 2, 2, 3, 2, 1, 3, 3]
def baseStart_391128 : Nat := 118140960795 + 391128 * 2 ^ 59
def prefixEnd_391128 : Nat := 4983230072969 + 3 ^ 40 * 391128 * 2
def baseEnd_391128 : Nat := 200836661431850943601241

theorem tailTrace_391128 : CollatzResearch.WordTrace tailWord_391128 prefixEnd_391128 200836661431850943601241 := by
  unfold tailWord_391128
  simp only [CollatzResearch.WordTrace]
  refine ⟨7132805063508765094671019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9510406751345020126228025 7132805063508765094671019)
  ·
    refine ⟨10699207595263147642006529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7132805063508765094671019 10699207595263147642006529)
    ·
      refine ⟨8024405696447360731504897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10699207595263147642006529 8024405696447360731504897)
      ·
        refine ⟨6018304272335520548628673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8024405696447360731504897 6018304272335520548628673)
        ·
          refine ⟨4513728204251640411471505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6018304272335520548628673 4513728204251640411471505)
          ·
            refine ⟨3385296153188730308603629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4513728204251640411471505 3385296153188730308603629)
            ·
              refine ⟨1269486057445773865726361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3385296153188730308603629 1269486057445773865726361)
              ·
                refine ⟨952114543084330399294771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1269486057445773865726361 952114543084330399294771)
                ·
                  refine ⟨1428171814626495598942157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 952114543084330399294771 1428171814626495598942157)
                  ·
                    refine ⟨535564430484935849603309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1428171814626495598942157 535564430484935849603309)
                    ·
                      refine ⟨200836661431850943601241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 535564430484935849603309 200836661431850943601241)
                      ·
                        rfl

theorem cell23_391128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 2, 1, 3, 3].length) (baseStart_391128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_391128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_391128 prefixEnd_391128 := by exact prefixLift 391128
  have htrace : WordTrace (prefixWord ++ tailWord_391128) baseStart_391128 baseEnd_391128 := by
    simpa [prefixWord, tailWord_391128, baseEnd_391128] using wordTrace_append hprefix tailTrace_391128
  have hstable : (prefixWord ++ tailWord_391128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391128).length < 2 ^ (prefixWord ++ tailWord_391128).sum := by decide
  have hdescent : baseEnd_391128 < baseStart_391128 := by decide
  rcases family_descends (prefixWord ++ tailWord_391128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391151 : List Nat := [1, 1, 2, 1, 4, 2, 1, 1, 1, 5, 4]
def baseStart_391151 : Nat := 118140960795 + 391151 * 2 ^ 59
def prefixEnd_391151 : Nat := 4983230072969 + 3 ^ 40 * 391151 * 2
def baseEnd_391151 : Nat := 200848471486904353613635

theorem tailTrace_391151 : CollatzResearch.WordTrace tailWord_391151 prefixEnd_391151 200848471486904353613635 := by
  unfold tailWord_391151
  simp only [CollatzResearch.WordTrace]
  refine ⟨14266449005934205117429307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9510966003956136744952871 14266449005934205117429307)
  ·
    refine ⟨21399673508901307676143961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14266449005934205117429307 21399673508901307676143961)
    ·
      refine ⟨16049755131675980757107971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21399673508901307676143961 16049755131675980757107971)
      ·
        refine ⟨24074632697513971135661957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16049755131675980757107971 24074632697513971135661957)
        ·
          refine ⟨4513993630783869587936617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24074632697513971135661957 4513993630783869587936617)
          ·
            refine ⟨3385495223087902190952463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4513993630783869587936617 3385495223087902190952463)
            ·
              refine ⟨5078242834631853286428695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3385495223087902190952463 5078242834631853286428695)
              ·
                refine ⟨7617364251947779929643043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5078242834631853286428695 7617364251947779929643043)
                ·
                  refine ⟨11426046377921669894464565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7617364251947779929643043 11426046377921669894464565)
                  ·
                    refine ⟨1071191847930156552606053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11426046377921669894464565 1071191847930156552606053)
                    ·
                      refine ⟨200848471486904353613635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1071191847930156552606053 200848471486904353613635)
                      ·
                        rfl

theorem cell23_391151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 5, 4].length) (baseStart_391151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_391151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_391151 prefixEnd_391151 := by exact prefixLift 391151
  have htrace : WordTrace (prefixWord ++ tailWord_391151) baseStart_391151 baseEnd_391151 := by
    simpa [prefixWord, tailWord_391151, baseEnd_391151] using wordTrace_append hprefix tailTrace_391151
  have hstable : (prefixWord ++ tailWord_391151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391151).length < 2 ^ (prefixWord ++ tailWord_391151).sum := by decide
  have hdescent : baseEnd_391151 < baseStart_391151 := by decide
  rcases family_descends (prefixWord ++ tailWord_391151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391161 : List Nat := [1, 2, 1, 3, 1, 4, 1, 1, 1, 8]
def baseStart_391161 : Nat := 118140960795 + 391161 * 2 ^ 59
def prefixEnd_391161 : Nat := 4983230072969 + 3 ^ 40 * 391161 * 2
def baseEnd_391161 : Nat := 66951202097816438162863

theorem tailTrace_391161 : CollatzResearch.WordTrace tailWord_391161 prefixEnd_391161 66951202097816438162863 := by
  unfold tailWord_391161
  simp only [CollatzResearch.WordTrace]
  refine ⟨14266813735897976825293337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9511209157265317883528891 14266813735897976825293337)
  ·
    refine ⟨10700110301923482618970003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14266813735897976825293337 10700110301923482618970003)
    ·
      refine ⟨16050165452885223928455005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10700110301923482618970003 16050165452885223928455005)
      ·
        refine ⟨6018812044831958973170627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16050165452885223928455005 6018812044831958973170627)
        ·
          refine ⟨9028218067247938459755941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6018812044831958973170627 9028218067247938459755941)
          ·
            refine ⟨1692790887608988461204239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9028218067247938459755941 1692790887608988461204239)
            ·
              refine ⟨2539186331413482691806359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1692790887608988461204239 2539186331413482691806359)
              ·
                refine ⟨3808779497120224037709539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2539186331413482691806359 3808779497120224037709539)
                ·
                  refine ⟨5713169245680336056564309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3808779497120224037709539 5713169245680336056564309)
                  ·
                    refine ⟨66951202097816438162863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 5713169245680336056564309 66951202097816438162863)
                    ·
                      rfl

theorem cell23_391161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 8].length) (baseStart_391161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_391161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_391161 prefixEnd_391161 := by exact prefixLift 391161
  have htrace : WordTrace (prefixWord ++ tailWord_391161) baseStart_391161 baseEnd_391161 := by
    simpa [prefixWord, tailWord_391161, baseEnd_391161] using wordTrace_append hprefix tailTrace_391161
  have hstable : (prefixWord ++ tailWord_391161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391161).length < 2 ^ (prefixWord ++ tailWord_391161).sum := by decide
  have hdescent : baseEnd_391161 < baseStart_391161 := by decide
  rcases family_descends (prefixWord ++ tailWord_391161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391171 : List Nat := [1, 1, 1, 3, 2, 1, 1, 3, 4, 1, 5]
def baseStart_391171 : Nat := 118140960795 + 391171 * 2 ^ 59
def prefixEnd_391171 : Nat := 4983230072969 + 3 ^ 40 * 391171 * 2
def baseEnd_391171 : Nat := 200858741099994275363543

theorem tailTrace_391171 : CollatzResearch.WordTrace tailWord_391171 prefixEnd_391171 200858741099994275363543 := by
  unfold tailWord_391171
  simp only [CollatzResearch.WordTrace]
  refine ⟨14267178465861748533157367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9511452310574499022104911 14267178465861748533157367)
  ·
    refine ⟨21400767698792622799736051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14267178465861748533157367 21400767698792622799736051)
    ·
      refine ⟨32101151548188934199604077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21400767698792622799736051 32101151548188934199604077)
      ·
        refine ⟨12037931830570850324851529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32101151548188934199604077 12037931830570850324851529)
        ·
          refine ⟨9028448872928137743638647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12037931830570850324851529 9028448872928137743638647)
          ·
            refine ⟨13542673309392206615457971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9028448872928137743638647 13542673309392206615457971)
            ·
              refine ⟨20314009964088309923186957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13542673309392206615457971 20314009964088309923186957)
              ·
                refine ⟨7617753736533116221195109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20314009964088309923186957 7617753736533116221195109)
                ·
                  refine ⟨1428328825599959291474083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7617753736533116221195109 1428328825599959291474083)
                  ·
                    refine ⟨2142493238399938937211125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1428328825599959291474083 2142493238399938937211125)
                    ·
                      refine ⟨200858741099994275363543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2142493238399938937211125 200858741099994275363543)
                      ·
                        rfl

theorem cell23_391171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 4, 1, 5].length) (baseStart_391171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_391171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_391171 prefixEnd_391171 := by exact prefixLift 391171
  have htrace : WordTrace (prefixWord ++ tailWord_391171) baseStart_391171 baseEnd_391171 := by
    simpa [prefixWord, tailWord_391171, baseEnd_391171] using wordTrace_append hprefix tailTrace_391171
  have hstable : (prefixWord ++ tailWord_391171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391171).length < 2 ^ (prefixWord ++ tailWord_391171).sum := by decide
  have hdescent : baseEnd_391171 < baseStart_391171 := by decide
  rcases family_descends (prefixWord ++ tailWord_391171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391202 : List Nat := [3, 3, 1, 1, 1, 2, 3, 1, 4, 2, 2]
def baseStart_391202 : Nat := 118140960795 + 391202 * 2 ^ 59
def prefixEnd_391202 : Nat := 4983230072969 + 3 ^ 40 * 391202 * 2
def baseEnd_391202 : Nat := 200874659000283654075901

theorem tailTrace_391202 : CollatzResearch.WordTrace tailWord_391202 prefixEnd_391202 200874659000283654075901 := by
  unfold tailWord_391202
  simp only [CollatzResearch.WordTrace]
  refine ⟨3567077282187360206883965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9512206085832960551690573 3567077282187360206883965)
  ·
    refine ⟨1337653980820260077581487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3567077282187360206883965 1337653980820260077581487)
    ·
      refine ⟨2006480971230390116372231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1337653980820260077581487 2006480971230390116372231)
      ·
        refine ⟨3009721456845585174558347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2006480971230390116372231 3009721456845585174558347)
        ·
          refine ⟨4514582185268377761837521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3009721456845585174558347 4514582185268377761837521)
          ·
            refine ⟨3385936638951283321378141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4514582185268377761837521 3385936638951283321378141)
            ·
              refine ⟨1269726239606731245516803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3385936638951283321378141 1269726239606731245516803)
              ·
                refine ⟨1904589359410096868275205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1269726239606731245516803 1904589359410096868275205)
                ·
                  refine ⟨357110504889393162801601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1904589359410096868275205 357110504889393162801601)
                  ·
                    refine ⟨267832878667044872101201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 357110504889393162801601 267832878667044872101201)
                    ·
                      refine ⟨200874659000283654075901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 267832878667044872101201 200874659000283654075901)
                      ·
                        rfl

theorem cell23_391202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 1, 4, 2, 2].length) (baseStart_391202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_391202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_391202 prefixEnd_391202 := by exact prefixLift 391202
  have htrace : WordTrace (prefixWord ++ tailWord_391202) baseStart_391202 baseEnd_391202 := by
    simpa [prefixWord, tailWord_391202, baseEnd_391202] using wordTrace_append hprefix tailTrace_391202
  have hstable : (prefixWord ++ tailWord_391202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391202).length < 2 ^ (prefixWord ++ tailWord_391202).sum := by decide
  have hdescent : baseEnd_391202 < baseStart_391202 := by decide
  rcases family_descends (prefixWord ++ tailWord_391202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391251 : List Nat := [1, 1, 1, 2, 1, 1, 2, 2, 4, 8]
def baseStart_391251 : Nat := 118140960795 + 391251 * 2 ^ 59
def prefixEnd_391251 : Nat := 4983230072969 + 3 ^ 40 * 391251 * 2
def baseEnd_391251 : Nat := 66966606517451320787725

theorem tailTrace_391251 : CollatzResearch.WordTrace tailWord_391251 prefixEnd_391251 66966606517451320787725 := by
  unfold tailWord_391251
  simp only [CollatzResearch.WordTrace]
  refine ⟨14270096305571922196069607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9513397537047948130713071 14270096305571922196069607)
  ·
    refine ⟨21405144458357883294104411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14270096305571922196069607 21405144458357883294104411)
    ·
      refine ⟨32107716687536824941156617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21405144458357883294104411 32107716687536824941156617)
      ·
        refine ⟨24080787515652618705867463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32107716687536824941156617 24080787515652618705867463)
        ·
          refine ⟨36121181273478928058801195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24080787515652618705867463 36121181273478928058801195)
          ·
            refine ⟨54181771910218392088201793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36121181273478928058801195 54181771910218392088201793)
            ·
              refine ⟨40636328932663794066151345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54181771910218392088201793 40636328932663794066151345)
              ·
                refine ⟨30477246699497845549613509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40636328932663794066151345 30477246699497845549613509)
                ·
                  refine ⟨5714483756155846040552533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30477246699497845549613509 5714483756155846040552533)
                  ·
                    refine ⟨66966606517451320787725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 5714483756155846040552533 66966606517451320787725)
                    ·
                      rfl

theorem cell23_391251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 8].length) (baseStart_391251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_391251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_391251 prefixEnd_391251 := by exact prefixLift 391251
  have htrace : WordTrace (prefixWord ++ tailWord_391251) baseStart_391251 baseEnd_391251 := by
    simpa [prefixWord, tailWord_391251, baseEnd_391251] using wordTrace_append hprefix tailTrace_391251
  have hstable : (prefixWord ++ tailWord_391251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391251).length < 2 ^ (prefixWord ++ tailWord_391251).sum := by decide
  have hdescent : baseEnd_391251 < baseStart_391251 := by decide
  rcases family_descends (prefixWord ++ tailWord_391251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391319 : List Nat := [1, 1, 3, 3, 4, 1, 1, 4, 1, 4]
def baseStart_391319 : Nat := 118140960795 + 391319 * 2 ^ 59
def prefixEnd_391319 : Nat := 4983230072969 + 3 ^ 40 * 391319 * 2
def baseEnd_391319 : Nat := 66978245412286565437621

theorem tailTrace_391319 : CollatzResearch.WordTrace tailWord_391319 prefixEnd_391319 66978245412286565437621 := by
  unfold tailWord_391319
  simp only [CollatzResearch.WordTrace]
  refine ⟨14272576469325569809545011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9515050979550379873030007 14272576469325569809545011)
  ·
    refine ⟨21408864703988354714317517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14272576469325569809545011 21408864703988354714317517)
    ·
      refine ⟨8028324263995633017869069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21408864703988354714317517 8028324263995633017869069)
      ·
        refine ⟨3010621598998362381700901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8028324263995633017869069 3010621598998362381700901)
        ·
          refine ⟨564491549812192946568919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3010621598998362381700901 564491549812192946568919)
          ·
            refine ⟨846737324718289419853379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 564491549812192946568919 846737324718289419853379)
            ·
              refine ⟨1270105987077434129780069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 846737324718289419853379 1270105987077434129780069)
              ·
                refine ⟨238144872577018899333763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1270105987077434129780069 238144872577018899333763)
                ·
                  refine ⟨357217308865528349000645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 238144872577018899333763 357217308865528349000645)
                  ·
                    refine ⟨66978245412286565437621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 357217308865528349000645 66978245412286565437621)
                    ·
                      rfl

theorem cell23_391319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 4, 1, 4].length) (baseStart_391319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_391319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_391319 prefixEnd_391319 := by exact prefixLift 391319
  have htrace : WordTrace (prefixWord ++ tailWord_391319) baseStart_391319 baseEnd_391319 := by
    simpa [prefixWord, tailWord_391319, baseEnd_391319] using wordTrace_append hprefix tailTrace_391319
  have hstable : (prefixWord ++ tailWord_391319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391319).length < 2 ^ (prefixWord ++ tailWord_391319).sum := by decide
  have hdescent : baseEnd_391319 < baseStart_391319 := by decide
  rcases family_descends (prefixWord ++ tailWord_391319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391375 : List Nat := [1, 1, 2, 1, 1, 3, 5, 1, 4, 4]
def baseStart_391375 : Nat := 118140960795 + 391375 * 2 ^ 59
def prefixEnd_391375 : Nat := 4983230072969 + 3 ^ 40 * 391375 * 2
def baseEnd_391375 : Nat := 66987830384503825737535

theorem tailTrace_391375 : CollatzResearch.WordTrace tailWord_391375 prefixEnd_391375 66987830384503825737535 := by
  unfold tailWord_391375
  simp only [CollatzResearch.WordTrace]
  refine ⟨14274618957122691373583579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9516412638081794249055719 14274618957122691373583579)
  ·
    refine ⟨21411928435684037060375369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14274618957122691373583579 21411928435684037060375369)
    ·
      refine ⟨16058946326763027795281527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21411928435684037060375369 16058946326763027795281527)
      ·
        refine ⟨24088419490144541692922291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16058946326763027795281527 24088419490144541692922291)
        ·
          refine ⟨36132629235216812539383437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24088419490144541692922291 36132629235216812539383437)
          ·
            refine ⟨13549735963206304702268789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36132629235216812539383437 13549735963206304702268789)
            ·
              refine ⟨1270287746550591065837699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13549735963206304702268789 1270287746550591065837699)
              ·
                refine ⟨1905431619825886598756549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1270287746550591065837699 1905431619825886598756549)
                ·
                  refine ⟨357268428717353737266853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1905431619825886598756549 357268428717353737266853)
                  ·
                    refine ⟨66987830384503825737535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 357268428717353737266853 66987830384503825737535)
                    ·
                      rfl

theorem cell23_391375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 1, 4, 4].length) (baseStart_391375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_391375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_391375 prefixEnd_391375 := by exact prefixLift 391375
  have htrace : WordTrace (prefixWord ++ tailWord_391375) baseStart_391375 baseEnd_391375 := by
    simpa [prefixWord, tailWord_391375, baseEnd_391375] using wordTrace_append hprefix tailTrace_391375
  have hstable : (prefixWord ++ tailWord_391375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391375).length < 2 ^ (prefixWord ++ tailWord_391375).sum := by decide
  have hdescent : baseEnd_391375 < baseStart_391375 := by decide
  rcases family_descends (prefixWord ++ tailWord_391375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391385 : List Nat := [1, 2, 1, 2, 3, 1, 2, 1, 5, 2, 3]
def baseStart_391385 : Nat := 118140960795 + 391385 * 2 ^ 59
def prefixEnd_391385 : Nat := 4983230072969 + 3 ^ 40 * 391385 * 2
def baseEnd_391385 : Nat := 200968625960056438087559

theorem tailTrace_391385 : CollatzResearch.WordTrace tailWord_391385 prefixEnd_391385 200968625960056438087559 := by
  unfold tailWord_391385
  simp only [CollatzResearch.WordTrace]
  refine ⟨14274983687086463081447609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9516655791390975387631739 14274983687086463081447609)
  ·
    refine ⟨10706237765314847311085707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14274983687086463081447609 10706237765314847311085707)
    ·
      refine ⟨16059356647972270966628561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10706237765314847311085707 16059356647972270966628561)
      ·
        refine ⟨12044517485979203224971421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16059356647972270966628561 12044517485979203224971421)
        ·
          refine ⟨4516694057242201209364283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12044517485979203224971421 4516694057242201209364283)
          ·
            refine ⟨6775041085863301814046425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4516694057242201209364283 6775041085863301814046425)
            ·
              refine ⟨5081280814397476360534819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6775041085863301814046425 5081280814397476360534819)
              ·
                refine ⟨7621921221596214540802229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5081280814397476360534819 7621921221596214540802229)
                ·
                  refine ⟨714555114524645113200209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7621921221596214540802229 714555114524645113200209)
                  ·
                    refine ⟨535916335893483834900157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 714555114524645113200209 535916335893483834900157)
                    ·
                      refine ⟨200968625960056438087559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 535916335893483834900157 200968625960056438087559)
                      ·
                        rfl

theorem cell23_391385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 5, 2, 3].length) (baseStart_391385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_391385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_391385 prefixEnd_391385 := by exact prefixLift 391385
  have htrace : WordTrace (prefixWord ++ tailWord_391385) baseStart_391385 baseEnd_391385 := by
    simpa [prefixWord, tailWord_391385, baseEnd_391385] using wordTrace_append hprefix tailTrace_391385
  have hstable : (prefixWord ++ tailWord_391385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391385).length < 2 ^ (prefixWord ++ tailWord_391385).sum := by decide
  have hdescent : baseEnd_391385 < baseStart_391385 := by decide
  rcases family_descends (prefixWord ++ tailWord_391385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391399 : List Nat := [1, 1, 5, 3, 1, 2, 2, 2, 1, 1, 4]
def baseStart_391399 : Nat := 118140960795 + 391399 * 2 ^ 59
def prefixEnd_391399 : Nat := 4983230072969 + 3 ^ 40 * 391399 * 2
def baseEnd_391399 : Nat := 200975814689219383312495

theorem tailTrace_391399 : CollatzResearch.WordTrace tailWord_391399 prefixEnd_391399 200975814689219383312495 := by
  unfold tailWord_391399
  simp only [CollatzResearch.WordTrace]
  refine ⟨14275494309035743472457251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9516996206023828981638167 14275494309035743472457251)
  ·
    refine ⟨21413241463553615208685877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14275494309035743472457251 21413241463553615208685877)
    ·
      refine ⟨2007491387208151425814301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21413241463553615208685877 2007491387208151425814301)
      ·
        refine ⟨752809270203056784680363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2007491387208151425814301 752809270203056784680363)
        ·
          refine ⟨1129213905304585177020545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 752809270203056784680363 1129213905304585177020545)
          ·
            refine ⟨846910428978438882765409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1129213905304585177020545 846910428978438882765409)
            ·
              refine ⟨635182821733829162074057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 846910428978438882765409 635182821733829162074057)
              ·
                refine ⟨476387116300371871555543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 635182821733829162074057 476387116300371871555543)
                ·
                  refine ⟨714580674450557807333315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 476387116300371871555543 714580674450557807333315)
                  ·
                    refine ⟨1071871011675836710999973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 714580674450557807333315 1071871011675836710999973)
                    ·
                      refine ⟨200975814689219383312495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1071871011675836710999973 200975814689219383312495)
                      ·
                        rfl

theorem cell23_391399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_391399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_391399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_391399 prefixEnd_391399 := by exact prefixLift 391399
  have htrace : WordTrace (prefixWord ++ tailWord_391399) baseStart_391399 baseEnd_391399 := by
    simpa [prefixWord, tailWord_391399, baseEnd_391399] using wordTrace_append hprefix tailTrace_391399
  have hstable : (prefixWord ++ tailWord_391399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391399).length < 2 ^ (prefixWord ++ tailWord_391399).sum := by decide
  have hdescent : baseEnd_391399 < baseStart_391399 := by decide
  rcases family_descends (prefixWord ++ tailWord_391399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391408 : List Nat := [2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 6]
def baseStart_391408 : Nat := 118140960795 + 391408 * 2 ^ 59
def prefixEnd_391408 : Nat := 4983230072969 + 3 ^ 40 * 391408 * 2
def baseEnd_391408 : Nat := 200980436015109848099953

theorem tailTrace_391408 : CollatzResearch.WordTrace tailWord_391408 prefixEnd_391408 200980436015109848099953 := by
  unfold tailWord_391408
  simp only [CollatzResearch.WordTrace]
  refine ⟨7137911283001569004767439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9517215044002092006356585 7137911283001569004767439)
  ·
    refine ⟨10706866924502353507151159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7137911283001569004767439 10706866924502353507151159)
    ·
      refine ⟨16060300386753530260726739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10706866924502353507151159 16060300386753530260726739)
      ·
        refine ⟨24090450580130295391090109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16060300386753530260726739 24090450580130295391090109)
        ·
          refine ⟨9033918967548860771658791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24090450580130295391090109 9033918967548860771658791)
          ·
            refine ⟨13550878451323291157488187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9033918967548860771658791 13550878451323291157488187)
            ·
              refine ⟨20326317676984936736232281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13550878451323291157488187 20326317676984936736232281)
              ·
                refine ⟨15244738257738702552174211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20326317676984936736232281 15244738257738702552174211)
                ·
                  refine ⟨22867107386608053828261317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15244738257738702552174211 22867107386608053828261317)
                  ·
                    refine ⟨4287582634989010092798997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22867107386608053828261317 4287582634989010092798997)
                    ·
                      refine ⟨200980436015109848099953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4287582634989010092798997 200980436015109848099953)
                      ·
                        rfl

theorem cell23_391408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 6].length) (baseStart_391408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_391408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_391408 prefixEnd_391408 := by exact prefixLift 391408
  have htrace : WordTrace (prefixWord ++ tailWord_391408) baseStart_391408 baseEnd_391408 := by
    simpa [prefixWord, tailWord_391408, baseEnd_391408] using wordTrace_append hprefix tailTrace_391408
  have hstable : (prefixWord ++ tailWord_391408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391408).length < 2 ^ (prefixWord ++ tailWord_391408).sum := by decide
  have hdescent : baseEnd_391408 < baseStart_391408 := by decide
  rcases family_descends (prefixWord ++ tailWord_391408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391433 : List Nat := [1, 2, 1, 1, 3, 5, 3, 2, 1, 2, 2]
def baseStart_391433 : Nat := 118140960795 + 391433 * 2 ^ 59
def prefixEnd_391433 : Nat := 4983230072969 + 3 ^ 40 * 391433 * 2
def baseEnd_391433 : Nat := 200993273031472250287339

theorem tailTrace_391433 : CollatzResearch.WordTrace tailWord_391433 prefixEnd_391433 200993273031472250287339 := by
  unfold tailWord_391433
  simp only [CollatzResearch.WordTrace]
  refine ⟨14276734390912567279194953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9517822927275044852796635 14276734390912567279194953)
  ·
    refine ⟨10707550793184425459396215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14276734390912567279194953 10707550793184425459396215)
    ·
      refine ⟨16061326189776638189094323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10707550793184425459396215 16061326189776638189094323)
      ·
        refine ⟨24091989284664957283641485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16061326189776638189094323 24091989284664957283641485)
        ·
          refine ⟨9034495981749358981365557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24091989284664957283641485 9034495981749358981365557)
          ·
            refine ⟨846983998289002404503021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9034495981749358981365557 846983998289002404503021)
            ·
              refine ⟨317618999358375901688633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 846983998289002404503021 317618999358375901688633)
              ·
                refine ⟨238214249518781926266475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 317618999358375901688633 238214249518781926266475)
                ·
                  refine ⟨357321374278172889399713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 238214249518781926266475 357321374278172889399713)
                  ·
                    refine ⟨267991030708629667049785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 357321374278172889399713 267991030708629667049785)
                    ·
                      refine ⟨200993273031472250287339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 267991030708629667049785 200993273031472250287339)
                      ·
                        rfl

theorem cell23_391433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 3, 2, 1, 2, 2].length) (baseStart_391433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_391433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_391433 prefixEnd_391433 := by exact prefixLift 391433
  have htrace : WordTrace (prefixWord ++ tailWord_391433) baseStart_391433 baseEnd_391433 := by
    simpa [prefixWord, tailWord_391433, baseEnd_391433] using wordTrace_append hprefix tailTrace_391433
  have hstable : (prefixWord ++ tailWord_391433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391433).length < 2 ^ (prefixWord ++ tailWord_391433).sum := by decide
  have hdescent : baseEnd_391433 < baseStart_391433 := by decide
  rcases family_descends (prefixWord ++ tailWord_391433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391453 : List Nat := [1, 4, 2, 3, 3, 1, 1, 2, 1, 2, 3]
def baseStart_391453 : Nat := 118140960795 + 391453 * 2 ^ 59
def prefixEnd_391453 : Nat := 4983230072969 + 3 ^ 40 * 391453 * 2
def baseEnd_391453 : Nat := 201003542644562172037247

theorem tailTrace_391453 : CollatzResearch.WordTrace tailWord_391453 prefixEnd_391453 201003542644562172037247 := by
  unfold tailWord_391453
  simp only [CollatzResearch.WordTrace]
  refine ⟨14277463850840110694923013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9518309233893407129948675 14277463850840110694923013)
  ·
    refine ⟨2677024472032520755298065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14277463850840110694923013 2677024472032520755298065)
    ·
      refine ⟨2007768354024390566473549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2677024472032520755298065 2007768354024390566473549)
      ·
        refine ⟨752913132759146462427581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2007768354024390566473549 752913132759146462427581)
        ·
          refine ⟨282342424784679923410343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 752913132759146462427581 282342424784679923410343)
          ·
            refine ⟨423513637177019885115515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 282342424784679923410343 423513637177019885115515)
            ·
              refine ⟨635270455765529827673273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 423513637177019885115515 635270455765529827673273)
              ·
                refine ⟨476452841824147370754955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 635270455765529827673273 476452841824147370754955)
                ·
                  refine ⟨714679262736221056132433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 476452841824147370754955 714679262736221056132433)
                  ·
                    refine ⟨536009447052165792099325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 714679262736221056132433 536009447052165792099325)
                    ·
                      refine ⟨201003542644562172037247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 536009447052165792099325 201003542644562172037247)
                      ·
                        rfl

theorem cell23_391453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_391453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_391453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_391453 prefixEnd_391453 := by exact prefixLift 391453
  have htrace : WordTrace (prefixWord ++ tailWord_391453) baseStart_391453 baseEnd_391453 := by
    simpa [prefixWord, tailWord_391453, baseEnd_391453] using wordTrace_append hprefix tailTrace_391453
  have hstable : (prefixWord ++ tailWord_391453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391453).length < 2 ^ (prefixWord ++ tailWord_391453).sum := by decide
  have hdescent : baseEnd_391453 < baseStart_391453 := by decide
  rcases family_descends (prefixWord ++ tailWord_391453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391475 : List Nat := [1, 1, 1, 2, 5, 1, 1, 3, 2, 1, 5]
def baseStart_391475 : Nat := 118140960795 + 391475 * 2 ^ 59
def prefixEnd_391475 : Nat := 4983230072969 + 3 ^ 40 * 391475 * 2
def baseEnd_391475 : Nat := 201014839218961085962145

theorem tailTrace_391475 : CollatzResearch.WordTrace tailWord_391475 prefixEnd_391475 201014839218961085962145 := by
  unfold tailWord_391475
  simp only [CollatzResearch.WordTrace]
  refine ⟨14278266256760408452223879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9518844171173605634815919 14278266256760408452223879)
  ·
    refine ⟨21417399385140612678335819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14278266256760408452223879 21417399385140612678335819)
    ·
      refine ⟨32126099077710919017503729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21417399385140612678335819 32126099077710919017503729)
      ·
        refine ⟨24094574308283189263127797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32126099077710919017503729 24094574308283189263127797)
        ·
          refine ⟨2258866341401548993418231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24094574308283189263127797 2258866341401548993418231)
          ·
            refine ⟨3388299512102323490127347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2258866341401548993418231 3388299512102323490127347)
            ·
              refine ⟨5082449268153485235191021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3388299512102323490127347 5082449268153485235191021)
              ·
                refine ⟨1905918475557556963196633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5082449268153485235191021 1905918475557556963196633)
                ·
                  refine ⟨1429438856668167722397475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1905918475557556963196633 1429438856668167722397475)
                  ·
                    refine ⟨2144158285002251583596213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1429438856668167722397475 2144158285002251583596213)
                    ·
                      refine ⟨201014839218961085962145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2144158285002251583596213 201014839218961085962145)
                      ·
                        rfl

theorem cell23_391475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 3, 2, 1, 5].length) (baseStart_391475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_391475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_391475 prefixEnd_391475 := by exact prefixLift 391475
  have htrace : WordTrace (prefixWord ++ tailWord_391475) baseStart_391475 baseEnd_391475 := by
    simpa [prefixWord, tailWord_391475, baseEnd_391475] using wordTrace_append hprefix tailTrace_391475
  have hstable : (prefixWord ++ tailWord_391475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391475).length < 2 ^ (prefixWord ++ tailWord_391475).sum := by decide
  have hdescent : baseEnd_391475 < baseStart_391475 := by decide
  rcases family_descends (prefixWord ++ tailWord_391475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391495 : List Nat := [1, 1, 4, 1, 2, 2, 2, 3, 7]
def baseStart_391495 : Nat := 118140960795 + 391495 * 2 ^ 59
def prefixEnd_391495 : Nat := 4983230072969 + 3 ^ 40 * 391495 * 2
def baseEnd_391495 : Nat := 22336123203561223079117

theorem tailTrace_391495 : CollatzResearch.WordTrace tailWord_391495 prefixEnd_391495 22336123203561223079117 := by
  unfold tailWord_391495
  simp only [CollatzResearch.WordTrace]
  refine ⟨14278995716687951867951939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9519330477791967911967959 14278995716687951867951939)
  ·
    refine ⟨21418493575031927801927909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14278995716687951867951939 21418493575031927801927909)
    ·
      refine ⟨4015967545318486462861483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21418493575031927801927909 4015967545318486462861483)
      ·
        refine ⟨6023951317977729694292225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4015967545318486462861483 6023951317977729694292225)
        ·
          refine ⟨4517963488483297270719169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6023951317977729694292225 4517963488483297270719169)
          ·
            refine ⟨3388472616362472953039377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4517963488483297270719169 3388472616362472953039377)
            ·
              refine ⟨2541354462271854714779533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3388472616362472953039377 2541354462271854714779533)
              ·
                refine ⟨953007923351945518042325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2541354462271854714779533 953007923351945518042325)
                ·
                  refine ⟨22336123203561223079117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 953007923351945518042325 22336123203561223079117)
                  ·
                    rfl

theorem cell23_391495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 3, 7].length) (baseStart_391495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_391495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_391495 prefixEnd_391495 := by exact prefixLift 391495
  have htrace : WordTrace (prefixWord ++ tailWord_391495) baseStart_391495 baseEnd_391495 := by
    simpa [prefixWord, tailWord_391495, baseEnd_391495] using wordTrace_append hprefix tailTrace_391495
  have hstable : (prefixWord ++ tailWord_391495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391495).length < 2 ^ (prefixWord ++ tailWord_391495).sum := by decide
  have hdescent : baseEnd_391495 < baseStart_391495 := by decide
  rcases family_descends (prefixWord ++ tailWord_391495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391506 : List Nat := [3, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2]
def baseStart_391506 : Nat := 118140960795 + 391506 * 2 ^ 59
def prefixEnd_391506 : Nat := 4983230072969 + 3 ^ 40 * 391506 * 2
def baseEnd_391506 : Nat := 201030757119250464674503

theorem tailTrace_391506 : CollatzResearch.WordTrace tailWord_391506 prefixEnd_391506 201030757119250464674503 := by
  unfold tailWord_391506
  simp only [CollatzResearch.WordTrace]
  refine ⟨3569849229912025186650593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9519597946432067164401581 3569849229912025186650593)
  ·
    refine ⟨2677386922434018889987945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3569849229912025186650593 2677386922434018889987945)
    ·
      refine ⟨2008040191825514167490959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2677386922434018889987945 2008040191825514167490959)
      ·
        refine ⟨3012060287738271251236439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2008040191825514167490959 3012060287738271251236439)
        ·
          refine ⟨4518090431607406876854659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3012060287738271251236439 4518090431607406876854659)
          ·
            refine ⟨6777135647411110315281989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4518090431607406876854659 6777135647411110315281989)
            ·
              refine ⟨1270712933889583184115373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6777135647411110315281989 1270712933889583184115373)
              ·
                refine ⟨476517350208593694043265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1270712933889583184115373 476517350208593694043265)
                ·
                  refine ⟨357388012656445270532449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 476517350208593694043265 357388012656445270532449)
                  ·
                    refine ⟨268041009492333952899337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 357388012656445270532449 268041009492333952899337)
                    ·
                      refine ⟨201030757119250464674503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 268041009492333952899337 201030757119250464674503)
                      ·
                        rfl

theorem cell23_391506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2].length) (baseStart_391506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_391506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_391506 prefixEnd_391506 := by exact prefixLift 391506
  have htrace : WordTrace (prefixWord ++ tailWord_391506) baseStart_391506 baseEnd_391506 := by
    simpa [prefixWord, tailWord_391506, baseEnd_391506] using wordTrace_append hprefix tailTrace_391506
  have hstable : (prefixWord ++ tailWord_391506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391506).length < 2 ^ (prefixWord ++ tailWord_391506).sum := by decide
  have hdescent : baseEnd_391506 < baseStart_391506 := by decide
  rcases family_descends (prefixWord ++ tailWord_391506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391535 : List Nat := [1, 1, 2, 1, 3, 1, 2, 4, 1, 2, 5]
def baseStart_391535 : Nat := 118140960795 + 391535 * 2 ^ 59
def prefixEnd_391535 : Nat := 4983230072969 + 3 ^ 40 * 391535 * 2
def baseEnd_391535 : Nat := 201045648058230851211869

theorem tailTrace_391535 : CollatzResearch.WordTrace tailWord_391535 prefixEnd_391535 201045648058230851211869 := by
  unfold tailWord_391535
  simp only [CollatzResearch.WordTrace]
  refine ⟨14280454636543038699408059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9520303091028692466272039 14280454636543038699408059)
  ·
    refine ⟨21420681954814558049112089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14280454636543038699408059 21420681954814558049112089)
    ·
      refine ⟨16065511466110918536834067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21420681954814558049112089 16065511466110918536834067)
      ·
        refine ⟨24098267199166377805251101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16065511466110918536834067 24098267199166377805251101)
        ·
          refine ⟨9036850199687391676969163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24098267199166377805251101 9036850199687391676969163)
          ·
            refine ⟨13555275299531087515453745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9036850199687391676969163 13555275299531087515453745)
            ·
              refine ⟨10166456474648315636590309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13555275299531087515453745 10166456474648315636590309)
              ·
                refine ⟨1906210588996559181860683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10166456474648315636590309 1906210588996559181860683)
                ·
                  refine ⟨2859315883494838772791025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1906210588996559181860683 2859315883494838772791025)
                  ·
                    refine ⟨2144486912621129079593269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2859315883494838772791025 2144486912621129079593269)
                    ·
                      refine ⟨201045648058230851211869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2144486912621129079593269 201045648058230851211869)
                      ·
                        rfl

theorem cell23_391535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 4, 1, 2, 5].length) (baseStart_391535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_391535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_391535 prefixEnd_391535 := by exact prefixLift 391535
  have htrace : WordTrace (prefixWord ++ tailWord_391535) baseStart_391535 baseEnd_391535 := by
    simpa [prefixWord, tailWord_391535, baseEnd_391535] using wordTrace_append hprefix tailTrace_391535
  have hstable : (prefixWord ++ tailWord_391535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391535).length < 2 ^ (prefixWord ++ tailWord_391535).sum := by decide
  have hdescent : baseEnd_391535 < baseStart_391535 := by decide
  rcases family_descends (prefixWord ++ tailWord_391535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391602 : List Nat := [3, 2, 1, 1, 1, 1, 4, 4, 6]
def baseStart_391602 : Nat := 118140960795 + 391602 * 2 ^ 59
def prefixEnd_391602 : Nat := 4983230072969 + 3 ^ 40 * 391602 * 2
def baseEnd_391602 : Nat := 22342227918009121008229

theorem tailTrace_391602 : CollatzResearch.WordTrace tailWord_391602 prefixEnd_391602 22342227918009121008229 := by
  unfold tailWord_391602
  simp only [CollatzResearch.WordTrace]
  refine ⟨3570724581825077285524265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9521932218200206094731373 3570724581825077285524265)
  ·
    refine ⟨2678043436368807964143199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3570724581825077285524265 2678043436368807964143199)
    ·
      refine ⟨4017065154553211946214799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2678043436368807964143199 4017065154553211946214799)
      ·
        refine ⟨6025597731829817919322199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4017065154553211946214799 6025597731829817919322199)
        ·
          refine ⟨9038396597744726878983299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6025597731829817919322199 9038396597744726878983299)
          ·
            refine ⟨13557594896617090318474949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9038396597744726878983299 13557594896617090318474949)
            ·
              refine ⟨2542049043115704434714053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13557594896617090318474949 2542049043115704434714053)
              ·
                refine ⟨476634195584194581508885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2542049043115704434714053 476634195584194581508885)
                ·
                  refine ⟨22342227918009121008229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 476634195584194581508885 22342227918009121008229)
                  ·
                    rfl

theorem cell23_391602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 4, 6].length) (baseStart_391602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_391602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_391602 prefixEnd_391602 := by exact prefixLift 391602
  have htrace : WordTrace (prefixWord ++ tailWord_391602) baseStart_391602 baseEnd_391602 := by
    simpa [prefixWord, tailWord_391602, baseEnd_391602] using wordTrace_append hprefix tailTrace_391602
  have hstable : (prefixWord ++ tailWord_391602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391602).length < 2 ^ (prefixWord ++ tailWord_391602).sum := by decide
  have hdescent : baseEnd_391602 < baseStart_391602 := by decide
  rcases family_descends (prefixWord ++ tailWord_391602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391615 : List Nat := [1, 1, 2, 2, 2, 1, 1, 1, 1, 11]
def baseStart_391615 : Nat := 118140960795 + 391615 * 2 ^ 59
def prefixEnd_391615 : Nat := 4983230072969 + 3 ^ 40 * 391615 * 2
def baseEnd_391615 : Nat := 67028908836863512737167

theorem tailTrace_391615 : CollatzResearch.WordTrace tailWord_391615 prefixEnd_391615 67028908836863512737167 := by
  unfold tailWord_391615
  simp only [CollatzResearch.WordTrace]
  refine ⟨14283372476253212362320299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9522248317502141574880199 14283372476253212362320299)
  ·
    refine ⟨21425058714379818543480449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14283372476253212362320299 21425058714379818543480449)
    ·
      refine ⟨16068794035784863907610337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21425058714379818543480449 16068794035784863907610337)
      ·
        refine ⟨12051595526838647930707753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16068794035784863907610337 12051595526838647930707753)
        ·
          refine ⟨9038696645128985948030815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12051595526838647930707753 9038696645128985948030815)
          ·
            refine ⟨13558044967693478922046223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9038696645128985948030815 13558044967693478922046223)
            ·
              refine ⟨20337067451540218383069335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13558044967693478922046223 20337067451540218383069335)
              ·
                refine ⟨30505601177310327574604003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20337067451540218383069335 30505601177310327574604003)
                ·
                  refine ⟨45758401765965491361906005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30505601177310327574604003 45758401765965491361906005)
                  ·
                    refine ⟨67028908836863512737167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 45758401765965491361906005 67028908836863512737167)
                    ·
                      rfl

theorem cell23_391615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 11].length) (baseStart_391615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_391615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_391615 prefixEnd_391615 := by exact prefixLift 391615
  have htrace : WordTrace (prefixWord ++ tailWord_391615) baseStart_391615 baseEnd_391615 := by
    simpa [prefixWord, tailWord_391615, baseEnd_391615] using wordTrace_append hprefix tailTrace_391615
  have hstable : (prefixWord ++ tailWord_391615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391615).length < 2 ^ (prefixWord ++ tailWord_391615).sum := by decide
  have hdescent : baseEnd_391615 < baseStart_391615 := by decide
  rcases family_descends (prefixWord ++ tailWord_391615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391656 : List Nat := [2, 1, 4, 1, 1, 3, 2, 2, 2, 3, 2]
def baseStart_391656 : Nat := 118140960795 + 391656 * 2 ^ 59
def prefixEnd_391656 : Nat := 4983230072969 + 3 ^ 40 * 391656 * 2
def baseEnd_391656 : Nat := 201107779217424877798813

theorem tailTrace_391656 : CollatzResearch.WordTrace tailWord_391656 prefixEnd_391656 201107779217424877798813 := by
  unfold tailWord_391656
  simp only [CollatzResearch.WordTrace]
  refine ⟨7142433934552338182281411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9523245246069784243041881 7142433934552338182281411)
  ·
    refine ⟨10713650901828507273422117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7142433934552338182281411 10713650901828507273422117)
    ·
      refine ⟨2008809544092845113766647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10713650901828507273422117 2008809544092845113766647)
      ·
        refine ⟨3013214316139267670649971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2008809544092845113766647 3013214316139267670649971)
        ·
          refine ⟨4519821474208901505974957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3013214316139267670649971 4519821474208901505974957)
          ·
            refine ⟨1694933052828338064740609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4519821474208901505974957 1694933052828338064740609)
            ·
              refine ⟨1271199789621253548555457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1694933052828338064740609 1271199789621253548555457)
              ·
                refine ⟨953399842215940161416593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1271199789621253548555457 953399842215940161416593)
                ·
                  refine ⟨715049881661955121062445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 953399842215940161416593 715049881661955121062445)
                  ·
                    refine ⟨268143705623233170398417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 715049881661955121062445 268143705623233170398417)
                    ·
                      refine ⟨201107779217424877798813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 268143705623233170398417 201107779217424877798813)
                      ·
                        rfl

theorem cell23_391656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 2, 2, 3, 2].length) (baseStart_391656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_391656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_391656 prefixEnd_391656 := by exact prefixLift 391656
  have htrace : WordTrace (prefixWord ++ tailWord_391656) baseStart_391656 baseEnd_391656 := by
    simpa [prefixWord, tailWord_391656, baseEnd_391656] using wordTrace_append hprefix tailTrace_391656
  have hstable : (prefixWord ++ tailWord_391656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391656).length < 2 ^ (prefixWord ++ tailWord_391656).sum := by decide
  have hdescent : baseEnd_391656 < baseStart_391656 := by decide
  rcases family_descends (prefixWord ++ tailWord_391656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391672 : List Nat := [2, 1, 2, 1, 1, 4, 2, 1, 3, 1, 5]
def baseStart_391672 : Nat := 118140960795 + 391672 * 2 ^ 59
def prefixEnd_391672 : Nat := 4983230072969 + 3 ^ 40 * 391672 * 2
def baseEnd_391672 : Nat := 201115994907896815198739

theorem tailTrace_391672 : CollatzResearch.WordTrace tailWord_391672 prefixEnd_391672 201115994907896815198739 := by
  unfold tailWord_391672
  simp only [CollatzResearch.WordTrace]
  refine ⟨7142725718523355548572635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9523634291364474064763513 7142725718523355548572635)
  ·
    refine ⟨10714088577785033322858953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7142725718523355548572635 10714088577785033322858953)
    ·
      refine ⟨8035566433338774992144215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10714088577785033322858953 8035566433338774992144215)
      ·
        refine ⟨12053349650008162488216323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8035566433338774992144215 12053349650008162488216323)
        ·
          refine ⟨18080024475012243732324485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12053349650008162488216323 18080024475012243732324485)
          ·
            refine ⟨3390004589064795699810841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18080024475012243732324485 3390004589064795699810841)
            ·
              refine ⟨2542503441798596774858131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3390004589064795699810841 2542503441798596774858131)
              ·
                refine ⟨3813755162697895162287197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2542503441798596774858131 3813755162697895162287197)
                ·
                  refine ⟨1430158186011710685857699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3813755162697895162287197 1430158186011710685857699)
                  ·
                    refine ⟨2145237279017566028786549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1430158186011710685857699 2145237279017566028786549)
                    ·
                      refine ⟨201115994907896815198739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2145237279017566028786549 201115994907896815198739)
                      ·
                        rfl

theorem cell23_391672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 3, 1, 5].length) (baseStart_391672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_391672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_391672 prefixEnd_391672 := by exact prefixLift 391672
  have htrace : WordTrace (prefixWord ++ tailWord_391672) baseStart_391672 baseEnd_391672 := by
    simpa [prefixWord, tailWord_391672, baseEnd_391672] using wordTrace_append hprefix tailTrace_391672
  have hstable : (prefixWord ++ tailWord_391672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391672).length < 2 ^ (prefixWord ++ tailWord_391672).sum := by decide
  have hdescent : baseEnd_391672 < baseStart_391672 := by decide
  rcases family_descends (prefixWord ++ tailWord_391672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391679 : List Nat := [1, 1, 2, 2, 1, 2, 3, 5, 2, 4]
def baseStart_391679 : Nat := 118140960795 + 391679 * 2 ^ 59
def prefixEnd_391679 : Nat := 4983230072969 + 3 ^ 40 * 391679 * 2
def baseEnd_391679 : Nat := 67039863090826095937069

theorem tailTrace_391679 : CollatzResearch.WordTrace tailWord_391679 prefixEnd_391679 67039863090826095937069 := by
  unfold tailWord_391679
  simp only [CollatzResearch.WordTrace]
  refine ⟨14285706748021351292650091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9523804498680900861766727 14285706748021351292650091)
  ·
    refine ⟨21428560122032026938975137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14285706748021351292650091 21428560122032026938975137)
    ·
      refine ⟨16071420091524020204231353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21428560122032026938975137 16071420091524020204231353)
      ·
        refine ⟨12053565068643015153173515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16071420091524020204231353 12053565068643015153173515)
        ·
          refine ⟨18080347602964522729760273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12053565068643015153173515 18080347602964522729760273)
          ·
            refine ⟨13560260702223392047320205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18080347602964522729760273 13560260702223392047320205)
            ·
              refine ⟨5085097763333772017745077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13560260702223392047320205 5085097763333772017745077)
              ·
                refine ⟨476727915312541126663601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5085097763333772017745077 476727915312541126663601)
                ·
                  refine ⟨357545936484405844997701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 476727915312541126663601 357545936484405844997701)
                  ·
                    refine ⟨67039863090826095937069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 357545936484405844997701 67039863090826095937069)
                    ·
                      rfl

theorem cell23_391679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 5, 2, 4].length) (baseStart_391679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_391679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_391679 prefixEnd_391679 := by exact prefixLift 391679
  have htrace : WordTrace (prefixWord ++ tailWord_391679) baseStart_391679 baseEnd_391679 := by
    simpa [prefixWord, tailWord_391679, baseEnd_391679] using wordTrace_append hprefix tailTrace_391679
  have hstable : (prefixWord ++ tailWord_391679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391679).length < 2 ^ (prefixWord ++ tailWord_391679).sum := by decide
  have hdescent : baseEnd_391679 < baseStart_391679 := by decide
  rcases family_descends (prefixWord ++ tailWord_391679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391700 : List Nat := [2, 4, 3, 1, 1, 3, 2, 1, 1, 5]
def baseStart_391700 : Nat := 118140960795 + 391700 * 2 ^ 59
def prefixEnd_391700 : Nat := 4983230072969 + 3 ^ 40 * 391700 * 2
def baseEnd_391700 : Nat := 67043457455407568549537

theorem tailTrace_391700 : CollatzResearch.WordTrace tailWord_391700 prefixEnd_391700 67043457455407568549537 := by
  unfold tailWord_391700
  simp only [CollatzResearch.WordTrace]
  refine ⟨7143236340472635939582277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9524315120630181252776369 7143236340472635939582277)
  ·
    refine ⟨1339356813838619238671677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7143236340472635939582277 1339356813838619238671677)
    ·
      refine ⟨502258805189482214501879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1339356813838619238671677 502258805189482214501879)
      ·
        refine ⟨753388207784223321752819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 502258805189482214501879 753388207784223321752819)
        ·
          refine ⟨1130082311676334982629229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 753388207784223321752819 1130082311676334982629229)
          ·
            refine ⟨423780866878625618485961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1130082311676334982629229 423780866878625618485961)
            ·
              refine ⟨317835650158969213864471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 423780866878625618485961 317835650158969213864471)
              ·
                refine ⟨476753475238453820796707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 317835650158969213864471 476753475238453820796707)
                ·
                  refine ⟨715130212857680731195061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 476753475238453820796707 715130212857680731195061)
                  ·
                    refine ⟨67043457455407568549537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 715130212857680731195061 67043457455407568549537)
                    ·
                      rfl

theorem cell23_391700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_391700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_391700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_391700 prefixEnd_391700 := by exact prefixLift 391700
  have htrace : WordTrace (prefixWord ++ tailWord_391700) baseStart_391700 baseEnd_391700 := by
    simpa [prefixWord, tailWord_391700, baseEnd_391700] using wordTrace_append hprefix tailTrace_391700
  have hstable : (prefixWord ++ tailWord_391700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391700).length < 2 ^ (prefixWord ++ tailWord_391700).sum := by decide
  have hdescent : baseEnd_391700 < baseStart_391700 := by decide
  rcases family_descends (prefixWord ++ tailWord_391700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391703 : List Nat := [1, 1, 3, 6, 1, 1, 1, 3, 1, 1, 4]
def baseStart_391703 : Nat := 118140960795 + 391703 * 2 ^ 59
def prefixEnd_391703 : Nat := 4983230072969 + 3 ^ 40 * 391703 * 2
def baseEnd_391703 : Nat := 201131912808186193911097

theorem tailTrace_391703 : CollatzResearch.WordTrace tailWord_391703 prefixEnd_391703 201131912808186193911097 := by
  unfold tailWord_391703
  simp only [CollatzResearch.WordTrace]
  refine ⟨14286582099934403391523763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9524388066622935594349175 14286582099934403391523763)
  ·
    refine ⟨21429873149901605087285645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14286582099934403391523763 21429873149901605087285645)
    ·
      refine ⟨8036202431213101907732117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21429873149901605087285645 8036202431213101907732117)
      ·
        refine ⟨376696988963114151924943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 8036202431213101907732117 376696988963114151924943)
        ·
          refine ⟨565045483444671227887415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 376696988963114151924943 565045483444671227887415)
          ·
            refine ⟨847568225167006841831123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 565045483444671227887415 847568225167006841831123)
            ·
              refine ⟨1271352337750510262746685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 847568225167006841831123 1271352337750510262746685)
              ·
                refine ⟨476757126656441348530007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1271352337750510262746685 476757126656441348530007)
                ·
                  refine ⟨715135689984662022795011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 476757126656441348530007 715135689984662022795011)
                  ·
                    refine ⟨1072703534976993034192517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 715135689984662022795011 1072703534976993034192517)
                    ·
                      refine ⟨201131912808186193911097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1072703534976993034192517 201131912808186193911097)
                      ·
                        rfl

theorem cell23_391703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_391703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_391703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_391703 prefixEnd_391703 := by exact prefixLift 391703
  have htrace : WordTrace (prefixWord ++ tailWord_391703) baseStart_391703 baseEnd_391703 := by
    simpa [prefixWord, tailWord_391703, baseEnd_391703] using wordTrace_append hprefix tailTrace_391703
  have hstable : (prefixWord ++ tailWord_391703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391703).length < 2 ^ (prefixWord ++ tailWord_391703).sum := by decide
  have hdescent : baseEnd_391703 < baseStart_391703 := by decide
  rcases family_descends (prefixWord ++ tailWord_391703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391720 : List Nat := [2, 1, 5, 2, 1, 2, 2, 1, 3, 2, 2]
def baseStart_391720 : Nat := 118140960795 + 391720 * 2 ^ 59
def prefixEnd_391720 : Nat := 4983230072969 + 3 ^ 40 * 391720 * 2
def baseEnd_391720 : Nat := 201140641979312627398519

theorem tailTrace_391720 : CollatzResearch.WordTrace tailWord_391720 prefixEnd_391720 201140641979312627398519 := by
  unfold tailWord_391720
  simp only [CollatzResearch.WordTrace]
  refine ⟨7143601070436407647446307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9524801427248543529928409 7143601070436407647446307)
  ·
    refine ⟨10715401605654611471169461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7143601070436407647446307 10715401605654611471169461)
    ·
      refine ⟨1004568900530119825422137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10715401605654611471169461 1004568900530119825422137)
      ·
        refine ⟨753426675397589869066603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1004568900530119825422137 753426675397589869066603)
        ·
          refine ⟨1130140013096384803599905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 753426675397589869066603 1130140013096384803599905)
          ·
            refine ⟨847605009822288602699929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1130140013096384803599905 847605009822288602699929)
            ·
              refine ⟨635703757366716452024947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 847605009822288602699929 635703757366716452024947)
              ·
                refine ⟨953555636050074678037421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 635703757366716452024947 953555636050074678037421)
                ·
                  refine ⟨357583363518778004264033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 953555636050074678037421 357583363518778004264033)
                  ·
                    refine ⟨268187522639083503198025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 357583363518778004264033 268187522639083503198025)
                    ·
                      refine ⟨201140641979312627398519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 268187522639083503198025 201140641979312627398519)
                      ·
                        rfl

theorem cell23_391720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_391720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_391720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_391720 prefixEnd_391720 := by exact prefixLift 391720
  have htrace : WordTrace (prefixWord ++ tailWord_391720) baseStart_391720 baseEnd_391720 := by
    simpa [prefixWord, tailWord_391720, baseEnd_391720] using wordTrace_append hprefix tailTrace_391720
  have hstable : (prefixWord ++ tailWord_391720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391720).length < 2 ^ (prefixWord ++ tailWord_391720).sum := by decide
  have hdescent : baseEnd_391720 < baseStart_391720 := by decide
  rcases family_descends (prefixWord ++ tailWord_391720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391752 : List Nat := [2, 1, 3, 1, 1, 1, 1, 4, 1, 8]
def baseStart_391752 : Nat := 118140960795 + 391752 * 2 ^ 59
def prefixEnd_391752 : Nat := 4983230072969 + 3 ^ 40 * 391752 * 2
def baseEnd_391752 : Nat := 67052357786752167399457

theorem tailTrace_391752 : CollatzResearch.WordTrace tailWord_391752 prefixEnd_391752 67052357786752167399457 := by
  unfold tailWord_391752
  simp only [CollatzResearch.WordTrace]
  refine ⟨7144184638378442380028755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9525579517837923173371673 7144184638378442380028755)
  ·
    refine ⟨10716276957567663570043133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7144184638378442380028755 10716276957567663570043133)
    ·
      refine ⟨4018603859087873838766175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10716276957567663570043133 4018603859087873838766175)
      ·
        refine ⟨6027905788631810758149263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4018603859087873838766175 6027905788631810758149263)
        ·
          refine ⟨9041858682947716137223895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6027905788631810758149263 9041858682947716137223895)
          ·
            refine ⟨13562788024421574205835843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9041858682947716137223895 13562788024421574205835843)
            ·
              refine ⟨20344182036632361308753765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13562788024421574205835843 20344182036632361308753765)
              ·
                refine ⟨3814534131868567745391331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20344182036632361308753765 3814534131868567745391331)
                ·
                  refine ⟨5721801197802851618086997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3814534131868567745391331 5721801197802851618086997)
                  ·
                    refine ⟨67052357786752167399457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 5721801197802851618086997 67052357786752167399457)
                    ·
                      rfl

theorem cell23_391752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 1, 8].length) (baseStart_391752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_391752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_391752 prefixEnd_391752 := by exact prefixLift 391752
  have htrace : WordTrace (prefixWord ++ tailWord_391752) baseStart_391752 baseEnd_391752 := by
    simpa [prefixWord, tailWord_391752, baseEnd_391752] using wordTrace_append hprefix tailTrace_391752
  have hstable : (prefixWord ++ tailWord_391752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391752).length < 2 ^ (prefixWord ++ tailWord_391752).sum := by decide
  have hdescent : baseEnd_391752 < baseStart_391752 := by decide
  rcases family_descends (prefixWord ++ tailWord_391752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391779 : List Nat := [1, 1, 1, 5, 1, 2, 2, 1, 2, 4, 3]
def baseStart_391779 : Nat := 118140960795 + 391779 * 2 ^ 59
def prefixEnd_391779 : Nat := 4983230072969 + 3 ^ 40 * 391779 * 2
def baseEnd_391779 : Nat := 201170937337927896560747

theorem tailTrace_391779 : CollatzResearch.WordTrace tailWord_391779 prefixEnd_391779 201170937337927896560747 := by
  unfold tailWord_391779
  simp only [CollatzResearch.WordTrace]
  refine ⟨14289354047659068371290391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9526236031772712247526927 14289354047659068371290391)
  ·
    refine ⟨21434031071488602556935587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14289354047659068371290391 21434031071488602556935587)
    ·
      refine ⟨32151046607232903835403381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21434031071488602556935587 32151046607232903835403381)
      ·
        refine ⟨3014160619428084734569067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32151046607232903835403381 3014160619428084734569067)
        ·
          refine ⟨4521240929142127101853601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3014160619428084734569067 4521240929142127101853601)
          ·
            refine ⟨3390930696856595326390201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4521240929142127101853601 3390930696856595326390201)
            ·
              refine ⟨2543198022642446494792651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3390930696856595326390201 2543198022642446494792651)
              ·
                refine ⟨3814797033963669742188977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2543198022642446494792651 3814797033963669742188977)
                ·
                  refine ⟨2861097775472752306641733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3814797033963669742188977 2861097775472752306641733)
                  ·
                    refine ⟨536455832901141057495325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2861097775472752306641733 536455832901141057495325)
                    ·
                      refine ⟨201170937337927896560747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 536455832901141057495325 201170937337927896560747)
                      ·
                        rfl

theorem cell23_391779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 2, 4, 3].length) (baseStart_391779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_391779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_391779 prefixEnd_391779 := by exact prefixLift 391779
  have htrace : WordTrace (prefixWord ++ tailWord_391779) baseStart_391779 baseEnd_391779 := by
    simpa [prefixWord, tailWord_391779, baseEnd_391779] using wordTrace_append hprefix tailTrace_391779
  have hstable : (prefixWord ++ tailWord_391779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391779).length < 2 ^ (prefixWord ++ tailWord_391779).sum := by decide
  have hdescent : baseEnd_391779 < baseStart_391779 := by decide
  rcases family_descends (prefixWord ++ tailWord_391779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391797 : List Nat := [1, 3, 4, 2, 2, 2, 1, 2, 1, 3, 2]
def baseStart_391797 : Nat := 118140960795 + 391797 * 2 ^ 59
def prefixEnd_391797 : Nat := 4983230072969 + 3 ^ 40 * 391797 * 2
def baseEnd_391797 : Nat := 201180179989708826135665

theorem tailTrace_391797 : CollatzResearch.WordTrace tailWord_391797 prefixEnd_391797 201180179989708826135665 := by
  unfold tailWord_391797
  simp only [CollatzResearch.WordTrace]
  refine ⟨14290010561593857445445645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9526673707729238296963763 14290010561593857445445645)
  ·
    refine ⟨5358753960597696542042117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14290010561593857445445645 5358753960597696542042117)
    ·
      refine ⟨1004766367612068101632897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5358753960597696542042117 1004766367612068101632897)
      ·
        refine ⟨753574775709051076224673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1004766367612068101632897 753574775709051076224673)
        ·
          refine ⟨565181081781788307168505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 753574775709051076224673 565181081781788307168505)
          ·
            refine ⟨423885811336341230376379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 565181081781788307168505 423885811336341230376379)
            ·
              refine ⟨635828717004511845564569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 423885811336341230376379 635828717004511845564569)
              ·
                refine ⟨476871537753383884173427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 635828717004511845564569 476871537753383884173427)
                ·
                  refine ⟨715307306630075826260141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 476871537753383884173427 715307306630075826260141)
                  ·
                    refine ⟨268240239986278434847553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 715307306630075826260141 268240239986278434847553)
                    ·
                      refine ⟨201180179989708826135665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 268240239986278434847553 201180179989708826135665)
                      ·
                        rfl

theorem cell23_391797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_391797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_391797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_391797 prefixEnd_391797 := by exact prefixLift 391797
  have htrace : WordTrace (prefixWord ++ tailWord_391797) baseStart_391797 baseEnd_391797 := by
    simpa [prefixWord, tailWord_391797, baseEnd_391797] using wordTrace_append hprefix tailTrace_391797
  have hstable : (prefixWord ++ tailWord_391797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391797).length < 2 ^ (prefixWord ++ tailWord_391797).sum := by decide
  have hdescent : baseEnd_391797 < baseStart_391797 := by decide
  rcases family_descends (prefixWord ++ tailWord_391797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391849 : List Nat := [1, 2, 1, 1, 1, 1, 2, 3, 6, 1, 4]
def baseStart_391849 : Nat := 118140960795 + 391849 * 2 ^ 59
def prefixEnd_391849 : Nat := 4983230072969 + 3 ^ 40 * 391849 * 2
def baseEnd_391849 : Nat := 201206880983742622685425

theorem tailTrace_391849 : CollatzResearch.WordTrace tailWord_391849 prefixEnd_391849 201206880983742622685425 := by
  unfold tailWord_391849
  simp only [CollatzResearch.WordTrace]
  refine ⟨14291907157405470326338601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9527938104936980217559067 14291907157405470326338601)
  ·
    refine ⟨10718930368054102744753951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14291907157405470326338601 10718930368054102744753951)
    ·
      refine ⟨16078395552081154117130927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10718930368054102744753951 16078395552081154117130927)
      ·
        refine ⟨24117593328121731175696391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16078395552081154117130927 24117593328121731175696391)
        ·
          refine ⟨36176389992182596763544587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24117593328121731175696391 36176389992182596763544587)
          ·
            refine ⟨54264584988273895145316881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36176389992182596763544587 54264584988273895145316881)
            ·
              refine ⟨40698438741205421358987661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54264584988273895145316881 40698438741205421358987661)
              ·
                refine ⟨15261914527952033009620373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40698438741205421358987661 15261914527952033009620373)
                ·
                  refine ⟨715402243497751547325955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 15261914527952033009620373 715402243497751547325955)
                  ·
                    refine ⟨1073103365246627320988933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 715402243497751547325955 1073103365246627320988933)
                    ·
                      refine ⟨201206880983742622685425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1073103365246627320988933 201206880983742622685425)
                      ·
                        rfl

theorem cell23_391849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 6, 1, 4].length) (baseStart_391849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_391849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_391849 prefixEnd_391849 := by exact prefixLift 391849
  have htrace : WordTrace (prefixWord ++ tailWord_391849) baseStart_391849 baseEnd_391849 := by
    simpa [prefixWord, tailWord_391849, baseEnd_391849] using wordTrace_append hprefix tailTrace_391849
  have hstable : (prefixWord ++ tailWord_391849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391849).length < 2 ^ (prefixWord ++ tailWord_391849).sum := by decide
  have hdescent : baseEnd_391849 < baseStart_391849 := by decide
  rcases family_descends (prefixWord ++ tailWord_391849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391863 : List Nat := [1, 1, 3, 1, 6, 2, 1, 1, 2, 5]
def baseStart_391863 : Nat := 118140960795 + 391863 * 2 ^ 59
def prefixEnd_391863 : Nat := 4983230072969 + 3 ^ 40 * 391863 * 2
def baseEnd_391863 : Nat := 67071356570968522636787

theorem tailTrace_391863 : CollatzResearch.WordTrace tailWord_391863 prefixEnd_391863 67071356570968522636787 := by
  unfold tailWord_391863
  simp only [CollatzResearch.WordTrace]
  refine ⟨14292417779354750717348243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9528278519569833811565495 14292417779354750717348243)
  ·
    refine ⟨21438626669032126076022365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14292417779354750717348243 21438626669032126076022365)
    ·
      refine ⟨8039485000887047278508387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21438626669032126076022365 8039485000887047278508387)
      ·
        refine ⟨12059227501330570917762581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8039485000887047278508387 12059227501330570917762581)
        ·
          refine ⟨565276289124870511770121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 12059227501330570917762581 565276289124870511770121)
          ·
            refine ⟨423957216843652883827591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 565276289124870511770121 423957216843652883827591)
            ·
              refine ⟨635935825265479325741387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 423957216843652883827591 635935825265479325741387)
              ·
                refine ⟨953903737898218988612081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 635935825265479325741387 953903737898218988612081)
                ·
                  refine ⟨715427803423664241459061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 953903737898218988612081 715427803423664241459061)
                  ·
                    refine ⟨67071356570968522636787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 715427803423664241459061 67071356570968522636787)
                    ·
                      rfl

theorem cell23_391863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 1, 2, 5].length) (baseStart_391863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_391863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_391863 prefixEnd_391863 := by exact prefixLift 391863
  have htrace : WordTrace (prefixWord ++ tailWord_391863) baseStart_391863 baseEnd_391863 := by
    simpa [prefixWord, tailWord_391863, baseEnd_391863] using wordTrace_append hprefix tailTrace_391863
  have hstable : (prefixWord ++ tailWord_391863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391863).length < 2 ^ (prefixWord ++ tailWord_391863).sum := by decide
  have hdescent : baseEnd_391863 < baseStart_391863 := by decide
  rcases family_descends (prefixWord ++ tailWord_391863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391866 : List Nat := [3, 1, 1, 1, 2, 3, 1, 2, 1, 6, 2]
def baseStart_391866 : Nat := 118140960795 + 391866 * 2 ^ 59
def prefixEnd_391866 : Nat := 4983230072969 + 3 ^ 40 * 391866 * 2
def baseEnd_391866 : Nat := 201215610154869056172847

theorem tailTrace_391866 : CollatzResearch.WordTrace tailWord_391866 prefixEnd_391866 201215610154869056172847 := by
  unfold tailWord_391866
  simp only [CollatzResearch.WordTrace]
  refine ⟨3573131799585970557426863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9528351465562588153138301 3573131799585970557426863)
  ·
    refine ⟨5359697699378955836140295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3573131799585970557426863 5359697699378955836140295)
    ·
      refine ⟨8039546549068433754210443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5359697699378955836140295 8039546549068433754210443)
      ·
        refine ⟨12059319823602650631315665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8039546549068433754210443 12059319823602650631315665)
        ·
          refine ⟨9044489867701987973486749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12059319823602650631315665 9044489867701987973486749)
          ·
            refine ⟨3391683700388245490057531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9044489867701987973486749 3391683700388245490057531)
            ·
              refine ⟨5087525550582368235086297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3391683700388245490057531 5087525550582368235086297)
              ·
                refine ⟨3815644162936776176314723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5087525550582368235086297 3815644162936776176314723)
                ·
                  refine ⟨5723466244405164264472085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3815644162936776176314723 5723466244405164264472085)
                  ·
                    refine ⟨268287480206492074897129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5723466244405164264472085 268287480206492074897129)
                    ·
                      refine ⟨201215610154869056172847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 268287480206492074897129 201215610154869056172847)
                      ·
                        rfl

theorem cell23_391866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 1, 6, 2].length) (baseStart_391866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_391866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_391866 prefixEnd_391866 := by exact prefixLift 391866
  have htrace : WordTrace (prefixWord ++ tailWord_391866) baseStart_391866 baseEnd_391866 := by
    simpa [prefixWord, tailWord_391866, baseEnd_391866] using wordTrace_append hprefix tailTrace_391866
  have hstable : (prefixWord ++ tailWord_391866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391866).length < 2 ^ (prefixWord ++ tailWord_391866).sum := by decide
  have hdescent : baseEnd_391866 < baseStart_391866 := by decide
  rcases family_descends (prefixWord ++ tailWord_391866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391878 : List Nat := [6, 1, 2, 1, 3, 1, 1, 2, 2, 2, 2]
def baseStart_391878 : Nat := 118140960795 + 391878 * 2 ^ 59
def prefixEnd_391878 : Nat := 4983230072969 + 3 ^ 40 * 391878 * 2
def baseEnd_391878 : Nat := 201221771922723009222793

theorem tailTrace_391878 : CollatzResearch.WordTrace tailWord_391878 prefixEnd_391878 201221771922723009222793 := by
  unfold tailWord_391878
  simp only [CollatzResearch.WordTrace]
  refine ⟨446655152321887758723259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 9528643249533605519429525 446655152321887758723259)
  ·
    refine ⟨669982728482831638084889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 446655152321887758723259 669982728482831638084889)
    ·
      refine ⟨502487046362123728563667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 669982728482831638084889 502487046362123728563667)
      ·
        refine ⟨753730569543185592845501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 502487046362123728563667 753730569543185592845501)
        ·
          refine ⟨282648963578694597317063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 753730569543185592845501 282648963578694597317063)
          ·
            refine ⟨423973445368041895975595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 282648963578694597317063 423973445368041895975595)
            ·
              refine ⟨635960168052062843963393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 423973445368041895975595 635960168052062843963393)
              ·
                refine ⟨476970126039047132972545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 635960168052062843963393 476970126039047132972545)
                ·
                  refine ⟨357727594529285349729409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 476970126039047132972545 357727594529285349729409)
                  ·
                    refine ⟨268295695896964012297057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 357727594529285349729409 268295695896964012297057)
                    ·
                      refine ⟨201221771922723009222793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 268295695896964012297057 201221771922723009222793)
                      ·
                        rfl

theorem cell23_391878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_391878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_391878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_391878 prefixEnd_391878 := by exact prefixLift 391878
  have htrace : WordTrace (prefixWord ++ tailWord_391878) baseStart_391878 baseEnd_391878 := by
    simpa [prefixWord, tailWord_391878, baseEnd_391878] using wordTrace_append hprefix tailTrace_391878
  have hstable : (prefixWord ++ tailWord_391878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391878).length < 2 ^ (prefixWord ++ tailWord_391878).sum := by decide
  have hdescent : baseEnd_391878 < baseStart_391878 := by decide
  rcases family_descends (prefixWord ++ tailWord_391878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391889 : List Nat := [1, 2, 2, 1, 2, 3, 3, 1, 8]
def baseStart_391889 : Nat := 118140960795 + 391889 * 2 ^ 59
def prefixEnd_391889 : Nat := 4983230072969 + 3 ^ 40 * 391889 * 2
def baseEnd_391889 : Nat := 22358602245546940687249

theorem tailTrace_391889 : CollatzResearch.WordTrace tailWord_391889 prefixEnd_391889 22358602245546940687249 := by
  unfold tailWord_391889
  simp only [CollatzResearch.WordTrace]
  refine ⟨14293366077260557157794721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9528910718173704771863147 14293366077260557157794721)
  ·
    refine ⟨10720024557945417868346041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14293366077260557157794721 10720024557945417868346041)
    ·
      refine ⟨8040018418459063401259531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10720024557945417868346041 8040018418459063401259531)
      ·
        refine ⟨12060027627688595101889297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8040018418459063401259531 12060027627688595101889297)
        ·
          refine ⟨9045020720766446326416973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12060027627688595101889297 9045020720766446326416973)
          ·
            refine ⟨3391882770287417372406365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9045020720766446326416973 3391882770287417372406365)
            ·
              refine ⟨1271956038857781514652387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3391882770287417372406365 1271956038857781514652387)
              ·
                refine ⟨1907934058286672271978581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1271956038857781514652387 1907934058286672271978581)
                ·
                  refine ⟨22358602245546940687249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1907934058286672271978581 22358602245546940687249)
                  ·
                    rfl

theorem cell23_391889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 1, 8].length) (baseStart_391889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_391889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_391889 prefixEnd_391889 := by exact prefixLift 391889
  have htrace : WordTrace (prefixWord ++ tailWord_391889) baseStart_391889 baseEnd_391889 := by
    simpa [prefixWord, tailWord_391889, baseEnd_391889] using wordTrace_append hprefix tailTrace_391889
  have hstable : (prefixWord ++ tailWord_391889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391889).length < 2 ^ (prefixWord ++ tailWord_391889).sum := by decide
  have hdescent : baseEnd_391889 < baseStart_391889 := by decide
  rcases family_descends (prefixWord ++ tailWord_391889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391900 : List Nat := [2, 2, 5, 1, 1, 1, 2, 1, 2, 4, 2]
def baseStart_391900 : Nat := 118140960795 + 391900 * 2 ^ 59
def prefixEnd_391900 : Nat := 4983230072969 + 3 ^ 40 * 391900 * 2
def baseEnd_391900 : Nat := 201233068497121923147691

theorem tailTrace_391900 : CollatzResearch.WordTrace tailWord_391900 prefixEnd_391900 201233068497121923147691 := by
  unfold tailWord_391900
  simp only [CollatzResearch.WordTrace]
  refine ⟨7146883640110353018222577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9529178186813804024296769 7146883640110353018222577)
  ·
    refine ⟨5360162730082764763666933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7146883640110353018222577 5360162730082764763666933)
    ·
      refine ⟨502515255945259196593775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5360162730082764763666933 502515255945259196593775)
      ·
        refine ⟨753772883917888794890663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 502515255945259196593775 753772883917888794890663)
        ·
          refine ⟨1130659325876833192335995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 753772883917888794890663 1130659325876833192335995)
          ·
            refine ⟨1695988988815249788503993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1130659325876833192335995 1695988988815249788503993)
            ·
              refine ⟨1271991741611437341377995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1695988988815249788503993 1271991741611437341377995)
              ·
                refine ⟨1907987612417156012066993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1271991741611437341377995 1907987612417156012066993)
                ·
                  refine ⟨1430990709312867009050245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1907987612417156012066993 1430990709312867009050245)
                  ·
                    refine ⟨268310757996162564196921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1430990709312867009050245 268310757996162564196921)
                    ·
                      refine ⟨201233068497121923147691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 268310757996162564196921 201233068497121923147691)
                      ·
                        rfl

theorem cell23_391900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_391900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_391900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_391900 prefixEnd_391900 := by exact prefixLift 391900
  have htrace : WordTrace (prefixWord ++ tailWord_391900) baseStart_391900 baseEnd_391900 := by
    simpa [prefixWord, tailWord_391900, baseEnd_391900] using wordTrace_append hprefix tailTrace_391900
  have hstable : (prefixWord ++ tailWord_391900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391900).length < 2 ^ (prefixWord ++ tailWord_391900).sum := by decide
  have hdescent : baseEnd_391900 < baseStart_391900 := by decide
  rcases family_descends (prefixWord ++ tailWord_391900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391970 : List Nat := [3, 3, 1, 1, 2, 4, 1, 2, 1, 5]
def baseStart_391970 : Nat := 118140960795 + 391970 * 2 ^ 59
def prefixEnd_391970 : Nat := 4983230072969 + 3 ^ 40 * 391970 * 2
def baseEnd_391970 : Nat := 67089670714312216424123

theorem tailTrace_391970 : CollatzResearch.WordTrace tailWord_391970 prefixEnd_391970 67089670714312216424123 := by
  unfold tailWord_391970
  simp only [CollatzResearch.WordTrace]
  refine ⟨3574080097491776997873341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9530880259978071994328909 3574080097491776997873341)
  ·
    refine ⟨1340280036559416374202503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3574080097491776997873341 1340280036559416374202503)
    ·
      refine ⟨2010420054839124561303755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1340280036559416374202503 2010420054839124561303755)
      ·
        refine ⟨3015630082258686841955633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2010420054839124561303755 3015630082258686841955633)
        ·
          refine ⟨2261722561694015131466725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3015630082258686841955633 2261722561694015131466725)
          ·
            refine ⟨424072980317627837150011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2261722561694015131466725 424072980317627837150011)
            ·
              refine ⟨636109470476441755725017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 424072980317627837150011 636109470476441755725017)
              ·
                refine ⟨477082102857331316793763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 636109470476441755725017 477082102857331316793763)
                ·
                  refine ⟨715623154285996975190645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 477082102857331316793763 715623154285996975190645)
                  ·
                    refine ⟨67089670714312216424123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 715623154285996975190645 67089670714312216424123)
                    ·
                      rfl

theorem cell23_391970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 2, 1, 5].length) (baseStart_391970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_391970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_391970 prefixEnd_391970 := by exact prefixLift 391970
  have htrace : WordTrace (prefixWord ++ tailWord_391970) baseStart_391970 baseEnd_391970 := by
    simpa [prefixWord, tailWord_391970, baseEnd_391970] using wordTrace_append hprefix tailTrace_391970
  have hstable : (prefixWord ++ tailWord_391970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391970).length < 2 ^ (prefixWord ++ tailWord_391970).sum := by decide
  have hdescent : baseEnd_391970 < baseStart_391970 := by decide
  rcases family_descends (prefixWord ++ tailWord_391970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392020 : List Nat := [2, 4, 1, 1, 4, 1, 2, 1, 1, 2, 4]
def baseStart_392020 : Nat := 118140960795 + 392020 * 2 ^ 59
def prefixEnd_392020 : Nat := 4983230072969 + 3 ^ 40 * 392020 * 2
def baseEnd_392020 : Nat := 201294686175661453647139

theorem tailTrace_392020 : CollatzResearch.WordTrace tailWord_392020 prefixEnd_392020 201294686175661453647139 := by
  unfold tailWord_392020
  simp only [CollatzResearch.WordTrace]
  refine ⟨7149072019892983265406757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9532096026523977687209009 7149072019892983265406757)
  ·
    refine ⟨1340451003729934362263767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7149072019892983265406757 1340451003729934362263767)
    ·
      refine ⟨2010676505594901543395651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1340451003729934362263767 2010676505594901543395651)
      ·
        refine ⟨3016014758392352315093477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2010676505594901543395651 3016014758392352315093477)
        ·
          refine ⟨565502767198566059080027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3016014758392352315093477 565502767198566059080027)
          ·
            refine ⟨848254150797849088620041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 565502767198566059080027 848254150797849088620041)
            ·
              refine ⟨636190613098386816465031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 848254150797849088620041 636190613098386816465031)
              ·
                refine ⟨954285919647580224697547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 636190613098386816465031 954285919647580224697547)
                ·
                  refine ⟨1431428879471370337046321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 954285919647580224697547 1431428879471370337046321)
                  ·
                    refine ⟨1073571659603527752784741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1431428879471370337046321 1073571659603527752784741)
                    ·
                      refine ⟨201294686175661453647139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1073571659603527752784741 201294686175661453647139)
                      ·
                        rfl

theorem cell23_392020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 1, 1, 2, 4].length) (baseStart_392020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_392020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_392020 prefixEnd_392020 := by exact prefixLift 392020
  have htrace : WordTrace (prefixWord ++ tailWord_392020) baseStart_392020 baseEnd_392020 := by
    simpa [prefixWord, tailWord_392020, baseEnd_392020] using wordTrace_append hprefix tailTrace_392020
  have hstable : (prefixWord ++ tailWord_392020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392020).length < 2 ^ (prefixWord ++ tailWord_392020).sum := by decide
  have hdescent : baseEnd_392020 < baseStart_392020 := by decide
  rcases family_descends (prefixWord ++ tailWord_392020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392023 : List Nat := [1, 1, 3, 2, 4, 1, 1, 3, 1, 3, 3]
def baseStart_392023 : Nat := 118140960795 + 392023 * 2 ^ 59
def prefixEnd_392023 : Nat := 4983230072969 + 3 ^ 40 * 392023 * 2
def baseEnd_392023 : Nat := 201296226617624941909625

theorem tailTrace_392023 : CollatzResearch.WordTrace tailWord_392023 prefixEnd_392023 201296226617624941909625 := by
  unfold tailWord_392023
  simp only [CollatzResearch.WordTrace]
  refine ⟨14298253458775098043172723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9532168972516732028781815 14298253458775098043172723)
  ·
    refine ⟨21447380188162647064759085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14298253458775098043172723 21447380188162647064759085)
    ·
      refine ⟨8042767570560992649284657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21447380188162647064759085 8042767570560992649284657)
      ·
        refine ⟨6032075677920744486963493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8042767570560992649284657 6032075677920744486963493)
        ·
          refine ⟨1131014189610139591305655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6032075677920744486963493 1131014189610139591305655)
          ·
            refine ⟨1696521284415209386958483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1131014189610139591305655 1696521284415209386958483)
            ·
              refine ⟨2544781926622814080437725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1696521284415209386958483 2544781926622814080437725)
              ·
                refine ⟨954293222483555280164147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2544781926622814080437725 954293222483555280164147)
                ·
                  refine ⟨1431439833725332920246221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 954293222483555280164147 1431439833725332920246221)
                  ·
                    refine ⟨536789937646999845092333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1431439833725332920246221 536789937646999845092333)
                    ·
                      refine ⟨201296226617624941909625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 536789937646999845092333 201296226617624941909625)
                      ·
                        rfl

theorem cell23_392023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 3, 1, 3, 3].length) (baseStart_392023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_392023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_392023 prefixEnd_392023 := by exact prefixLift 392023
  have htrace : WordTrace (prefixWord ++ tailWord_392023) baseStart_392023 baseEnd_392023 := by
    simpa [prefixWord, tailWord_392023, baseEnd_392023] using wordTrace_append hprefix tailTrace_392023
  have hstable : (prefixWord ++ tailWord_392023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392023).length < 2 ^ (prefixWord ++ tailWord_392023).sum := by decide
  have hdescent : baseEnd_392023 < baseStart_392023 := by decide
  rcases family_descends (prefixWord ++ tailWord_392023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392057 : List Nat := [1, 2, 1, 3, 2, 5, 1, 2, 2, 1, 3]
def baseStart_392057 : Nat := 118140960795 + 392057 * 2 ^ 59
def prefixEnd_392057 : Nat := 4983230072969 + 3 ^ 40 * 392057 * 2
def baseEnd_392057 : Nat := 201313684959877808884469

theorem tailTrace_392057 : CollatzResearch.WordTrace tailWord_392057 prefixEnd_392057 201313684959877808884469 := by
  unfold tailWord_392057
  simp only [CollatzResearch.WordTrace]
  refine ⟨14299493540651921849910425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9532995693767947899940283 14299493540651921849910425)
  ·
    refine ⟨10724620155488941387432819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14299493540651921849910425 10724620155488941387432819)
    ·
      refine ⟨16086930233233412081149229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10724620155488941387432819 16086930233233412081149229)
      ·
        refine ⟨6032598837462529530430961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16086930233233412081149229 6032598837462529530430961)
        ·
          refine ⟨4524449128096897147823221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6032598837462529530430961 4524449128096897147823221)
          ·
            refine ⟨424167105759084107608427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4524449128096897147823221 424167105759084107608427)
            ·
              refine ⟨636250658638626161412641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 424167105759084107608427 636250658638626161412641)
              ·
                refine ⟨477187993978969621059481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 636250658638626161412641 477187993978969621059481)
                ·
                  refine ⟨357890995484227215794611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 477187993978969621059481 357890995484227215794611)
                  ·
                    refine ⟨536836493226340823691917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 357890995484227215794611 536836493226340823691917)
                    ·
                      refine ⟨201313684959877808884469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 536836493226340823691917 201313684959877808884469)
                      ·
                        rfl

theorem cell23_392057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 2, 2, 1, 3].length) (baseStart_392057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_392057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_392057 prefixEnd_392057 := by exact prefixLift 392057
  have htrace : WordTrace (prefixWord ++ tailWord_392057) baseStart_392057 baseEnd_392057 := by
    simpa [prefixWord, tailWord_392057, baseEnd_392057] using wordTrace_append hprefix tailTrace_392057
  have hstable : (prefixWord ++ tailWord_392057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392057).length < 2 ^ (prefixWord ++ tailWord_392057).sum := by decide
  have hdescent : baseEnd_392057 < baseStart_392057 := by decide
  rcases family_descends (prefixWord ++ tailWord_392057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392063 : List Nat := [1, 1, 2, 2, 1, 1, 4, 2, 3, 4, 2]
def baseStart_392063 : Nat := 118140960795 + 392063 * 2 ^ 59
def prefixEnd_392063 : Nat := 4983230072969 + 3 ^ 40 * 392063 * 2
def baseEnd_392063 : Nat := 201316765843804785409441

theorem tailTrace_392063 : CollatzResearch.WordTrace tailWord_392063 prefixEnd_392063 201316765843804785409441 := by
  unfold tailWord_392063
  simp only [CollatzResearch.WordTrace]
  refine ⟨14299712378630184874628843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9533141585753456583085895 14299712378630184874628843)
  ·
    refine ⟨21449568567945277311943265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14299712378630184874628843 21449568567945277311943265)
    ·
      refine ⟨16087176425958957983957449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21449568567945277311943265 16087176425958957983957449)
      ·
        refine ⟨12065382319469218487968087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16087176425958957983957449 12065382319469218487968087)
        ·
          refine ⟨18098073479203827731952131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12065382319469218487968087 18098073479203827731952131)
          ·
            refine ⟨27147110218805741597928197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18098073479203827731952131 27147110218805741597928197)
            ·
              refine ⟨5090083166026076549611537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27147110218805741597928197 5090083166026076549611537)
              ·
                refine ⟨3817562374519557412208653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5090083166026076549611537 3817562374519557412208653)
                ·
                  refine ⟨1431585890444834029578245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3817562374519557412208653 1431585890444834029578245)
                  ·
                    refine ⟨268422354458406380545921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1431585890444834029578245 268422354458406380545921)
                    ·
                      refine ⟨201316765843804785409441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 268422354458406380545921 201316765843804785409441)
                      ·
                        rfl

theorem cell23_392063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 3, 4, 2].length) (baseStart_392063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_392063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_392063 prefixEnd_392063 := by exact prefixLift 392063
  have htrace : WordTrace (prefixWord ++ tailWord_392063) baseStart_392063 baseEnd_392063 := by
    simpa [prefixWord, tailWord_392063, baseEnd_392063] using wordTrace_append hprefix tailTrace_392063
  have hstable : (prefixWord ++ tailWord_392063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392063).length < 2 ^ (prefixWord ++ tailWord_392063).sum := by decide
  have hdescent : baseEnd_392063 < baseStart_392063 := by decide
  rcases family_descends (prefixWord ++ tailWord_392063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392074 : List Nat := [3, 1, 2, 4, 1, 2, 3, 1, 2, 1, 3]
def baseStart_392074 : Nat := 118140960795 + 392074 * 2 ^ 59
def prefixEnd_392074 : Nat := 4983230072969 + 3 ^ 40 * 392074 * 2
def baseEnd_392074 : Nat := 201322414131004242371891

theorem tailTrace_392074 : CollatzResearch.WordTrace tailWord_392074 prefixEnd_392074 201322414131004242371891 := by
  unfold tailWord_392074
  simp only [CollatzResearch.WordTrace]
  refine ⟨3575028395397583438319819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9533409054393555835519517 3575028395397583438319819)
  ·
    refine ⟨5362542593096375157479729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3575028395397583438319819 5362542593096375157479729)
    ·
      refine ⟨4021906944822281368109797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5362542593096375157479729 4021906944822281368109797)
      ·
        refine ⟨754107552154177756520587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4021906944822281368109797 754107552154177756520587)
        ·
          refine ⟨1131161328231266634780881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 754107552154177756520587 1131161328231266634780881)
          ·
            refine ⟨848370996173449976085661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1131161328231266634780881 848370996173449976085661)
            ·
              refine ⟨318139123565043741032123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 848370996173449976085661 318139123565043741032123)
              ·
                refine ⟨477208685347565611548185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 318139123565043741032123 477208685347565611548185)
                ·
                  refine ⟨357906514010674208661139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 477208685347565611548185 357906514010674208661139)
                  ·
                    refine ⟨536859771016011312991709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 357906514010674208661139 536859771016011312991709)
                    ·
                      refine ⟨201322414131004242371891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 536859771016011312991709 201322414131004242371891)
                      ·
                        rfl

theorem cell23_392074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_392074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_392074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_392074 prefixEnd_392074 := by exact prefixLift 392074
  have htrace : WordTrace (prefixWord ++ tailWord_392074) baseStart_392074 baseEnd_392074 := by
    simpa [prefixWord, tailWord_392074, baseEnd_392074] using wordTrace_append hprefix tailTrace_392074
  have hstable : (prefixWord ++ tailWord_392074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392074).length < 2 ^ (prefixWord ++ tailWord_392074).sum := by decide
  have hdescent : baseEnd_392074 < baseStart_392074 := by decide
  rcases family_descends (prefixWord ++ tailWord_392074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392097 : List Nat := [1, 2, 3, 4, 1, 1, 1, 2, 4, 2, 2]
def baseStart_392097 : Nat := 118140960795 + 392097 * 2 ^ 59
def prefixEnd_392097 : Nat := 4983230072969 + 3 ^ 40 * 392097 * 2
def baseEnd_392097 : Nat := 201334224186057652384285

theorem tailTrace_392097 : CollatzResearch.WordTrace tailWord_392097 prefixEnd_392097 201334224186057652384285 := by
  unfold tailWord_392097
  simp only [CollatzResearch.WordTrace]
  refine ⟨14300952460507008681366545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9533968307004672454244363 14300952460507008681366545)
  ·
    refine ⟨10725714345380256511024909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14300952460507008681366545 10725714345380256511024909)
    ·
      refine ⟨4022142879517596191634341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10725714345380256511024909 4022142879517596191634341)
      ·
        refine ⟨754151789909549285931439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4022142879517596191634341 754151789909549285931439)
        ·
          refine ⟨1131227684864323928897159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 754151789909549285931439 1131227684864323928897159)
          ·
            refine ⟨1696841527296485893345739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1131227684864323928897159 1696841527296485893345739)
            ·
              refine ⟨2545262290944728840018609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1696841527296485893345739 2545262290944728840018609)
              ·
                refine ⟨1908946718208546630013957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2545262290944728840018609 1908946718208546630013957)
                ·
                  refine ⟨357927509664102493127617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1908946718208546630013957 357927509664102493127617)
                  ·
                    refine ⟨268445632248076869845713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 357927509664102493127617 268445632248076869845713)
                    ·
                      refine ⟨201334224186057652384285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 268445632248076869845713 201334224186057652384285)
                      ·
                        rfl

theorem cell23_392097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_392097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_392097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_392097 prefixEnd_392097 := by exact prefixLift 392097
  have htrace : WordTrace (prefixWord ++ tailWord_392097) baseStart_392097 baseEnd_392097 := by
    simpa [prefixWord, tailWord_392097, baseEnd_392097] using wordTrace_append hprefix tailTrace_392097
  have hstable : (prefixWord ++ tailWord_392097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392097).length < 2 ^ (prefixWord ++ tailWord_392097).sum := by decide
  have hdescent : baseEnd_392097 < baseStart_392097 := by decide
  rcases family_descends (prefixWord ++ tailWord_392097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392170 : List Nat := [3, 1, 3, 1, 2, 2, 2, 2, 2, 1, 4]
def baseStart_392170 : Nat := 118140960795 + 392170 * 2 ^ 59
def prefixEnd_392170 : Nat := 4983230072969 + 3 ^ 40 * 392170 * 2
def baseEnd_392170 : Nat := 201371708273835866771449

theorem tailTrace_392170 : CollatzResearch.WordTrace tailWord_392170 prefixEnd_392170 201371708273835866771449 := by
  unfold tailWord_392170
  simp only [CollatzResearch.WordTrace]
  refine ⟨3575903747310635537193491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9535743326161694765849309 3575903747310635537193491)
  ·
    refine ⟨5363855620965953305790237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3575903747310635537193491 5363855620965953305790237)
    ·
      refine ⟨2011445857862232489671339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5363855620965953305790237 2011445857862232489671339)
      ·
        refine ⟨3017168786793348734507009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2011445857862232489671339 3017168786793348734507009)
        ·
          refine ⟨2262876590095011550880257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3017168786793348734507009 2262876590095011550880257)
          ·
            refine ⟨1697157442571258663160193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2262876590095011550880257 1697157442571258663160193)
            ·
              refine ⟨1272868081928443997370145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1697157442571258663160193 1272868081928443997370145)
              ·
                refine ⟨954651061446332998027609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1272868081928443997370145 954651061446332998027609)
                ·
                  refine ⟨715988296084749748520707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 954651061446332998027609 715988296084749748520707)
                  ·
                    refine ⟨1073982444127124622781061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 715988296084749748520707 1073982444127124622781061)
                    ·
                      refine ⟨201371708273835866771449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1073982444127124622781061 201371708273835866771449)
                      ·
                        rfl

theorem cell23_392170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_392170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_392170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_392170 prefixEnd_392170 := by exact prefixLift 392170
  have htrace : WordTrace (prefixWord ++ tailWord_392170) baseStart_392170 baseEnd_392170 := by
    simpa [prefixWord, tailWord_392170, baseEnd_392170] using wordTrace_append hprefix tailTrace_392170
  have hstable : (prefixWord ++ tailWord_392170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392170).length < 2 ^ (prefixWord ++ tailWord_392170).sum := by decide
  have hdescent : baseEnd_392170 < baseStart_392170 := by decide
  rcases family_descends (prefixWord ++ tailWord_392170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392244 : List Nat := [2, 5, 1, 2, 1, 2, 3, 1, 6]
def baseStart_392244 : Nat := 118140960795 + 392244 * 2 ^ 59
def prefixEnd_392244 : Nat := 4983230072969 + 3 ^ 40 * 392244 * 2
def baseEnd_392244 : Nat := 22378856204696508582901

theorem tailTrace_392244 : CollatzResearch.WordTrace tailWord_392244 prefixEnd_392244 22378856204696508582901 := by
  unfold tailWord_392244
  simp only [CollatzResearch.WordTrace]
  refine ⟨7153156995487226393483893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9537542660649635191311857 7153156995487226393483893)
  ·
    refine ⟨670608468326927474389115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7153156995487226393483893 670608468326927474389115)
    ·
      refine ⟨1005912702490391211583673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 670608468326927474389115 1005912702490391211583673)
      ·
        refine ⟨754434526867793408687755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1005912702490391211583673 754434526867793408687755)
        ·
          refine ⟨1131651790301690113031633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 754434526867793408687755 1131651790301690113031633)
          ·
            refine ⟨848738842726267584773725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1131651790301690113031633 848738842726267584773725)
            ·
              refine ⟨318277066022350344290147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 848738842726267584773725 318277066022350344290147)
              ·
                refine ⟨477415599033525516435221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 318277066022350344290147 477415599033525516435221)
                ·
                  refine ⟨22378856204696508582901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 477415599033525516435221 22378856204696508582901)
                  ·
                    rfl

theorem cell23_392244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 3, 1, 6].length) (baseStart_392244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_392244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_392244 prefixEnd_392244 := by exact prefixLift 392244
  have htrace : WordTrace (prefixWord ++ tailWord_392244) baseStart_392244 baseEnd_392244 := by
    simpa [prefixWord, tailWord_392244, baseEnd_392244] using wordTrace_append hprefix tailTrace_392244
  have hstable : (prefixWord ++ tailWord_392244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392244).length < 2 ^ (prefixWord ++ tailWord_392244).sum := by decide
  have hdescent : baseEnd_392244 < baseStart_392244 := by decide
  rcases family_descends (prefixWord ++ tailWord_392244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392254 : List Nat := [4, 2, 1, 3, 1, 1, 2, 2, 3, 1, 3]
def baseStart_392254 : Nat := 118140960795 + 392254 * 2 ^ 59
def prefixEnd_392254 : Nat := 4983230072969 + 3 ^ 40 * 392254 * 2
def baseEnd_392254 : Nat := 201414840648813538121063

theorem tailTrace_392254 : CollatzResearch.WordTrace tailWord_392254 prefixEnd_392254 201414840648813538121063 := by
  unfold tailWord_392254
  simp only [CollatzResearch.WordTrace]
  refine ⟨1788334840117278061853977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9537785813958816329887877 1788334840117278061853977)
  ·
    refine ⟨1341251130087958546390483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1788334840117278061853977 1341251130087958546390483)
    ·
      refine ⟨2011876695131937819585725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1341251130087958546390483 2011876695131937819585725)
      ·
        refine ⟨754453760674476682344647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2011876695131937819585725 754453760674476682344647)
        ·
          refine ⟨1131680641011715023516971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 754453760674476682344647 1131680641011715023516971)
          ·
            refine ⟨1697520961517572535275457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1131680641011715023516971 1697520961517572535275457)
            ·
              refine ⟨1273140721138179401456593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1697520961517572535275457 1273140721138179401456593)
              ·
                refine ⟨954855540853634551092445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1273140721138179401456593 954855540853634551092445)
                ·
                  refine ⟨358070827820112956659667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 954855540853634551092445 358070827820112956659667)
                  ·
                    refine ⟨537106241730169434989501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 358070827820112956659667 537106241730169434989501)
                    ·
                      refine ⟨201414840648813538121063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 537106241730169434989501 201414840648813538121063)
                      ·
                        rfl

theorem cell23_392254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_392254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_392254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_392254 prefixEnd_392254 := by exact prefixLift 392254
  have htrace : WordTrace (prefixWord ++ tailWord_392254) baseStart_392254 baseEnd_392254 := by
    simpa [prefixWord, tailWord_392254, baseEnd_392254] using wordTrace_append hprefix tailTrace_392254
  have hstable : (prefixWord ++ tailWord_392254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392254).length < 2 ^ (prefixWord ++ tailWord_392254).sum := by decide
  have hdescent : baseEnd_392254 < baseStart_392254 := by decide
  rcases family_descends (prefixWord ++ tailWord_392254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392270 : List Nat := [4, 1, 1, 1, 1, 3, 1, 1, 6, 4]
def baseStart_392270 : Nat := 118140960795 + 392270 * 2 ^ 59
def prefixEnd_392270 : Nat := 4983230072969 + 3 ^ 40 * 392270 * 2
def baseEnd_392270 : Nat := 67141018779761825173663

theorem tailTrace_392270 : CollatzResearch.WordTrace tailWord_392270 prefixEnd_392270 67141018779761825173663 := by
  unfold tailWord_392270
  simp only [CollatzResearch.WordTrace]
  refine ⟨1788407786110032403426783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9538174859253506151609509 1788407786110032403426783)
  ·
    refine ⟨2682611679165048605140175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1788407786110032403426783 2682611679165048605140175)
    ·
      refine ⟨4023917518747572907710263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2682611679165048605140175 4023917518747572907710263)
      ·
        refine ⟨6035876278121359361565395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4023917518747572907710263 6035876278121359361565395)
        ·
          refine ⟨9053814417182039042348093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6035876278121359361565395 9053814417182039042348093)
          ·
            refine ⟨3395180406443264640880535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9053814417182039042348093 3395180406443264640880535)
            ·
              refine ⟨5092770609664896961320803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3395180406443264640880535 5092770609664896961320803)
              ·
                refine ⟨7639155914497345441981205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5092770609664896961320803 7639155914497345441981205)
                ·
                  refine ⟨358085433492063067592869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7639155914497345441981205 358085433492063067592869)
                  ·
                    refine ⟨67141018779761825173663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 358085433492063067592869 67141018779761825173663)
                    ·
                      rfl

theorem cell23_392270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 6, 4].length) (baseStart_392270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_392270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_392270 prefixEnd_392270 := by exact prefixLift 392270
  have htrace : WordTrace (prefixWord ++ tailWord_392270) baseStart_392270 baseEnd_392270 := by
    simpa [prefixWord, tailWord_392270, baseEnd_392270] using wordTrace_append hprefix tailTrace_392270
  have hstable : (prefixWord ++ tailWord_392270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392270).length < 2 ^ (prefixWord ++ tailWord_392270).sum := by decide
  have hdescent : baseEnd_392270 < baseStart_392270 := by decide
  rcases family_descends (prefixWord ++ tailWord_392270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392280 : List Nat := [2, 1, 2, 2, 1, 3, 4, 1, 1, 1, 5]
def baseStart_392280 : Nat := 118140960795 + 392280 * 2 ^ 59
def prefixEnd_392280 : Nat := 4983230072969 + 3 ^ 40 * 392280 * 2
def baseEnd_392280 : Nat := 201428191145830436395943

theorem tailTrace_392280 : CollatzResearch.WordTrace tailWord_392280 prefixEnd_392280 201428191145830436395943 := by
  unfold tailWord_392280
  simp only [CollatzResearch.WordTrace]
  refine ⟨7153813509422015467639147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9538418012562687290185529 7153813509422015467639147)
  ·
    refine ⟨10730720264133023201458721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7153813509422015467639147 10730720264133023201458721)
    ·
      refine ⟨8048040198099767401094041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10730720264133023201458721 8048040198099767401094041)
      ·
        refine ⟨6036030148574825550820531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8048040198099767401094041 6036030148574825550820531)
        ·
          refine ⟨9054045222862238326230797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6036030148574825550820531 9054045222862238326230797)
          ·
            refine ⟨3395266958573339372336549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9054045222862238326230797 3395266958573339372336549)
            ·
              refine ⟨636612554732501132313103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3395266958573339372336549 636612554732501132313103)
              ·
                refine ⟨954918832098751698469655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 636612554732501132313103 954918832098751698469655)
                ·
                  refine ⟨1432378248148127547704483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 954918832098751698469655 1432378248148127547704483)
                  ·
                    refine ⟨2148567372222191321556725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1432378248148127547704483 2148567372222191321556725)
                    ·
                      refine ⟨201428191145830436395943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2148567372222191321556725 201428191145830436395943)
                      ·
                        rfl

theorem cell23_392280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 1, 1, 1, 5].length) (baseStart_392280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_392280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_392280 prefixEnd_392280 := by exact prefixLift 392280
  have htrace : WordTrace (prefixWord ++ tailWord_392280) baseStart_392280 baseEnd_392280 := by
    simpa [prefixWord, tailWord_392280, baseEnd_392280] using wordTrace_append hprefix tailTrace_392280
  have hstable : (prefixWord ++ tailWord_392280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392280).length < 2 ^ (prefixWord ++ tailWord_392280).sum := by decide
  have hdescent : baseEnd_392280 < baseStart_392280 := by decide
  rcases family_descends (prefixWord ++ tailWord_392280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392303 : List Nat := [1, 1, 2, 1, 3, 3, 1, 1, 2, 2, 6]
def baseStart_392303 : Nat := 118140960795 + 392303 * 2 ^ 59
def prefixEnd_392303 : Nat := 4983230072969 + 3 ^ 40 * 392303 * 2
def baseEnd_392303 : Nat := 201440001200883846408337

theorem tailTrace_392303 : CollatzResearch.WordTrace tailWord_392303 prefixEnd_392303 201440001200883846408337 := by
  unfold tailWord_392303
  simp only [CollatzResearch.WordTrace]
  refine ⟨14308465897760705863365563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9538977265173803908910375 14308465897760705863365563)
  ·
    refine ⟨21462698846641058795048345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14308465897760705863365563 21462698846641058795048345)
    ·
      refine ⟨16097024134980794096286259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21462698846641058795048345 16097024134980794096286259)
      ·
        refine ⟨24145536202471191144429389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16097024134980794096286259 24145536202471191144429389)
        ·
          refine ⟨9054576075926696679161021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24145536202471191144429389 9054576075926696679161021)
          ·
            refine ⟨3395466028472511254685383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9054576075926696679161021 3395466028472511254685383)
            ·
              refine ⟨5093199042708766882028075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3395466028472511254685383 5093199042708766882028075)
              ·
                refine ⟨7639798564063150323042113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5093199042708766882028075 7639798564063150323042113)
                ·
                  refine ⟨5729848923047362742281585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7639798564063150323042113 5729848923047362742281585)
                  ·
                    refine ⟨4297386692285522056711189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5729848923047362742281585 4297386692285522056711189)
                    ·
                      refine ⟨201440001200883846408337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4297386692285522056711189 201440001200883846408337)
                      ·
                        rfl

theorem cell23_392303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 2, 6].length) (baseStart_392303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_392303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_392303 prefixEnd_392303 := by exact prefixLift 392303
  have htrace : WordTrace (prefixWord ++ tailWord_392303) baseStart_392303 baseEnd_392303 := by
    simpa [prefixWord, tailWord_392303, baseEnd_392303] using wordTrace_append hprefix tailTrace_392303
  have hstable : (prefixWord ++ tailWord_392303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392303).length < 2 ^ (prefixWord ++ tailWord_392303).sum := by decide
  have hdescent : baseEnd_392303 < baseStart_392303 := by decide
  rcases family_descends (prefixWord ++ tailWord_392303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392344 : List Nat := [2, 1, 2, 4, 2, 1, 1, 4, 2, 1, 3]
def baseStart_392344 : Nat := 118140960795 + 392344 * 2 ^ 59
def prefixEnd_392344 : Nat := 4983230072969 + 3 ^ 40 * 392344 * 2
def baseEnd_392344 : Nat := 201461053907718185995649

theorem tailTrace_392344 : CollatzResearch.WordTrace tailWord_392344 prefixEnd_392344 201461053907718185995649 := by
  unfold tailWord_392344
  simp only [CollatzResearch.WordTrace]
  refine ⟨7154980645306084932804043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9539974193741446577072057 7154980645306084932804043)
  ·
    refine ⟨10732470967959127399206065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7154980645306084932804043 10732470967959127399206065)
    ·
      refine ⟨8049353225969345549404549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10732470967959127399206065 8049353225969345549404549)
      ·
        refine ⟨1509253729869252290513353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8049353225969345549404549 1509253729869252290513353)
        ·
          refine ⟨1131940297401939217885015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1509253729869252290513353 1131940297401939217885015)
          ·
            refine ⟨1697910446102908826827523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1131940297401939217885015 1697910446102908826827523)
            ·
              refine ⟨2546865669154363240241285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1697910446102908826827523 2546865669154363240241285)
              ·
                refine ⟨477537312966443107545241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2546865669154363240241285 477537312966443107545241)
                ·
                  refine ⟨358152984724832330658931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 477537312966443107545241 358152984724832330658931)
                  ·
                    refine ⟨537229477087248495988397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 358152984724832330658931 537229477087248495988397)
                    ·
                      refine ⟨201461053907718185995649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 537229477087248495988397 201461053907718185995649)
                      ·
                        rfl

theorem cell23_392344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_392344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_392344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_392344 prefixEnd_392344 := by exact prefixLift 392344
  have htrace : WordTrace (prefixWord ++ tailWord_392344) baseStart_392344 baseEnd_392344 := by
    simpa [prefixWord, tailWord_392344, baseEnd_392344] using wordTrace_append hprefix tailTrace_392344
  have hstable : (prefixWord ++ tailWord_392344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392344).length < 2 ^ (prefixWord ++ tailWord_392344).sum := by decide
  have hdescent : baseEnd_392344 < baseStart_392344 := by decide
  rcases family_descends (prefixWord ++ tailWord_392344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392367 : List Nat := [1, 1, 2, 1, 2, 3, 3, 3, 1, 4, 2]
def baseStart_392367 : Nat := 118140960795 + 392367 * 2 ^ 59
def prefixEnd_392367 : Nat := 4983230072969 + 3 ^ 40 * 392367 * 2
def baseEnd_392367 : Nat := 201472863962771596008043

theorem tailTrace_392367 : CollatzResearch.WordTrace tailWord_392367 prefixEnd_392367 201472863962771596008043 := by
  unfold tailWord_392367
  simp only [CollatzResearch.WordTrace]
  refine ⟨14310800169528844793695355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9540533446352563195796903 14310800169528844793695355)
  ·
    refine ⟨21466200254293267190543033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14310800169528844793695355 21466200254293267190543033)
    ·
      refine ⟨16099650190719950392907275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21466200254293267190543033 16099650190719950392907275)
      ·
        refine ⟨24149475286079925589360913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16099650190719950392907275 24149475286079925589360913)
        ·
          refine ⟨18112106464559944192020685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24149475286079925589360913 18112106464559944192020685)
          ·
            refine ⟨6792039924209979072007757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18112106464559944192020685 6792039924209979072007757)
            ·
              refine ⟨2547014971578742152002909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6792039924209979072007757 2547014971578742152002909)
              ·
                refine ⟨955130614342028307001091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2547014971578742152002909 955130614342028307001091)
                ·
                  refine ⟨1432695921513042460501637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 955130614342028307001091 1432695921513042460501637)
                  ·
                    refine ⟨268630485283695461344057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1432695921513042460501637 268630485283695461344057)
                    ·
                      refine ⟨201472863962771596008043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 268630485283695461344057 201472863962771596008043)
                      ·
                        rfl

theorem cell23_392367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 3, 1, 4, 2].length) (baseStart_392367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_392367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_392367 prefixEnd_392367 := by exact prefixLift 392367
  have htrace : WordTrace (prefixWord ++ tailWord_392367) baseStart_392367 baseEnd_392367 := by
    simpa [prefixWord, tailWord_392367, baseEnd_392367] using wordTrace_append hprefix tailTrace_392367
  have hstable : (prefixWord ++ tailWord_392367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392367).length < 2 ^ (prefixWord ++ tailWord_392367).sum := by decide
  have hdescent : baseEnd_392367 < baseStart_392367 := by decide
  rcases family_descends (prefixWord ++ tailWord_392367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392407 : List Nat := [1, 1, 3, 2, 1, 2, 4, 4, 5]
def baseStart_392407 : Nat := 118140960795 + 392407 * 2 ^ 59
def prefixEnd_392407 : Nat := 4983230072969 + 3 ^ 40 * 392407 * 2
def baseEnd_392407 : Nat := 22388155909883493278651

theorem tailTrace_392407 : CollatzResearch.WordTrace tailWord_392407 prefixEnd_392407 22388155909883493278651 := by
  unfold tailWord_392407
  simp only [CollatzResearch.WordTrace]
  refine ⟨14312259089383931625151475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9541506059589287750100983 14312259089383931625151475)
  ·
    refine ⟨21468388634075897437727213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14312259089383931625151475 21468388634075897437727213)
    ·
      refine ⟨8050645737778461539147705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21468388634075897437727213 8050645737778461539147705)
      ·
        refine ⟨6037984303333846154360779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8050645737778461539147705 6037984303333846154360779)
        ·
          refine ⟨9056976455000769231541169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6037984303333846154360779 9056976455000769231541169)
          ·
            refine ⟨6792732341250576923655877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9056976455000769231541169 6792732341250576923655877)
            ·
              refine ⟨1273637313984483173185477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6792732341250576923655877 1273637313984483173185477)
              ·
                refine ⟨238806996372090594972277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1273637313984483173185477 238806996372090594972277)
                ·
                  refine ⟨22388155909883493278651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 238806996372090594972277 22388155909883493278651)
                  ·
                    rfl

theorem cell23_392407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 4, 5].length) (baseStart_392407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_392407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_392407 prefixEnd_392407 := by exact prefixLift 392407
  have htrace : WordTrace (prefixWord ++ tailWord_392407) baseStart_392407 baseEnd_392407 := by
    simpa [prefixWord, tailWord_392407, baseEnd_392407] using wordTrace_append hprefix tailTrace_392407
  have hstable : (prefixWord ++ tailWord_392407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392407).length < 2 ^ (prefixWord ++ tailWord_392407).sum := by decide
  have hdescent : baseEnd_392407 < baseStart_392407 := by decide
  rcases family_descends (prefixWord ++ tailWord_392407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392417 : List Nat := [1, 2, 3, 1, 3, 2, 2, 1, 2, 3, 3]
def baseStart_392417 : Nat := 118140960795 + 392417 * 2 ^ 59
def prefixEnd_392417 : Nat := 4983230072969 + 3 ^ 40 * 392417 * 2
def baseEnd_392417 : Nat := 201498537995496400382813

theorem tailTrace_392417 : CollatzResearch.WordTrace tailWord_392417 prefixEnd_392417 201498537995496400382813 := by
  unfold tailWord_392417
  simp only [CollatzResearch.WordTrace]
  refine ⟨14312623819347703333015505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9541749212898468888677003 14312623819347703333015505)
  ·
    refine ⟨10734467864510777499761629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14312623819347703333015505 10734467864510777499761629)
    ·
      refine ⟨4025425449191541562410611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10734467864510777499761629 4025425449191541562410611)
      ·
        refine ⟨6038138173787312343615917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4025425449191541562410611 6038138173787312343615917)
        ·
          refine ⟨2264301815170242128855969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6038138173787312343615917 2264301815170242128855969)
          ·
            refine ⟨1698226361377681596641977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2264301815170242128855969 1698226361377681596641977)
            ·
              refine ⟨1273669771033261197481483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1698226361377681596641977 1273669771033261197481483)
              ·
                refine ⟨1910504656549891796222225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1273669771033261197481483 1910504656549891796222225)
                ·
                  refine ⟨1432878492412418847166669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1910504656549891796222225 1432878492412418847166669)
                  ·
                    refine ⟨537329434654657067687501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1432878492412418847166669 537329434654657067687501)
                    ·
                      refine ⟨201498537995496400382813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 537329434654657067687501 201498537995496400382813)
                      ·
                        rfl

theorem cell23_392417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 1, 2, 3, 3].length) (baseStart_392417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_392417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_392417 prefixEnd_392417 := by exact prefixLift 392417
  have htrace : WordTrace (prefixWord ++ tailWord_392417) baseStart_392417 baseEnd_392417 := by
    simpa [prefixWord, tailWord_392417, baseEnd_392417] using wordTrace_append hprefix tailTrace_392417
  have hstable : (prefixWord ++ tailWord_392417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392417).length < 2 ^ (prefixWord ++ tailWord_392417).sum := by decide
  have hdescent : baseEnd_392417 < baseStart_392417 := by decide
  rcases family_descends (prefixWord ++ tailWord_392417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392420 : List Nat := [2, 3, 1, 1, 1, 2, 3, 2, 1, 7]
def baseStart_392420 : Nat := 118140960795 + 392420 * 2 ^ 59
def prefixEnd_392420 : Nat := 4983230072969 + 3 ^ 40 * 392420 * 2
def baseEnd_392420 : Nat := 67166692812486629548433

theorem tailTrace_392420 : CollatzResearch.WordTrace tailWord_392420 prefixEnd_392420 67166692812486629548433 := by
  unfold tailWord_392420
  simp only [CollatzResearch.WordTrace]
  refine ⟨7156366619168417422687357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9541822158891223230249809 7156366619168417422687357)
  ·
    refine ⟨2683637482188156533507759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7156366619168417422687357 2683637482188156533507759)
    ·
      refine ⟨4025456223282234800261639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2683637482188156533507759 4025456223282234800261639)
      ·
        refine ⟨6038184334923352200392459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4025456223282234800261639 6038184334923352200392459)
        ·
          refine ⟨9057276502385028300588689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6038184334923352200392459 9057276502385028300588689)
          ·
            refine ⟨6792957376788771225441517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9057276502385028300588689 6792957376788771225441517)
            ·
              refine ⟨2547359016295789209540569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6792957376788771225441517 2547359016295789209540569)
              ·
                refine ⟨1910519262221841907155427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2547359016295789209540569 1910519262221841907155427)
                ·
                  refine ⟨2865778893332762860733141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1910519262221841907155427 2865778893332762860733141)
                  ·
                    refine ⟨67166692812486629548433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2865778893332762860733141 67166692812486629548433)
                    ·
                      rfl

theorem cell23_392420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 2, 1, 7].length) (baseStart_392420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_392420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_392420 prefixEnd_392420 := by exact prefixLift 392420
  have htrace : WordTrace (prefixWord ++ tailWord_392420) baseStart_392420 baseEnd_392420 := by
    simpa [prefixWord, tailWord_392420, baseEnd_392420] using wordTrace_append hprefix tailTrace_392420
  have hstable : (prefixWord ++ tailWord_392420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392420).length < 2 ^ (prefixWord ++ tailWord_392420).sum := by decide
  have hdescent : baseEnd_392420 < baseStart_392420 := by decide
  rcases family_descends (prefixWord ++ tailWord_392420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392457 : List Nat := [1, 2, 1, 1, 3, 3, 3, 2, 2, 1, 4]
def baseStart_392457 : Nat := 118140960795 + 392457 * 2 ^ 59
def prefixEnd_392457 : Nat := 4983230072969 + 3 ^ 40 * 392457 * 2
def baseEnd_392457 : Nat := 201519077221676243882629

theorem tailTrace_392457 : CollatzResearch.WordTrace tailWord_392457 prefixEnd_392457 201519077221676243882629 := by
  unfold tailWord_392457
  simp only [CollatzResearch.WordTrace]
  refine ⟨14314082739202790164471625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9542721826135193442981083 14314082739202790164471625)
  ·
    refine ⟨10735562054402092623353719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14314082739202790164471625 10735562054402092623353719)
    ·
      refine ⟨16103343081603138935030579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10735562054402092623353719 16103343081603138935030579)
      ·
        refine ⟨24155014622404708402545869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16103343081603138935030579 24155014622404708402545869)
        ·
          refine ⟨9058130483401765650954701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24155014622404708402545869 9058130483401765650954701)
          ·
            refine ⟨3396798931275662119108013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9058130483401765650954701 3396798931275662119108013)
            ·
              refine ⟨1273799599228373294665505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3396798931275662119108013 1273799599228373294665505)
              ·
                refine ⟨955349699421279970999129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1273799599228373294665505 955349699421279970999129)
                ·
                  refine ⟨716512274565959978249347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 955349699421279970999129 716512274565959978249347)
                  ·
                    refine ⟨1074768411848939967374021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 716512274565959978249347 1074768411848939967374021)
                    ·
                      refine ⟨201519077221676243882629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1074768411848939967374021 201519077221676243882629)
                      ·
                        rfl

theorem cell23_392457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 2, 2, 1, 4].length) (baseStart_392457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_392457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_392457 prefixEnd_392457 := by exact prefixLift 392457
  have htrace : WordTrace (prefixWord ++ tailWord_392457) baseStart_392457 baseEnd_392457 := by
    simpa [prefixWord, tailWord_392457, baseEnd_392457] using wordTrace_append hprefix tailTrace_392457
  have hstable : (prefixWord ++ tailWord_392457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392457).length < 2 ^ (prefixWord ++ tailWord_392457).sum := by decide
  have hdescent : baseEnd_392457 < baseStart_392457 := by decide
  rcases family_descends (prefixWord ++ tailWord_392457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392551 : List Nat := [1, 1, 5, 1, 4, 1, 1, 1, 1, 5, 2]
def baseStart_392551 : Nat := 118140960795 + 392551 * 2 ^ 59
def prefixEnd_392551 : Nat := 4983230072969 + 3 ^ 40 * 392551 * 2
def baseEnd_392551 : Nat := 201567344403198876107197

theorem tailTrace_392551 : CollatzResearch.WordTrace tailWord_392551 prefixEnd_392551 201567344403198876107197 := by
  unfold tailWord_392551
  simp only [CollatzResearch.WordTrace]
  refine ⟨14317511200862244218393507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9545007467241496145595671 14317511200862244218393507)
  ·
    refine ⟨21476266801293366327590261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14317511200862244218393507 21476266801293366327590261)
    ·
      refine ⟨2013400012621253093211587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21476266801293366327590261 2013400012621253093211587)
      ·
        refine ⟨3020100018931879639817381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2013400012621253093211587 3020100018931879639817381)
        ·
          refine ⟨566268753549727432465759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3020100018931879639817381 566268753549727432465759)
          ·
            refine ⟨849403130324591148698639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 566268753549727432465759 849403130324591148698639)
            ·
              refine ⟨1274104695486886723047959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 849403130324591148698639 1274104695486886723047959)
              ·
                refine ⟨1911157043230330084571939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1274104695486886723047959 1911157043230330084571939)
                ·
                  refine ⟨2866735564845495126857909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1911157043230330084571939 2866735564845495126857909)
                  ·
                    refine ⟨268756459204265168142929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2866735564845495126857909 268756459204265168142929)
                    ·
                      refine ⟨201567344403198876107197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 268756459204265168142929 201567344403198876107197)
                      ·
                        rfl

theorem cell23_392551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 1, 1, 5, 2].length) (baseStart_392551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_392551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_392551 prefixEnd_392551 := by exact prefixLift 392551
  have htrace : WordTrace (prefixWord ++ tailWord_392551) baseStart_392551 baseEnd_392551 := by
    simpa [prefixWord, tailWord_392551, baseEnd_392551] using wordTrace_append hprefix tailTrace_392551
  have hstable : (prefixWord ++ tailWord_392551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392551).length < 2 ^ (prefixWord ++ tailWord_392551).sum := by decide
  have hdescent : baseEnd_392551 < baseStart_392551 := by decide
  rcases family_descends (prefixWord ++ tailWord_392551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392567 : List Nat := [1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 5]
def baseStart_392567 : Nat := 118140960795 + 392567 * 2 ^ 59
def prefixEnd_392567 : Nat := 4983230072969 + 3 ^ 40 * 392567 * 2
def baseEnd_392567 : Nat := 201575560093670813507123

theorem tailTrace_392567 : CollatzResearch.WordTrace tailWord_392567 prefixEnd_392567 201575560093670813507123 := by
  unfold tailWord_392567
  simp only [CollatzResearch.WordTrace]
  refine ⟨14318094768804278950975955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9545396512536185967317303 14318094768804278950975955)
  ·
    refine ⟨21477142153206418426463933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14318094768804278950975955 21477142153206418426463933)
    ·
      refine ⟨8053928307452406909923975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21477142153206418426463933 8053928307452406909923975)
      ·
        refine ⟨12080892461178610364885963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8053928307452406909923975 12080892461178610364885963)
        ·
          refine ⟨18121338691767915547328945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12080892461178610364885963 18121338691767915547328945)
          ·
            refine ⟨13591004018825936660496709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18121338691767915547328945 13591004018825936660496709)
            ·
              refine ⟨2548313253529863123843133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13591004018825936660496709 2548313253529863123843133)
              ·
                refine ⟨955617470073698671441175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2548313253529863123843133 955617470073698671441175)
                ·
                  refine ⟨1433426205110548007161763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 955617470073698671441175 1433426205110548007161763)
                  ·
                    refine ⟨2150139307665822010742645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1433426205110548007161763 2150139307665822010742645)
                    ·
                      refine ⟨201575560093670813507123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2150139307665822010742645 201575560093670813507123)
                      ·
                        rfl

theorem cell23_392567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 5].length) (baseStart_392567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_392567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_392567 prefixEnd_392567 := by exact prefixLift 392567
  have htrace : WordTrace (prefixWord ++ tailWord_392567) baseStart_392567 baseEnd_392567 := by
    simpa [prefixWord, tailWord_392567, baseEnd_392567] using wordTrace_append hprefix tailTrace_392567
  have hstable : (prefixWord ++ tailWord_392567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392567).length < 2 ^ (prefixWord ++ tailWord_392567).sum := by decide
  have hdescent : baseEnd_392567 < baseStart_392567 := by decide
  rcases family_descends (prefixWord ++ tailWord_392567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392581 : List Nat := [1, 3, 1, 1, 3, 1, 3, 3, 3, 2, 2]
def baseStart_392581 : Nat := 118140960795 + 392581 * 2 ^ 59
def prefixEnd_392581 : Nat := 4983230072969 + 3 ^ 40 * 392581 * 2
def baseEnd_392581 : Nat := 201582748822833758732059

theorem tailTrace_392581 : CollatzResearch.WordTrace tailWord_392581 prefixEnd_392581 201582748822833758732059 := by
  unfold tailWord_392581
  simp only [CollatzResearch.WordTrace]
  refine ⟨14318605390753559341985597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9545736927169039561323731 14318605390753559341985597)
  ·
    refine ⟨5369477021532584753244599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14318605390753559341985597 5369477021532584753244599)
    ·
      refine ⟨8054215532298877129866899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5369477021532584753244599 8054215532298877129866899)
      ·
        refine ⟨12081323298448315694800349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8054215532298877129866899 12081323298448315694800349)
        ·
          refine ⟨4530496236918118385550131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12081323298448315694800349 4530496236918118385550131)
          ·
            refine ⟨6795744355377177578325197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4530496236918118385550131 6795744355377177578325197)
            ·
              refine ⟨2548404133266441591871949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6795744355377177578325197 2548404133266441591871949)
              ·
                refine ⟨955651549974915596951981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2548404133266441591871949 955651549974915596951981)
                ·
                  refine ⟨358369331240593348856993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 955651549974915596951981 358369331240593348856993)
                  ·
                    refine ⟨268776998430445011642745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 358369331240593348856993 268776998430445011642745)
                    ·
                      refine ⟨201582748822833758732059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 268776998430445011642745 201582748822833758732059)
                      ·
                        rfl

theorem cell23_392581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 3, 3, 2, 2].length) (baseStart_392581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_392581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_392581 prefixEnd_392581 := by exact prefixLift 392581
  have htrace : WordTrace (prefixWord ++ tailWord_392581) baseStart_392581 baseEnd_392581 := by
    simpa [prefixWord, tailWord_392581, baseEnd_392581] using wordTrace_append hprefix tailTrace_392581
  have hstable : (prefixWord ++ tailWord_392581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392581).length < 2 ^ (prefixWord ++ tailWord_392581).sum := by decide
  have hdescent : baseEnd_392581 < baseStart_392581 := by decide
  rcases family_descends (prefixWord ++ tailWord_392581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392584 : List Nat := [2, 1, 3, 3, 1, 3, 1, 2, 1, 1, 5]
def baseStart_392584 : Nat := 118140960795 + 392584 * 2 ^ 59
def prefixEnd_392584 : Nat := 4983230072969 + 3 ^ 40 * 392584 * 2
def baseEnd_392584 : Nat := 201584289264797246994545

theorem tailTrace_392584 : CollatzResearch.WordTrace tailWord_392584 prefixEnd_392584 201584289264797246994545 := by
  unfold tailWord_392584
  simp only [CollatzResearch.WordTrace]
  refine ⟨7159357404871345427172403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9545809873161793902896537 7159357404871345427172403)
  ·
    refine ⟨10739036107307018140758605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7159357404871345427172403 10739036107307018140758605)
    ·
      refine ⟨4027138540240131802784477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10739036107307018140758605 4027138540240131802784477)
      ·
        refine ⟨1510176952590049426044179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4027138540240131802784477 1510176952590049426044179)
        ·
          refine ⟨2265265428885074139066269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1510176952590049426044179 2265265428885074139066269)
          ·
            refine ⟨849474535831902802149851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2265265428885074139066269 849474535831902802149851)
            ·
              refine ⟨1274211803747854203224777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 849474535831902802149851 1274211803747854203224777)
              ·
                refine ⟨955658852810890652418583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1274211803747854203224777 955658852810890652418583)
                ·
                  refine ⟨1433488279216335978627875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 955658852810890652418583 1433488279216335978627875)
                  ·
                    refine ⟨2150232418824503967941813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1433488279216335978627875 2150232418824503967941813)
                    ·
                      refine ⟨201584289264797246994545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2150232418824503967941813 201584289264797246994545)
                      ·
                        rfl

theorem cell23_392584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_392584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_392584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_392584 prefixEnd_392584 := by exact prefixLift 392584
  have htrace : WordTrace (prefixWord ++ tailWord_392584) baseStart_392584 baseEnd_392584 := by
    simpa [prefixWord, tailWord_392584, baseEnd_392584] using wordTrace_append hprefix tailTrace_392584
  have hstable : (prefixWord ++ tailWord_392584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392584).length < 2 ^ (prefixWord ++ tailWord_392584).sum := by decide
  have hdescent : baseEnd_392584 < baseStart_392584 := by decide
  rcases family_descends (prefixWord ++ tailWord_392584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392601 : List Nat := [1, 2, 1, 2, 1, 6, 2, 2, 1, 2, 3]
def baseStart_392601 : Nat := 118140960795 + 392601 * 2 ^ 59
def prefixEnd_392601 : Nat := 4983230072969 + 3 ^ 40 * 392601 * 2
def baseEnd_392601 : Nat := 201593018435923680481967

theorem tailTrace_392601 : CollatzResearch.WordTrace tailWord_392601 prefixEnd_392601 201593018435923680481967 := by
  unfold tailWord_392601
  simp only [CollatzResearch.WordTrace]
  refine ⟨14319334850681102757713657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9546223233787401838475771 14319334850681102757713657)
  ·
    refine ⟨10739501138010827068285243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14319334850681102757713657 10739501138010827068285243)
    ·
      refine ⟨16109251707016240602427865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10739501138010827068285243 16109251707016240602427865)
      ·
        refine ⟨12081938780262180451820899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16109251707016240602427865 12081938780262180451820899)
        ·
          refine ⟨18122908170393270677731349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12081938780262180451820899 18122908170393270677731349)
          ·
            refine ⟨849511320487184563018657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 18122908170393270677731349 849511320487184563018657)
            ·
              refine ⟨637133490365388422263993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 849511320487184563018657 637133490365388422263993)
              ·
                refine ⟨477850117774041316697995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 637133490365388422263993 477850117774041316697995)
                ·
                  refine ⟨716775176661061975046993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 477850117774041316697995 716775176661061975046993)
                  ·
                    refine ⟨537581382495796481285245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 716775176661061975046993 537581382495796481285245)
                    ·
                      refine ⟨201593018435923680481967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 537581382495796481285245 201593018435923680481967)
                      ·
                        rfl

theorem cell23_392601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 2, 1, 2, 3].length) (baseStart_392601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_392601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_392601 prefixEnd_392601 := by exact prefixLift 392601
  have htrace : WordTrace (prefixWord ++ tailWord_392601) baseStart_392601 baseEnd_392601 := by
    simpa [prefixWord, tailWord_392601, baseEnd_392601] using wordTrace_append hprefix tailTrace_392601
  have hstable : (prefixWord ++ tailWord_392601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392601).length < 2 ^ (prefixWord ++ tailWord_392601).sum := by decide
  have hdescent : baseEnd_392601 < baseStart_392601 := by decide
  rcases family_descends (prefixWord ++ tailWord_392601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392631 : List Nat := [1, 1, 3, 1, 3, 2, 2, 4, 2, 1, 3]
def baseStart_392631 : Nat := 118140960795 + 392631 * 2 ^ 59
def prefixEnd_392631 : Nat := 4983230072969 + 3 ^ 40 * 392631 * 2
def baseEnd_392631 : Nat := 201608422855558563106829

theorem tailTrace_392631 : CollatzResearch.WordTrace tailWord_392631 prefixEnd_392631 201608422855558563106829 := by
  unfold tailWord_392631
  simp only [CollatzResearch.WordTrace]
  refine ⟨14320429040572417881305747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9546952693714945254203831 14320429040572417881305747)
  ·
    refine ⟨21480643560858626821958621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14320429040572417881305747 21480643560858626821958621)
    ·
      refine ⟨8055241335321985058234483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21480643560858626821958621 8055241335321985058234483)
      ·
        refine ⟨12082862002982977587351725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8055241335321985058234483 12082862002982977587351725)
        ·
          refine ⟨4531073251118616595256897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12082862002982977587351725 4531073251118616595256897)
          ·
            refine ⟨3398304938338962446442673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4531073251118616595256897 3398304938338962446442673)
            ·
              refine ⟨2548728703754221834832005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3398304938338962446442673 2548728703754221834832005)
              ·
                refine ⟨477886631953916594031001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2548728703754221834832005 477886631953916594031001)
                ·
                  refine ⟨358414973965437445523251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 477886631953916594031001 358414973965437445523251)
                  ·
                    refine ⟨537622460948156168284877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 358414973965437445523251 537622460948156168284877)
                    ·
                      refine ⟨201608422855558563106829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 537622460948156168284877 201608422855558563106829)
                      ·
                        rfl

theorem cell23_392631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 4, 2, 1, 3].length) (baseStart_392631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_392631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_392631 prefixEnd_392631 := by exact prefixLift 392631
  have htrace : WordTrace (prefixWord ++ tailWord_392631) baseStart_392631 baseEnd_392631 := by
    simpa [prefixWord, tailWord_392631, baseEnd_392631] using wordTrace_append hprefix tailTrace_392631
  have hstable : (prefixWord ++ tailWord_392631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392631).length < 2 ^ (prefixWord ++ tailWord_392631).sum := by decide
  have hdescent : baseEnd_392631 < baseStart_392631 := by decide
  rcases family_descends (prefixWord ++ tailWord_392631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392647 : List Nat := [1, 1, 4, 1, 1, 3, 2, 1, 1, 8]
def baseStart_392647 : Nat := 118140960795 + 392647 * 2 ^ 59
def prefixEnd_392647 : Nat := 4983230072969 + 3 ^ 40 * 392647 * 2
def baseEnd_392647 : Nat := 67205546182010166835585

theorem tailTrace_392647 : CollatzResearch.WordTrace tailWord_392647 prefixEnd_392647 67205546182010166835585 := by
  unfold tailWord_392647
  simp only [CollatzResearch.WordTrace]
  refine ⟨14321012608514452613888195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9547341739009635075925463 14321012608514452613888195)
  ·
    refine ⟨21481518912771678920832293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14321012608514452613888195 21481518912771678920832293)
    ·
      refine ⟨4027784796144689797656055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21481518912771678920832293 4027784796144689797656055)
      ·
        refine ⟨6041677194217034696484083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4027784796144689797656055 6041677194217034696484083)
        ·
          refine ⟨9062515791325552044726125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6041677194217034696484083 9062515791325552044726125)
          ·
            refine ⟨3398443421747082016772297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9062515791325552044726125 3398443421747082016772297)
            ·
              refine ⟨2548832566310311512579223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3398443421747082016772297 2548832566310311512579223)
              ·
                refine ⟨3823248849465467268868835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2548832566310311512579223 3823248849465467268868835)
                ·
                  refine ⟨5734873274198200903303253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3823248849465467268868835 5734873274198200903303253)
                  ·
                    refine ⟨67205546182010166835585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 5734873274198200903303253 67205546182010166835585)
                    ·
                      rfl

theorem cell23_392647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 8].length) (baseStart_392647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_392647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_392647 prefixEnd_392647 := by exact prefixLift 392647
  have htrace : WordTrace (prefixWord ++ tailWord_392647) baseStart_392647 baseEnd_392647 := by
    simpa [prefixWord, tailWord_392647, baseEnd_392647] using wordTrace_append hprefix tailTrace_392647
  have hstable : (prefixWord ++ tailWord_392647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392647).length < 2 ^ (prefixWord ++ tailWord_392647).sum := by decide
  have hdescent : baseEnd_392647 < baseStart_392647 := by decide
  rcases family_descends (prefixWord ++ tailWord_392647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392671 : List Nat := [1, 1, 2, 3, 3, 1, 3, 2, 1, 4, 2]
def baseStart_392671 : Nat := 118140960795 + 392671 * 2 ^ 59
def prefixEnd_392671 : Nat := 4983230072969 + 3 ^ 40 * 392671 * 2
def baseEnd_392671 : Nat := 201628962081738406606645

theorem tailTrace_392671 : CollatzResearch.WordTrace tailWord_392671 prefixEnd_392671 201628962081738406606645 := by
  unfold tailWord_392671
  simp only [CollatzResearch.WordTrace]
  refine ⟨14321887960427504712761867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9547925306951669808507911 14321887960427504712761867)
  ·
    refine ⟨21482831940641257069142801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14321887960427504712761867 21482831940641257069142801)
    ·
      refine ⟨16112123955480942801857101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21482831940641257069142801 16112123955480942801857101)
      ·
        refine ⟨6042046483305353550696413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16112123955480942801857101 6042046483305353550696413)
        ·
          refine ⟨2265767431239507581511155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6042046483305353550696413 2265767431239507581511155)
          ·
            refine ⟨3398651146859261372266733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2265767431239507581511155 3398651146859261372266733)
            ·
              refine ⟨1274494180072223014600025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3398651146859261372266733 1274494180072223014600025)
              ·
                refine ⟨955870635054167260950019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1274494180072223014600025 955870635054167260950019)
                ·
                  refine ⟨1433805952581250891425029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 955870635054167260950019 1433805952581250891425029)
                  ·
                    refine ⟨268838616108984542142193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1433805952581250891425029 268838616108984542142193)
                    ·
                      refine ⟨201628962081738406606645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 268838616108984542142193 201628962081738406606645)
                      ·
                        rfl

theorem cell23_392671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 2, 1, 4, 2].length) (baseStart_392671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_392671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_392671 prefixEnd_392671 := by exact prefixLift 392671
  have htrace : WordTrace (prefixWord ++ tailWord_392671) baseStart_392671 baseEnd_392671 := by
    simpa [prefixWord, tailWord_392671, baseEnd_392671] using wordTrace_append hprefix tailTrace_392671
  have hstable : (prefixWord ++ tailWord_392671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392671).length < 2 ^ (prefixWord ++ tailWord_392671).sum := by decide
  have hdescent : baseEnd_392671 < baseStart_392671 := by decide
  rcases family_descends (prefixWord ++ tailWord_392671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392675 : List Nat := [1, 1, 1, 6, 2, 2, 3, 1, 1, 3, 2]
def baseStart_392675 : Nat := 118140960795 + 392675 * 2 ^ 59
def prefixEnd_392675 : Nat := 4983230072969 + 3 ^ 40 * 392675 * 2
def baseEnd_392675 : Nat := 201631016004356390956627

theorem tailTrace_392675 : CollatzResearch.WordTrace tailWord_392675 prefixEnd_392675 201631016004356390956627 := by
  unfold tailWord_392675
  simp only [CollatzResearch.WordTrace]
  refine ⟨14322033852413013395907479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9548022568275342263938319 14322033852413013395907479)
  ·
    refine ⟨21483050778619520093861219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14322033852413013395907479 21483050778619520093861219)
    ·
      refine ⟨32224576167929280140791829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21483050778619520093861219 32224576167929280140791829)
      ·
        refine ⟨1510527007871685006599617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 32224576167929280140791829 1510527007871685006599617)
        ·
          refine ⟨1132895255903763754949713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1510527007871685006599617 1132895255903763754949713)
          ·
            refine ⟨849671441927822816212285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1132895255903763754949713 849671441927822816212285)
            ·
              refine ⟨318626790722933556079607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 849671441927822816212285 318626790722933556079607)
              ·
                refine ⟨477940186084400334119411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 318626790722933556079607 477940186084400334119411)
                ·
                  refine ⟨716910279126600501179117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 477940186084400334119411 716910279126600501179117)
                  ·
                    refine ⟨268841354672475187942169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 716910279126600501179117 268841354672475187942169)
                    ·
                      refine ⟨201631016004356390956627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 268841354672475187942169 201631016004356390956627)
                      ·
                        rfl

theorem cell23_392675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 3, 1, 1, 3, 2].length) (baseStart_392675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_392675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_392675 prefixEnd_392675 := by exact prefixLift 392675
  have htrace : WordTrace (prefixWord ++ tailWord_392675) baseStart_392675 baseEnd_392675 := by
    simpa [prefixWord, tailWord_392675, baseEnd_392675] using wordTrace_append hprefix tailTrace_392675
  have hstable : (prefixWord ++ tailWord_392675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392675).length < 2 ^ (prefixWord ++ tailWord_392675).sum := by decide
  have hdescent : baseEnd_392675 < baseStart_392675 := by decide
  rcases family_descends (prefixWord ++ tailWord_392675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392687 : List Nat := [1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 7]
def baseStart_392687 : Nat := 118140960795 + 392687 * 2 ^ 59
def prefixEnd_392687 : Nat := 4983230072969 + 3 ^ 40 * 392687 * 2
def baseEnd_392687 : Nat := 201637177772210344006571

theorem tailTrace_392687 : CollatzResearch.WordTrace tailWord_392687 prefixEnd_392687 201637177772210344006571 := by
  unfold tailWord_392687
  simp only [CollatzResearch.WordTrace]
  refine ⟨14322471528369539445344315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9548314352246359630229543 14322471528369539445344315)
  ·
    refine ⟨21483707292554309168016473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14322471528369539445344315 21483707292554309168016473)
    ·
      refine ⟨16112780469415731876012355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21483707292554309168016473 16112780469415731876012355)
      ·
        refine ⟨24169170704123597814018533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16112780469415731876012355 24169170704123597814018533)
        ·
          refine ⟨4531719507023174590128475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24169170704123597814018533 4531719507023174590128475)
          ·
            refine ⟨6797579260534761885192713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4531719507023174590128475 6797579260534761885192713)
            ·
              refine ⟨5098184445401071413894535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6797579260534761885192713 5098184445401071413894535)
              ·
                refine ⟨7647276668101607120841803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5098184445401071413894535 7647276668101607120841803)
                ·
                  refine ⟨11470915002152410681262705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7647276668101607120841803 11470915002152410681262705)
                  ·
                    refine ⟨8603186251614308010947029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11470915002152410681262705 8603186251614308010947029)
                    ·
                      refine ⟨201637177772210344006571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 8603186251614308010947029 201637177772210344006571)
                      ·
                        rfl

theorem cell23_392687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 7].length) (baseStart_392687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_392687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_392687 prefixEnd_392687 := by exact prefixLift 392687
  have htrace : WordTrace (prefixWord ++ tailWord_392687) baseStart_392687 baseEnd_392687 := by
    simpa [prefixWord, tailWord_392687, baseEnd_392687] using wordTrace_append hprefix tailTrace_392687
  have hstable : (prefixWord ++ tailWord_392687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392687).length < 2 ^ (prefixWord ++ tailWord_392687).sum := by decide
  have hdescent : baseEnd_392687 < baseStart_392687 := by decide
  rcases family_descends (prefixWord ++ tailWord_392687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392688 : List Nat := [2, 1, 1, 1, 3, 4, 1, 4, 2, 2, 2]
def baseStart_392688 : Nat := 118140960795 + 392688 * 2 ^ 59
def prefixEnd_392688 : Nat := 4983230072969 + 3 ^ 40 * 392688 * 2
def baseEnd_392688 : Nat := 201637691252864840094067

theorem tailTrace_392688 : CollatzResearch.WordTrace tailWord_392688 prefixEnd_392688 201637691252864840094067 := by
  unfold tailWord_392688
  simp only [CollatzResearch.WordTrace]
  refine ⟨7161254000682958308065359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9548338667577277744087145 7161254000682958308065359)
  ·
    refine ⟨10741881001024437462098039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7161254000682958308065359 10741881001024437462098039)
    ·
      refine ⟨16112821501536656193147059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10741881001024437462098039 16112821501536656193147059)
      ·
        refine ⟨24169232252304984289720589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16112821501536656193147059 24169232252304984289720589)
        ·
          refine ⟨9063462094614369108645221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24169232252304984289720589 9063462094614369108645221)
          ·
            refine ⟨1699399142740194207870979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9063462094614369108645221 1699399142740194207870979)
            ·
              refine ⟨2549098714110291311806469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1699399142740194207870979 2549098714110291311806469)
              ·
                refine ⟨477956008895679620963713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2549098714110291311806469 477956008895679620963713)
                ·
                  refine ⟨358467006671759715722785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 477956008895679620963713 358467006671759715722785)
                  ·
                    refine ⟨268850255003819786792089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 358467006671759715722785 268850255003819786792089)
                    ·
                      refine ⟨201637691252864840094067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 268850255003819786792089 201637691252864840094067)
                      ·
                        rfl

theorem cell23_392688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 4, 2, 2, 2].length) (baseStart_392688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_392688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_392688 prefixEnd_392688 := by exact prefixLift 392688
  have htrace : WordTrace (prefixWord ++ tailWord_392688) baseStart_392688 baseEnd_392688 := by
    simpa [prefixWord, tailWord_392688, baseEnd_392688] using wordTrace_append hprefix tailTrace_392688
  have hstable : (prefixWord ++ tailWord_392688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392688).length < 2 ^ (prefixWord ++ tailWord_392688).sum := by decide
  have hdescent : baseEnd_392688 < baseStart_392688 := by decide
  rcases family_descends (prefixWord ++ tailWord_392688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392697 : List Nat := [1, 2, 1, 3, 1, 2, 1, 1, 2, 1, 8]
def baseStart_392697 : Nat := 118140960795 + 392697 * 2 ^ 59
def prefixEnd_392697 : Nat := 4983230072969 + 3 ^ 40 * 392697 * 2
def baseEnd_392697 : Nat := 201642312578755304881525

theorem tailTrace_392697 : CollatzResearch.WordTrace tailWord_392697 prefixEnd_392697 201642312578755304881525 := by
  unfold tailWord_392697
  simp only [CollatzResearch.WordTrace]
  refine ⟨14322836258333311153208345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9548557505555540768805563 14322836258333311153208345)
  ·
    refine ⟨10742127193749983364906259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14322836258333311153208345 10742127193749983364906259)
    ·
      refine ⟨16113190790624975047359389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10742127193749983364906259 16113190790624975047359389)
      ·
        refine ⟨6042446546484365642759771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16113190790624975047359389 6042446546484365642759771)
        ·
          refine ⟨9063669819726548464139657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6042446546484365642759771 9063669819726548464139657)
          ·
            refine ⟨6797752364794911348104743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9063669819726548464139657 6797752364794911348104743)
            ·
              refine ⟨10196628547192367022157115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6797752364794911348104743 10196628547192367022157115)
              ·
                refine ⟨15294942820788550533235673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10196628547192367022157115 15294942820788550533235673)
                ·
                  refine ⟨11471207115591412899926755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15294942820788550533235673 11471207115591412899926755)
                  ·
                    refine ⟨17206810673387119349890133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11471207115591412899926755 17206810673387119349890133)
                    ·
                      refine ⟨201642312578755304881525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 17206810673387119349890133 201642312578755304881525)
                      ·
                        rfl

theorem cell23_392697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 1, 8].length) (baseStart_392697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_392697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_392697 prefixEnd_392697 := by exact prefixLift 392697
  have htrace : WordTrace (prefixWord ++ tailWord_392697) baseStart_392697 baseEnd_392697 := by
    simpa [prefixWord, tailWord_392697, baseEnd_392697] using wordTrace_append hprefix tailTrace_392697
  have hstable : (prefixWord ++ tailWord_392697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392697).length < 2 ^ (prefixWord ++ tailWord_392697).sum := by decide
  have hdescent : baseEnd_392697 < baseStart_392697 := by decide
  rcases family_descends (prefixWord ++ tailWord_392697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392728 : List Nat := [2, 1, 2, 3, 4, 1, 2, 3, 5]
def baseStart_392728 : Nat := 118140960795 + 392728 * 2 ^ 59
def prefixEnd_392728 : Nat := 4983230072969 + 3 ^ 40 * 392728 * 2
def baseEnd_392728 : Nat := 22406470053227187065987

theorem tailTrace_392728 : CollatzResearch.WordTrace tailWord_392728 prefixEnd_392728 22406470053227187065987 := by
  unfold tailWord_392728
  simp only [CollatzResearch.WordTrace]
  refine ⟨7161983460610501723793419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9549311280814002298391225 7161983460610501723793419)
  ·
    refine ⟨10742975190915752585690129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7161983460610501723793419 10742975190915752585690129)
    ·
      refine ⟨8057231393186814439267597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10742975190915752585690129 8057231393186814439267597)
      ·
        refine ⟨3021461772445055414725349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8057231393186814439267597 3021461772445055414725349)
        ·
          refine ⟨566524082333447890261003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3021461772445055414725349 566524082333447890261003)
          ·
            refine ⟨849786123500171835391505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 566524082333447890261003 849786123500171835391505)
            ·
              refine ⟨637339592625128876543629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 849786123500171835391505 637339592625128876543629)
              ·
                refine ⟨239002347234423328703861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 637339592625128876543629 239002347234423328703861)
                ·
                  refine ⟨22406470053227187065987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 239002347234423328703861 22406470053227187065987)
                  ·
                    rfl

theorem cell23_392728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 3, 5].length) (baseStart_392728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_392728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_392728 prefixEnd_392728 := by exact prefixLift 392728
  have htrace : WordTrace (prefixWord ++ tailWord_392728) baseStart_392728 baseEnd_392728 := by
    simpa [prefixWord, tailWord_392728, baseEnd_392728] using wordTrace_append hprefix tailTrace_392728
  have hstable : (prefixWord ++ tailWord_392728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392728).length < 2 ^ (prefixWord ++ tailWord_392728).sum := by decide
  have hdescent : baseEnd_392728 < baseStart_392728 := by decide
  rcases family_descends (prefixWord ++ tailWord_392728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392818 : List Nat := [3, 2, 1, 2, 3, 1, 4, 1, 6]
def baseStart_392818 : Nat := 118140960795 + 392818 * 2 ^ 59
def prefixEnd_392818 : Nat := 4983230072969 + 3 ^ 40 * 392818 * 2
def baseEnd_392818 : Nat := 22411604859772147940941

theorem tailTrace_392818 : CollatzResearch.WordTrace tailWord_392818 prefixEnd_392818 22411604859772147940941 := by
  unfold tailWord_392818
  simp only [CollatzResearch.WordTrace]
  refine ⟨3581812372723737204590777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9551499660596632545575405 3581812372723737204590777)
  ·
    refine ⟨2686359279542802903443083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3581812372723737204590777 2686359279542802903443083)
    ·
      refine ⟨4029538919314204355164625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2686359279542802903443083 4029538919314204355164625)
      ·
        refine ⟨3022154189485653266373469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4029538919314204355164625 3022154189485653266373469)
        ·
          refine ⟨1133307821057119974890051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3022154189485653266373469 1133307821057119974890051)
          ·
            refine ⟨1699961731585679962335077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1133307821057119974890051 1699961731585679962335077)
            ·
              refine ⟨318742824672314992937827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1699961731585679962335077 318742824672314992937827)
              ·
                refine ⟨478114237008472489406741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 318742824672314992937827 478114237008472489406741)
                ·
                  refine ⟨22411604859772147940941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 478114237008472489406741 22411604859772147940941)
                  ·
                    rfl

theorem cell23_392818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 4, 1, 6].length) (baseStart_392818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_392818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_392818 prefixEnd_392818 := by exact prefixLift 392818
  have htrace : WordTrace (prefixWord ++ tailWord_392818) baseStart_392818 baseEnd_392818 := by
    simpa [prefixWord, tailWord_392818, baseEnd_392818] using wordTrace_append hprefix tailTrace_392818
  have hstable : (prefixWord ++ tailWord_392818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392818).length < 2 ^ (prefixWord ++ tailWord_392818).sum := by decide
  have hdescent : baseEnd_392818 < baseStart_392818 := by decide
  rcases family_descends (prefixWord ++ tailWord_392818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392928 : List Nat := [2, 1, 1, 3, 1, 2, 2, 1, 5, 3, 2]
def baseStart_392928 : Nat := 118140960795 + 392928 * 2 ^ 59
def prefixEnd_392928 : Nat := 4983230072969 + 3 ^ 40 * 392928 * 2
def baseEnd_392928 : Nat := 201760926609943901092963

theorem tailTrace_392928 : CollatzResearch.WordTrace tailWord_392928 prefixEnd_392928 201760926609943901092963 := by
  unfold tailWord_392928
  simp only [CollatzResearch.WordTrace]
  refine ⟨7165630760248218802433719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9554174346997625069911625 7165630760248218802433719)
  ·
    refine ⟨10748446140372328203650579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7165630760248218802433719 10748446140372328203650579)
    ·
      refine ⟨16122669210558492305475869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10748446140372328203650579 16122669210558492305475869)
      ·
        refine ⟨6046000953959434614553451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16122669210558492305475869 6046000953959434614553451)
        ·
          refine ⟨9069001430939151921830177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6046000953959434614553451 9069001430939151921830177)
          ·
            refine ⟨6801751073204363941372633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9069001430939151921830177 6801751073204363941372633)
            ·
              refine ⟨5101313304903272956029475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6801751073204363941372633 5101313304903272956029475)
              ·
                refine ⟨7651969957354909434044213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5101313304903272956029475 7651969957354909434044213)
                ·
                  refine ⟨717372183502022759441645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7651969957354909434044213 717372183502022759441645)
                  ·
                    refine ⟨269014568813258534790617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 717372183502022759441645 269014568813258534790617)
                    ·
                      refine ⟨201760926609943901092963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 269014568813258534790617 201760926609943901092963)
                      ·
                        rfl

theorem cell23_392928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 5, 3, 2].length) (baseStart_392928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_392928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_392928 prefixEnd_392928 := by exact prefixLift 392928
  have htrace : WordTrace (prefixWord ++ tailWord_392928) baseStart_392928 baseEnd_392928 := by
    simpa [prefixWord, tailWord_392928, baseEnd_392928] using wordTrace_append hprefix tailTrace_392928
  have hstable : (prefixWord ++ tailWord_392928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392928).length < 2 ^ (prefixWord ++ tailWord_392928).sum := by decide
  have hdescent : baseEnd_392928 < baseStart_392928 := by decide
  rcases family_descends (prefixWord ++ tailWord_392928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392945 : List Nat := [1, 2, 2, 2, 2, 3, 1, 4, 1, 3, 2]
def baseStart_392945 : Nat := 118140960795 + 392945 * 2 ^ 59
def prefixEnd_392945 : Nat := 4983230072969 + 3 ^ 40 * 392945 * 2
def baseEnd_392945 : Nat := 201769655781070334580385

theorem tailTrace_392945 : CollatzResearch.WordTrace tailWord_392945 prefixEnd_392945 201769655781070334580385 := by
  unfold tailWord_392945
  simp only [CollatzResearch.WordTrace]
  refine ⟨14331881561434849508236289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9554587707623233005490859 14331881561434849508236289)
  ·
    refine ⟨10748911171076137131177217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14331881561434849508236289 10748911171076137131177217)
    ·
      refine ⟨8061683378307102848382913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10748911171076137131177217 8061683378307102848382913)
      ·
        refine ⟨6046262533730327136287185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8061683378307102848382913 6046262533730327136287185)
        ·
          refine ⟨4534696900297745352215389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6046262533730327136287185 4534696900297745352215389)
          ·
            refine ⟨1700511337611654507080771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4534696900297745352215389 1700511337611654507080771)
            ·
              refine ⟨2550767006417481760621157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1700511337611654507080771 2550767006417481760621157)
              ·
                refine ⟨478268813703277830116467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2550767006417481760621157 478268813703277830116467)
                ·
                  refine ⟨717403220554916745174701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 478268813703277830116467 717403220554916745174701)
                  ·
                    refine ⟨269026207708093779440513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 717403220554916745174701 269026207708093779440513)
                    ·
                      refine ⟨201769655781070334580385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 269026207708093779440513 201769655781070334580385)
                      ·
                        rfl

theorem cell23_392945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 4, 1, 3, 2].length) (baseStart_392945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_392945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_392945 prefixEnd_392945 := by exact prefixLift 392945
  have htrace : WordTrace (prefixWord ++ tailWord_392945) baseStart_392945 baseEnd_392945 := by
    simpa [prefixWord, tailWord_392945, baseEnd_392945] using wordTrace_append hprefix tailTrace_392945
  have hstable : (prefixWord ++ tailWord_392945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392945).length < 2 ^ (prefixWord ++ tailWord_392945).sum := by decide
  have hdescent : baseEnd_392945 < baseStart_392945 := by decide
  rcases family_descends (prefixWord ++ tailWord_392945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392961 : List Nat := [1, 2, 4, 1, 1, 1, 3, 1, 1, 3, 5]
def baseStart_392961 : Nat := 118140960795 + 392961 * 2 ^ 59
def prefixEnd_392961 : Nat := 4983230072969 + 3 ^ 40 * 392961 * 2
def baseEnd_392961 : Nat := 201777871471542271980311

theorem tailTrace_392961 : CollatzResearch.WordTrace tailWord_392961 prefixEnd_392961 201777871471542271980311 := by
  unfold tailWord_392961
  simp only [CollatzResearch.WordTrace]
  refine ⟨14332465129376884240818737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9554976752917922827212491 14332465129376884240818737)
  ·
    refine ⟨10749348847032663180614053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14332465129376884240818737 10749348847032663180614053)
    ·
      refine ⟨2015502908818624346365135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10749348847032663180614053 2015502908818624346365135)
      ·
        refine ⟨3023254363227936519547703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2015502908818624346365135 3023254363227936519547703)
        ·
          refine ⟨4534881544841904779321555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3023254363227936519547703 4534881544841904779321555)
          ·
            refine ⟨6802322317262857168982333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4534881544841904779321555 6802322317262857168982333)
            ·
              refine ⟨2550870868973571438368375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6802322317262857168982333 2550870868973571438368375)
              ·
                refine ⟨3826306303460357157552563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2550870868973571438368375 3826306303460357157552563)
                ·
                  refine ⟨5739459455190535736328845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3826306303460357157552563 5739459455190535736328845)
                  ·
                    refine ⟨2152297295696450901123317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5739459455190535736328845 2152297295696450901123317)
                    ·
                      refine ⟨201777871471542271980311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2152297295696450901123317 201777871471542271980311)
                      ·
                        rfl

theorem cell23_392961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_392961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_392961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_392961 prefixEnd_392961 := by exact prefixLift 392961
  have htrace : WordTrace (prefixWord ++ tailWord_392961) baseStart_392961 baseEnd_392961 := by
    simpa [prefixWord, tailWord_392961, baseEnd_392961] using wordTrace_append hprefix tailTrace_392961
  have hstable : (prefixWord ++ tailWord_392961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392961).length < 2 ^ (prefixWord ++ tailWord_392961).sum := by decide
  have hdescent : baseEnd_392961 < baseStart_392961 := by decide
  rcases family_descends (prefixWord ++ tailWord_392961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392962 : List Nat := [3, 4, 1, 1, 1, 1, 1, 5, 1, 3, 2]
def baseStart_392962 : Nat := 118140960795 + 392962 * 2 ^ 59
def prefixEnd_392962 : Nat := 4983230072969 + 3 ^ 40 * 392962 * 2
def baseEnd_392962 : Nat := 201778384952196768067807

theorem tailTrace_392962 : CollatzResearch.WordTrace tailWord_392962 prefixEnd_392962 201778384952196768067807 := by
  unfold tailWord_392962
  simp only [CollatzResearch.WordTrace]
  refine ⟨3583125400593315352901285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9555001068248840941070093 3583125400593315352901285)
  ·
    refine ⟨671836012611246628668991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3583125400593315352901285 671836012611246628668991)
    ·
      refine ⟨1007754018916869943003487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 671836012611246628668991 1007754018916869943003487)
      ·
        refine ⟨1511631028375304914505231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1007754018916869943003487 1511631028375304914505231)
        ·
          refine ⟨2267446542562957371757847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1511631028375304914505231 2267446542562957371757847)
          ·
            refine ⟨3401169813844436057636771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2267446542562957371757847 3401169813844436057636771)
            ·
              refine ⟨5101754720766654086455157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3401169813844436057636771 5101754720766654086455157)
              ·
                refine ⟨478289505071873820605171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5101754720766654086455157 478289505071873820605171)
                ·
                  refine ⟨717434257607810730907757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 478289505071873820605171 717434257607810730907757)
                  ·
                    refine ⟨269037846602929024090409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 717434257607810730907757 269037846602929024090409)
                    ·
                      refine ⟨201778384952196768067807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 269037846602929024090409 201778384952196768067807)
                      ·
                        rfl

theorem cell23_392962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 5, 1, 3, 2].length) (baseStart_392962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_392962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_392962 prefixEnd_392962 := by exact prefixLift 392962
  have htrace : WordTrace (prefixWord ++ tailWord_392962) baseStart_392962 baseEnd_392962 := by
    simpa [prefixWord, tailWord_392962, baseEnd_392962] using wordTrace_append hprefix tailTrace_392962
  have hstable : (prefixWord ++ tailWord_392962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392962).length < 2 ^ (prefixWord ++ tailWord_392962).sum := by decide
  have hdescent : baseEnd_392962 < baseStart_392962 := by decide
  rcases family_descends (prefixWord ++ tailWord_392962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392971 : List Nat := [1, 1, 1, 1, 5, 1, 2, 1, 4, 2, 4]
def baseStart_392971 : Nat := 118140960795 + 392971 * 2 ^ 59
def prefixEnd_392971 : Nat := 4983230072969 + 3 ^ 40 * 392971 * 2
def baseEnd_392971 : Nat := 201783006278087232855265

theorem tailTrace_392971 : CollatzResearch.WordTrace tailWord_392971 prefixEnd_392971 201783006278087232855265 := by
  unfold tailWord_392971
  simp only [CollatzResearch.WordTrace]
  refine ⟨14332829859340655948682767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9555219906227103965788511 14332829859340655948682767)
  ·
    refine ⟨21499244789010983923024151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14332829859340655948682767 21499244789010983923024151)
    ·
      refine ⟨32248867183516475884536227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21499244789010983923024151 32248867183516475884536227)
      ·
        refine ⟨48373300775274713826804341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32248867183516475884536227 48373300775274713826804341)
        ·
          refine ⟨4534996947682004421262907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48373300775274713826804341 4534996947682004421262907)
          ·
            refine ⟨6802495421523006631894361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4534996947682004421262907 6802495421523006631894361)
            ·
              refine ⟨5101871566142254973920771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6802495421523006631894361 5101871566142254973920771)
              ·
                refine ⟨7652807349213382460881157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5101871566142254973920771 7652807349213382460881157)
                ·
                  refine ⟨1434901377977509211415217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7652807349213382460881157 1434901377977509211415217)
                  ·
                    refine ⟨1076176033483131908561413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1434901377977509211415217 1076176033483131908561413)
                    ·
                      refine ⟨201783006278087232855265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1076176033483131908561413 201783006278087232855265)
                      ·
                        rfl

theorem cell23_392971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 4, 2, 4].length) (baseStart_392971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_392971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_392971 prefixEnd_392971 := by exact prefixLift 392971
  have htrace : WordTrace (prefixWord ++ tailWord_392971) baseStart_392971 baseEnd_392971 := by
    simpa [prefixWord, tailWord_392971, baseEnd_392971] using wordTrace_append hprefix tailTrace_392971
  have hstable : (prefixWord ++ tailWord_392971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392971).length < 2 ^ (prefixWord ++ tailWord_392971).sum := by decide
  have hdescent : baseEnd_392971 < baseStart_392971 := by decide
  rcases family_descends (prefixWord ++ tailWord_392971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392992 : List Nat := [2, 1, 1, 5, 1, 1, 3, 3, 2, 2, 2]
def baseStart_392992 : Nat := 118140960795 + 392992 * 2 ^ 59
def prefixEnd_392992 : Nat := 4983230072969 + 3 ^ 40 * 392992 * 2
def baseEnd_392992 : Nat := 201793789371831650692669

theorem tailTrace_392992 : CollatzResearch.WordTrace tailWord_392992 prefixEnd_392992 201793789371831650692669 := by
  unfold tailWord_392992
  simp only [CollatzResearch.WordTrace]
  refine ⟨7166797896132288267598615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9555730528176384356798153 7166797896132288267598615)
  ·
    refine ⟨10750196844198432401397923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7166797896132288267598615 10750196844198432401397923)
    ·
      refine ⟨16125295266297648602096885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10750196844198432401397923 16125295266297648602096885)
      ·
        refine ⟨1511746431215404556446583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16125295266297648602096885 1511746431215404556446583)
        ·
          refine ⟨2267619646823106834669875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1511746431215404556446583 2267619646823106834669875)
          ·
            refine ⟨3401429470234660252004813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2267619646823106834669875 3401429470234660252004813)
            ·
              refine ⟨1275536051337997594501805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3401429470234660252004813 1275536051337997594501805)
              ·
                refine ⟨478326019251749097938177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1275536051337997594501805 478326019251749097938177)
                ·
                  refine ⟨358744514438811823453633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 478326019251749097938177 358744514438811823453633)
                  ·
                    refine ⟨269058385829108867590225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 358744514438811823453633 269058385829108867590225)
                    ·
                      refine ⟨201793789371831650692669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 269058385829108867590225 201793789371831650692669)
                      ·
                        rfl

theorem cell23_392992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 3, 2, 2, 2].length) (baseStart_392992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_392992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_392992 prefixEnd_392992 := by exact prefixLift 392992
  have htrace : WordTrace (prefixWord ++ tailWord_392992) baseStart_392992 baseEnd_392992 := by
    simpa [prefixWord, tailWord_392992, baseEnd_392992] using wordTrace_append hprefix tailTrace_392992
  have hstable : (prefixWord ++ tailWord_392992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392992).length < 2 ^ (prefixWord ++ tailWord_392992).sum := by decide
  have hdescent : baseEnd_392992 < baseStart_392992 := by decide
  rcases family_descends (prefixWord ++ tailWord_392992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393032 : List Nat := [2, 1, 3, 1, 1, 6, 2, 2, 5]
def baseStart_393032 : Nat := 118140960795 + 393032 * 2 ^ 59
def prefixEnd_393032 : Nat := 4983230072969 + 3 ^ 40 * 393032 * 2
def baseEnd_393032 : Nat := 22423814288667943799165

theorem tailTrace_393032 : CollatzResearch.WordTrace tailWord_393032 prefixEnd_393032 22423814288667943799165 := by
  unfold tailWord_393032
  simp only [CollatzResearch.WordTrace]
  refine ⟨7167527356059831683326675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9556703141413108911102233 7167527356059831683326675)
  ·
    refine ⟨10751291034089747524990013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7167527356059831683326675 10751291034089747524990013)
    ·
      refine ⟨4031734137783655321871255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10751291034089747524990013 4031734137783655321871255)
      ·
        refine ⟨6047601206675482982806883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4031734137783655321871255 6047601206675482982806883)
        ·
          refine ⟨9071401810013224474210325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6047601206675482982806883 9071401810013224474210325)
          ·
            refine ⟨425221959844369897228609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 9071401810013224474210325 425221959844369897228609)
            ·
              refine ⟨318916469883277422921457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 425221959844369897228609 318916469883277422921457)
              ·
                refine ⟨239187352412458067191093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 318916469883277422921457 239187352412458067191093)
                ·
                  refine ⟨22423814288667943799165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 239187352412458067191093 22423814288667943799165)
                  ·
                    rfl

theorem cell23_393032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 2, 2, 5].length) (baseStart_393032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_393032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_393032 prefixEnd_393032 := by exact prefixLift 393032
  have htrace : WordTrace (prefixWord ++ tailWord_393032) baseStart_393032 baseEnd_393032 := by
    simpa [prefixWord, tailWord_393032, baseEnd_393032] using wordTrace_append hprefix tailTrace_393032
  have hstable : (prefixWord ++ tailWord_393032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393032).length < 2 ^ (prefixWord ++ tailWord_393032).sum := by decide
  have hdescent : baseEnd_393032 < baseStart_393032 := by decide
  rcases family_descends (prefixWord ++ tailWord_393032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393092 : List Nat := [2, 3, 2, 1, 1, 1, 4, 4, 1, 4]
def baseStart_393092 : Nat := 118140960795 + 393092 * 2 ^ 59
def prefixEnd_393092 : Nat := 4983230072969 + 3 ^ 40 * 393092 * 2
def baseEnd_393092 : Nat := 67281712479093753147403

theorem tailTrace_393092 : CollatzResearch.WordTrace tailWord_393092 prefixEnd_393092 67281712479093753147403 := by
  unfold tailWord_393092
  simp only [CollatzResearch.WordTrace]
  refine ⟨7168621545951146806918765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9558162061268195742558353 7168621545951146806918765)
  ·
    refine ⟨2688233079731680052594537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7168621545951146806918765 2688233079731680052594537)
    ·
      refine ⟨2016174809798760039445903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2688233079731680052594537 2016174809798760039445903)
      ·
        refine ⟨3024262214698140059168855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2016174809798760039445903 3024262214698140059168855)
        ·
          refine ⟨4536393322047210088753283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3024262214698140059168855 4536393322047210088753283)
          ·
            refine ⟨6804589983070815133129925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4536393322047210088753283 6804589983070815133129925)
            ·
              refine ⟨1275860621825777837461861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6804589983070815133129925 1275860621825777837461861)
              ·
                refine ⟨239223866592333344524099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1275860621825777837461861 239223866592333344524099)
                ·
                  refine ⟨358835799888500016786149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 239223866592333344524099 358835799888500016786149)
                  ·
                    refine ⟨67281712479093753147403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 358835799888500016786149 67281712479093753147403)
                    ·
                      rfl

theorem cell23_393092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 4, 1, 4].length) (baseStart_393092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_393092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_393092 prefixEnd_393092 := by exact prefixLift 393092
  have htrace : WordTrace (prefixWord ++ tailWord_393092) baseStart_393092 baseEnd_393092 := by
    simpa [prefixWord, tailWord_393092, baseEnd_393092] using wordTrace_append hprefix tailTrace_393092
  have hstable : (prefixWord ++ tailWord_393092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393092).length < 2 ^ (prefixWord ++ tailWord_393092).sum := by decide
  have hdescent : baseEnd_393092 < baseStart_393092 := by decide
  rcases family_descends (prefixWord ++ tailWord_393092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393125 : List Nat := [1, 3, 1, 2, 1, 1, 1, 2, 6, 3, 2]
def baseStart_393125 : Nat := 118140960795 + 393125 * 2 ^ 59
def prefixEnd_393125 : Nat := 4983230072969 + 3 ^ 40 * 393125 * 2
def baseEnd_393125 : Nat := 201862082298879630329557

theorem tailTrace_393125 : CollatzResearch.WordTrace tailWord_393125 prefixEnd_393125 201862082298879630329557 := by
  unfold tailWord_393125
  simp only [CollatzResearch.WordTrace]
  refine ⟨14338446700782740249788829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9558964467188493499859219 14338446700782740249788829)
  ·
    refine ⟨5376917512793527593670811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14338446700782740249788829 5376917512793527593670811)
    ·
      refine ⟨8065376269190291390506217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5376917512793527593670811 8065376269190291390506217)
      ·
        refine ⟨6049032201892718542879663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8065376269190291390506217 6049032201892718542879663)
        ·
          refine ⟨9073548302839077814319495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6049032201892718542879663 9073548302839077814319495)
          ·
            refine ⟨13610322454258616721479243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9073548302839077814319495 13610322454258616721479243)
            ·
              refine ⟨20415483681387925082218865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13610322454258616721479243 20415483681387925082218865)
              ·
                refine ⟨15311612761040943811664149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20415483681387925082218865 15311612761040943811664149)
                ·
                  refine ⟨717731848173794241171757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 15311612761040943811664149 717731848173794241171757)
                  ·
                    refine ⟨269149443065172840439409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 717731848173794241171757 269149443065172840439409)
                    ·
                      refine ⟨201862082298879630329557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 269149443065172840439409 201862082298879630329557)
                      ·
                        rfl

theorem cell23_393125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 6, 3, 2].length) (baseStart_393125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_393125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_393125 prefixEnd_393125 := by exact prefixLift 393125
  have htrace : WordTrace (prefixWord ++ tailWord_393125) baseStart_393125 baseEnd_393125 := by
    simpa [prefixWord, tailWord_393125, baseEnd_393125] using wordTrace_append hprefix tailTrace_393125
  have hstable : (prefixWord ++ tailWord_393125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393125).length < 2 ^ (prefixWord ++ tailWord_393125).sum := by decide
  have hdescent : baseEnd_393125 < baseStart_393125 := by decide
  rcases family_descends (prefixWord ++ tailWord_393125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393149 : List Nat := [1, 4, 1, 2, 3, 3, 1, 1, 3, 1, 3]
def baseStart_393149 : Nat := 118140960795 + 393149 * 2 ^ 59
def prefixEnd_393149 : Nat := 4983230072969 + 3 ^ 40 * 393149 * 2
def baseEnd_393149 : Nat := 201874405834587536429447

theorem tailTrace_393149 : CollatzResearch.WordTrace tailWord_393149 prefixEnd_393149 201874405834587536429447 := by
  unfold tailWord_393149
  simp only [CollatzResearch.WordTrace]
  refine ⟨14339322052695792348662501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9559548035130528232441667 14339322052695792348662501)
  ·
    refine ⟨2688622884880461065374219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14339322052695792348662501 2688622884880461065374219)
    ·
      refine ⟨4032934327320691598061329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2688622884880461065374219 4032934327320691598061329)
      ·
        refine ⟨3024700745490518698545997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4032934327320691598061329 3024700745490518698545997)
        ·
          refine ⟨1134262779558944511954749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3024700745490518698545997 1134262779558944511954749)
          ·
            refine ⟨425348542334604191983031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1134262779558944511954749 425348542334604191983031)
            ·
              refine ⟨638022813501906287974547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 425348542334604191983031 638022813501906287974547)
              ·
                refine ⟨957034220252859431961821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 638022813501906287974547 957034220252859431961821)
                ·
                  refine ⟨358887832594822286985683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 957034220252859431961821 358887832594822286985683)
                  ·
                    refine ⟨538331748892233430478525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 358887832594822286985683 538331748892233430478525)
                    ·
                      refine ⟨201874405834587536429447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 538331748892233430478525 201874405834587536429447)
                      ·
                        rfl

theorem cell23_393149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 1, 3, 1, 3].length) (baseStart_393149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_393149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_393149 prefixEnd_393149 := by exact prefixLift 393149
  have htrace : WordTrace (prefixWord ++ tailWord_393149) baseStart_393149 baseEnd_393149 := by
    simpa [prefixWord, tailWord_393149, baseEnd_393149] using wordTrace_append hprefix tailTrace_393149
  have hstable : (prefixWord ++ tailWord_393149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393149).length < 2 ^ (prefixWord ++ tailWord_393149).sum := by decide
  have hdescent : baseEnd_393149 < baseStart_393149 := by decide
  rcases family_descends (prefixWord ++ tailWord_393149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393168 : List Nat := [2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 6]
def baseStart_393168 : Nat := 118140960795 + 393168 * 2 ^ 59
def prefixEnd_393168 : Nat := 4983230072969 + 3 ^ 40 * 393168 * 2
def baseEnd_393168 : Nat := 201884161967022962091859

theorem tailTrace_393168 : CollatzResearch.WordTrace tailWord_393168 prefixEnd_393168 201884161967022962091859 := by
  unfold tailWord_393168
  simp only [CollatzResearch.WordTrace]
  refine ⟨7170007519813479296802079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9560010026417972395736105 7170007519813479296802079)
  ·
    refine ⟨10755011279720218945203119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7170007519813479296802079 10755011279720218945203119)
    ·
      refine ⟨16132516919580328417804679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10755011279720218945203119 16132516919580328417804679)
      ·
        refine ⟨24198775379370492626707019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16132516919580328417804679 24198775379370492626707019)
        ·
          refine ⟨36298163069055738940060529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24198775379370492626707019 36298163069055738940060529)
          ·
            refine ⟨27223622301791804205045397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36298163069055738940060529 27223622301791804205045397)
            ·
              refine ⟨1276107295396490822111503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 27223622301791804205045397 1276107295396490822111503)
              ·
                refine ⟨1914160943094736233167255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1276107295396490822111503 1914160943094736233167255)
                ·
                  refine ⟨2871241414642104349750883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1914160943094736233167255 2871241414642104349750883)
                  ·
                    refine ⟨4306862121963156524626325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2871241414642104349750883 4306862121963156524626325)
                    ·
                      refine ⟨201884161967022962091859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4306862121963156524626325 201884161967022962091859)
                      ·
                        rfl

theorem cell23_393168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 6].length) (baseStart_393168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_393168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_393168 prefixEnd_393168 := by exact prefixLift 393168
  have htrace : WordTrace (prefixWord ++ tailWord_393168) baseStart_393168 baseEnd_393168 := by
    simpa [prefixWord, tailWord_393168, baseEnd_393168] using wordTrace_append hprefix tailTrace_393168
  have hstable : (prefixWord ++ tailWord_393168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393168).length < 2 ^ (prefixWord ++ tailWord_393168).sum := by decide
  have hdescent : baseEnd_393168 < baseStart_393168 := by decide
  rcases family_descends (prefixWord ++ tailWord_393168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393175 : List Nat := [1, 1, 3, 2, 1, 1, 5, 1, 3, 2, 3]
def baseStart_393175 : Nat := 118140960795 + 393175 * 2 ^ 59
def prefixEnd_393175 : Nat := 4983230072969 + 3 ^ 40 * 393175 * 2
def baseEnd_393175 : Nat := 201887756331604434704327

theorem tailTrace_393175 : CollatzResearch.WordTrace tailWord_393175 prefixEnd_393175 201887756331604434704327 := by
  unfold tailWord_393175
  simp only [CollatzResearch.WordTrace]
  refine ⟨14340270350601598789108979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9560180233734399192739319 14340270350601598789108979)
  ·
    refine ⟨21510405525902398183663469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14340270350601598789108979 21510405525902398183663469)
    ·
      refine ⟨8066402072213399318873801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21510405525902398183663469 8066402072213399318873801)
      ·
        refine ⟨6049801554160049489155351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8066402072213399318873801 6049801554160049489155351)
        ·
          refine ⟨9074702331240074233733027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6049801554160049489155351 9074702331240074233733027)
          ·
            refine ⟨13612053496860111350599541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9074702331240074233733027 13612053496860111350599541)
            ·
              refine ⟨1276130015330635439118707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13612053496860111350599541 1276130015330635439118707)
              ·
                refine ⟨1914195022995953158678061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1276130015330635439118707 1914195022995953158678061)
                ·
                  refine ⟨717823133623482434504273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1914195022995953158678061 717823133623482434504273)
                  ·
                    refine ⟨538367350217611825878205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 717823133623482434504273 538367350217611825878205)
                    ·
                      refine ⟨201887756331604434704327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 538367350217611825878205 201887756331604434704327)
                      ·
                        rfl

theorem cell23_393175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 1, 3, 2, 3].length) (baseStart_393175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_393175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_393175 prefixEnd_393175 := by exact prefixLift 393175
  have htrace : WordTrace (prefixWord ++ tailWord_393175) baseStart_393175 baseEnd_393175 := by
    simpa [prefixWord, tailWord_393175, baseEnd_393175] using wordTrace_append hprefix tailTrace_393175
  have hstable : (prefixWord ++ tailWord_393175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393175).length < 2 ^ (prefixWord ++ tailWord_393175).sum := by decide
  have hdescent : baseEnd_393175 < baseStart_393175 := by decide
  rcases family_descends (prefixWord ++ tailWord_393175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393186 : List Nat := [3, 3, 3, 1, 2, 1, 3, 1, 1, 5]
def baseStart_393186 : Nat := 118140960795 + 393186 * 2 ^ 59
def prefixEnd_393186 : Nat := 4983230072969 + 3 ^ 40 * 393186 * 2
def baseEnd_393186 : Nat := 67297801539601297222259

theorem tailTrace_393186 : CollatzResearch.WordTrace tailWord_393186 prefixEnd_393186 67297801539601297222259 := by
  unfold tailWord_393186
  simp only [CollatzResearch.WordTrace]
  refine ⟨3585167888390436916939853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9560447702374498445172941 3585167888390436916939853)
  ·
    refine ⟨1344437958146413843852445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3585167888390436916939853 1344437958146413843852445)
    ·
      refine ⟨504164234304905191444667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1344437958146413843852445 504164234304905191444667)
      ·
        refine ⟨756246351457357787167001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 504164234304905191444667 756246351457357787167001)
        ·
          refine ⟨567184763593018340375251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 756246351457357787167001 567184763593018340375251)
          ·
            refine ⟨850777145389527510562877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 567184763593018340375251 850777145389527510562877)
            ·
              refine ⟨319041429521072816461079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 850777145389527510562877 319041429521072816461079)
              ·
                refine ⟨478562144281609224691619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 319041429521072816461079 478562144281609224691619)
                ·
                  refine ⟨717843216422413837037429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 478562144281609224691619 717843216422413837037429)
                  ·
                    refine ⟨67297801539601297222259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 717843216422413837037429 67297801539601297222259)
                    ·
                      rfl

theorem cell23_393186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_393186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_393186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_393186 prefixEnd_393186 := by exact prefixLift 393186
  have htrace : WordTrace (prefixWord ++ tailWord_393186) baseStart_393186 baseEnd_393186 := by
    simpa [prefixWord, tailWord_393186, baseEnd_393186] using wordTrace_append hprefix tailTrace_393186
  have hstable : (prefixWord ++ tailWord_393186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393186).length < 2 ^ (prefixWord ++ tailWord_393186).sum := by decide
  have hdescent : baseEnd_393186 < baseStart_393186 := by decide
  rcases family_descends (prefixWord ++ tailWord_393186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393208 : List Nat := [2, 1, 2, 1, 1, 3, 3, 1, 2, 7]
def baseStart_393208 : Nat := 118140960795 + 393208 * 2 ^ 59
def prefixEnd_393208 : Nat := 4983230072969 + 3 ^ 40 * 393208 * 2
def baseEnd_393208 : Nat := 67301567064400935197225

theorem tailTrace_393208 : CollatzResearch.WordTrace tailWord_393208 prefixEnd_393208 67301567064400935197225 := by
  unfold tailWord_393208
  simp only [CollatzResearch.WordTrace]
  refine ⟨7170736979741022712530139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9560982639654696950040185 7170736979741022712530139)
  ·
    refine ⟨10756105469611534068795209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7170736979741022712530139 10756105469611534068795209)
    ·
      refine ⟨8067079102208650551596407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10756105469611534068795209 8067079102208650551596407)
      ·
        refine ⟨12100618653312975827394611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8067079102208650551596407 12100618653312975827394611)
        ·
          refine ⟨18150927979969463741091917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12100618653312975827394611 18150927979969463741091917)
          ·
            refine ⟨6806597992488548902909469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18150927979969463741091917 6806597992488548902909469)
            ·
              refine ⟨2552474247183205838591051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6806597992488548902909469 2552474247183205838591051)
              ·
                refine ⟨3828711370774808757886577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2552474247183205838591051 3828711370774808757886577)
                ·
                  refine ⟨2871533528081106568414933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3828711370774808757886577 2871533528081106568414933)
                  ·
                    refine ⟨67301567064400935197225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2871533528081106568414933 67301567064400935197225)
                    ·
                      rfl

theorem cell23_393208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 2, 7].length) (baseStart_393208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_393208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_393208 prefixEnd_393208 := by exact prefixLift 393208
  have htrace : WordTrace (prefixWord ++ tailWord_393208) baseStart_393208 baseEnd_393208 := by
    simpa [prefixWord, tailWord_393208, baseEnd_393208] using wordTrace_append hprefix tailTrace_393208
  have hstable : (prefixWord ++ tailWord_393208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393208).length < 2 ^ (prefixWord ++ tailWord_393208).sum := by decide
  have hdescent : baseEnd_393208 < baseStart_393208 := by decide
  rcases family_descends (prefixWord ++ tailWord_393208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393256 : List Nat := [2, 1, 5, 3, 1, 1, 1, 1, 4, 1, 3]
def baseStart_393256 : Nat := 118140960795 + 393256 * 2 ^ 59
def prefixEnd_393256 : Nat := 4983230072969 + 3 ^ 40 * 393256 * 2
def baseEnd_393256 : Nat := 201929348264618617791455

theorem tailTrace_393256 : CollatzResearch.WordTrace tailWord_393256 prefixEnd_393256 201929348264618617791455 := by
  unfold tailWord_393256
  simp only [CollatzResearch.WordTrace]
  refine ⟨7171612331654074811403811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9562149775538766415205081 7171612331654074811403811)
  ·
    refine ⟨10757418497481112217105717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7171612331654074811403811 10757418497481112217105717)
    ·
      refine ⟨1008507984138854270353661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10757418497481112217105717 1008507984138854270353661)
      ·
        refine ⟨378190494052070351382623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1008507984138854270353661 378190494052070351382623)
        ·
          refine ⟨567285741078105527073935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 378190494052070351382623 567285741078105527073935)
          ·
            refine ⟨850928611617158290610903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 567285741078105527073935 850928611617158290610903)
            ·
              refine ⟨1276392917425737435916355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 850928611617158290610903 1276392917425737435916355)
              ·
                refine ⟨1914589376138606153874533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1276392917425737435916355 1914589376138606153874533)
                ·
                  refine ⟨358985508025988653851475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1914589376138606153874533 358985508025988653851475)
                  ·
                    refine ⟨538478262038982980777213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 358985508025988653851475 538478262038982980777213)
                    ·
                      refine ⟨201929348264618617791455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 538478262038982980777213 201929348264618617791455)
                      ·
                        rfl

theorem cell23_393256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_393256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_393256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_393256 prefixEnd_393256 := by exact prefixLift 393256
  have htrace : WordTrace (prefixWord ++ tailWord_393256) baseStart_393256 baseEnd_393256 := by
    simpa [prefixWord, tailWord_393256, baseEnd_393256] using wordTrace_append hprefix tailTrace_393256
  have hstable : (prefixWord ++ tailWord_393256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393256).length < 2 ^ (prefixWord ++ tailWord_393256).sum := by decide
  have hdescent : baseEnd_393256 < baseStart_393256 := by decide
  rcases family_descends (prefixWord ++ tailWord_393256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393279 : List Nat := [1, 1, 2, 2, 3, 1, 2, 5, 2, 2, 2]
def baseStart_393279 : Nat := 118140960795 + 393279 * 2 ^ 59
def prefixEnd_393279 : Nat := 4983230072969 + 3 ^ 40 * 393279 * 2
def baseEnd_393279 : Nat := 201941158319672027803849

theorem tailTrace_393279 : CollatzResearch.WordTrace tailWord_393279 prefixEnd_393279 201941158319672027803849 := by
  unfold tailWord_393279
  simp only [CollatzResearch.WordTrace]
  refine ⟨14344063542224824550894891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9562709028149883033929927 14344063542224824550894891)
  ·
    refine ⟨21516095313337236826342337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14344063542224824550894891 21516095313337236826342337)
    ·
      refine ⟨16137071485002927619756753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21516095313337236826342337 16137071485002927619756753)
      ·
        refine ⟨12102803613752195714817565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16137071485002927619756753 12102803613752195714817565)
        ·
          refine ⟨4538551355157073393056587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12102803613752195714817565 4538551355157073393056587)
          ·
            refine ⟨6807827032735610089584881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4538551355157073393056587 6807827032735610089584881)
            ·
              refine ⟨5105870274551707567188661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6807827032735610089584881 5105870274551707567188661)
              ·
                refine ⟨478675338239222584423937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5105870274551707567188661 478675338239222584423937)
                ·
                  refine ⟨359006503679416938317953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 478675338239222584423937 359006503679416938317953)
                  ·
                    refine ⟨269254877759562703738465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 359006503679416938317953 269254877759562703738465)
                    ·
                      refine ⟨201941158319672027803849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 269254877759562703738465 201941158319672027803849)
                      ·
                        rfl

theorem cell23_393279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 5, 2, 2, 2].length) (baseStart_393279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_393279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_393279 prefixEnd_393279 := by exact prefixLift 393279
  have htrace : WordTrace (prefixWord ++ tailWord_393279) baseStart_393279 baseEnd_393279 := by
    simpa [prefixWord, tailWord_393279, baseEnd_393279] using wordTrace_append hprefix tailTrace_393279
  have hstable : (prefixWord ++ tailWord_393279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393279).length < 2 ^ (prefixWord ++ tailWord_393279).sum := by decide
  have hdescent : baseEnd_393279 < baseStart_393279 := by decide
  rcases family_descends (prefixWord ++ tailWord_393279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393315 : List Nat := [1, 1, 1, 5, 1, 1, 3, 1, 4, 5]
def baseStart_393315 : Nat := 118140960795 + 393315 * 2 ^ 59
def prefixEnd_393315 : Nat := 4983230072969 + 3 ^ 40 * 393315 * 2
def baseEnd_393315 : Nat := 67319881207744628984561

theorem tailTrace_393315 : CollatzResearch.WordTrace tailWord_393315 prefixEnd_393315 67319881207744628984561 := by
  unfold tailWord_393315
  simp only [CollatzResearch.WordTrace]
  refine ⟨14345376570094402699205399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9563584380062935132803599 14345376570094402699205399)
  ·
    refine ⟨21518064855141604048808099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14345376570094402699205399 21518064855141604048808099)
    ·
      refine ⟨32277097282712406073212149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21518064855141604048808099 32277097282712406073212149)
      ·
        refine ⟨3025977870254288069363639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32277097282712406073212149 3025977870254288069363639)
        ·
          refine ⟨4538966805381432104045459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3025977870254288069363639 4538966805381432104045459)
          ·
            refine ⟨6808450208072148156068189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4538966805381432104045459 6808450208072148156068189)
            ·
              refine ⟨2553168828027055558525571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6808450208072148156068189 2553168828027055558525571)
              ·
                refine ⟨3829753242040583337788357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2553168828027055558525571 3829753242040583337788357)
                ·
                  refine ⟨718078732882609375835317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3829753242040583337788357 718078732882609375835317)
                  ·
                    refine ⟨67319881207744628984561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 718078732882609375835317 67319881207744628984561)
                    ·
                      rfl

theorem cell23_393315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 4, 5].length) (baseStart_393315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_393315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_393315 prefixEnd_393315 := by exact prefixLift 393315
  have htrace : WordTrace (prefixWord ++ tailWord_393315) baseStart_393315 baseEnd_393315 := by
    simpa [prefixWord, tailWord_393315, baseEnd_393315] using wordTrace_append hprefix tailTrace_393315
  have hstable : (prefixWord ++ tailWord_393315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393315).length < 2 ^ (prefixWord ++ tailWord_393315).sum := by decide
  have hdescent : baseEnd_393315 < baseStart_393315 := by decide
  rcases family_descends (prefixWord ++ tailWord_393315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393319 : List Nat := [1, 1, 5, 1, 1, 2, 5, 2, 5]
def baseStart_393319 : Nat := 118140960795 + 393319 * 2 ^ 59
def prefixEnd_393319 : Nat := 4983230072969 + 3 ^ 40 * 393319 * 2
def baseEnd_393319 : Nat := 22440188616205763478185

theorem tailTrace_393319 : CollatzResearch.WordTrace tailWord_393319 prefixEnd_393319 22440188616205763478185 := by
  unfold tailWord_393319
  simp only [CollatzResearch.WordTrace]
  refine ⟨14345522462079911382351011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9563681641386607588234007 14345522462079911382351011)
  ·
    refine ⟨21518283693119867073526517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14345522462079911382351011 21518283693119867073526517)
    ·
      refine ⟨2017339096229987538143111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21518283693119867073526517 2017339096229987538143111)
      ·
        refine ⟨3026008644344981307214667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2017339096229987538143111 3026008644344981307214667)
        ·
          refine ⟨4539012966517471960822001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3026008644344981307214667 4539012966517471960822001)
          ·
            refine ⟨3404259724888103970616501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4539012966517471960822001 3404259724888103970616501)
            ·
              refine ⟨319149349208259747245297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3404259724888103970616501 319149349208259747245297)
              ·
                refine ⟨239362011906194810433973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 319149349208259747245297 239362011906194810433973)
                ·
                  refine ⟨22440188616205763478185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 239362011906194810433973 22440188616205763478185)
                  ·
                    rfl

theorem cell23_393319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 5, 2, 5].length) (baseStart_393319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_393319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_393319 prefixEnd_393319 := by exact prefixLift 393319
  have htrace : WordTrace (prefixWord ++ tailWord_393319) baseStart_393319 baseEnd_393319 := by
    simpa [prefixWord, tailWord_393319, baseEnd_393319] using wordTrace_append hprefix tailTrace_393319
  have hstable : (prefixWord ++ tailWord_393319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393319).length < 2 ^ (prefixWord ++ tailWord_393319).sum := by decide
  have hdescent : baseEnd_393319 < baseStart_393319 := by decide
  rcases family_descends (prefixWord ++ tailWord_393319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393365 : List Nat := [1, 3, 2, 1, 1, 1, 4, 1, 2, 1, 6]
def baseStart_393365 : Nat := 118140960795 + 393365 * 2 ^ 59
def prefixEnd_393365 : Nat := 4983230072969 + 3 ^ 40 * 393365 * 2
def baseEnd_393365 : Nat := 201985317655958691328453

theorem tailTrace_393365 : CollatzResearch.WordTrace tailWord_393365 prefixEnd_393365 201985317655958691328453 := by
  unfold tailWord_393365
  simp only [CollatzResearch.WordTrace]
  refine ⟨14347200219913261238525549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9564800146608840825683699 14347200219913261238525549)
  ·
    refine ⟨5380200082467472964447081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14347200219913261238525549 5380200082467472964447081)
    ·
      refine ⟨4035150061850604723335311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5380200082467472964447081 4035150061850604723335311)
      ·
        refine ⟨6052725092775907085002967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4035150061850604723335311 6052725092775907085002967)
        ·
          refine ⟨9079087639163860627504451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6052725092775907085002967 9079087639163860627504451)
          ·
            refine ⟨13618631458745790941256677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9079087639163860627504451 13618631458745790941256677)
            ·
              refine ⟨2553493398514835801485627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13618631458745790941256677 2553493398514835801485627)
              ·
                refine ⟨3830240097772253702228441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2553493398514835801485627 3830240097772253702228441)
                ·
                  refine ⟨2872680073329190276671331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3830240097772253702228441 2872680073329190276671331)
                  ·
                    refine ⟨4309020109993785415006997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2872680073329190276671331 4309020109993785415006997)
                    ·
                      refine ⟨201985317655958691328453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4309020109993785415006997 201985317655958691328453)
                      ·
                        rfl

theorem cell23_393365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 2, 1, 6].length) (baseStart_393365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_393365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_393365 prefixEnd_393365 := by exact prefixLift 393365
  have htrace : WordTrace (prefixWord ++ tailWord_393365) baseStart_393365 baseEnd_393365 := by
    simpa [prefixWord, tailWord_393365, baseEnd_393365] using wordTrace_append hprefix tailTrace_393365
  have hstable : (prefixWord ++ tailWord_393365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393365).length < 2 ^ (prefixWord ++ tailWord_393365).sum := by decide
  have hdescent : baseEnd_393365 < baseStart_393365 := by decide
  rcases family_descends (prefixWord ++ tailWord_393365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393415 : List Nat := [1, 1, 4, 1, 1, 1, 1, 1, 1, 6, 5]
def baseStart_393415 : Nat := 118140960795 + 393415 * 2 ^ 59
def prefixEnd_393415 : Nat := 4983230072969 + 3 ^ 40 * 393415 * 2
def baseEnd_393415 : Nat := 202010991688683495703223

theorem tailTrace_393415 : CollatzResearch.WordTrace tailWord_393415 prefixEnd_393415 202010991688683495703223 := by
  unfold tailWord_393415
  simp only [CollatzResearch.WordTrace]
  refine ⟨14349023869732119777845699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9566015913154746518563799 14349023869732119777845699)
  ·
    refine ⟨21523535804598179666768549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14349023869732119777845699 21523535804598179666768549)
    ·
      refine ⟨4035662963362158687519103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21523535804598179666768549 4035662963362158687519103)
      ·
        refine ⟨6053494445043238031278655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4035662963362158687519103 6053494445043238031278655)
        ·
          refine ⟨9080241667564857046917983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6053494445043238031278655 9080241667564857046917983)
          ·
            refine ⟨13620362501347285570376975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9080241667564857046917983 13620362501347285570376975)
            ·
              refine ⟨20430543752020928355565463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13620362501347285570376975 20430543752020928355565463)
              ·
                refine ⟨30645815628031392533348195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20430543752020928355565463 30645815628031392533348195)
                ·
                  refine ⟨45968723442047088800022293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30645815628031392533348195 45968723442047088800022293)
                  ·
                    refine ⟨2154783911345957287501045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 45968723442047088800022293 2154783911345957287501045)
                    ·
                      refine ⟨202010991688683495703223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2154783911345957287501045 202010991688683495703223)
                      ·
                        rfl

theorem cell23_393415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 6, 5].length) (baseStart_393415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_393415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_393415 prefixEnd_393415 := by exact prefixLift 393415
  have htrace : WordTrace (prefixWord ++ tailWord_393415) baseStart_393415 baseEnd_393415 := by
    simpa [prefixWord, tailWord_393415, baseEnd_393415] using wordTrace_append hprefix tailTrace_393415
  have hstable : (prefixWord ++ tailWord_393415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393415).length < 2 ^ (prefixWord ++ tailWord_393415).sum := by decide
  have hdescent : baseEnd_393415 < baseStart_393415 := by decide
  rcases family_descends (prefixWord ++ tailWord_393415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393435 : List Nat := [1, 1, 1, 1, 1, 1, 1, 5, 5, 6]
def baseStart_393435 : Nat := 118140960795 + 393435 * 2 ^ 59
def prefixEnd_393435 : Nat := 4983230072969 + 3 ^ 40 * 393435 * 2
def baseEnd_393435 : Nat := 67340420433924472484377

theorem tailTrace_393435 : CollatzResearch.WordTrace tailWord_393435 prefixEnd_393435 67340420433924472484377 := by
  unfold tailWord_393435
  simp only [CollatzResearch.WordTrace]
  refine ⟨14349753329659663193573759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9566502219773108795715839 14349753329659663193573759)
  ·
    refine ⟨21524629994489494790360639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14349753329659663193573759 21524629994489494790360639)
    ·
      refine ⟨32286944991734242185540959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21524629994489494790360639 32286944991734242185540959)
      ·
        refine ⟨48430417487601363278311439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32286944991734242185540959 48430417487601363278311439)
        ·
          refine ⟨72645626231402044917467159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48430417487601363278311439 72645626231402044917467159)
          ·
            refine ⟨108968439347103067376200739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72645626231402044917467159 108968439347103067376200739)
            ·
              refine ⟨163452659020654601064301109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108968439347103067376200739 163452659020654601064301109)
              ·
                refine ⟨15323686783186368849778229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 163452659020654601064301109 15323686783186368849778229)
                ·
                  refine ⟨1436595635923722079666709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15323686783186368849778229 1436595635923722079666709)
                  ·
                    refine ⟨67340420433924472484377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1436595635923722079666709 67340420433924472484377)
                    ·
                      rfl

theorem cell23_393435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5, 6].length) (baseStart_393435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_393435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_393435 prefixEnd_393435 := by exact prefixLift 393435
  have htrace : WordTrace (prefixWord ++ tailWord_393435) baseStart_393435 baseEnd_393435 := by
    simpa [prefixWord, tailWord_393435, baseEnd_393435] using wordTrace_append hprefix tailTrace_393435
  have hstable : (prefixWord ++ tailWord_393435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393435).length < 2 ^ (prefixWord ++ tailWord_393435).sum := by decide
  have hdescent : baseEnd_393435 < baseStart_393435 := by decide
  rcases family_descends (prefixWord ++ tailWord_393435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393459 : List Nat := [1, 1, 1, 2, 2, 4, 4, 2, 1, 1, 4]
def baseStart_393459 : Nat := 118140960795 + 393459 * 2 ^ 59
def prefixEnd_393459 : Nat := 4983230072969 + 3 ^ 40 * 393459 * 2
def baseEnd_393459 : Nat := 202033584837481323553021

theorem tailTrace_393459 : CollatzResearch.WordTrace tailWord_393459 prefixEnd_393459 202033584837481323553021 := by
  unfold tailWord_393459
  simp only [CollatzResearch.WordTrace]
  refine ⟨14350628681572715292447431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9567085787715143528298287 14350628681572715292447431)
  ·
    refine ⟨21525943022359072938671147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14350628681572715292447431 21525943022359072938671147)
    ·
      refine ⟨32288914533538609408006721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21525943022359072938671147 32288914533538609408006721)
      ·
        refine ⟨24216685900153957056005041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32288914533538609408006721 24216685900153957056005041)
        ·
          refine ⟨18162514425115467792003781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24216685900153957056005041 18162514425115467792003781)
          ·
            refine ⟨3405471454709150211000709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18162514425115467792003781 3405471454709150211000709)
            ·
              refine ⟨638525897757965664562633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3405471454709150211000709 638525897757965664562633)
              ·
                refine ⟨478894423318474248421975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 638525897757965664562633 478894423318474248421975)
                ·
                  refine ⟨718341634977711372632963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 478894423318474248421975 718341634977711372632963)
                  ·
                    refine ⟨1077512452466567058949445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 718341634977711372632963 1077512452466567058949445)
                    ·
                      refine ⟨202033584837481323553021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1077512452466567058949445 202033584837481323553021)
                      ·
                        rfl

theorem cell23_393459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 2, 1, 1, 4].length) (baseStart_393459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_393459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_393459 prefixEnd_393459 := by exact prefixLift 393459
  have htrace : WordTrace (prefixWord ++ tailWord_393459) baseStart_393459 baseEnd_393459 := by
    simpa [prefixWord, tailWord_393459, baseEnd_393459] using wordTrace_append hprefix tailTrace_393459
  have hstable : (prefixWord ++ tailWord_393459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393459).length < 2 ^ (prefixWord ++ tailWord_393459).sum := by decide
  have hdescent : baseEnd_393459 < baseStart_393459 := by decide
  rcases family_descends (prefixWord ++ tailWord_393459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393472 : List Nat := [2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 4]
def baseStart_393472 : Nat := 118140960795 + 393472 * 2 ^ 59
def prefixEnd_393472 : Nat := 4983230072969 + 3 ^ 40 * 393472 * 2
def baseEnd_393472 : Nat := 202040260085989772690461

theorem tailTrace_393472 : CollatzResearch.WordTrace tailWord_393472 prefixEnd_393472 202040260085989772690461 := by
  unfold tailWord_393472
  simp only [CollatzResearch.WordTrace]
  refine ⟨7175551415262809256335335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9567401887017079008447113 7175551415262809256335335)
  ·
    refine ⟨10763327122894213884503003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7175551415262809256335335 10763327122894213884503003)
    ·
      refine ⟨16144990684341320826754505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10763327122894213884503003 16144990684341320826754505)
      ·
        refine ⟨12108743013255990620065879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16144990684341320826754505 12108743013255990620065879)
        ·
          refine ⟨18163114519883985930098819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12108743013255990620065879 18163114519883985930098819)
          ·
            refine ⟨27244671779825978895148229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18163114519883985930098819 27244671779825978895148229)
            ·
              refine ⟨5108375958717371042840293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27244671779825978895148229 5108375958717371042840293)
              ·
                refine ⟨957820492259507070532555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5108375958717371042840293 957820492259507070532555)
                ·
                  refine ⟨1436730738389260605798833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 957820492259507070532555 1436730738389260605798833)
                  ·
                    refine ⟨1077548053791945454349125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1436730738389260605798833 1077548053791945454349125)
                    ·
                      refine ⟨202040260085989772690461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1077548053791945454349125 202040260085989772690461)
                      ·
                        rfl

theorem cell23_393472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 4].length) (baseStart_393472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_393472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_393472 prefixEnd_393472 := by exact prefixLift 393472
  have htrace : WordTrace (prefixWord ++ tailWord_393472) baseStart_393472 baseEnd_393472 := by
    simpa [prefixWord, tailWord_393472, baseEnd_393472] using wordTrace_append hprefix tailTrace_393472
  have hstable : (prefixWord ++ tailWord_393472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393472).length < 2 ^ (prefixWord ++ tailWord_393472).sum := by decide
  have hdescent : baseEnd_393472 < baseStart_393472 := by decide
  rcases family_descends (prefixWord ++ tailWord_393472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393493 : List Nat := [1, 3, 2, 1, 2, 1, 2, 6, 1, 2, 2]
def baseStart_393493 : Nat := 118140960795 + 393493 * 2 ^ 59
def prefixEnd_393493 : Nat := 4983230072969 + 3 ^ 40 * 393493 * 2
def baseEnd_393493 : Nat := 202051043179734190527865

theorem tailTrace_393493 : CollatzResearch.WordTrace tailWord_393493 prefixEnd_393493 202051043179734190527865 := by
  unfold tailWord_393493
  simp only [CollatzResearch.WordTrace]
  refine ⟨14351868763449539099185133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9567912508966359399456755 14351868763449539099185133)
  ·
    refine ⟨5381950786293577162194425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14351868763449539099185133 5381950786293577162194425)
    ·
      refine ⟨4036463089720182871645819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5381950786293577162194425 4036463089720182871645819)
      ·
        refine ⟨6054694634580274307468729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4036463089720182871645819 6054694634580274307468729)
        ·
          refine ⟨4541020975935205730601547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6054694634580274307468729 4541020975935205730601547)
          ·
            refine ⟨6811531463902808595902321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4541020975935205730601547 6811531463902808595902321)
            ·
              refine ⟨5108648597927106446926741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6811531463902808595902321 5108648597927106446926741)
              ·
                refine ⟨239467903027833114699691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5108648597927106446926741 239467903027833114699691)
                ·
                  refine ⟨359201854541749672049537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 239467903027833114699691 359201854541749672049537)
                  ·
                    refine ⟨269401390906312254037153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 359201854541749672049537 269401390906312254037153)
                    ·
                      refine ⟨202051043179734190527865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 269401390906312254037153 202051043179734190527865)
                      ·
                        rfl

theorem cell23_393493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 6, 1, 2, 2].length) (baseStart_393493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_393493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_393493 prefixEnd_393493 := by exact prefixLift 393493
  have htrace : WordTrace (prefixWord ++ tailWord_393493) baseStart_393493 baseEnd_393493 := by
    simpa [prefixWord, tailWord_393493, baseEnd_393493] using wordTrace_append hprefix tailTrace_393493
  have hstable : (prefixWord ++ tailWord_393493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393493).length < 2 ^ (prefixWord ++ tailWord_393493).sum := by decide
  have hdescent : baseEnd_393493 < baseStart_393493 := by decide
  rcases family_descends (prefixWord ++ tailWord_393493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393503 : List Nat := [1, 1, 2, 4, 3, 3, 2, 1, 2, 4]
def baseStart_393503 : Nat := 118140960795 + 393503 * 2 ^ 59
def prefixEnd_393503 : Nat := 4983230072969 + 3 ^ 40 * 393503 * 2
def baseEnd_393503 : Nat := 67352059328759717134273

theorem tailTrace_393503 : CollatzResearch.WordTrace tailWord_393503 prefixEnd_393503 67352059328759717134273 := by
  unfold tailWord_393503
  simp only [CollatzResearch.WordTrace]
  refine ⟨14352233493413310807049163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9568155662275540538032775 14352233493413310807049163)
  ·
    refine ⟨21528350240119966210573745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14352233493413310807049163 21528350240119966210573745)
    ·
      refine ⟨16146262680089974657930309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21528350240119966210573745 16146262680089974657930309)
      ·
        refine ⟨3027424252516870248361933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16146262680089974657930309 3027424252516870248361933)
        ·
          refine ⟨1135284094693826343135725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3027424252516870248361933 1135284094693826343135725)
          ·
            refine ⟨425731535510184878675897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1135284094693826343135725 425731535510184878675897)
            ·
              refine ⟨319298651632638659006923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 425731535510184878675897 319298651632638659006923)
              ·
                refine ⟨478947977448957988510385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 319298651632638659006923 478947977448957988510385)
                ·
                  refine ⟨359210983086718491382789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 478947977448957988510385 359210983086718491382789)
                  ·
                    refine ⟨67352059328759717134273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 359210983086718491382789 67352059328759717134273)
                    ·
                      rfl

theorem cell23_393503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 2, 1, 2, 4].length) (baseStart_393503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_393503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_393503 prefixEnd_393503 := by exact prefixLift 393503
  have htrace : WordTrace (prefixWord ++ tailWord_393503) baseStart_393503 baseEnd_393503 := by
    simpa [prefixWord, tailWord_393503, baseEnd_393503] using wordTrace_append hprefix tailTrace_393503
  have hstable : (prefixWord ++ tailWord_393503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393503).length < 2 ^ (prefixWord ++ tailWord_393503).sum := by decide
  have hdescent : baseEnd_393503 < baseStart_393503 := by decide
  rcases family_descends (prefixWord ++ tailWord_393503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393640 : List Nat := [2, 1, 6, 1, 1, 3, 1, 3, 5]
def baseStart_393640 : Nat := 118140960795 + 393640 * 2 ^ 59
def prefixEnd_393640 : Nat := 4983230072969 + 3 ^ 40 * 393640 * 2
def baseEnd_393640 : Nat := 22458502759549457265521

theorem tailTrace_393640 : CollatzResearch.WordTrace tailWord_393640 prefixEnd_393640 22458502759549457265521 := by
  unfold tailWord_393640
  simp only [CollatzResearch.WordTrace]
  refine ⟨7178615146958491602393187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9571486862611322136524249 7178615146958491602393187)
  ·
    refine ⟨10767922720437737403589781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7178615146958491602393187 10767922720437737403589781)
    ·
      refine ⟨504746377520518940793271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 10767922720437737403589781 504746377520518940793271)
      ·
        refine ⟨757119566280778411189907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 504746377520518940793271 757119566280778411189907)
        ·
          refine ⟨1135679349421167616784861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 757119566280778411189907 1135679349421167616784861)
          ·
            refine ⟨425879756032937856294323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1135679349421167616784861 425879756032937856294323)
            ·
              refine ⟨638819634049406784441485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 425879756032937856294323 638819634049406784441485)
              ·
                refine ⟨239557362768527544165557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 638819634049406784441485 239557362768527544165557)
                ·
                  refine ⟨22458502759549457265521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 239557362768527544165557 22458502759549457265521)
                  ·
                    rfl

theorem cell23_393640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 3, 5].length) (baseStart_393640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_393640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_393640 prefixEnd_393640 := by exact prefixLift 393640
  have htrace : WordTrace (prefixWord ++ tailWord_393640) baseStart_393640 baseEnd_393640 := by
    simpa [prefixWord, tailWord_393640, baseEnd_393640] using wordTrace_append hprefix tailTrace_393640
  have hstable : (prefixWord ++ tailWord_393640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393640).length < 2 ^ (prefixWord ++ tailWord_393640).sum := by decide
  have hdescent : baseEnd_393640 < baseStart_393640 := by decide
  rcases family_descends (prefixWord ++ tailWord_393640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393693 : List Nat := [1, 4, 3, 1, 1, 1, 4, 1, 2, 2, 3]
def baseStart_393693 : Nat := 118140960795 + 393693 * 2 ^ 59
def prefixEnd_393693 : Nat := 4983230072969 + 3 ^ 40 * 393693 * 2
def baseEnd_393693 : Nat := 202153739310633408026945

theorem tailTrace_393693 : CollatzResearch.WordTrace tailWord_393693 prefixEnd_393693 202153739310633408026945 := by
  unfold tailWord_393693
  simp only [CollatzResearch.WordTrace]
  refine ⟨14359163362724973256465733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9572775575149982170977155 14359163362724973256465733)
  ·
    refine ⟨2692343130510932485587325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14359163362724973256465733 2692343130510932485587325)
    ·
      refine ⟨1009628673941599682095247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2692343130510932485587325 1009628673941599682095247)
      ·
        refine ⟨1514443010912399523142871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1009628673941599682095247 1514443010912399523142871)
        ·
          refine ⟨2271664516368599284714307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1514443010912399523142871 2271664516368599284714307)
          ·
            refine ⟨3407496774552898927071461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2271664516368599284714307 3407496774552898927071461)
            ·
              refine ⟨638905645228668548825899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3407496774552898927071461 638905645228668548825899)
              ·
                refine ⟨958358467843002823238849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 638905645228668548825899 958358467843002823238849)
                ·
                  refine ⟨718768850882252117429137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 958358467843002823238849 718768850882252117429137)
                  ·
                    refine ⟨539076638161689088071853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 718768850882252117429137 539076638161689088071853)
                    ·
                      refine ⟨202153739310633408026945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 539076638161689088071853 202153739310633408026945)
                      ·
                        rfl

theorem cell23_393693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_393693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_393693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_393693 prefixEnd_393693 := by exact prefixLift 393693
  have htrace : WordTrace (prefixWord ++ tailWord_393693) baseStart_393693 baseEnd_393693 := by
    simpa [prefixWord, tailWord_393693, baseEnd_393693] using wordTrace_append hprefix tailTrace_393693
  have hstable : (prefixWord ++ tailWord_393693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393693).length < 2 ^ (prefixWord ++ tailWord_393693).sum := by decide
  have hdescent : baseEnd_393693 < baseStart_393693 := by decide
  rcases family_descends (prefixWord ++ tailWord_393693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393717 : List Nat := [1, 3, 5, 1, 2, 1, 1, 4, 1, 4]
def baseStart_393717 : Nat := 118140960795 + 393717 * 2 ^ 59
def prefixEnd_393717 : Nat := 4983230072969 + 3 ^ 40 * 393717 * 2
def baseEnd_393717 : Nat := 67388687615447104708945

theorem tailTrace_393717 : CollatzResearch.WordTrace tailWord_393717 prefixEnd_393717 67388687615447104708945 := by
  unfold tailWord_393717
  simp only [CollatzResearch.WordTrace]
  refine ⟨14360038714638025355339405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9573359143092016903559603 14360038714638025355339405)
  ·
    refine ⟨5385014517989259508252277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14360038714638025355339405 5385014517989259508252277)
    ·
      refine ⟨504845111061493078898651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5385014517989259508252277 504845111061493078898651)
      ·
        refine ⟨757267666592239618347977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 504845111061493078898651 757267666592239618347977)
        ·
          refine ⟨567950749944179713760983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 757267666592239618347977 567950749944179713760983)
          ·
            refine ⟨851926124916269570641475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 567950749944179713760983 851926124916269570641475)
            ·
              refine ⟨1277889187374404355962213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 851926124916269570641475 1277889187374404355962213)
              ·
                refine ⟨239604222632700816742915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1277889187374404355962213 239604222632700816742915)
                ·
                  refine ⟨359406333949051225114373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 239604222632700816742915 359406333949051225114373)
                  ·
                    refine ⟨67388687615447104708945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 359406333949051225114373 67388687615447104708945)
                    ·
                      rfl

theorem cell23_393717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_393717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_393717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_393717 prefixEnd_393717 := by exact prefixLift 393717
  have htrace : WordTrace (prefixWord ++ tailWord_393717) baseStart_393717 baseEnd_393717 := by
    simpa [prefixWord, tailWord_393717, baseEnd_393717] using wordTrace_append hprefix tailTrace_393717
  have hstable : (prefixWord ++ tailWord_393717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393717).length < 2 ^ (prefixWord ++ tailWord_393717).sum := by decide
  have hdescent : baseEnd_393717 < baseStart_393717 := by decide
  rcases family_descends (prefixWord ++ tailWord_393717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393756 : List Nat := [2, 2, 3, 1, 2, 2, 2, 2, 1, 6]
def baseStart_393756 : Nat := 118140960795 + 393756 * 2 ^ 59
def prefixEnd_393756 : Nat := 4983230072969 + 3 ^ 40 * 393756 * 2
def baseEnd_393756 : Nat := 67395362863955553846385

theorem tailTrace_393756 : CollatzResearch.WordTrace tailWord_393756 prefixEnd_393756 67395362863955553846385 := by
  unfold tailWord_393756
  simp only [CollatzResearch.WordTrace]
  refine ⟨7180730580748367508004561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9574307440997823344006081 7180730580748367508004561)
  ·
    refine ⟨5385547935561275631003421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7180730580748367508004561 5385547935561275631003421)
    ·
      refine ⟨2019580475835478361626283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5385547935561275631003421 2019580475835478361626283)
      ·
        refine ⟨3029370713753217542439425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2019580475835478361626283 3029370713753217542439425)
        ·
          refine ⟨2272028035314913156829569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3029370713753217542439425 2272028035314913156829569)
          ·
            refine ⟨1704021026486184867622177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2272028035314913156829569 1704021026486184867622177)
            ·
              refine ⟨1278015769864638650716633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1704021026486184867622177 1278015769864638650716633)
              ·
                refine ⟨958511827398478988037475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1278015769864638650716633 958511827398478988037475)
                ·
                  refine ⟨1437767741097718482056213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 958511827398478988037475 1437767741097718482056213)
                  ·
                    refine ⟨67395362863955553846385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1437767741097718482056213 67395362863955553846385)
                    ·
                      rfl

theorem cell23_393756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 2, 1, 6].length) (baseStart_393756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_393756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_393756 prefixEnd_393756 := by exact prefixLift 393756
  have htrace : WordTrace (prefixWord ++ tailWord_393756) baseStart_393756 baseEnd_393756 := by
    simpa [prefixWord, tailWord_393756, baseEnd_393756] using wordTrace_append hprefix tailTrace_393756
  have hstable : (prefixWord ++ tailWord_393756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393756).length < 2 ^ (prefixWord ++ tailWord_393756).sum := by decide
  have hdescent : baseEnd_393756 < baseStart_393756 := by decide
  rcases family_descends (prefixWord ++ tailWord_393756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393757 : List Nat := [1, 4, 2, 2, 1, 3, 2, 3, 1, 1, 3]
def baseStart_393757 : Nat := 118140960795 + 393757 * 2 ^ 59
def prefixEnd_393757 : Nat := 4983230072969 + 3 ^ 40 * 393757 * 2
def baseEnd_393757 : Nat := 202186602072521157626651

theorem tailTrace_393757 : CollatzResearch.WordTrace tailWord_393757 prefixEnd_393757 202186602072521157626651 := by
  unfold tailWord_393757
  simp only [CollatzResearch.WordTrace]
  refine ⟨14361497634493112186795525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9574331756328741457863683 14361497634493112186795525)
  ·
    refine ⟨2692780806467458535024161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14361497634493112186795525 2692780806467458535024161)
    ·
      refine ⟨2019585604850593901268121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2692780806467458535024161 2019585604850593901268121)
      ·
        refine ⟨1514689203637945425951091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2019585604850593901268121 1514689203637945425951091)
        ·
          refine ⟨2272033805456918138926637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1514689203637945425951091 2272033805456918138926637)
          ·
            refine ⟨852012677046344302097489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2272033805456918138926637 852012677046344302097489)
            ·
              refine ⟨639009507784758226573117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 852012677046344302097489 639009507784758226573117)
              ·
                refine ⟨239628565419284334964919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 639009507784758226573117 239628565419284334964919)
                ·
                  refine ⟨359442848128926502447379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 239628565419284334964919 359442848128926502447379)
                  ·
                    refine ⟨539164272193389753671069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 359442848128926502447379 539164272193389753671069)
                    ·
                      refine ⟨202186602072521157626651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 539164272193389753671069 202186602072521157626651)
                      ·
                        rfl

theorem cell23_393757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 3, 1, 1, 3].length) (baseStart_393757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_393757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_393757 prefixEnd_393757 := by exact prefixLift 393757
  have htrace : WordTrace (prefixWord ++ tailWord_393757) baseStart_393757 baseEnd_393757 := by
    simpa [prefixWord, tailWord_393757, baseEnd_393757] using wordTrace_append hprefix tailTrace_393757
  have hstable : (prefixWord ++ tailWord_393757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393757).length < 2 ^ (prefixWord ++ tailWord_393757).sum := by decide
  have hdescent : baseEnd_393757 < baseStart_393757 := by decide
  rcases family_descends (prefixWord ++ tailWord_393757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393759 : List Nat := [1, 1, 2, 4, 1, 1, 1, 2, 3, 1, 6]
def baseStart_393759 : Nat := 118140960795 + 393759 * 2 ^ 59
def prefixEnd_393759 : Nat := 4983230072969 + 3 ^ 40 * 393759 * 2
def baseEnd_393759 : Nat := 202187629033830149801641

theorem tailTrace_393759 : CollatzResearch.WordTrace tailWord_393759 prefixEnd_393759 202187629033830149801641 := by
  unfold tailWord_393759
  simp only [CollatzResearch.WordTrace]
  refine ⟨14361570580485866528368331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9574380386990577685578887 14361570580485866528368331)
  ·
    refine ⟨21542355870728799792552497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14361570580485866528368331 21542355870728799792552497)
    ·
      refine ⟨16156766903046599844414373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21542355870728799792552497 16156766903046599844414373)
      ·
        refine ⟨3029393794321237470827695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16156766903046599844414373 3029393794321237470827695)
        ·
          refine ⟨4544090691481856206241543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3029393794321237470827695 4544090691481856206241543)
          ·
            refine ⟨6816136037222784309362315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4544090691481856206241543 6816136037222784309362315)
            ·
              refine ⟨10224204055834176464043473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6816136037222784309362315 10224204055834176464043473)
              ·
                refine ⟨7668153041875632348032605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10224204055834176464043473 7668153041875632348032605)
                ·
                  refine ⟨2875557390703362130512227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7668153041875632348032605 2875557390703362130512227)
                  ·
                    refine ⟨4313336086055043195768341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2875557390703362130512227 4313336086055043195768341)
                    ·
                      refine ⟨202187629033830149801641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4313336086055043195768341 202187629033830149801641)
                      ·
                        rfl

theorem cell23_393759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_393759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_393759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_393759 prefixEnd_393759 := by exact prefixLift 393759
  have htrace : WordTrace (prefixWord ++ tailWord_393759) baseStart_393759 baseEnd_393759 := by
    simpa [prefixWord, tailWord_393759, baseEnd_393759] using wordTrace_append hprefix tailTrace_393759
  have hstable : (prefixWord ++ tailWord_393759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393759).length < 2 ^ (prefixWord ++ tailWord_393759).sum := by decide
  have hdescent : baseEnd_393759 < baseStart_393759 := by decide
  rcases family_descends (prefixWord ++ tailWord_393759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393763 : List Nat := [1, 1, 1, 4, 4, 2, 1, 3, 1, 1, 4]
def baseStart_393763 : Nat := 118140960795 + 393763 * 2 ^ 59
def prefixEnd_393763 : Nat := 4983230072969 + 3 ^ 40 * 393763 * 2
def baseEnd_393763 : Nat := 202189682956448134151623

theorem tailTrace_393763 : CollatzResearch.WordTrace tailWord_393763 prefixEnd_393763 202189682956448134151623 := by
  unfold tailWord_393763
  simp only [CollatzResearch.WordTrace]
  refine ⟨14361716472471375211513943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9574477648314250141009295 14361716472471375211513943)
  ·
    refine ⟨21542574708707062817270915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14361716472471375211513943 21542574708707062817270915)
    ·
      refine ⟨32313862063060594225906373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21542574708707062817270915 32313862063060594225906373)
      ·
        refine ⟨6058849136823861417357445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32313862063060594225906373 6058849136823861417357445)
        ·
          refine ⟨1136034213154474015754521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6058849136823861417357445 1136034213154474015754521)
          ·
            refine ⟨852025659865855511815891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1136034213154474015754521 852025659865855511815891)
            ·
              refine ⟨1278038489798783267723837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 852025659865855511815891 1278038489798783267723837)
              ·
                refine ⟨479264433674543725396439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1278038489798783267723837 479264433674543725396439)
                ·
                  refine ⟨718896650511815588094659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 479264433674543725396439 718896650511815588094659)
                  ·
                    refine ⟨1078344975767723382141989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 718896650511815588094659 1078344975767723382141989)
                    ·
                      refine ⟨202189682956448134151623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1078344975767723382141989 202189682956448134151623)
                      ·
                        rfl

theorem cell23_393763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 3, 1, 1, 4].length) (baseStart_393763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_393763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_393763 prefixEnd_393763 := by exact prefixLift 393763
  have htrace : WordTrace (prefixWord ++ tailWord_393763) baseStart_393763 baseEnd_393763 := by
    simpa [prefixWord, tailWord_393763, baseEnd_393763] using wordTrace_append hprefix tailTrace_393763
  have hstable : (prefixWord ++ tailWord_393763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393763).length < 2 ^ (prefixWord ++ tailWord_393763).sum := by decide
  have hdescent : baseEnd_393763 < baseStart_393763 := by decide
  rcases family_descends (prefixWord ++ tailWord_393763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393793 : List Nat := [1, 2, 5, 1, 1, 2, 3, 1, 1, 2, 4]
def baseStart_393793 : Nat := 118140960795 + 393793 * 2 ^ 59
def prefixEnd_393793 : Nat := 4983230072969 + 3 ^ 40 * 393793 * 2
def baseEnd_393793 : Nat := 202205087376083016776485

theorem tailTrace_393793 : CollatzResearch.WordTrace tailWord_393793 prefixEnd_393793 202205087376083016776485 := by
  unfold tailWord_393793
  simp only [CollatzResearch.WordTrace]
  refine ⟨14362810662362690335106033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9575207108241793556737355 14362810662362690335106033)
  ·
    refine ⟨10772107996772017751329525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14362810662362690335106033 10772107996772017751329525)
    ·
      refine ⟨1009885124697376664187143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10772107996772017751329525 1009885124697376664187143)
      ·
        refine ⟨1514827687046064996280715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1009885124697376664187143 1514827687046064996280715)
        ·
          refine ⟨2272241530569097494421073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1514827687046064996280715 2272241530569097494421073)
          ·
            refine ⟨1704181147926823120815805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2272241530569097494421073 1704181147926823120815805)
            ·
              refine ⟨639067930472558670305927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1704181147926823120815805 639067930472558670305927)
              ·
                refine ⟨958601895708838005458891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 639067930472558670305927 958601895708838005458891)
                ·
                  refine ⟨1437902843563257008188337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 958601895708838005458891 1437902843563257008188337)
                  ·
                    refine ⟨1078427132672442756141253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1437902843563257008188337 1078427132672442756141253)
                    ·
                      refine ⟨202205087376083016776485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1078427132672442756141253 202205087376083016776485)
                      ·
                        rfl

theorem cell23_393793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_393793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_393793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_393793 prefixEnd_393793 := by exact prefixLift 393793
  have htrace : WordTrace (prefixWord ++ tailWord_393793) baseStart_393793 baseEnd_393793 := by
    simpa [prefixWord, tailWord_393793, baseEnd_393793] using wordTrace_append hprefix tailTrace_393793
  have hstable : (prefixWord ++ tailWord_393793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393793).length < 2 ^ (prefixWord ++ tailWord_393793).sum := by decide
  have hdescent : baseEnd_393793 < baseStart_393793 := by decide
  rcases family_descends (prefixWord ++ tailWord_393793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393813 : List Nat := [1, 3, 2, 2, 1, 1, 3, 2, 4, 1, 3]
def baseStart_393813 : Nat := 118140960795 + 393813 * 2 ^ 59
def prefixEnd_393813 : Nat := 4983230072969 + 3 ^ 40 * 393813 * 2
def baseEnd_393813 : Nat := 202215356989172938526393

theorem tailTrace_393813 : CollatzResearch.WordTrace tailWord_393813 prefixEnd_393813 202215356989172938526393 := by
  unfold tailWord_393813
  simp only [CollatzResearch.WordTrace]
  refine ⟨14363540122290233750834093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9575693414860155833889395 14363540122290233750834093)
  ·
    refine ⟨5386327545858837656562785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14363540122290233750834093 5386327545858837656562785)
    ·
      refine ⟨4039745659394128242422089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5386327545858837656562785 4039745659394128242422089)
      ·
        refine ⟨3029809244545596181816567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4039745659394128242422089 3029809244545596181816567)
        ·
          refine ⟨4544713866818394272724851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3029809244545596181816567 4544713866818394272724851)
          ·
            refine ⟨6817070800227591409087277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4544713866818394272724851 6817070800227591409087277)
            ·
              refine ⟨2556401550085346778407729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6817070800227591409087277 2556401550085346778407729)
              ·
                refine ⟨1917301162564010083805797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2556401550085346778407729 1917301162564010083805797)
                ·
                  refine ⟨359493967980751890713587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1917301162564010083805797 359493967980751890713587)
                  ·
                    refine ⟨539240951971127836070381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 359493967980751890713587 539240951971127836070381)
                    ·
                      refine ⟨202215356989172938526393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 539240951971127836070381 202215356989172938526393)
                      ·
                        rfl

theorem cell23_393813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 2, 4, 1, 3].length) (baseStart_393813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_393813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_393813 prefixEnd_393813 := by exact prefixLift 393813
  have htrace : WordTrace (prefixWord ++ tailWord_393813) baseStart_393813 baseEnd_393813 := by
    simpa [prefixWord, tailWord_393813, baseEnd_393813] using wordTrace_append hprefix tailTrace_393813
  have hstable : (prefixWord ++ tailWord_393813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393813).length < 2 ^ (prefixWord ++ tailWord_393813).sum := by decide
  have hdescent : baseEnd_393813 < baseStart_393813 := by decide
  rcases family_descends (prefixWord ++ tailWord_393813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393856 : List Nat := [2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 5]
def baseStart_393856 : Nat := 118140960795 + 393856 * 2 ^ 59
def prefixEnd_393856 : Nat := 4983230072969 + 3 ^ 40 * 393856 * 2
def baseEnd_393856 : Nat := 202237436657316270288695

theorem tailTrace_393856 : CollatzResearch.WordTrace tailWord_393856 prefixEnd_393856 202237436657316270288695 := by
  unfold tailWord_393856
  simp only [CollatzResearch.WordTrace]
  refine ⟨7182554230567226047324711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9576738974089634729766281 7182554230567226047324711)
  ·
    refine ⟨10773831345850839070987067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7182554230567226047324711 10773831345850839070987067)
    ·
      refine ⟨16160747018776258606480601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10773831345850839070987067 16160747018776258606480601)
      ·
        refine ⟨12120560264082193954860451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16160747018776258606480601 12120560264082193954860451)
        ·
          refine ⟨18180840396123290932290677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12120560264082193954860451 18180840396123290932290677)
          ·
            refine ⟨1704453787136558524902251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18180840396123290932290677 1704453787136558524902251)
            ·
              refine ⟨2556680680704837787353377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1704453787136558524902251 2556680680704837787353377)
              ·
                refine ⟨1917510510528628340515033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2556680680704837787353377 1917510510528628340515033)
                ·
                  refine ⟨1438132882896471255386275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1917510510528628340515033 1438132882896471255386275)
                  ·
                    refine ⟨2157199324344706883079413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1438132882896471255386275 2157199324344706883079413)
                    ·
                      refine ⟨202237436657316270288695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2157199324344706883079413 202237436657316270288695)
                      ·
                        rfl

theorem cell23_393856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 5].length) (baseStart_393856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_393856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_393856 prefixEnd_393856 := by exact prefixLift 393856
  have htrace : WordTrace (prefixWord ++ tailWord_393856) baseStart_393856 baseEnd_393856 := by
    simpa [prefixWord, tailWord_393856, baseEnd_393856] using wordTrace_append hprefix tailTrace_393856
  have hstable : (prefixWord ++ tailWord_393856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393856).length < 2 ^ (prefixWord ++ tailWord_393856).sum := by decide
  have hdescent : baseEnd_393856 < baseStart_393856 := by decide
  rcases family_descends (prefixWord ++ tailWord_393856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393870 : List Nat := [4, 1, 1, 3, 1, 1, 3, 2, 1, 4, 2]
def baseStart_393870 : Nat := 118140960795 + 393870 * 2 ^ 59
def prefixEnd_393870 : Nat := 4983230072969 + 3 ^ 40 * 393870 * 2
def baseEnd_393870 : Nat := 202244625386479215513631

theorem tailTrace_393870 : CollatzResearch.WordTrace tailWord_393870 prefixEnd_393870 202244625386479215513631 := by
  unfold tailWord_393870
  simp only [CollatzResearch.WordTrace]
  refine ⟨1795702385385466560707383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9577079388722488323772709 1795702385385466560707383)
  ·
    refine ⟨2693553578078199841061075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1795702385385466560707383 2693553578078199841061075)
    ·
      refine ⟨4040330367117299761591613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2693553578078199841061075 4040330367117299761591613)
      ·
        refine ⟨1515123887668987410596855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4040330367117299761591613 1515123887668987410596855)
        ·
          refine ⟨2272685831503481115895283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1515123887668987410596855 2272685831503481115895283)
          ·
            refine ⟨3409028747255221673842925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2272685831503481115895283 3409028747255221673842925)
            ·
              refine ⟨1278385780220708127691097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3409028747255221673842925 1278385780220708127691097)
              ·
                refine ⟨958789335165531095768323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1278385780220708127691097 958789335165531095768323)
                ·
                  refine ⟨1438184002748296643652485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 958789335165531095768323 1438184002748296643652485)
                  ·
                    refine ⟨269659500515305620684841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1438184002748296643652485 269659500515305620684841)
                    ·
                      refine ⟨202244625386479215513631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 269659500515305620684841 202244625386479215513631)
                      ·
                        rfl

theorem cell23_393870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 2, 1, 4, 2].length) (baseStart_393870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_393870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_393870 prefixEnd_393870 := by exact prefixLift 393870
  have htrace : WordTrace (prefixWord ++ tailWord_393870) baseStart_393870 baseEnd_393870 := by
    simpa [prefixWord, tailWord_393870, baseEnd_393870] using wordTrace_append hprefix tailTrace_393870
  have hstable : (prefixWord ++ tailWord_393870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393870).length < 2 ^ (prefixWord ++ tailWord_393870).sum := by decide
  have hdescent : baseEnd_393870 < baseStart_393870 := by decide
  rcases family_descends (prefixWord ++ tailWord_393870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393874 : List Nat := [3, 2, 3, 1, 2, 2, 3, 1, 1, 3, 2]
def baseStart_393874 : Nat := 118140960795 + 393874 * 2 ^ 59
def prefixEnd_393874 : Nat := 4983230072969 + 3 ^ 40 * 393874 * 2
def baseEnd_393874 : Nat := 202246679309097199863613

theorem tailTrace_393874 : CollatzResearch.WordTrace tailWord_393874 prefixEnd_393874 202246679309097199863613 := by
  unfold tailWord_393874
  simp only [CollatzResearch.WordTrace]
  refine ⟨3591441243767310292201169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9577176650046160779203117 3591441243767310292201169)
  ·
    refine ⟨2693580932825482719150877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3591441243767310292201169 2693580932825482719150877)
    ·
      refine ⟨1010092849809556019681579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2693580932825482719150877 1010092849809556019681579)
      ·
        refine ⟨1515139274714334029522369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1010092849809556019681579 1515139274714334029522369)
        ·
          refine ⟨1136354456035750522141777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1515139274714334029522369 1136354456035750522141777)
          ·
            refine ⟨852265842026812891606333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1136354456035750522141777 852265842026812891606333)
            ·
              refine ⟨319599690760054834352375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 852265842026812891606333 319599690760054834352375)
              ·
                refine ⟨479399536140082251528563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 319599690760054834352375 479399536140082251528563)
                ·
                  refine ⟨719099304210123377292845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 479399536140082251528563 719099304210123377292845)
                  ·
                    refine ⟨269662239078796266484817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 719099304210123377292845 269662239078796266484817)
                    ·
                      refine ⟨202246679309097199863613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 269662239078796266484817 202246679309097199863613)
                      ·
                        rfl

theorem cell23_393874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 3, 1, 1, 3, 2].length) (baseStart_393874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_393874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_393874 prefixEnd_393874 := by exact prefixLift 393874
  have htrace : WordTrace (prefixWord ++ tailWord_393874) baseStart_393874 baseEnd_393874 := by
    simpa [prefixWord, tailWord_393874, baseEnd_393874] using wordTrace_append hprefix tailTrace_393874
  have hstable : (prefixWord ++ tailWord_393874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393874).length < 2 ^ (prefixWord ++ tailWord_393874).sum := by decide
  have hdescent : baseEnd_393874 < baseStart_393874 := by decide
  rcases family_descends (prefixWord ++ tailWord_393874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393903 : List Nat := [1, 1, 2, 1, 2, 6, 1, 1, 2, 3, 3]
def baseStart_393903 : Nat := 118140960795 + 393903 * 2 ^ 59
def prefixEnd_393903 : Nat := 4983230072969 + 3 ^ 40 * 393903 * 2
def baseEnd_393903 : Nat := 202261570248077586400979

theorem tailTrace_393903 : CollatzResearch.WordTrace tailWord_393903 prefixEnd_393903 202261570248077586400979 := by
  unfold tailWord_393903
  simp only [CollatzResearch.WordTrace]
  refine ⟨14366822691964179121610363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9577881794642786081073575 14366822691964179121610363)
  ·
    refine ⟨21550234037946268682415545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14366822691964179121610363 21550234037946268682415545)
    ·
      refine ⟨16162675528459701511811659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21550234037946268682415545 16162675528459701511811659)
      ·
        refine ⟨24244013292689552267717489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16162675528459701511811659 24244013292689552267717489)
        ·
          refine ⟨18183009969517164200788117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24244013292689552267717489 18183009969517164200788117)
          ·
            refine ⟨852328592321117071911943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 18183009969517164200788117 852328592321117071911943)
            ·
              refine ⟨1278492888481675607867915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 852328592321117071911943 1278492888481675607867915)
              ·
                refine ⟨1917739332722513411801873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1278492888481675607867915 1917739332722513411801873)
                ·
                  refine ⟨1438304499541885058851405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1917739332722513411801873 1438304499541885058851405)
                  ·
                    refine ⟨539364187328206897069277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1438304499541885058851405 539364187328206897069277)
                    ·
                      refine ⟨202261570248077586400979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 539364187328206897069277 202261570248077586400979)
                      ·
                        rfl

theorem cell23_393903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 1, 2, 3, 3].length) (baseStart_393903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_393903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_393903 prefixEnd_393903 := by exact prefixLift 393903
  have htrace : WordTrace (prefixWord ++ tailWord_393903) baseStart_393903 baseEnd_393903 := by
    simpa [prefixWord, tailWord_393903, baseEnd_393903] using wordTrace_append hprefix tailTrace_393903
  have hstable : (prefixWord ++ tailWord_393903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393903).length < 2 ^ (prefixWord ++ tailWord_393903).sum := by decide
  have hdescent : baseEnd_393903 < baseStart_393903 := by decide
  rcases family_descends (prefixWord ++ tailWord_393903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393906 : List Nat := [3, 2, 1, 1, 1, 2, 1, 4, 1, 7]
def baseStart_393906 : Nat := 118140960795 + 393906 * 2 ^ 59
def prefixEnd_393906 : Nat := 4983230072969 + 3 ^ 40 * 393906 * 2
def baseEnd_393906 : Nat := 67421036896680358221155

theorem tailTrace_393906 : CollatzResearch.WordTrace tailWord_393906 prefixEnd_393906 67421036896680358221155 := by
  unfold tailWord_393906
  simp only [CollatzResearch.WordTrace]
  refine ⟨3591733027738327658492393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9577954740635540422646381 3591733027738327658492393)
  ·
    refine ⟨2693799770803745743869295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3591733027738327658492393 2693799770803745743869295)
    ·
      refine ⟨4040699656205618615803943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2693799770803745743869295 4040699656205618615803943)
      ·
        refine ⟨6061049484308427923705915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4040699656205618615803943 6061049484308427923705915)
        ·
          refine ⟨9091574226462641885558873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6061049484308427923705915 9091574226462641885558873)
          ·
            refine ⟨6818680669846981414169155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9091574226462641885558873 6818680669846981414169155)
            ·
              refine ⟨10228021004770472121253733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6818680669846981414169155 10228021004770472121253733)
              ·
                refine ⟨1917753938394463522735075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10228021004770472121253733 1917753938394463522735075)
                ·
                  refine ⟨2876630907591695284102613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1917753938394463522735075 2876630907591695284102613)
                  ·
                    refine ⟨67421036896680358221155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2876630907591695284102613 67421036896680358221155)
                    ·
                      rfl

theorem cell23_393906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 4, 1, 7].length) (baseStart_393906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_393906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_393906 prefixEnd_393906 := by exact prefixLift 393906
  have htrace : WordTrace (prefixWord ++ tailWord_393906) baseStart_393906 baseEnd_393906 := by
    simpa [prefixWord, tailWord_393906, baseEnd_393906] using wordTrace_append hprefix tailTrace_393906
  have hstable : (prefixWord ++ tailWord_393906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393906).length < 2 ^ (prefixWord ++ tailWord_393906).sum := by decide
  have hdescent : baseEnd_393906 < baseStart_393906 := by decide
  rcases family_descends (prefixWord ++ tailWord_393906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393913 : List Nat := [1, 2, 1, 4, 1, 1, 1, 1, 4, 5, 2]
def baseStart_393913 : Nat := 118140960795 + 393913 * 2 ^ 59
def prefixEnd_393913 : Nat := 4983230072969 + 3 ^ 40 * 393913 * 2
def baseEnd_393913 : Nat := 202266705054622547275933

theorem tailTrace_393913 : CollatzResearch.WordTrace tailWord_393913 prefixEnd_393913 202266705054622547275933 := by
  unfold tailWord_393913
  simp only [CollatzResearch.WordTrace]
  refine ⟨14367187421927950829474393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9578124947951967219649595 14367187421927950829474393)
  ·
    refine ⟨10775390566445963122105795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14367187421927950829474393 10775390566445963122105795)
    ·
      refine ⟨16163085849668944683158693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10775390566445963122105795 16163085849668944683158693)
      ·
        refine ⟨3030578596812927128092255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16163085849668944683158693 3030578596812927128092255)
        ·
          refine ⟨4545867895219390692138383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3030578596812927128092255 4545867895219390692138383)
          ·
            refine ⟨6818801842829086038207575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4545867895219390692138383 6818801842829086038207575)
            ·
              refine ⟨10228202764243629057311363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6818801842829086038207575 10228202764243629057311363)
              ·
                refine ⟨15342304146365443585967045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10228202764243629057311363 15342304146365443585967045)
                ·
                  refine ⟨2876682027443520672368821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15342304146365443585967045 2876682027443520672368821)
                  ·
                    refine ⟨269688940072830063034577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2876682027443520672368821 269688940072830063034577)
                    ·
                      refine ⟨202266705054622547275933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 269688940072830063034577 202266705054622547275933)
                      ·
                        rfl

theorem cell23_393913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 4, 5, 2].length) (baseStart_393913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_393913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_393913 prefixEnd_393913 := by exact prefixLift 393913
  have htrace : WordTrace (prefixWord ++ tailWord_393913) baseStart_393913 baseEnd_393913 := by
    simpa [prefixWord, tailWord_393913, baseEnd_393913] using wordTrace_append hprefix tailTrace_393913
  have hstable : (prefixWord ++ tailWord_393913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393913).length < 2 ^ (prefixWord ++ tailWord_393913).sum := by decide
  have hdescent : baseEnd_393913 < baseStart_393913 := by decide
  rcases family_descends (prefixWord ++ tailWord_393913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393970 : List Nat := [3, 2, 1, 3, 1, 2, 2, 2, 3, 4]
def baseStart_393970 : Nat := 118140960795 + 393970 * 2 ^ 59
def prefixEnd_393970 : Nat := 4983230072969 + 3 ^ 40 * 393970 * 2
def baseEnd_393970 : Nat := 67431991150642941421057

theorem tailTrace_393970 : CollatzResearch.WordTrace tailWord_393970 prefixEnd_393970 67431991150642941421057 := by
  unfold tailWord_393970
  simp only [CollatzResearch.WordTrace]
  refine ⟨3592316595680362391074841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9579510921814299709532909 3592316595680362391074841)
  ·
    refine ⟨2694237446760271793306131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3592316595680362391074841 2694237446760271793306131)
    ·
      refine ⟨4041356170140407689959197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2694237446760271793306131 4041356170140407689959197)
      ·
        refine ⟨1515508563802652883734699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4041356170140407689959197 1515508563802652883734699)
        ·
          refine ⟨2273262845703979325602049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1515508563802652883734699 2273262845703979325602049)
          ·
            refine ⟨1704947134277984494201537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2273262845703979325602049 1704947134277984494201537)
            ·
              refine ⟨1278710350708488370651153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1704947134277984494201537 1278710350708488370651153)
              ·
                refine ⟨959032763031366277988365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1278710350708488370651153 959032763031366277988365)
                ·
                  refine ⟨359637286136762354245637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 959032763031366277988365 359637286136762354245637)
                  ·
                    refine ⟨67431991150642941421057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 359637286136762354245637 67431991150642941421057)
                    ·
                      rfl

theorem cell23_393970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 2, 3, 4].length) (baseStart_393970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_393970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_393970 prefixEnd_393970 := by exact prefixLift 393970
  have htrace : WordTrace (prefixWord ++ tailWord_393970) baseStart_393970 baseEnd_393970 := by
    simpa [prefixWord, tailWord_393970, baseEnd_393970] using wordTrace_append hprefix tailTrace_393970
  have hstable : (prefixWord ++ tailWord_393970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393970).length < 2 ^ (prefixWord ++ tailWord_393970).sum := by decide
  have hdescent : baseEnd_393970 < baseStart_393970 := by decide
  rcases family_descends (prefixWord ++ tailWord_393970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394037 : List Nat := [1, 3, 3, 1, 3, 1, 1, 3, 2, 3, 2]
def baseStart_394037 : Nat := 118140960795 + 394037 * 2 ^ 59
def prefixEnd_394037 : Nat := 4983230072969 + 3 ^ 40 * 394037 * 2
def baseEnd_394037 : Nat := 202330376655780062125363

theorem tailTrace_394037 : CollatzResearch.WordTrace tailWord_394037 prefixEnd_394037 202330376655780062125363 := by
  unfold tailWord_394037
  simp only [CollatzResearch.WordTrace]
  refine ⟨14371710073478720006988365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9581140048985813337992243 14371710073478720006988365)
  ·
    refine ⟨5389391277554520002620637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14371710073478720006988365 5389391277554520002620637)
    ·
      refine ⟨2021021729082945000982739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5389391277554520002620637 2021021729082945000982739)
      ·
        refine ⟨3031532593624417501474109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2021021729082945000982739 3031532593624417501474109)
        ·
          refine ⟨1136824722609156563052791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3031532593624417501474109 1136824722609156563052791)
          ·
            refine ⟨1705237083913734844579187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1136824722609156563052791 1705237083913734844579187)
            ·
              refine ⟨2557855625870602266868781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1705237083913734844579187 2557855625870602266868781)
              ·
                refine ⟨959195859701475850075793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2557855625870602266868781 959195859701475850075793)
                ·
                  refine ⟨719396894776106887556845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 959195859701475850075793 719396894776106887556845)
                  ·
                    refine ⟨269773835541040082833817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 719396894776106887556845 269773835541040082833817)
                    ·
                      refine ⟨202330376655780062125363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 269773835541040082833817 202330376655780062125363)
                      ·
                        rfl

theorem cell23_394037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 3, 2, 3, 2].length) (baseStart_394037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_394037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_394037 prefixEnd_394037 := by exact prefixLift 394037
  have htrace : WordTrace (prefixWord ++ tailWord_394037) baseStart_394037 baseEnd_394037 := by
    simpa [prefixWord, tailWord_394037, baseEnd_394037] using wordTrace_append hprefix tailTrace_394037
  have hstable : (prefixWord ++ tailWord_394037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394037).length < 2 ^ (prefixWord ++ tailWord_394037).sum := by decide
  have hdescent : baseEnd_394037 < baseStart_394037 := by decide
  rcases family_descends (prefixWord ++ tailWord_394037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394047 : List Nat := [1, 1, 2, 2, 5, 2, 3, 1, 1, 5]
def baseStart_394047 : Nat := 118140960795 + 394047 * 2 ^ 59
def prefixEnd_394047 : Nat := 4983230072969 + 3 ^ 40 * 394047 * 2
def baseEnd_394047 : Nat := 67445170487441674333439

theorem tailTrace_394047 : CollatzResearch.WordTrace tailWord_394047 prefixEnd_394047 67445170487441674333439 := by
  unfold tailWord_394047
  simp only [CollatzResearch.WordTrace]
  refine ⟨14372074803442491714852395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9581383202294994476568263 14372074803442491714852395)
  ·
    refine ⟨21558112205163737572278593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14372074803442491714852395 21558112205163737572278593)
    ·
      refine ⟨16168584153872803179208945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21558112205163737572278593 16168584153872803179208945)
      ·
        refine ⟨12126438115404602384406709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16168584153872803179208945 12126438115404602384406709)
        ·
          refine ⟨1136853573319181473538129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12126438115404602384406709 1136853573319181473538129)
          ·
            refine ⟨852640179989386105153597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1136853573319181473538129 852640179989386105153597)
            ·
              refine ⟨319740067496019789432599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 852640179989386105153597 319740067496019789432599)
              ·
                refine ⟨479610101244029684148899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 319740067496019789432599 479610101244029684148899)
                ·
                  refine ⟨719415151866044526223349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 479610101244029684148899 719415151866044526223349)
                  ·
                    refine ⟨67445170487441674333439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 719415151866044526223349 67445170487441674333439)
                    ·
                      rfl

theorem cell23_394047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 3, 1, 1, 5].length) (baseStart_394047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_394047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_394047 prefixEnd_394047 := by exact prefixLift 394047
  have htrace : WordTrace (prefixWord ++ tailWord_394047) baseStart_394047 baseEnd_394047 := by
    simpa [prefixWord, tailWord_394047, baseEnd_394047] using wordTrace_append hprefix tailTrace_394047
  have hstable : (prefixWord ++ tailWord_394047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394047).length < 2 ^ (prefixWord ++ tailWord_394047).sum := by decide
  have hdescent : baseEnd_394047 < baseStart_394047 := by decide
  rcases family_descends (prefixWord ++ tailWord_394047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394053 : List Nat := [1, 3, 1, 1, 1, 2, 2, 5, 1, 1, 5]
def baseStart_394053 : Nat := 118140960795 + 394053 * 2 ^ 59
def prefixEnd_394053 : Nat := 4983230072969 + 3 ^ 40 * 394053 * 2
def baseEnd_394053 : Nat := 202338592346251999525289

theorem tailTrace_394053 : CollatzResearch.WordTrace tailWord_394053 prefixEnd_394053 202338592346251999525289 := by
  unfold tailWord_394053
  simp only [CollatzResearch.WordTrace]
  refine ⟨14372293641420754739570813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9581529094280503159713875 14372293641420754739570813)
  ·
    refine ⟨5389610115532783027339055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14372293641420754739570813 5389610115532783027339055)
    ·
      refine ⟨8084415173299174541008583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5389610115532783027339055 8084415173299174541008583)
      ·
        refine ⟨12126622759948761811512875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8084415173299174541008583 12126622759948761811512875)
        ·
          refine ⟨18189934139923142717269313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12126622759948761811512875 18189934139923142717269313)
          ·
            refine ⟨13642450604942357037951985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18189934139923142717269313 13642450604942357037951985)
            ·
              refine ⟨10231837953706767778463989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13642450604942357037951985 10231837953706767778463989)
              ·
                refine ⟨959234808160009479230999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10231837953706767778463989 959234808160009479230999)
                ·
                  refine ⟨1438852212240014218846499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 959234808160009479230999 1438852212240014218846499)
                  ·
                    refine ⟨2158278318360021328269749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1438852212240014218846499 2158278318360021328269749)
                    ·
                      refine ⟨202338592346251999525289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2158278318360021328269749 202338592346251999525289)
                      ·
                        rfl

theorem cell23_394053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 5, 1, 1, 5].length) (baseStart_394053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_394053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_394053 prefixEnd_394053 := by exact prefixLift 394053
  have htrace : WordTrace (prefixWord ++ tailWord_394053) baseStart_394053 baseEnd_394053 := by
    simpa [prefixWord, tailWord_394053, baseEnd_394053] using wordTrace_append hprefix tailTrace_394053
  have hstable : (prefixWord ++ tailWord_394053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394053).length < 2 ^ (prefixWord ++ tailWord_394053).sum := by decide
  have hdescent : baseEnd_394053 < baseStart_394053 := by decide
  rcases family_descends (prefixWord ++ tailWord_394053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394073 : List Nat := [1, 2, 1, 2, 2, 4, 3, 8]
def baseStart_394073 : Nat := 118140960795 + 394073 * 2 ^ 59
def prefixEnd_394073 : Nat := 4983230072969 + 3 ^ 40 * 394073 * 2
def baseEnd_394073 : Nat := 7494402294790441528711

theorem tailTrace_394073 : CollatzResearch.WordTrace tailWord_394073 prefixEnd_394073 7494402294790441528711 := by
  unfold tailWord_394073
  simp only [CollatzResearch.WordTrace]
  refine ⟨14373023101348298155298873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9582015400898865436865915 14373023101348298155298873)
  ·
    refine ⟨10779767326011223616474155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14373023101348298155298873 10779767326011223616474155)
    ·
      refine ⟨16169650989016835424711233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10779767326011223616474155 16169650989016835424711233)
      ·
        refine ⟨12127238241762626568533425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16169650989016835424711233 12127238241762626568533425)
        ·
          refine ⟨9095428681321969926400069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12127238241762626568533425 9095428681321969926400069)
          ·
            refine ⟨1705392877747869361200013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9095428681321969926400069 1705392877747869361200013)
            ·
              refine ⟨639522329155451010450005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1705392877747869361200013 639522329155451010450005)
              ·
                refine ⟨7494402294790441528711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 639522329155451010450005 7494402294790441528711)
                ·
                  rfl

theorem cell23_394073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 8].length) (baseStart_394073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_394073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_394073 prefixEnd_394073 := by exact prefixLift 394073
  have htrace : WordTrace (prefixWord ++ tailWord_394073) baseStart_394073 baseEnd_394073 := by
    simpa [prefixWord, tailWord_394073, baseEnd_394073] using wordTrace_append hprefix tailTrace_394073
  have hstable : (prefixWord ++ tailWord_394073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394073).length < 2 ^ (prefixWord ++ tailWord_394073).sum := by decide
  have hdescent : baseEnd_394073 < baseStart_394073 := by decide
  rcases family_descends (prefixWord ++ tailWord_394073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394080 : List Nat := [2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 4]
def baseStart_394080 : Nat := 118140960795 + 394080 * 2 ^ 59
def prefixEnd_394080 : Nat := 4983230072969 + 3 ^ 40 * 394080 * 2
def baseEnd_394080 : Nat := 202352456323923393887665

theorem tailTrace_394080 : CollatzResearch.WordTrace tailWord_394080 prefixEnd_394080 202352456323923393887665 := by
  unfold tailWord_394080
  simp only [CollatzResearch.WordTrace]
  refine ⟨7186639206161469175401847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9582185608215292233869129 7186639206161469175401847)
  ·
    refine ⟨10779958809242203763102771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7186639206161469175401847 10779958809242203763102771)
    ·
      refine ⟨16169938213863305644654157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10779958809242203763102771 16169938213863305644654157)
      ·
        refine ⟨6063726830198739616745309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16169938213863305644654157 6063726830198739616745309)
        ·
          refine ⟨2273897561324527356279491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6063726830198739616745309 2273897561324527356279491)
          ·
            refine ⟨3410846341986791034419237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2273897561324527356279491 3410846341986791034419237)
            ·
              refine ⟨639533689122523318953607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3410846341986791034419237 639533689122523318953607)
              ·
                refine ⟨959300533683784978430411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 639533689122523318953607 959300533683784978430411)
                ·
                  refine ⟨1438950800525677467645617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 959300533683784978430411 1438950800525677467645617)
                  ·
                    refine ⟨1079213100394258100734213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1438950800525677467645617 1079213100394258100734213)
                    ·
                      refine ⟨202352456323923393887665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1079213100394258100734213 202352456323923393887665)
                      ·
                        rfl

theorem cell23_394080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 4].length) (baseStart_394080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_394080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_394080 prefixEnd_394080 := by exact prefixLift 394080
  have htrace : WordTrace (prefixWord ++ tailWord_394080) baseStart_394080 baseEnd_394080 := by
    simpa [prefixWord, tailWord_394080, baseEnd_394080] using wordTrace_append hprefix tailTrace_394080
  have hstable : (prefixWord ++ tailWord_394080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394080).length < 2 ^ (prefixWord ++ tailWord_394080).sum := by decide
  have hdescent : baseEnd_394080 < baseStart_394080 := by decide
  rcases family_descends (prefixWord ++ tailWord_394080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394084 : List Nat := [2, 3, 1, 1, 4, 2, 1, 2, 3, 2, 2]
def baseStart_394084 : Nat := 118140960795 + 394084 * 2 ^ 59
def prefixEnd_394084 : Nat := 4983230072969 + 3 ^ 40 * 394084 * 2
def baseEnd_394084 : Nat := 202354510246541378237647

theorem tailTrace_394084 : CollatzResearch.WordTrace tailWord_394084 prefixEnd_394084 202354510246541378237647 := by
  unfold tailWord_394084
  simp only [CollatzResearch.WordTrace]
  refine ⟨7186712152154223516974653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9582282869538964689299537 7186712152154223516974653)
  ·
    refine ⟨2695017057057833818865495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7186712152154223516974653 2695017057057833818865495)
    ·
      refine ⟨4042525585586750728298243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2695017057057833818865495 4042525585586750728298243)
      ·
        refine ⟨6063788378380126092447365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4042525585586750728298243 6063788378380126092447365)
        ·
          refine ⟨1136960320946273642333881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6063788378380126092447365 1136960320946273642333881)
          ·
            refine ⟨852720240709705231750411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1136960320946273642333881 852720240709705231750411)
            ·
              refine ⟨1279080361064557847625617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 852720240709705231750411 1279080361064557847625617)
              ·
                refine ⟨959310270798418385719213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1279080361064557847625617 959310270798418385719213)
                ·
                  refine ⟨359741351549406894644705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 959310270798418385719213 359741351549406894644705)
                  ·
                    refine ⟨269806013662055170983529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 359741351549406894644705 269806013662055170983529)
                    ·
                      refine ⟨202354510246541378237647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 269806013662055170983529 202354510246541378237647)
                      ·
                        rfl

theorem cell23_394084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 2, 3, 2, 2].length) (baseStart_394084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_394084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_394084 prefixEnd_394084 := by exact prefixLift 394084
  have htrace : WordTrace (prefixWord ++ tailWord_394084) baseStart_394084 baseEnd_394084 := by
    simpa [prefixWord, tailWord_394084, baseEnd_394084] using wordTrace_append hprefix tailTrace_394084
  have hstable : (prefixWord ++ tailWord_394084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394084).length < 2 ^ (prefixWord ++ tailWord_394084).sum := by decide
  have hdescent : baseEnd_394084 < baseStart_394084 := by decide
  rcases family_descends (prefixWord ++ tailWord_394084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394101 : List Nat := [1, 3, 4, 1, 1, 2, 1, 5, 1, 2, 2]
def baseStart_394101 : Nat := 118140960795 + 394101 * 2 ^ 59
def prefixEnd_394101 : Nat := 4983230072969 + 3 ^ 40 * 394101 * 2
def baseEnd_394101 : Nat := 202363239417667811725069

theorem tailTrace_394101 : CollatzResearch.WordTrace tailWord_394101 prefixEnd_394101 202363239417667811725069 := by
  unfold tailWord_394101
  simp only [CollatzResearch.WordTrace]
  refine ⟨14374044345246858937318157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9582696230164572624878771 14374044345246858937318157)
  ·
    refine ⟨5390266629467572101494309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14374044345246858937318157 5390266629467572101494309)
    ·
      refine ⟨1010674993025169769030183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5390266629467572101494309 1010674993025169769030183)
      ·
        refine ⟨1516012489537754653545275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1010674993025169769030183 1516012489537754653545275)
        ·
          refine ⟨2274018734306631980317913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1516012489537754653545275 2274018734306631980317913)
          ·
            refine ⟨1705514050729973985238435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2274018734306631980317913 1705514050729973985238435)
            ·
              refine ⟨2558271076094960977857653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1705514050729973985238435 2558271076094960977857653)
              ·
                refine ⟨239837913383902591674155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2558271076094960977857653 239837913383902591674155)
                ·
                  refine ⟨359756870075853887511233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 239837913383902591674155 359756870075853887511233)
                  ·
                    refine ⟨269817652556890415633425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 359756870075853887511233 269817652556890415633425)
                    ·
                      refine ⟨202363239417667811725069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 269817652556890415633425 202363239417667811725069)
                      ·
                        rfl

theorem cell23_394101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 5, 1, 2, 2].length) (baseStart_394101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_394101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_394101 prefixEnd_394101 := by exact prefixLift 394101
  have htrace : WordTrace (prefixWord ++ tailWord_394101) baseStart_394101 baseEnd_394101 := by
    simpa [prefixWord, tailWord_394101, baseEnd_394101] using wordTrace_append hprefix tailTrace_394101
  have hstable : (prefixWord ++ tailWord_394101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394101).length < 2 ^ (prefixWord ++ tailWord_394101).sum := by decide
  have hdescent : baseEnd_394101 < baseStart_394101 := by decide
  rcases family_descends (prefixWord ++ tailWord_394101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394117 : List Nat := [1, 3, 1, 1, 3, 4, 1, 1, 4, 1, 3]
def baseStart_394117 : Nat := 118140960795 + 394117 * 2 ^ 59
def prefixEnd_394117 : Nat := 4983230072969 + 3 ^ 40 * 394117 * 2
def baseEnd_394117 : Nat := 202371455108139749124995

theorem tailTrace_394117 : CollatzResearch.WordTrace tailWord_394117 prefixEnd_394117 202371455108139749124995 := by
  unfold tailWord_394117
  simp only [CollatzResearch.WordTrace]
  refine ⟨14374627913188893669900605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9583085275459262446600403 14374627913188893669900605)
  ·
    refine ⟨5390485467445835126212727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14374627913188893669900605 5390485467445835126212727)
    ·
      refine ⟨8085728201168752689319091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5390485467445835126212727 8085728201168752689319091)
      ·
        refine ⟨12128592301753129033978637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8085728201168752689319091 12128592301753129033978637)
        ·
          refine ⟨4548222113157423387741989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12128592301753129033978637 4548222113157423387741989)
          ·
            refine ⟨852791646217016885201623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4548222113157423387741989 852791646217016885201623)
            ·
              refine ⟨1279187469325525327802435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 852791646217016885201623 1279187469325525327802435)
              ·
                refine ⟨1918781203988287991703653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1279187469325525327802435 1918781203988287991703653)
                ·
                  refine ⟨359771475747803998444435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1918781203988287991703653 359771475747803998444435)
                  ·
                    refine ⟨539657213621705997666653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 359771475747803998444435 539657213621705997666653)
                    ·
                      refine ⟨202371455108139749124995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 539657213621705997666653 202371455108139749124995)
                      ·
                        rfl

theorem cell23_394117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 1, 4, 1, 3].length) (baseStart_394117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_394117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_394117 prefixEnd_394117 := by exact prefixLift 394117
  have htrace : WordTrace (prefixWord ++ tailWord_394117) baseStart_394117 baseEnd_394117 := by
    simpa [prefixWord, tailWord_394117, baseEnd_394117] using wordTrace_append hprefix tailTrace_394117
  have hstable : (prefixWord ++ tailWord_394117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394117).length < 2 ^ (prefixWord ++ tailWord_394117).sum := by decide
  have hdescent : baseEnd_394117 < baseStart_394117 := by decide
  rcases family_descends (prefixWord ++ tailWord_394117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394123 : List Nat := [1, 1, 1, 1, 4, 2, 2, 1, 1, 5, 4]
def baseStart_394123 : Nat := 118140960795 + 394123 * 2 ^ 59
def prefixEnd_394123 : Nat := 4983230072969 + 3 ^ 40 * 394123 * 2
def baseEnd_394123 : Nat := 202374535992066725649967

theorem tailTrace_394123 : CollatzResearch.WordTrace tailWord_394123 prefixEnd_394123 202374535992066725649967 := by
  unfold tailWord_394123
  simp only [CollatzResearch.WordTrace]
  refine ⟨14374846751167156694619023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9583231167444771129746015 14374846751167156694619023)
  ·
    refine ⟨21562270126750735041928535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14374846751167156694619023 21562270126750735041928535)
    ·
      refine ⟨32343405190126102562892803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21562270126750735041928535 32343405190126102562892803)
      ·
        refine ⟨48515107785189153844339205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32343405190126102562892803 48515107785189153844339205)
        ·
          refine ⟨9096582709722966345813601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48515107785189153844339205 9096582709722966345813601)
          ·
            refine ⟨6822437032292224759360201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9096582709722966345813601 6822437032292224759360201)
            ·
              refine ⟨5116827774219168569520151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6822437032292224759360201 5116827774219168569520151)
              ·
                refine ⟨7675241661328752854280227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5116827774219168569520151 7675241661328752854280227)
                ·
                  refine ⟨11512862491993129281420341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7675241661328752854280227 11512862491993129281420341)
                  ·
                    refine ⟨1079330858624355870133157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11512862491993129281420341 1079330858624355870133157)
                    ·
                      refine ⟨202374535992066725649967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1079330858624355870133157 202374535992066725649967)
                      ·
                        rfl

theorem cell23_394123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 5, 4].length) (baseStart_394123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_394123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_394123 prefixEnd_394123 := by exact prefixLift 394123
  have htrace : WordTrace (prefixWord ++ tailWord_394123) baseStart_394123 baseEnd_394123 := by
    simpa [prefixWord, tailWord_394123, baseEnd_394123] using wordTrace_append hprefix tailTrace_394123
  have hstable : (prefixWord ++ tailWord_394123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394123).length < 2 ^ (prefixWord ++ tailWord_394123).sum := by decide
  have hdescent : baseEnd_394123 < baseStart_394123 := by decide
  rcases family_descends (prefixWord ++ tailWord_394123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394174 : List Nat := [4, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2]
def baseStart_394174 : Nat := 118140960795 + 394174 * 2 ^ 59
def prefixEnd_394174 : Nat := 4983230072969 + 3 ^ 40 * 394174 * 2
def baseEnd_394174 : Nat := 202400723505446026112233

theorem tailTrace_394174 : CollatzResearch.WordTrace tailWord_394174 prefixEnd_394174 202400723505446026112233 := by
  unfold tailWord_394174
  simp only [CollatzResearch.WordTrace]
  refine ⟨1797088359247799050590697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9584471249321594936483717 1797088359247799050590697)
  ·
    refine ⟨1347816269435849287943023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1797088359247799050590697 1347816269435849287943023)
    ·
      refine ⟨2021724404153773931914535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1347816269435849287943023 2021724404153773931914535)
      ·
        refine ⟨3032586606230660897871803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2021724404153773931914535 3032586606230660897871803)
        ·
          refine ⟨4548879909345991346807705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3032586606230660897871803 4548879909345991346807705)
          ·
            refine ⟨3411659932009493510105779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4548879909345991346807705 3411659932009493510105779)
            ·
              refine ⟨5117489898014240265158669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3411659932009493510105779 5117489898014240265158669)
              ·
                refine ⟨1919058711755340099434501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5117489898014240265158669 1919058711755340099434501)
                ·
                  refine ⟨359823508454126268643969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1919058711755340099434501 359823508454126268643969)
                  ·
                    refine ⟨269867631340594701482977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 359823508454126268643969 269867631340594701482977)
                    ·
                      refine ⟨202400723505446026112233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 269867631340594701482977 202400723505446026112233)
                      ·
                        rfl

theorem cell23_394174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2].length) (baseStart_394174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_394174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_394174 prefixEnd_394174 := by exact prefixLift 394174
  have htrace : WordTrace (prefixWord ++ tailWord_394174) baseStart_394174 baseEnd_394174 := by
    simpa [prefixWord, tailWord_394174, baseEnd_394174] using wordTrace_append hprefix tailTrace_394174
  have hstable : (prefixWord ++ tailWord_394174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394174).length < 2 ^ (prefixWord ++ tailWord_394174).sum := by decide
  have hdescent : baseEnd_394174 < baseStart_394174 := by decide
  rcases family_descends (prefixWord ++ tailWord_394174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394191 : List Nat := [1, 1, 2, 1, 1, 6, 4, 1, 2, 2, 2]
def baseStart_394191 : Nat := 118140960795 + 394191 * 2 ^ 59
def prefixEnd_394191 : Nat := 4983230072969 + 3 ^ 40 * 394191 * 2
def baseEnd_394191 : Nat := 202409452676572459599655

theorem tailTrace_394191 : CollatzResearch.WordTrace tailWord_394191 prefixEnd_394191 202409452676572459599655 := by
  unfold tailWord_394191
  simp only [CollatzResearch.WordTrace]
  refine ⟨14377326914920804308094427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9584884609947202872062951 14377326914920804308094427)
  ·
    refine ⟨21565990372381206462141641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14377326914920804308094427 21565990372381206462141641)
    ·
      refine ⟨16174492779285904846606231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21565990372381206462141641 16174492779285904846606231)
      ·
        refine ⟨24261739168928857269909347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16174492779285904846606231 24261739168928857269909347)
        ·
          refine ⟨36392608753393285904864021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24261739168928857269909347 36392608753393285904864021)
          ·
            refine ⟨1705903535315310276790501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 36392608753393285904864021 1705903535315310276790501)
            ·
              refine ⟨319856912871620676898219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1705903535315310276790501 319856912871620676898219)
              ·
                refine ⟨479785369307431015347329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 319856912871620676898219 479785369307431015347329)
                ·
                  refine ⟨359839026980573261510497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 479785369307431015347329 359839026980573261510497)
                  ·
                    refine ⟨269879270235429946132873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 359839026980573261510497 269879270235429946132873)
                    ·
                      refine ⟨202409452676572459599655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 269879270235429946132873 202409452676572459599655)
                      ·
                        rfl

theorem cell23_394191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 4, 1, 2, 2, 2].length) (baseStart_394191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_394191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_394191 prefixEnd_394191 := by exact prefixLift 394191
  have htrace : WordTrace (prefixWord ++ tailWord_394191) baseStart_394191 baseEnd_394191 := by
    simpa [prefixWord, tailWord_394191, baseEnd_394191] using wordTrace_append hprefix tailTrace_394191
  have hstable : (prefixWord ++ tailWord_394191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394191).length < 2 ^ (prefixWord ++ tailWord_394191).sum := by decide
  have hdescent : baseEnd_394191 < baseStart_394191 := by decide
  rcases family_descends (prefixWord ++ tailWord_394191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394264 : List Nat := [2, 1, 2, 3, 2, 4, 1, 1, 2, 1, 4]
def baseStart_394264 : Nat := 118140960795 + 394264 * 2 ^ 59
def prefixEnd_394264 : Nat := 4983230072969 + 3 ^ 40 * 394264 * 2
def baseEnd_394264 : Nat := 202446936764350673986819

theorem tailTrace_394264 : CollatzResearch.WordTrace tailWord_394264 prefixEnd_394264 202446936764350673986819 := by
  unfold tailWord_394264
  simp only [CollatzResearch.WordTrace]
  refine ⟨7189994721828168887750923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9586659629104225183667897 7189994721828168887750923)
  ·
    refine ⟨10784992082742253331626385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7189994721828168887750923 10784992082742253331626385)
    ·
      refine ⟨8088744062056689998719789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10784992082742253331626385 8088744062056689998719789)
      ·
        refine ⟨3033279023271258749519921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8088744062056689998719789 3033279023271258749519921)
        ·
          refine ⟨2274959267453444062139941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3033279023271258749519921 2274959267453444062139941)
          ·
            refine ⟨426554862647520761651239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2274959267453444062139941 426554862647520761651239)
            ·
              refine ⟨639832293971281142476859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 426554862647520761651239 639832293971281142476859)
              ·
                refine ⟨959748440956921713715289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 639832293971281142476859 959748440956921713715289)
                ·
                  refine ⟨719811330717691285286467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 959748440956921713715289 719811330717691285286467)
                  ·
                    refine ⟨1079716996076536927929701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 719811330717691285286467 1079716996076536927929701)
                    ·
                      refine ⟨202446936764350673986819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1079716996076536927929701 202446936764350673986819)
                      ·
                        rfl

theorem cell23_394264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 1, 2, 1, 4].length) (baseStart_394264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_394264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_394264 prefixEnd_394264 := by exact prefixLift 394264
  have htrace : WordTrace (prefixWord ++ tailWord_394264) baseStart_394264 baseEnd_394264 := by
    simpa [prefixWord, tailWord_394264, baseEnd_394264] using wordTrace_append hprefix tailTrace_394264
  have hstable : (prefixWord ++ tailWord_394264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394264).length < 2 ^ (prefixWord ++ tailWord_394264).sum := by decide
  have hdescent : baseEnd_394264 < baseStart_394264 := by decide
  rcases family_descends (prefixWord ++ tailWord_394264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394290 : List Nat := [3, 2, 1, 1, 2, 2, 1, 1, 1, 1, 8]
def baseStart_394290 : Nat := 118140960795 + 394290 * 2 ^ 59
def prefixEnd_394290 : Nat := 4983230072969 + 3 ^ 40 * 394290 * 2
def baseEnd_394290 : Nat := 202460287261367572261699

theorem tailTrace_394290 : CollatzResearch.WordTrace tailWord_394290 prefixEnd_394290 202460287261367572261699 := by
  unfold tailWord_394290
  simp only [CollatzResearch.WordTrace]
  refine ⟨3595234435390536053987081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9587291827708096143965549 3595234435390536053987081)
  ·
    refine ⟨2696425826542902040490311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3595234435390536053987081 2696425826542902040490311)
    ·
      refine ⟨4044638739814353060735467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2696425826542902040490311 4044638739814353060735467)
      ·
        refine ⟨6066958109721529591103201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4044638739814353060735467 6066958109721529591103201)
        ·
          refine ⟨4550218582291147193327401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6066958109721529591103201 4550218582291147193327401)
          ·
            refine ⟨3412663936718360394995551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4550218582291147193327401 3412663936718360394995551)
            ·
              refine ⟨5118995905077540592493327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3412663936718360394995551 5118995905077540592493327)
              ·
                refine ⟨7678493857616310888739991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5118995905077540592493327 7678493857616310888739991)
                ·
                  refine ⟨11517740786424466333109987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7678493857616310888739991 11517740786424466333109987)
                  ·
                    refine ⟨17276611179636699499664981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11517740786424466333109987 17276611179636699499664981)
                    ·
                      refine ⟨202460287261367572261699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 17276611179636699499664981 202460287261367572261699)
                      ·
                        rfl

theorem cell23_394290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 1, 1, 8].length) (baseStart_394290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_394290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_394290 prefixEnd_394290 := by exact prefixLift 394290
  have htrace : WordTrace (prefixWord ++ tailWord_394290) baseStart_394290 baseEnd_394290 := by
    simpa [prefixWord, tailWord_394290, baseEnd_394290] using wordTrace_append hprefix tailTrace_394290
  have hstable : (prefixWord ++ tailWord_394290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394290).length < 2 ^ (prefixWord ++ tailWord_394290).sum := by decide
  have hdescent : baseEnd_394290 < baseStart_394290 := by decide
  rcases family_descends (prefixWord ++ tailWord_394290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394307 : List Nat := [1, 1, 1, 3, 1, 2, 3, 1, 3, 5, 2]
def baseStart_394307 : Nat := 118140960795 + 394307 * 2 ^ 59
def prefixEnd_394307 : Nat := 4983230072969 + 3 ^ 40 * 394307 * 2
def baseEnd_394307 : Nat := 202469016432494005749121

theorem tailTrace_394307 : CollatzResearch.WordTrace tailWord_394307 prefixEnd_394307 202469016432494005749121 := by
  unfold tailWord_394307
  simp only [CollatzResearch.WordTrace]
  refine ⟨14381557782500556119317175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9587705188333704079544783 14381557782500556119317175)
  ·
    refine ⟨21572336673750834178975763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14381557782500556119317175 21572336673750834178975763)
    ·
      refine ⟨32358505010626251268463645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21572336673750834178975763 32358505010626251268463645)
      ·
        refine ⟨12134439378984844225673867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32358505010626251268463645 12134439378984844225673867)
        ·
          refine ⟨18201659068477266338510801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12134439378984844225673867 18201659068477266338510801)
          ·
            refine ⟨13651244301357949753883101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18201659068477266338510801 13651244301357949753883101)
            ·
              refine ⟨5119216613009231157706163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13651244301357949753883101 5119216613009231157706163)
              ·
                refine ⟨7678824919513846736559245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5119216613009231157706163 7678824919513846736559245)
                ·
                  refine ⟨2879559344817692526209717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7678824919513846736559245 2879559344817692526209717)
                  ·
                    refine ⟨269958688576658674332161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2879559344817692526209717 269958688576658674332161)
                    ·
                      refine ⟨202469016432494005749121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 269958688576658674332161 202469016432494005749121)
                      ·
                        rfl

theorem cell23_394307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 3, 5, 2].length) (baseStart_394307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_394307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_394307 prefixEnd_394307 := by exact prefixLift 394307
  have htrace : WordTrace (prefixWord ++ tailWord_394307) baseStart_394307 baseEnd_394307 := by
    simpa [prefixWord, tailWord_394307, baseEnd_394307] using wordTrace_append hprefix tailTrace_394307
  have hstable : (prefixWord ++ tailWord_394307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394307).length < 2 ^ (prefixWord ++ tailWord_394307).sum := by decide
  have hdescent : baseEnd_394307 < baseStart_394307 := by decide
  rcases family_descends (prefixWord ++ tailWord_394307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394314 : List Nat := [3, 1, 2, 1, 1, 2, 4, 2, 3, 1, 3]
def baseStart_394314 : Nat := 118140960795 + 394314 * 2 ^ 59
def prefixEnd_394314 : Nat := 4983230072969 + 3 ^ 40 * 394314 * 2
def baseEnd_394314 : Nat := 202472610797075478361589

theorem tailTrace_394314 : CollatzResearch.WordTrace tailWord_394314 prefixEnd_394314 202472610797075478361589 := by
  unfold tailWord_394314
  simp only [CollatzResearch.WordTrace]
  refine ⟨3595453273368799078705499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9587875395650130876547997 3595453273368799078705499)
  ·
    refine ⟨5393179910053198618058249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3595453273368799078705499 5393179910053198618058249)
    ·
      refine ⟨4044884932539898963543687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5393179910053198618058249 4044884932539898963543687)
      ·
        refine ⟨6067327398809848445315531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4044884932539898963543687 6067327398809848445315531)
        ·
          refine ⟨9100991098214772667973297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6067327398809848445315531 9100991098214772667973297)
          ·
            refine ⟨6825743323661079500979973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9100991098214772667973297 6825743323661079500979973)
            ·
              refine ⟨1279826873186452406433745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6825743323661079500979973 1279826873186452406433745)
              ·
                refine ⟨959870154889839304825309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1279826873186452406433745 959870154889839304825309)
                ·
                  refine ⟨359951308083689739309491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 959870154889839304825309 359951308083689739309491)
                  ·
                    refine ⟨539926962125534608964237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 359951308083689739309491 539926962125534608964237)
                    ·
                      refine ⟨202472610797075478361589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 539926962125534608964237 202472610797075478361589)
                      ·
                        rfl

theorem cell23_394314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 2, 3, 1, 3].length) (baseStart_394314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_394314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_394314 prefixEnd_394314 := by exact prefixLift 394314
  have htrace : WordTrace (prefixWord ++ tailWord_394314) baseStart_394314 baseEnd_394314 := by
    simpa [prefixWord, tailWord_394314, baseEnd_394314] using wordTrace_append hprefix tailTrace_394314
  have hstable : (prefixWord ++ tailWord_394314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394314).length < 2 ^ (prefixWord ++ tailWord_394314).sum := by decide
  have hdescent : baseEnd_394314 < baseStart_394314 := by decide
  rcases family_descends (prefixWord ++ tailWord_394314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394320 : List Nat := [2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 4]
def baseStart_394320 : Nat := 118140960795 + 394320 * 2 ^ 59
def prefixEnd_394320 : Nat := 4983230072969 + 3 ^ 40 * 394320 * 2
def baseEnd_394320 : Nat := 202475691681002454886561

theorem tailTrace_394320 : CollatzResearch.WordTrace tailWord_394320 prefixEnd_394320 202475691681002454886561 := by
  unfold tailWord_394320
  simp only [CollatzResearch.WordTrace]
  refine ⟨7191015965726729669770207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9588021287635639559693609 7191015965726729669770207)
  ·
    refine ⟨10786523948590094504655311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7191015965726729669770207 10786523948590094504655311)
    ·
      refine ⟨16179785922885141756982967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10786523948590094504655311 16179785922885141756982967)
      ·
        refine ⟨24269678884327712635474451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16179785922885141756982967 24269678884327712635474451)
        ·
          refine ⟨36404518326491568953211677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24269678884327712635474451 36404518326491568953211677)
          ·
            refine ⟨13651694372434338357454379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36404518326491568953211677 13651694372434338357454379)
            ·
              refine ⟨20477541558651507536181569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13651694372434338357454379 20477541558651507536181569)
              ·
                refine ⟨15358156168988630652136177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20477541558651507536181569 15358156168988630652136177)
                ·
                  refine ⟨11518617126741472989102133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15358156168988630652136177 11518617126741472989102133)
                  ·
                    refine ⟨1079870355632013092728325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11518617126741472989102133 1079870355632013092728325)
                    ·
                      refine ⟨202475691681002454886561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1079870355632013092728325 202475691681002454886561)
                      ·
                        rfl

theorem cell23_394320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 4].length) (baseStart_394320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_394320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_394320 prefixEnd_394320 := by exact prefixLift 394320
  have htrace : WordTrace (prefixWord ++ tailWord_394320) baseStart_394320 baseEnd_394320 := by
    simpa [prefixWord, tailWord_394320, baseEnd_394320] using wordTrace_append hprefix tailTrace_394320
  have hstable : (prefixWord ++ tailWord_394320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394320).length < 2 ^ (prefixWord ++ tailWord_394320).sum := by decide
  have hdescent : baseEnd_394320 < baseStart_394320 := by decide
  rcases family_descends (prefixWord ++ tailWord_394320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394324 : List Nat := [2, 4, 1, 1, 1, 1, 4, 1, 1, 5, 2]
def baseStart_394324 : Nat := 118140960795 + 394324 * 2 ^ 59
def prefixEnd_394324 : Nat := 4983230072969 + 3 ^ 40 * 394324 * 2
def baseEnd_394324 : Nat := 202477745603620439236543

theorem tailTrace_394324 : CollatzResearch.WordTrace tailWord_394324 prefixEnd_394324 202477745603620439236543 := by
  unfold tailWord_394324
  simp only [CollatzResearch.WordTrace]
  refine ⟨7191088911719484011343013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9588118548959312015124017 7191088911719484011343013)
  ·
    refine ⟨1348329170947403252126815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7191088911719484011343013 1348329170947403252126815)
    ·
      refine ⟨2022493756421104878190223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1348329170947403252126815 2022493756421104878190223)
      ·
        refine ⟨3033740634631657317285335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2022493756421104878190223 3033740634631657317285335)
        ·
          refine ⟨4550610951947485975928003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3033740634631657317285335 4550610951947485975928003)
          ·
            refine ⟨6825916427921228963892005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4550610951947485975928003 6825916427921228963892005)
            ·
              refine ⟨1279859330235230430729751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6825916427921228963892005 1279859330235230430729751)
              ·
                refine ⟨1919788995352845646094627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1279859330235230430729751 1919788995352845646094627)
                ·
                  refine ⟨2879683493029268469141941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1919788995352845646094627 2879683493029268469141941)
                  ·
                    refine ⟨269970327471493918982057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2879683493029268469141941 269970327471493918982057)
                    ·
                      refine ⟨202477745603620439236543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 269970327471493918982057 202477745603620439236543)
                      ·
                        rfl

theorem cell23_394324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 1, 1, 5, 2].length) (baseStart_394324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_394324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_394324 prefixEnd_394324 := by exact prefixLift 394324
  have htrace : WordTrace (prefixWord ++ tailWord_394324) baseStart_394324 baseEnd_394324 := by
    simpa [prefixWord, tailWord_394324, baseEnd_394324] using wordTrace_append hprefix tailTrace_394324
  have hstable : (prefixWord ++ tailWord_394324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394324).length < 2 ^ (prefixWord ++ tailWord_394324).sum := by decide
  have hdescent : baseEnd_394324 < baseStart_394324 := by decide
  rcases family_descends (prefixWord ++ tailWord_394324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394348 : List Nat := [2, 2, 1, 1, 3, 2, 5, 2, 1, 1, 3]
def baseStart_394348 : Nat := 118140960795 + 394348 * 2 ^ 59
def prefixEnd_394348 : Nat := 4983230072969 + 3 ^ 40 * 394348 * 2
def baseEnd_394348 : Nat := 202490069139328345336433

theorem tailTrace_394348 : CollatzResearch.WordTrace tailWord_394348 prefixEnd_394348 202490069139328345336433 := by
  unfold tailWord_394348
  simp only [CollatzResearch.WordTrace]
  refine ⟨7191526587676010060779849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9588702116901346747706465 7191526587676010060779849)
  ·
    refine ⟨5393644940757007545584887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7191526587676010060779849 5393644940757007545584887)
    ·
      refine ⟨8090467411135511318377331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5393644940757007545584887 8090467411135511318377331)
      ·
        refine ⟨12135701116703266977565997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8090467411135511318377331 12135701116703266977565997)
        ·
          refine ⟨4550887918763725116587249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12135701116703266977565997 4550887918763725116587249)
          ·
            refine ⟨3413165939072793837440437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4550887918763725116587249 3413165939072793837440437)
            ·
              refine ⟨319984306788074422260041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3413165939072793837440437 319984306788074422260041)
              ·
                refine ⟨239988230091055816695031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 319984306788074422260041 239988230091055816695031)
                ·
                  refine ⟨359982345136583725042547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 239988230091055816695031 359982345136583725042547)
                  ·
                    refine ⟨539973517704875587563821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 359982345136583725042547 539973517704875587563821)
                    ·
                      refine ⟨202490069139328345336433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 539973517704875587563821 202490069139328345336433)
                      ·
                        rfl

theorem cell23_394348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 5, 2, 1, 1, 3].length) (baseStart_394348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_394348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_394348 prefixEnd_394348 := by exact prefixLift 394348
  have htrace : WordTrace (prefixWord ++ tailWord_394348) baseStart_394348 baseEnd_394348 := by
    simpa [prefixWord, tailWord_394348, baseEnd_394348] using wordTrace_append hprefix tailTrace_394348
  have hstable : (prefixWord ++ tailWord_394348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394348).length < 2 ^ (prefixWord ++ tailWord_394348).sum := by decide
  have hdescent : baseEnd_394348 < baseStart_394348 := by decide
  rcases family_descends (prefixWord ++ tailWord_394348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394360 : List Nat := [2, 1, 2, 1, 1, 1, 5, 10]
def baseStart_394360 : Nat := 118140960795 + 394360 * 2 ^ 59
def prefixEnd_394360 : Nat := 4983230072969 + 3 ^ 40 * 394360 * 2
def baseEnd_394360 : Nat := 7499860403969714755051

theorem tailTrace_394360 : CollatzResearch.WordTrace tailWord_394360 prefixEnd_394360 7499860403969714755051 := by
  unfold tailWord_394360
  simp only [CollatzResearch.WordTrace]
  refine ⟨7191745425654273085498267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9588993900872364113997689 7191745425654273085498267)
  ·
    refine ⟨10787618138481409628247401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7191745425654273085498267 10787618138481409628247401)
    ·
      refine ⟨8090713603861057221185551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10787618138481409628247401 8090713603861057221185551)
      ·
        refine ⟨12136070405791585831778327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8090713603861057221185551 12136070405791585831778327)
        ·
          refine ⟨18204105608687378747667491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12136070405791585831778327 18204105608687378747667491)
          ·
            refine ⟨27306158413031068121501237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18204105608687378747667491 27306158413031068121501237)
            ·
              refine ⟨2559952351221662636390741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27306158413031068121501237 2559952351221662636390741)
              ·
                refine ⟨7499860403969714755051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 2559952351221662636390741 7499860403969714755051)
                ·
                  rfl

theorem cell23_394360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 10].length) (baseStart_394360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_394360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_394360 prefixEnd_394360 := by exact prefixLift 394360
  have htrace : WordTrace (prefixWord ++ tailWord_394360) baseStart_394360 baseEnd_394360 := by
    simpa [prefixWord, tailWord_394360, baseEnd_394360] using wordTrace_append hprefix tailTrace_394360
  have hstable : (prefixWord ++ tailWord_394360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394360).length < 2 ^ (prefixWord ++ tailWord_394360).sum := by decide
  have hdescent : baseEnd_394360 < baseStart_394360 := by decide
  rcases family_descends (prefixWord ++ tailWord_394360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394364 : List Nat := [2, 2, 2, 1, 1, 3, 3, 3, 2, 4]
def baseStart_394364 : Nat := 118140960795 + 394364 * 2 ^ 59
def prefixEnd_394364 : Nat := 4983230072969 + 3 ^ 40 * 394364 * 2
def baseEnd_394364 : Nat := 67499428276600094245453

theorem tailTrace_394364 : CollatzResearch.WordTrace tailWord_394364 prefixEnd_394364 67499428276600094245453 := by
  unfold tailWord_394364
  simp only [CollatzResearch.WordTrace]
  refine ⟨7191818371647027427071073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9589091162196036569428097 7191818371647027427071073)
  ·
    refine ⟨5393863778735270570303305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7191818371647027427071073 5393863778735270570303305)
    ·
      refine ⟨4045397834051452927727479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5393863778735270570303305 4045397834051452927727479)
      ·
        refine ⟨6068096751077179391591219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4045397834051452927727479 6068096751077179391591219)
        ·
          refine ⟨9102145126615769087386829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6068096751077179391591219 9102145126615769087386829)
          ·
            refine ⟨3413304422480913407770061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9102145126615769087386829 3413304422480913407770061)
            ·
              refine ⟨1279989158430342527913773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3413304422480913407770061 1279989158430342527913773)
              ·
                refine ⟨479995934411378447967665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1279989158430342527913773 479995934411378447967665)
                ·
                  refine ⟨359996950808533835975749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 479995934411378447967665 359996950808533835975749)
                  ·
                    refine ⟨67499428276600094245453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 359996950808533835975749 67499428276600094245453)
                    ·
                      rfl

theorem cell23_394364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 3, 2, 4].length) (baseStart_394364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_394364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_394364 prefixEnd_394364 := by exact prefixLift 394364
  have htrace : WordTrace (prefixWord ++ tailWord_394364) baseStart_394364 baseEnd_394364 := by
    simpa [prefixWord, tailWord_394364, baseEnd_394364] using wordTrace_append hprefix tailTrace_394364
  have hstable : (prefixWord ++ tailWord_394364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394364).length < 2 ^ (prefixWord ++ tailWord_394364).sum := by decide
  have hdescent : baseEnd_394364 < baseStart_394364 := by decide
  rcases family_descends (prefixWord ++ tailWord_394364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394387 : List Nat := [1, 1, 1, 2, 1, 2, 5, 1, 3, 3, 3]
def baseStart_394387 : Nat := 118140960795 + 394387 * 2 ^ 59
def prefixEnd_394387 : Nat := 4983230072969 + 3 ^ 40 * 394387 * 2
def baseEnd_394387 : Nat := 202510094884853692748753

theorem tailTrace_394387 : CollatzResearch.WordTrace tailWord_394387 prefixEnd_394387 202510094884853692748753 := by
  unfold tailWord_394387
  simp only [CollatzResearch.WordTrace]
  refine ⟨14384475622210729782229415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9589650414807153188152943 14384475622210729782229415)
  ·
    refine ⟨21576713433316094673344123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14384475622210729782229415 21576713433316094673344123)
    ·
      refine ⟨32365070149974142010016185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21576713433316094673344123 32365070149974142010016185)
      ·
        refine ⟨24273802612480606507512139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32365070149974142010016185 24273802612480606507512139)
        ·
          refine ⟨36410703918720909761268209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24273802612480606507512139 36410703918720909761268209)
          ·
            refine ⟨27308027939040682320951157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36410703918720909761268209 27308027939040682320951157)
            ·
              refine ⟨2560127619285063967589171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27308027939040682320951157 2560127619285063967589171)
              ·
                refine ⟨3840191428927595951383757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2560127619285063967589171 3840191428927595951383757)
                ·
                  refine ⟨1440071785847848481768909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3840191428927595951383757 1440071785847848481768909)
                  ·
                    refine ⟨540026919692943180663341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1440071785847848481768909 540026919692943180663341)
                    ·
                      refine ⟨202510094884853692748753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 540026919692943180663341 202510094884853692748753)
                      ·
                        rfl

theorem cell23_394387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 3, 3, 3].length) (baseStart_394387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_394387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_394387 prefixEnd_394387 := by exact prefixLift 394387
  have htrace : WordTrace (prefixWord ++ tailWord_394387) baseStart_394387 baseEnd_394387 := by
    simpa [prefixWord, tailWord_394387, baseEnd_394387] using wordTrace_append hprefix tailTrace_394387
  have hstable : (prefixWord ++ tailWord_394387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394387).length < 2 ^ (prefixWord ++ tailWord_394387).sum := by decide
  have hdescent : baseEnd_394387 < baseStart_394387 := by decide
  rcases family_descends (prefixWord ++ tailWord_394387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394398 : List Nat := [4, 3, 1, 1, 2, 2, 2, 2, 2, 4]
def baseStart_394398 : Nat := 118140960795 + 394398 * 2 ^ 59
def prefixEnd_394398 : Nat := 4983230072969 + 3 ^ 40 * 394398 * 2
def baseEnd_394398 : Nat := 67505247724017716570401

theorem tailTrace_394398 : CollatzResearch.WordTrace tailWord_394398 prefixEnd_394398 67505247724017716570401 := by
  unfold tailWord_394398
  simp only [CollatzResearch.WordTrace]
  refine ⟨1798109603146359832609981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9589917883447252440586565 1798109603146359832609981)
  ·
    refine ⟨674291101179884937228743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1798109603146359832609981 674291101179884937228743)
    ·
      refine ⟨1011436651769827405843115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 674291101179884937228743 1011436651769827405843115)
      ·
        refine ⟨1517154977654741108764673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1011436651769827405843115 1517154977654741108764673)
        ·
          refine ⟨1137866233241055831573505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1517154977654741108764673 1137866233241055831573505)
          ·
            refine ⟨853399674930791873680129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1137866233241055831573505 853399674930791873680129)
            ·
              refine ⟨640049756198093905260097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 853399674930791873680129 640049756198093905260097)
              ·
                refine ⟨480037317148570428945073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 640049756198093905260097 480037317148570428945073)
                ·
                  refine ⟨360027987861427821708805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 480037317148570428945073 360027987861427821708805)
                  ·
                    refine ⟨67505247724017716570401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 360027987861427821708805 67505247724017716570401)
                    ·
                      rfl

theorem cell23_394398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_394398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_394398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_394398 prefixEnd_394398 := by exact prefixLift 394398
  have htrace : WordTrace (prefixWord ++ tailWord_394398) baseStart_394398 baseEnd_394398 := by
    simpa [prefixWord, tailWord_394398, baseEnd_394398] using wordTrace_append hprefix tailTrace_394398
  have hstable : (prefixWord ++ tailWord_394398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394398).length < 2 ^ (prefixWord ++ tailWord_394398).sum := by decide
  have hdescent : baseEnd_394398 < baseStart_394398 := by decide
  rcases family_descends (prefixWord ++ tailWord_394398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394405 : List Nat := [1, 3, 1, 2, 1, 4, 4, 2, 1, 2, 2]
def baseStart_394405 : Nat := 118140960795 + 394405 * 2 ^ 59
def prefixEnd_394405 : Nat := 4983230072969 + 3 ^ 40 * 394405 * 2
def baseEnd_394405 : Nat := 202519337536634622323671

theorem tailTrace_394405 : CollatzResearch.WordTrace tailWord_394405 prefixEnd_394405 202519337536634622323671 := by
  unfold tailWord_394405
  simp only [CollatzResearch.WordTrace]
  refine ⟨14385132136145518856384669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9590088090763679237589779 14385132136145518856384669)
  ·
    refine ⟨5394424551054569571144251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14385132136145518856384669 5394424551054569571144251)
    ·
      refine ⟨8091636826581854356716377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5394424551054569571144251 8091636826581854356716377)
      ·
        refine ⟨6068727619936390767537283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8091636826581854356716377 6068727619936390767537283)
        ·
          refine ⟨9103091429904586151305925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6068727619936390767537283 9103091429904586151305925)
          ·
            refine ⟨1706829643107109903369861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9103091429904586151305925 1706829643107109903369861)
            ·
              refine ⟨320030558082583106881849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1706829643107109903369861 320030558082583106881849)
              ·
                refine ⟨240022918561937330161387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 320030558082583106881849 240022918561937330161387)
                ·
                  refine ⟨360034377842905995242081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 240022918561937330161387 360034377842905995242081)
                  ·
                    refine ⟨270025783382179496431561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 360034377842905995242081 270025783382179496431561)
                    ·
                      refine ⟨202519337536634622323671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 270025783382179496431561 202519337536634622323671)
                      ·
                        rfl

theorem cell23_394405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 4, 2, 1, 2, 2].length) (baseStart_394405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_394405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_394405 prefixEnd_394405 := by exact prefixLift 394405
  have htrace : WordTrace (prefixWord ++ tailWord_394405) baseStart_394405 baseEnd_394405 := by
    simpa [prefixWord, tailWord_394405, baseEnd_394405] using wordTrace_append hprefix tailTrace_394405
  have hstable : (prefixWord ++ tailWord_394405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394405).length < 2 ^ (prefixWord ++ tailWord_394405).sum := by decide
  have hdescent : baseEnd_394405 < baseStart_394405 := by decide
  rcases family_descends (prefixWord ++ tailWord_394405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394422 : List Nat := [5, 1, 3, 2, 1, 1, 1, 2, 3, 2, 2]
def baseStart_394422 : Nat := 118140960795 + 394422 * 2 ^ 59
def prefixEnd_394422 : Nat := 4983230072969 + 3 ^ 40 * 394422 * 2
def baseEnd_394422 : Nat := 202528066707761055811093

theorem tailTrace_394422 : CollatzResearch.WordTrace tailWord_394422 prefixEnd_394422 202528066707761055811093 := by
  unfold tailWord_394422
  simp only [CollatzResearch.WordTrace]
  refine ⟨899109511067745672484595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9590501451389287173169013 899109511067745672484595)
  ·
    refine ⟨1348664266601618508726893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 899109511067745672484595 1348664266601618508726893)
    ·
      refine ⟨505749099975606940772585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1348664266601618508726893 505749099975606940772585)
      ·
        refine ⟨379311824981705205579439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 505749099975606940772585 379311824981705205579439)
        ·
          refine ⟨568967737472557808369159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 379311824981705205579439 568967737472557808369159)
          ·
            refine ⟨853451606208836712553739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 568967737472557808369159 853451606208836712553739)
            ·
              refine ⟨1280177409313255068830609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 853451606208836712553739 1280177409313255068830609)
              ·
                refine ⟨960133056984941301622957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1280177409313255068830609 960133056984941301622957)
                ·
                  refine ⟨360049896369352988108609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 960133056984941301622957 360049896369352988108609)
                  ·
                    refine ⟨270037422277014741081457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 360049896369352988108609 270037422277014741081457)
                    ·
                      refine ⟨202528066707761055811093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 270037422277014741081457 202528066707761055811093)
                      ·
                        rfl

theorem cell23_394422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_394422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_394422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_394422 prefixEnd_394422 := by exact prefixLift 394422
  have htrace : WordTrace (prefixWord ++ tailWord_394422) baseStart_394422 baseEnd_394422 := by
    simpa [prefixWord, tailWord_394422, baseEnd_394422] using wordTrace_append hprefix tailTrace_394422
  have hstable : (prefixWord ++ tailWord_394422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394422).length < 2 ^ (prefixWord ++ tailWord_394422).sum := by decide
  have hdescent : baseEnd_394422 < baseStart_394422 := by decide
  rcases family_descends (prefixWord ++ tailWord_394422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394447 : List Nat := [1, 1, 2, 1, 1, 3, 2, 2, 1, 6, 3]
def baseStart_394447 : Nat := 118140960795 + 394447 * 2 ^ 59
def prefixEnd_394447 : Nat := 4983230072969 + 3 ^ 40 * 394447 * 2
def baseEnd_394447 : Nat := 202540903724123457998477

theorem tailTrace_394447 : CollatzResearch.WordTrace tailWord_394447 prefixEnd_394447 202540903724123457998477 := by
  unfold tailWord_394447
  simp only [CollatzResearch.WordTrace]
  refine ⟨14386664001993360029413595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9591109334662240019609063 14386664001993360029413595)
  ·
    refine ⟨21579996002990040044120393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14386664001993360029413595 21579996002990040044120393)
    ·
      refine ⟨16184997002242530033090295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21579996002990040044120393 16184997002242530033090295)
      ·
        refine ⟨24277495503363795049635443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16184997002242530033090295 24277495503363795049635443)
        ·
          refine ⟨36416243255045692574453165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24277495503363795049635443 36416243255045692574453165)
          ·
            refine ⟨13656091220642134715419937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36416243255045692574453165 13656091220642134715419937)
            ·
              refine ⟨10242068415481601036564953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13656091220642134715419937 10242068415481601036564953)
              ·
                refine ⟨7681551311611200777423715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10242068415481601036564953 7681551311611200777423715)
                ·
                  refine ⟨11522326967416801166135573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7681551311611200777423715 11522326967416801166135573)
                  ·
                    refine ⟨540109076597662554662605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11522326967416801166135573 540109076597662554662605)
                    ·
                      refine ⟨202540903724123457998477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 540109076597662554662605 202540903724123457998477)
                      ·
                        rfl

theorem cell23_394447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 6, 3].length) (baseStart_394447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_394447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_394447 prefixEnd_394447 := by exact prefixLift 394447
  have htrace : WordTrace (prefixWord ++ tailWord_394447) baseStart_394447 baseEnd_394447 := by
    simpa [prefixWord, tailWord_394447, baseEnd_394447] using wordTrace_append hprefix tailTrace_394447
  have hstable : (prefixWord ++ tailWord_394447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394447).length < 2 ^ (prefixWord ++ tailWord_394447).sum := by decide
  have hdescent : baseEnd_394447 < baseStart_394447 := by decide
  rcases family_descends (prefixWord ++ tailWord_394447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394474 : List Nat := [3, 1, 3, 1, 1, 3, 2, 1, 2, 2, 4]
def baseStart_394474 : Nat := 118140960795 + 394474 * 2 ^ 59
def prefixEnd_394474 : Nat := 4983230072969 + 3 ^ 40 * 394474 * 2
def baseEnd_394474 : Nat := 202554767701794852360853

theorem tailTrace_394474 : CollatzResearch.WordTrace tailWord_394474 prefixEnd_394474 202554767701794852360853 := by
  unfold tailWord_394474
  simp only [CollatzResearch.WordTrace]
  refine ⟨3596912193223885910161619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9591765848597029093764317 3596912193223885910161619)
  ·
    refine ⟨5395368289835828865242429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3596912193223885910161619 5395368289835828865242429)
    ·
      refine ⟨2023263108688435824465911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5395368289835828865242429 2023263108688435824465911)
      ·
        refine ⟨3034894663032653736698867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2023263108688435824465911 3034894663032653736698867)
        ·
          refine ⟨4552341994548980605048301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3034894663032653736698867 4552341994548980605048301)
          ·
            refine ⟨1707128247955867726893113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4552341994548980605048301 1707128247955867726893113)
            ·
              refine ⟨1280346185966900795169835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1707128247955867726893113 1280346185966900795169835)
              ·
                refine ⟨1920519278950351192754753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1280346185966900795169835 1920519278950351192754753)
                ·
                  refine ⟨1440389459212763394566065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1920519278950351192754753 1440389459212763394566065)
                  ·
                    refine ⟨1080292094409572545924549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1440389459212763394566065 1080292094409572545924549)
                    ·
                      refine ⟨202554767701794852360853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1080292094409572545924549 202554767701794852360853)
                      ·
                        rfl

theorem cell23_394474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_394474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_394474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_394474 prefixEnd_394474 := by exact prefixLift 394474
  have htrace : WordTrace (prefixWord ++ tailWord_394474) baseStart_394474 baseEnd_394474 := by
    simpa [prefixWord, tailWord_394474, baseEnd_394474] using wordTrace_append hprefix tailTrace_394474
  have hstable : (prefixWord ++ tailWord_394474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394474).length < 2 ^ (prefixWord ++ tailWord_394474).sum := by decide
  have hdescent : baseEnd_394474 < baseStart_394474 := by decide
  rcases family_descends (prefixWord ++ tailWord_394474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394478 : List Nat := [4, 1, 2, 1, 1, 1, 2, 5, 2, 2, 2]
def baseStart_394478 : Nat := 118140960795 + 394478 * 2 ^ 59
def prefixEnd_394478 : Nat := 4983230072969 + 3 ^ 40 * 394478 * 2
def baseEnd_394478 : Nat := 202556821624412836710835

theorem tailTrace_394478 : CollatzResearch.WordTrace tailWord_394478 prefixEnd_394478 202556821624412836710835 := by
  unfold tailWord_394478
  simp only [CollatzResearch.WordTrace]
  refine ⟨1798474333110131540474011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9591863109920701549194725 1798474333110131540474011)
  ·
    refine ⟨2697711499665197310711017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1798474333110131540474011 2697711499665197310711017)
    ·
      refine ⟨2023283624748897983033263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2697711499665197310711017 2023283624748897983033263)
      ·
        refine ⟨3034925437123346974549895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2023283624748897983033263 3034925437123346974549895)
        ·
          refine ⟨4552388155685020461824843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3034925437123346974549895 4552388155685020461824843)
          ·
            refine ⟨6828582233527530692737265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4552388155685020461824843 6828582233527530692737265)
            ·
              refine ⟨5121436675145648019552949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6828582233527530692737265 5121436675145648019552949)
              ·
                refine ⟨480134688294904501833089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5121436675145648019552949 480134688294904501833089)
                ·
                  refine ⟨360101016221178376374817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 480134688294904501833089 360101016221178376374817)
                  ·
                    refine ⟨270075762165883782281113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 360101016221178376374817 270075762165883782281113)
                    ·
                      refine ⟨202556821624412836710835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 270075762165883782281113 202556821624412836710835)
                      ·
                        rfl

theorem cell23_394478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 5, 2, 2, 2].length) (baseStart_394478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_394478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_394478 prefixEnd_394478 := by exact prefixLift 394478
  have htrace : WordTrace (prefixWord ++ tailWord_394478) baseStart_394478 baseEnd_394478 := by
    simpa [prefixWord, tailWord_394478, baseEnd_394478] using wordTrace_append hprefix tailTrace_394478
  have hstable : (prefixWord ++ tailWord_394478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394478).length < 2 ^ (prefixWord ++ tailWord_394478).sum := by decide
  have hdescent : baseEnd_394478 < baseStart_394478 := by decide
  rcases family_descends (prefixWord ++ tailWord_394478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394544 : List Nat := [2, 1, 1, 1, 2, 2, 4, 1, 5, 4]
def baseStart_394544 : Nat := 118140960795 + 394544 * 2 ^ 59
def prefixEnd_394544 : Nat := 4983230072969 + 3 ^ 40 * 394544 * 2
def baseEnd_394544 : Nat := 67530237115869859495177

theorem tailTrace_394544 : CollatzResearch.WordTrace tailWord_394544 prefixEnd_394544 67530237115869859495177 := by
  unfold tailWord_394544
  simp only [CollatzResearch.WordTrace]
  refine ⟨7195100941320972797847343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9593467921761297063796457 7195100941320972797847343)
  ·
    refine ⟨10792651411981459196771015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7195100941320972797847343 10792651411981459196771015)
    ·
      refine ⟨16188977117972188795156523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10792651411981459196771015 16188977117972188795156523)
      ·
        refine ⟨24283465676958283192734785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16188977117972188795156523 24283465676958283192734785)
        ·
          refine ⟨18212599257718712394551089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24283465676958283192734785 18212599257718712394551089)
          ·
            refine ⟨13659449443289034295913317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18212599257718712394551089 13659449443289034295913317)
            ·
              refine ⟨2561146770616693930483747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13659449443289034295913317 2561146770616693930483747)
              ·
                refine ⟨3841720155925040895725621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2561146770616693930483747 3841720155925040895725621)
                ·
                  refine ⟨360161264617972583974277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3841720155925040895725621 360161264617972583974277)
                  ·
                    refine ⟨67530237115869859495177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 360161264617972583974277 67530237115869859495177)
                    ·
                      rfl

theorem cell23_394544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 5, 4].length) (baseStart_394544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_394544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_394544 prefixEnd_394544 := by exact prefixLift 394544
  have htrace : WordTrace (prefixWord ++ tailWord_394544) baseStart_394544 baseEnd_394544 := by
    simpa [prefixWord, tailWord_394544, baseEnd_394544] using wordTrace_append hprefix tailTrace_394544
  have hstable : (prefixWord ++ tailWord_394544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394544).length < 2 ^ (prefixWord ++ tailWord_394544).sum := by decide
  have hdescent : baseEnd_394544 < baseStart_394544 := by decide
  rcases family_descends (prefixWord ++ tailWord_394544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394621 : List Nat := [1, 4, 1, 1, 2, 2, 3, 3, 1, 5]
def baseStart_394621 : Nat := 118140960795 + 394621 * 2 ^ 59
def prefixEnd_394621 : Nat := 4983230072969 + 3 ^ 40 * 394621 * 2
def baseEnd_394621 : Nat := 67543416452668592407559

theorem tailTrace_394621 : CollatzResearch.WordTrace tailWord_394621 prefixEnd_394621 67543416452668592407559 := by
  unfold tailWord_394621
  simp only [CollatzResearch.WordTrace]
  refine ⟨14393010303362987746247717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9595340202241991830831811 14393010303362987746247717)
  ·
    refine ⟨2698689431880560202421447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14393010303362987746247717 2698689431880560202421447)
    ·
      refine ⟨4048034147820840303632171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2698689431880560202421447 4048034147820840303632171)
      ·
        refine ⟨6072051221731260455448257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4048034147820840303632171 6072051221731260455448257)
        ·
          refine ⟨4554038416298445341586193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6072051221731260455448257 4554038416298445341586193)
          ·
            refine ⟨3415528812223834006189645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4554038416298445341586193 3415528812223834006189645)
            ·
              refine ⟨1280823304583937752321117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3415528812223834006189645 1280823304583937752321117)
              ·
                refine ⟨480308739218976657120419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1280823304583937752321117 480308739218976657120419)
                ·
                  refine ⟨720463108828464985680629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 480308739218976657120419 720463108828464985680629)
                  ·
                    refine ⟨67543416452668592407559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 720463108828464985680629 67543416452668592407559)
                    ·
                      rfl

theorem cell23_394621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 3, 1, 5].length) (baseStart_394621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_394621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_394621 prefixEnd_394621 := by exact prefixLift 394621
  have htrace : WordTrace (prefixWord ++ tailWord_394621) baseStart_394621 baseEnd_394621 := by
    simpa [prefixWord, tailWord_394621, baseEnd_394621] using wordTrace_append hprefix tailTrace_394621
  have hstable : (prefixWord ++ tailWord_394621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394621).length < 2 ^ (prefixWord ++ tailWord_394621).sum := by decide
  have hdescent : baseEnd_394621 < baseStart_394621 := by decide
  rcases family_descends (prefixWord ++ tailWord_394621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394625 : List Nat := [1, 2, 4, 3, 3, 1, 1, 2, 6]
def baseStart_394625 : Nat := 118140960795 + 394625 * 2 ^ 59
def prefixEnd_394625 : Nat := 4983230072969 + 3 ^ 40 * 394625 * 2
def baseEnd_394625 : Nat := 22514700364513751285851

theorem tailTrace_394625 : CollatzResearch.WordTrace tailWord_394625 prefixEnd_394625 22514700364513751285851 := by
  unfold tailWord_394625
  simp only [CollatzResearch.WordTrace]
  refine ⟨14393156195348496429393329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9595437463565664286262219 14393156195348496429393329)
  ·
    refine ⟨10794867146511372322044997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14393156195348496429393329 10794867146511372322044997)
    ·
      refine ⟨2024037589970882310383437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10794867146511372322044997 2024037589970882310383437)
      ·
        refine ⟨759014096239080866393789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2024037589970882310383437 759014096239080866393789)
        ·
          refine ⟨284630286089655324897671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 759014096239080866393789 284630286089655324897671)
          ·
            refine ⟨426945429134482987346507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284630286089655324897671 426945429134482987346507)
            ·
              refine ⟨640418143701724481019761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 426945429134482987346507 640418143701724481019761)
              ·
                refine ⟨480313607776293360764821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 640418143701724481019761 480313607776293360764821)
                ·
                  refine ⟨22514700364513751285851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 480313607776293360764821 22514700364513751285851)
                  ·
                    rfl

theorem cell23_394625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 2, 6].length) (baseStart_394625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_394625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_394625 prefixEnd_394625 := by exact prefixLift 394625
  have htrace : WordTrace (prefixWord ++ tailWord_394625) baseStart_394625 baseEnd_394625 := by
    simpa [prefixWord, tailWord_394625, baseEnd_394625] using wordTrace_append hprefix tailTrace_394625
  have hstable : (prefixWord ++ tailWord_394625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394625).length < 2 ^ (prefixWord ++ tailWord_394625).sum := by decide
  have hdescent : baseEnd_394625 < baseStart_394625 := by decide
  rcases family_descends (prefixWord ++ tailWord_394625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394658 : List Nat := [3, 3, 1, 2, 1, 2, 1, 4, 1, 1, 4]
def baseStart_394658 : Nat := 118140960795 + 394658 * 2 ^ 59
def prefixEnd_394658 : Nat := 4983230072969 + 3 ^ 40 * 394658 * 2
def baseEnd_394658 : Nat := 202649248142222132460007

theorem tailTrace_394658 : CollatzResearch.WordTrace tailWord_394658 prefixEnd_394658 202649248142222132460007 := by
  unfold tailWord_394658
  simp only [CollatzResearch.WordTrace]
  refine ⟨3598589951057235766336157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9596239869485962043563085 3598589951057235766336157)
  ·
    refine ⟨1349471231646463412376059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3598589951057235766336157 1349471231646463412376059)
    ·
      refine ⟨2024206847469695118564089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1349471231646463412376059 2024206847469695118564089)
      ·
        refine ⟨1518155135602271338923067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2024206847469695118564089 1518155135602271338923067)
        ·
          refine ⟨2277232703403407008384601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1518155135602271338923067 2277232703403407008384601)
          ·
            refine ⟨1707924527552555256288451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2277232703403407008384601 1707924527552555256288451)
            ·
              refine ⟨2561886791328832884432677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1707924527552555256288451 2561886791328832884432677)
              ·
                refine ⟨480353773374156165831127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2561886791328832884432677 480353773374156165831127)
                ·
                  refine ⟨720530660061234248746691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 480353773374156165831127 720530660061234248746691)
                  ·
                    refine ⟨1080795990091851373120037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 720530660061234248746691 1080795990091851373120037)
                    ·
                      refine ⟨202649248142222132460007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1080795990091851373120037 202649248142222132460007)
                      ·
                        rfl

theorem cell23_394658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_394658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_394658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_394658 prefixEnd_394658 := by exact prefixLift 394658
  have htrace : WordTrace (prefixWord ++ tailWord_394658) baseStart_394658 baseEnd_394658 := by
    simpa [prefixWord, tailWord_394658, baseEnd_394658] using wordTrace_append hprefix tailTrace_394658
  have hstable : (prefixWord ++ tailWord_394658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394658).length < 2 ^ (prefixWord ++ tailWord_394658).sum := by decide
  have hdescent : baseEnd_394658 < baseStart_394658 := by decide
  rcases family_descends (prefixWord ++ tailWord_394658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394669 : List Nat := [1, 5, 2, 2, 1, 3, 1, 3, 1, 1, 3]
def baseStart_394669 : Nat := 118140960795 + 394669 * 2 ^ 59
def prefixEnd_394669 : Nat := 4983230072969 + 3 ^ 40 * 394669 * 2
def baseEnd_394669 : Nat := 202654896429421589422457

theorem tailTrace_394669 : CollatzResearch.WordTrace tailWord_394669 prefixEnd_394669 202654896429421589422457 := by
  unfold tailWord_394669
  simp only [CollatzResearch.WordTrace]
  refine ⟨14394761007189091943995061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9596507338126061295996707 14394761007189091943995061)
  ·
    refine ⟨1349508844423977369749537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14394761007189091943995061 1349508844423977369749537)
    ·
      refine ⟨1012131633317983027312153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1349508844423977369749537 1012131633317983027312153)
      ·
        refine ⟨759098724988487270484115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1012131633317983027312153 759098724988487270484115)
        ·
          refine ⟨1138648087482730905726173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 759098724988487270484115 1138648087482730905726173)
          ·
            refine ⟨426993032806024089647315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1138648087482730905726173 426993032806024089647315)
            ·
              refine ⟨640489549209036134470973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 426993032806024089647315 640489549209036134470973)
              ·
                refine ⟨240183580953388550426615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 640489549209036134470973 240183580953388550426615)
                ·
                  refine ⟨360275371430082825639923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 240183580953388550426615 360275371430082825639923)
                  ·
                    refine ⟨540413057145124238459885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 360275371430082825639923 540413057145124238459885)
                    ·
                      refine ⟨202654896429421589422457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 540413057145124238459885 202654896429421589422457)
                      ·
                        rfl

theorem cell23_394669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_394669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_394669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_394669 prefixEnd_394669 := by exact prefixLift 394669
  have htrace : WordTrace (prefixWord ++ tailWord_394669) baseStart_394669 baseEnd_394669 := by
    simpa [prefixWord, tailWord_394669, baseEnd_394669] using wordTrace_append hprefix tailTrace_394669
  have hstable : (prefixWord ++ tailWord_394669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394669).length < 2 ^ (prefixWord ++ tailWord_394669).sum := by decide
  have hdescent : baseEnd_394669 < baseStart_394669 := by decide
  rcases family_descends (prefixWord ++ tailWord_394669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394681 : List Nat := [1, 2, 1, 4, 4, 2, 9]
def baseStart_394681 : Nat := 118140960795 + 394681 * 2 ^ 59
def prefixEnd_394681 : Nat := 4983230072969 + 3 ^ 40 * 394681 * 2
def baseEnd_394681 : Nat := 2501988372805870894721

theorem tailTrace_394681 : CollatzResearch.WordTrace tailWord_394681 prefixEnd_394681 2501988372805870894721 := by
  unfold tailWord_394681
  simp only [CollatzResearch.WordTrace]
  refine ⟨14395198683145617993431897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9596799122097078662287931 14395198683145617993431897)
  ·
    refine ⟨10796399012359213495073923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14395198683145617993431897 10796399012359213495073923)
    ·
      refine ⟨16194598518538820242610885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10796399012359213495073923 16194598518538820242610885)
      ·
        refine ⟨3036487222226028795489541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16194598518538820242610885 3036487222226028795489541)
        ·
          refine ⟨569341354167380399154289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3036487222226028795489541 569341354167380399154289)
          ·
            refine ⟨427006015625535299365717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 569341354167380399154289 427006015625535299365717)
            ·
              refine ⟨2501988372805870894721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 427006015625535299365717 2501988372805870894721)
              ·
                rfl

theorem cell23_394681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 9].length) (baseStart_394681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_394681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_394681 prefixEnd_394681 := by exact prefixLift 394681
  have htrace : WordTrace (prefixWord ++ tailWord_394681) baseStart_394681 baseEnd_394681 := by
    simpa [prefixWord, tailWord_394681, baseEnd_394681] using wordTrace_append hprefix tailTrace_394681
  have hstable : (prefixWord ++ tailWord_394681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394681).length < 2 ^ (prefixWord ++ tailWord_394681).sum := by decide
  have hdescent : baseEnd_394681 < baseStart_394681 := by decide
  rcases family_descends (prefixWord ++ tailWord_394681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394692 : List Nat := [2, 3, 3, 2, 1, 1, 3, 1, 3, 2, 2]
def baseStart_394692 : Nat := 118140960795 + 394692 * 2 ^ 59
def prefixEnd_394692 : Nat := 4983230072969 + 3 ^ 40 * 394692 * 2
def baseEnd_394692 : Nat := 202666706484474999434851

theorem tailTrace_394692 : CollatzResearch.WordTrace tailWord_394692 prefixEnd_394692 202666706484474999434851 := by
  unfold tailWord_394692
  simp only [CollatzResearch.WordTrace]
  refine ⟨7197799943052883436041165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9597066590737177914721553 7197799943052883436041165)
  ·
    refine ⟨2699174978644831288515437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7197799943052883436041165 2699174978644831288515437)
    ·
      refine ⟨1012190616991811733193289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2699174978644831288515437 1012190616991811733193289)
      ·
        refine ⟨759142962743858799894967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1012190616991811733193289 759142962743858799894967)
        ·
          refine ⟨1138714444115788199842451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 759142962743858799894967 1138714444115788199842451)
          ·
            refine ⟨1708071666173682299763677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1138714444115788199842451 1708071666173682299763677)
            ·
              refine ⟨640526874815130862411379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1708071666173682299763677 640526874815130862411379)
              ·
                refine ⟨960790312222696293617069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 640526874815130862411379 960790312222696293617069)
                ·
                  refine ⟨360296367083511110106401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 960790312222696293617069 360296367083511110106401)
                  ·
                    refine ⟨270222275312633332579801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 360296367083511110106401 270222275312633332579801)
                    ·
                      refine ⟨202666706484474999434851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 270222275312633332579801 202666706484474999434851)
                      ·
                        rfl

theorem cell23_394692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_394692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_394692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_394692 prefixEnd_394692 := by exact prefixLift 394692
  have htrace : WordTrace (prefixWord ++ tailWord_394692) baseStart_394692 baseEnd_394692 := by
    simpa [prefixWord, tailWord_394692, baseEnd_394692] using wordTrace_append hprefix tailTrace_394692
  have hstable : (prefixWord ++ tailWord_394692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394692).length < 2 ^ (prefixWord ++ tailWord_394692).sum := by decide
  have hdescent : baseEnd_394692 < baseStart_394692 := by decide
  rcases family_descends (prefixWord ++ tailWord_394692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394704 : List Nat := [2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 5]
def baseStart_394704 : Nat := 118140960795 + 394704 * 2 ^ 59
def prefixEnd_394704 : Nat := 4983230072969 + 3 ^ 40 * 394704 * 2
def baseEnd_394704 : Nat := 202672868252328952484795

theorem tailTrace_394704 : CollatzResearch.WordTrace tailWord_394704 prefixEnd_394704 202672868252328952484795 := by
  unfold tailWord_394704
  simp only [CollatzResearch.WordTrace]
  refine ⟨7198018781031146460759583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9597358374708195281012777 7198018781031146460759583)
  ·
    refine ⟨10797028171546719691139375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7198018781031146460759583 10797028171546719691139375)
    ·
      refine ⟨16195542257320079536709063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10797028171546719691139375 16195542257320079536709063)
      ·
        refine ⟨24293313385980119305063595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16195542257320079536709063 24293313385980119305063595)
        ·
          refine ⟨36439970078970178957595393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24293313385980119305063595 36439970078970178957595393)
          ·
            refine ⟨27329977559227634218196545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36439970078970178957595393 27329977559227634218196545)
            ·
              refine ⟨20497483169420725663647409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27329977559227634218196545 20497483169420725663647409)
              ·
                refine ⟨15373112377065544247735557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20497483169420725663647409 15373112377065544247735557)
                ·
                  refine ⟨2882458570699789546450417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15373112377065544247735557 2882458570699789546450417)
                  ·
                    refine ⟨2161843928024842159837813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2882458570699789546450417 2161843928024842159837813)
                    ·
                      refine ⟨202672868252328952484795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2161843928024842159837813 202672868252328952484795)
                      ·
                        rfl

theorem cell23_394704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 5].length) (baseStart_394704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_394704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_394704 prefixEnd_394704 := by exact prefixLift 394704
  have htrace : WordTrace (prefixWord ++ tailWord_394704) baseStart_394704 baseEnd_394704 := by
    simpa [prefixWord, tailWord_394704, baseEnd_394704] using wordTrace_append hprefix tailTrace_394704
  have hstable : (prefixWord ++ tailWord_394704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394704).length < 2 ^ (prefixWord ++ tailWord_394704).sum := by decide
  have hdescent : baseEnd_394704 < baseStart_394704 := by decide
  rcases family_descends (prefixWord ++ tailWord_394704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394742 : List Nat := [5, 1, 1, 1, 2, 3, 2, 2, 2, 1, 3]
def baseStart_394742 : Nat := 118140960795 + 394742 * 2 ^ 59
def prefixEnd_394742 : Nat := 4983230072969 + 3 ^ 40 * 394742 * 2
def baseEnd_394742 : Nat := 202692380517199803809621

theorem tailTrace_394742 : CollatzResearch.WordTrace tailWord_394742 prefixEnd_394742 202692380517199803809621 := by
  unfold tailWord_394742
  simp only [CollatzResearch.WordTrace]
  refine ⟨899838970995289088212655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9598282357283083607601653 899838970995289088212655)
  ·
    refine ⟨1349758456492933632318983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 899838970995289088212655 1349758456492933632318983)
    ·
      refine ⟨2024637684739400448478475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1349758456492933632318983 2024637684739400448478475)
      ·
        refine ⟨3036956527109100672717713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2024637684739400448478475 3036956527109100672717713)
        ·
          refine ⟨2277717395331825504538285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3036956527109100672717713 2277717395331825504538285)
          ·
            refine ⟨854144023249434564201857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2277717395331825504538285 854144023249434564201857)
            ·
              refine ⟨640608017437075923151393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 854144023249434564201857 640608017437075923151393)
              ·
                refine ⟨480456013077806942363545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 640608017437075923151393 480456013077806942363545)
                ·
                  refine ⟨360342009808355206772659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 480456013077806942363545 360342009808355206772659)
                  ·
                    refine ⟨540513014712532810158989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 360342009808355206772659 540513014712532810158989)
                    ·
                      refine ⟨202692380517199803809621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 540513014712532810158989 202692380517199803809621)
                      ·
                        rfl

theorem cell23_394742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 2, 2, 1, 3].length) (baseStart_394742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_394742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_394742 prefixEnd_394742 := by exact prefixLift 394742
  have htrace : WordTrace (prefixWord ++ tailWord_394742) baseStart_394742 baseEnd_394742 := by
    simpa [prefixWord, tailWord_394742, baseEnd_394742] using wordTrace_append hprefix tailTrace_394742
  have hstable : (prefixWord ++ tailWord_394742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394742).length < 2 ^ (prefixWord ++ tailWord_394742).sum := by decide
  have hdescent : baseEnd_394742 < baseStart_394742 := by decide
  rcases family_descends (prefixWord ++ tailWord_394742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394761 : List Nat := [1, 2, 1, 1, 3, 1, 5, 1, 2, 2, 4]
def baseStart_394761 : Nat := 118140960795 + 394761 * 2 ^ 59
def prefixEnd_394761 : Nat := 4983230072969 + 3 ^ 40 * 394761 * 2
def baseEnd_394761 : Nat := 202702136649635229472033

theorem tailTrace_394761 : CollatzResearch.WordTrace tailWord_394761 prefixEnd_394761 202702136649635229472033 := by
  unfold tailWord_394761
  simp only [CollatzResearch.WordTrace]
  refine ⟨14398116522855791656344137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9598744348570527770896091 14398116522855791656344137)
  ·
    refine ⟨10798587392141843742258103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14398116522855791656344137 10798587392141843742258103)
    ·
      refine ⟨16197881088212765613387155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10798587392141843742258103 16197881088212765613387155)
      ·
        refine ⟨24296821632319148420080733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16197881088212765613387155 24296821632319148420080733)
        ·
          refine ⟨9111308112119680657530275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24296821632319148420080733 9111308112119680657530275)
          ·
            refine ⟨13666962168179520986295413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9111308112119680657530275 13666962168179520986295413)
            ·
              refine ⟨1281277703266830092465195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13666962168179520986295413 1281277703266830092465195)
              ·
                refine ⟨1921916554900245138697793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1281277703266830092465195 1921916554900245138697793)
                ·
                  refine ⟨1441437416175183854023345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1921916554900245138697793 1441437416175183854023345)
                  ·
                    refine ⟨1081078062131387890517509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1441437416175183854023345 1081078062131387890517509)
                    ·
                      refine ⟨202702136649635229472033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1081078062131387890517509 202702136649635229472033)
                      ·
                        rfl

theorem cell23_394761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 1, 2, 2, 4].length) (baseStart_394761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_394761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_394761 prefixEnd_394761 := by exact prefixLift 394761
  have htrace : WordTrace (prefixWord ++ tailWord_394761) baseStart_394761 baseEnd_394761 := by
    simpa [prefixWord, tailWord_394761, baseEnd_394761] using wordTrace_append hprefix tailTrace_394761
  have hstable : (prefixWord ++ tailWord_394761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394761).length < 2 ^ (prefixWord ++ tailWord_394761).sum := by decide
  have hdescent : baseEnd_394761 < baseStart_394761 := by decide
  rcases family_descends (prefixWord ++ tailWord_394761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394771 : List Nat := [1, 1, 1, 2, 1, 7, 1, 2, 7]
def baseStart_394771 : Nat := 118140960795 + 394771 * 2 ^ 59
def prefixEnd_394771 : Nat := 4983230072969 + 3 ^ 40 * 394771 * 2
def baseEnd_394771 : Nat := 22523030161797798927443

theorem tailTrace_394771 : CollatzResearch.WordTrace tailWord_394771 prefixEnd_394771 22523030161797798927443 := by
  unfold tailWord_394771
  simp only [CollatzResearch.WordTrace]
  refine ⟨14398481252819563364208167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9598987501879708909472111 14398481252819563364208167)
  ·
    refine ⟨21597721879229345046312251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14398481252819563364208167 21597721879229345046312251)
    ·
      refine ⟨32396582818844017569468377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21597721879229345046312251 32396582818844017569468377)
      ·
        refine ⟨24297437114133013177101283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32396582818844017569468377 24297437114133013177101283)
        ·
          refine ⟨36446155671199519765651925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24297437114133013177101283 36446155671199519765651925)
          ·
            refine ⟨854206773543738744507467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 36446155671199519765651925 854206773543738744507467)
            ·
              refine ⟨1281310160315608116761201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 854206773543738744507467 1281310160315608116761201)
              ·
                refine ⟨960982620236706087570901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1281310160315608116761201 960982620236706087570901)
                ·
                  refine ⟨22523030161797798927443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 960982620236706087570901 22523030161797798927443)
                  ·
                    rfl

theorem cell23_394771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 2, 7].length) (baseStart_394771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_394771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_394771 prefixEnd_394771 := by exact prefixLift 394771
  have htrace : WordTrace (prefixWord ++ tailWord_394771) baseStart_394771 baseEnd_394771 := by
    simpa [prefixWord, tailWord_394771, baseEnd_394771] using wordTrace_append hprefix tailTrace_394771
  have hstable : (prefixWord ++ tailWord_394771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394771).length < 2 ^ (prefixWord ++ tailWord_394771).sum := by decide
  have hdescent : baseEnd_394771 < baseStart_394771 := by decide
  rcases family_descends (prefixWord ++ tailWord_394771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394801 : List Nat := [1, 2, 2, 3, 1, 1, 1, 3, 4, 5]
def baseStart_394801 : Nat := 118140960795 + 394801 * 2 ^ 59
def prefixEnd_394801 : Nat := 4983230072969 + 3 ^ 40 * 394801 * 2
def baseEnd_394801 : Nat := 67574225291938357657283

theorem tailTrace_394801 : CollatzResearch.WordTrace tailWord_394801 prefixEnd_394801 67574225291938357657283 := by
  unfold tailWord_394801
  simp only [CollatzResearch.WordTrace]
  refine ⟨14399575442710878487800257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9599716961807252325200171 14399575442710878487800257)
  ·
    refine ⟨10799681582033158865850193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14399575442710878487800257 10799681582033158865850193)
    ·
      refine ⟨8099761186524869149387645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10799681582033158865850193 8099761186524869149387645)
      ·
        refine ⟨3037410444946825931020367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8099761186524869149387645 3037410444946825931020367)
        ·
          refine ⟨4556115667420238896530551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3037410444946825931020367 4556115667420238896530551)
          ·
            refine ⟨6834173501130358344795827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4556115667420238896530551 6834173501130358344795827)
            ·
              refine ⟨10251260251695537517193741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6834173501130358344795827 10251260251695537517193741)
              ·
                refine ⟨3844222594385826568947653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10251260251695537517193741 3844222594385826568947653)
                ·
                  refine ⟨720791736447342481677685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3844222594385826568947653 720791736447342481677685)
                  ·
                    refine ⟨67574225291938357657283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 720791736447342481677685 67574225291938357657283)
                    ·
                      rfl

theorem cell23_394801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 4, 5].length) (baseStart_394801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_394801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_394801 prefixEnd_394801 := by exact prefixLift 394801
  have htrace : WordTrace (prefixWord ++ tailWord_394801) baseStart_394801 baseEnd_394801 := by
    simpa [prefixWord, tailWord_394801, baseEnd_394801] using wordTrace_append hprefix tailTrace_394801
  have hstable : (prefixWord ++ tailWord_394801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394801).length < 2 ^ (prefixWord ++ tailWord_394801).sum := by decide
  have hdescent : baseEnd_394801 < baseStart_394801 := by decide
  rcases family_descends (prefixWord ++ tailWord_394801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394821 : List Nat := [1, 3, 1, 1, 1, 4, 1, 1, 3, 3, 4]
def baseStart_394821 : Nat := 118140960795 + 394821 * 2 ^ 59
def prefixEnd_394821 : Nat := 4983230072969 + 3 ^ 40 * 394821 * 2
def baseEnd_394821 : Nat := 202732945488904994721757

theorem tailTrace_394821 : CollatzResearch.WordTrace tailWord_394821 prefixEnd_394821 202732945488904994721757 := by
  unfold tailWord_394821
  simp only [CollatzResearch.WordTrace]
  refine ⟨14400304902638421903528317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9600203268425614602352211 14400304902638421903528317)
  ·
    refine ⟨5400114338489408213823119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14400304902638421903528317 5400114338489408213823119)
    ·
      refine ⟨8100171507734112320734679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5400114338489408213823119 8100171507734112320734679)
      ·
        refine ⟨12150257261601168481102019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8100171507734112320734679 12150257261601168481102019)
        ·
          refine ⟨18225385892401752721653029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12150257261601168481102019 18225385892401752721653029)
          ·
            refine ⟨3417259854825328635309943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18225385892401752721653029 3417259854825328635309943)
            ·
              refine ⟨5125889782237992952964915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3417259854825328635309943 5125889782237992952964915)
              ·
                refine ⟨7688834673356989429447373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5125889782237992952964915 7688834673356989429447373)
                ·
                  refine ⟨2883313002508871036042765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7688834673356989429447373 2883313002508871036042765)
                  ·
                    refine ⟨1081242375940826638516037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2883313002508871036042765 1081242375940826638516037)
                    ·
                      refine ⟨202732945488904994721757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1081242375940826638516037 202732945488904994721757)
                      ·
                        rfl

theorem cell23_394821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 3, 3, 4].length) (baseStart_394821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_394821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_394821 prefixEnd_394821 := by exact prefixLift 394821
  have htrace : WordTrace (prefixWord ++ tailWord_394821) baseStart_394821 baseEnd_394821 := by
    simpa [prefixWord, tailWord_394821, baseEnd_394821] using wordTrace_append hprefix tailTrace_394821
  have hstable : (prefixWord ++ tailWord_394821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394821).length < 2 ^ (prefixWord ++ tailWord_394821).sum := by decide
  have hdescent : baseEnd_394821 < baseStart_394821 := by decide
  rcases family_descends (prefixWord ++ tailWord_394821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394865 : List Nat := [1, 2, 2, 2, 1, 1, 1, 8, 1, 4]
def baseStart_394865 : Nat := 118140960795 + 394865 * 2 ^ 59
def prefixEnd_394865 : Nat := 4983230072969 + 3 ^ 40 * 394865 * 2
def baseEnd_394865 : Nat := 67585179545900940857185

theorem tailTrace_394865 : CollatzResearch.WordTrace tailWord_394865 prefixEnd_394865 67585179545900940857185 := by
  unfold tailWord_394865
  simp only [CollatzResearch.WordTrace]
  refine ⟨14401909714479017418130049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9601273142986011612086699 14401909714479017418130049)
  ·
    refine ⟨10801432285859263063597537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14401909714479017418130049 10801432285859263063597537)
    ·
      refine ⟨8101074214394447297698153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10801432285859263063597537 8101074214394447297698153)
      ·
        refine ⟨6075805660795835473273615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8101074214394447297698153 6075805660795835473273615)
        ·
          refine ⟨9113708491193753209910423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6075805660795835473273615 9113708491193753209910423)
          ·
            refine ⟨13670562736790629814865635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9113708491193753209910423 13670562736790629814865635)
            ·
              refine ⟨20505844105185944722298453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13670562736790629814865635 20505844105185944722298453)
              ·
                refine ⟨240302860607647789714435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 20505844105185944722298453 240302860607647789714435)
                ·
                  refine ⟨360454290911471684571653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 240302860607647789714435 360454290911471684571653)
                  ·
                    refine ⟨67585179545900940857185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 360454290911471684571653 67585179545900940857185)
                    ·
                      rfl

theorem cell23_394865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 8, 1, 4].length) (baseStart_394865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_394865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_394865 prefixEnd_394865 := by exact prefixLift 394865
  have htrace : WordTrace (prefixWord ++ tailWord_394865) baseStart_394865 baseEnd_394865 := by
    simpa [prefixWord, tailWord_394865, baseEnd_394865] using wordTrace_append hprefix tailTrace_394865
  have hstable : (prefixWord ++ tailWord_394865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394865).length < 2 ^ (prefixWord ++ tailWord_394865).sum := by decide
  have hdescent : baseEnd_394865 < baseStart_394865 := by decide
  rcases family_descends (prefixWord ++ tailWord_394865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394901 : List Nat := [1, 3, 2, 1, 1, 1, 1, 2, 1, 3, 7]
def baseStart_394901 : Nat := 118140960795 + 394901 * 2 ^ 59
def prefixEnd_394901 : Nat := 4983230072969 + 3 ^ 40 * 394901 * 2
def baseEnd_394901 : Nat := 202774023941264681721389

theorem tailTrace_394901 : CollatzResearch.WordTrace tailWord_394901 prefixEnd_394901 202774023941264681721389 := by
  unfold tailWord_394901
  simp only [CollatzResearch.WordTrace]
  refine ⟨14403222742348595566440557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9602148494899063710960371 14403222742348595566440557)
  ·
    refine ⟨5401208528380723337415209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14403222742348595566440557 5401208528380723337415209)
    ·
      refine ⟨4050906396285542503061407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5401208528380723337415209 4050906396285542503061407)
      ·
        refine ⟨6076359594428313754592111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4050906396285542503061407 6076359594428313754592111)
        ·
          refine ⟨9114539391642470631888167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6076359594428313754592111 9114539391642470631888167)
          ·
            refine ⟨13671809087463705947832251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9114539391642470631888167 13671809087463705947832251)
            ·
              refine ⟨20507713631195558921748377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13671809087463705947832251 20507713631195558921748377)
              ·
                refine ⟨15380785223396669191311283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20507713631195558921748377 15380785223396669191311283)
                ·
                  refine ⟨23071177835095003786966925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15380785223396669191311283 23071177835095003786966925)
                  ·
                    refine ⟨8651691688160626420112597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23071177835095003786966925 8651691688160626420112597)
                    ·
                      refine ⟨202774023941264681721389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 8651691688160626420112597 202774023941264681721389)
                      ·
                        rfl

theorem cell23_394901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 3, 7].length) (baseStart_394901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_394901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_394901 prefixEnd_394901 := by exact prefixLift 394901
  have htrace : WordTrace (prefixWord ++ tailWord_394901) baseStart_394901 baseEnd_394901 := by
    simpa [prefixWord, tailWord_394901, baseEnd_394901] using wordTrace_append hprefix tailTrace_394901
  have hstable : (prefixWord ++ tailWord_394901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394901).length < 2 ^ (prefixWord ++ tailWord_394901).sum := by decide
  have hdescent : baseEnd_394901 < baseStart_394901 := by decide
  rcases family_descends (prefixWord ++ tailWord_394901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394915 : List Nat := [1, 1, 1, 4, 1, 1, 3, 4, 2, 3, 2]
def baseStart_394915 : Nat := 118140960795 + 394915 * 2 ^ 59
def prefixEnd_394915 : Nat := 4983230072969 + 3 ^ 40 * 394915 * 2
def baseEnd_394915 : Nat := 202781212670427626946325

theorem tailTrace_394915 : CollatzResearch.WordTrace tailWord_394915 prefixEnd_394915 202781212670427626946325 := by
  unfold tailWord_394915
  simp only [CollatzResearch.WordTrace]
  refine ⟨14403733364297875957450199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9602488909531917304966799 14403733364297875957450199)
  ·
    refine ⟨21605600046446813936175299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14403733364297875957450199 21605600046446813936175299)
    ·
      refine ⟨32408400069670220904262949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21605600046446813936175299 32408400069670220904262949)
      ·
        refine ⟨6076575013063166419549303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32408400069670220904262949 6076575013063166419549303)
        ·
          refine ⟨9114862519594749629323955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6076575013063166419549303 9114862519594749629323955)
          ·
            refine ⟨13672293779392124443985933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9114862519594749629323955 13672293779392124443985933)
            ·
              refine ⟨5127110167272046666494725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13672293779392124443985933 5127110167272046666494725)
              ·
                refine ⟨961333156363508749967761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5127110167272046666494725 961333156363508749967761)
                ·
                  refine ⟨720999867272631562475821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 961333156363508749967761 720999867272631562475821)
                  ·
                    refine ⟨270374950227236835928433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 720999867272631562475821 270374950227236835928433)
                    ·
                      refine ⟨202781212670427626946325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 270374950227236835928433 202781212670427626946325)
                      ·
                        rfl

theorem cell23_394915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 4, 2, 3, 2].length) (baseStart_394915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_394915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_394915 prefixEnd_394915 := by exact prefixLift 394915
  have htrace : WordTrace (prefixWord ++ tailWord_394915) baseStart_394915 baseEnd_394915 := by
    simpa [prefixWord, tailWord_394915, baseEnd_394915] using wordTrace_append hprefix tailTrace_394915
  have hstable : (prefixWord ++ tailWord_394915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394915).length < 2 ^ (prefixWord ++ tailWord_394915).sum := by decide
  have hdescent : baseEnd_394915 < baseStart_394915 := by decide
  rcases family_descends (prefixWord ++ tailWord_394915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394928 : List Nat := [2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 4]
def baseStart_394928 : Nat := 118140960795 + 394928 * 2 ^ 59
def prefixEnd_394928 : Nat := 4983230072969 + 3 ^ 40 * 394928 * 2
def baseEnd_394928 : Nat := 202787887918936076083765

theorem tailTrace_394928 : CollatzResearch.WordTrace tailWord_394928 prefixEnd_394928 202787887918936076083765 := by
  unfold tailWord_394928
  simp only [CollatzResearch.WordTrace]
  refine ⟨7202103756625389588836719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9602805008833852785115625 7202103756625389588836719)
  ·
    refine ⟨10803155634938084383255079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7202103756625389588836719 10803155634938084383255079)
    ·
      refine ⟨16204733452407126574882619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10803155634938084383255079 16204733452407126574882619)
      ·
        refine ⟨24307100178610689862323929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16204733452407126574882619 24307100178610689862323929)
        ·
          refine ⟨18230325133958017396742947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24307100178610689862323929 18230325133958017396742947)
          ·
            refine ⟨27345487700937026095114421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18230325133958017396742947 27345487700937026095114421)
            ·
              refine ⟨2563639471962846196416977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27345487700937026095114421 2563639471962846196416977)
              ·
                refine ⟨1922729603972134647312733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2563639471962846196416977 1922729603972134647312733)
                ·
                  refine ⟨721023601489550492742275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1922729603972134647312733 721023601489550492742275)
                  ·
                    refine ⟨1081535402234325739113413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 721023601489550492742275 1081535402234325739113413)
                    ·
                      refine ⟨202787887918936076083765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1081535402234325739113413 202787887918936076083765)
                      ·
                        rfl

theorem cell23_394928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 4].length) (baseStart_394928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_394928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_394928 prefixEnd_394928 := by exact prefixLift 394928
  have htrace : WordTrace (prefixWord ++ tailWord_394928) baseStart_394928 baseEnd_394928 := by
    simpa [prefixWord, tailWord_394928, baseEnd_394928] using wordTrace_append hprefix tailTrace_394928
  have hstable : (prefixWord ++ tailWord_394928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394928).length < 2 ^ (prefixWord ++ tailWord_394928).sum := by decide
  have hdescent : baseEnd_394928 < baseStart_394928 := by decide
  rcases family_descends (prefixWord ++ tailWord_394928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394938 : List Nat := [3, 1, 1, 1, 2, 4, 1, 3, 1, 6]
def baseStart_394938 : Nat := 118140960795 + 394938 * 2 ^ 59
def prefixEnd_394938 : Nat := 4983230072969 + 3 ^ 40 * 394938 * 2
def baseEnd_394938 : Nat := 67597674241827012319573

theorem tailTrace_394938 : CollatzResearch.WordTrace tailWord_394938 prefixEnd_394938 67597674241827012319573 := by
  unfold tailWord_394938
  simp only [CollatzResearch.WordTrace]
  refine ⟨3601143060803637721384367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9603048162143033923691645 3601143060803637721384367)
  ·
    refine ⟨5401714591205456582076551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3601143060803637721384367 5401714591205456582076551)
    ·
      refine ⟨8102571886808184873114827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5401714591205456582076551 8102571886808184873114827)
      ·
        refine ⟨12153857830212277309672241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8102571886808184873114827 12153857830212277309672241)
        ·
          refine ⟨9115393372659207982254181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12153857830212277309672241 9115393372659207982254181)
          ·
            refine ⟨1709136257373601496672659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9115393372659207982254181 1709136257373601496672659)
            ·
              refine ⟨2563704386060402245008989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1709136257373601496672659 2563704386060402245008989)
              ·
                refine ⟨961389144772650841878371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2563704386060402245008989 961389144772650841878371)
                ·
                  refine ⟨1442083717158976262817557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 961389144772650841878371 1442083717158976262817557)
                  ·
                    refine ⟨67597674241827012319573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1442083717158976262817557 67597674241827012319573)
                    ·
                      rfl

theorem cell23_394938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 3, 1, 6].length) (baseStart_394938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_394938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_394938 prefixEnd_394938 := by exact prefixLift 394938
  have htrace : WordTrace (prefixWord ++ tailWord_394938) baseStart_394938 baseEnd_394938 := by
    simpa [prefixWord, tailWord_394938, baseEnd_394938] using wordTrace_append hprefix tailTrace_394938
  have hstable : (prefixWord ++ tailWord_394938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394938).length < 2 ^ (prefixWord ++ tailWord_394938).sum := by decide
  have hdescent : baseEnd_394938 < baseStart_394938 := by decide
  rcases family_descends (prefixWord ++ tailWord_394938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394956 : List Nat := [2, 2, 1, 5, 2, 1, 2, 3, 1, 1, 3]
def baseStart_394956 : Nat := 118140960795 + 394956 * 2 ^ 59
def prefixEnd_394956 : Nat := 4983230072969 + 3 ^ 40 * 394956 * 2
def baseEnd_394956 : Nat := 202802265377261966533637

theorem tailTrace_394956 : CollatzResearch.WordTrace tailWord_394956 prefixEnd_394956 202802265377261966533637 := by
  unfold tailWord_394956
  simp only [CollatzResearch.WordTrace]
  refine ⟨7202614378574669979846361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9603485838099559973128481 7202614378574669979846361)
  ·
    refine ⟨5401960783931002484884771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7202614378574669979846361 5401960783931002484884771)
    ·
      refine ⟨8102941175896503727327157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5401960783931002484884771 8102941175896503727327157)
      ·
        refine ⟨759650735240297224436921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8102941175896503727327157 759650735240297224436921)
        ·
          refine ⟨569738051430222918327691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 759650735240297224436921 569738051430222918327691)
          ·
            refine ⟨854607077145334377491537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 569738051430222918327691 854607077145334377491537)
            ·
              refine ⟨640955307859000783118653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 854607077145334377491537 640955307859000783118653)
              ·
                refine ⟨240358240447125293669495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 640955307859000783118653 240358240447125293669495)
                ·
                  refine ⟨360537360670687940504243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 240358240447125293669495 360537360670687940504243)
                  ·
                    refine ⟨540806041006031910756365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 360537360670687940504243 540806041006031910756365)
                    ·
                      refine ⟨202802265377261966533637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 540806041006031910756365 202802265377261966533637)
                      ·
                        rfl

theorem cell23_394956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_394956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_394956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_394956 prefixEnd_394956 := by exact prefixLift 394956
  have htrace : WordTrace (prefixWord ++ tailWord_394956) baseStart_394956 baseEnd_394956 := by
    simpa [prefixWord, tailWord_394956, baseEnd_394956] using wordTrace_append hprefix tailTrace_394956
  have hstable : (prefixWord ++ tailWord_394956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394956).length < 2 ^ (prefixWord ++ tailWord_394956).sum := by decide
  have hdescent : baseEnd_394956 < baseStart_394956 := by decide
  rcases family_descends (prefixWord ++ tailWord_394956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394962 : List Nat := [3, 2, 2, 2, 2, 2, 1, 3, 1, 1, 4]
def baseStart_394962 : Nat := 118140960795 + 394962 * 2 ^ 59
def prefixEnd_394962 : Nat := 4983230072969 + 3 ^ 40 * 394962 * 2
def baseEnd_394962 : Nat := 202805346261188943058609

theorem tailTrace_394962 : CollatzResearch.WordTrace tailWord_394962 prefixEnd_394962 202805346261188943058609 := by
  unfold tailWord_394962
  simp only [CollatzResearch.WordTrace]
  refine ⟨3601361898781900746102785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9603631730085068656274093 3601361898781900746102785)
  ·
    refine ⟨2701021424086425559577089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3601361898781900746102785 2701021424086425559577089)
    ·
      refine ⟨2025766068064819169682817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2701021424086425559577089 2025766068064819169682817)
      ·
        refine ⟨1519324551048614377262113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2025766068064819169682817 1519324551048614377262113)
        ·
          refine ⟨1139493413286460782946585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1519324551048614377262113 1139493413286460782946585)
          ·
            refine ⟨854620059964845587209939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1139493413286460782946585 854620059964845587209939)
            ·
              refine ⟨1281930089947268380814909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 854620059964845587209939 1281930089947268380814909)
              ·
                refine ⟨480723783730225642805591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1281930089947268380814909 480723783730225642805591)
                ·
                  refine ⟨721085675595338464208387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 480723783730225642805591 721085675595338464208387)
                  ·
                    refine ⟨1081628513393007696312581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 721085675595338464208387 1081628513393007696312581)
                    ·
                      refine ⟨202805346261188943058609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1081628513393007696312581 202805346261188943058609)
                      ·
                        rfl

theorem cell23_394962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_394962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_394962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_394962 prefixEnd_394962 := by exact prefixLift 394962
  have htrace : WordTrace (prefixWord ++ tailWord_394962) baseStart_394962 baseEnd_394962 := by
    simpa [prefixWord, tailWord_394962, baseEnd_394962] using wordTrace_append hprefix tailTrace_394962
  have hstable : (prefixWord ++ tailWord_394962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394962).length < 2 ^ (prefixWord ++ tailWord_394962).sum := by decide
  have hdescent : baseEnd_394962 < baseStart_394962 := by decide
  rcases family_descends (prefixWord ++ tailWord_394962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394989 : List Nat := [1, 5, 1, 2, 1, 3, 3, 1, 2, 4]
def baseStart_394989 : Nat := 118140960795 + 394989 * 2 ^ 59
def prefixEnd_394989 : Nat := 4983230072969 + 3 ^ 40 * 394989 * 2
def baseEnd_394989 : Nat := 67606403412953445806995

theorem tailTrace_394989 : CollatzResearch.WordTrace tailWord_394989 prefixEnd_394989 67606403412953445806995 := by
  unfold tailWord_394989
  simp only [CollatzResearch.WordTrace]
  refine ⟨14406432366029786595644021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9604288244019857730429347 14406432366029786595644021)
  ·
    refine ⟨1350603034315292493341627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14406432366029786595644021 1350603034315292493341627)
    ·
      refine ⟨2025904551472938740012441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1350603034315292493341627 2025904551472938740012441)
      ·
        refine ⟨1519428413604704055009331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2025904551472938740012441 1519428413604704055009331)
        ·
          refine ⟨2279142620407056082513997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1519428413604704055009331 2279142620407056082513997)
          ·
            refine ⟨854678482652646030942749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2279142620407056082513997 854678482652646030942749)
            ·
              refine ⟨320504430994742261603531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 854678482652646030942749 320504430994742261603531)
              ·
                refine ⟨480756646492113392405297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 320504430994742261603531 480756646492113392405297)
                ·
                  refine ⟨360567484869085044303973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 480756646492113392405297 360567484869085044303973)
                  ·
                    refine ⟨67606403412953445806995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 360567484869085044303973 67606403412953445806995)
                    ·
                      rfl

theorem cell23_394989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 3, 1, 2, 4].length) (baseStart_394989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_394989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_394989 prefixEnd_394989 := by exact prefixLift 394989
  have htrace : WordTrace (prefixWord ++ tailWord_394989) baseStart_394989 baseEnd_394989 := by
    simpa [prefixWord, tailWord_394989, baseEnd_394989] using wordTrace_append hprefix tailTrace_394989
  have hstable : (prefixWord ++ tailWord_394989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394989).length < 2 ^ (prefixWord ++ tailWord_394989).sum := by decide
  have hdescent : baseEnd_394989 < baseStart_394989 := by decide
  rcases family_descends (prefixWord ++ tailWord_394989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394995 : List Nat := [1, 1, 1, 2, 2, 3, 5, 1, 1, 3, 3]
def baseStart_394995 : Nat := 118140960795 + 394995 * 2 ^ 59
def prefixEnd_394995 : Nat := 4983230072969 + 3 ^ 40 * 394995 * 2
def baseEnd_394995 : Nat := 202822291122787313945957

theorem tailTrace_394995 : CollatzResearch.WordTrace tailWord_394995 prefixEnd_394995 202822291122787313945957 := by
  unfold tailWord_394995
  simp only [CollatzResearch.WordTrace]
  refine ⟨14406651204008049620362439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9604434136005366413574959 14406651204008049620362439)
  ·
    refine ⟨21609976806012074430543659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14406651204008049620362439 21609976806012074430543659)
    ·
      refine ⟨32414965209018111645815489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21609976806012074430543659 32414965209018111645815489)
      ·
        refine ⟨24311223906763583734361617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32414965209018111645815489 24311223906763583734361617)
        ·
          refine ⟨18233417930072687800771213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24311223906763583734361617 18233417930072687800771213)
          ·
            refine ⟨6837531723777257925289205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18233417930072687800771213 6837531723777257925289205)
            ·
              refine ⟨641018599104117930495863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6837531723777257925289205 641018599104117930495863)
              ·
                refine ⟨961527898656176895743795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 641018599104117930495863 961527898656176895743795)
                ·
                  refine ⟨1442291847984265343615693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 961527898656176895743795 1442291847984265343615693)
                  ·
                    refine ⟨540859442994099503855885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1442291847984265343615693 540859442994099503855885)
                    ·
                      refine ⟨202822291122787313945957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 540859442994099503855885 202822291122787313945957)
                      ·
                        rfl

theorem cell23_394995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 1, 1, 3, 3].length) (baseStart_394995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_394995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_394995 prefixEnd_394995 := by exact prefixLift 394995
  have htrace : WordTrace (prefixWord ++ tailWord_394995) baseStart_394995 baseEnd_394995 := by
    simpa [prefixWord, tailWord_394995, baseEnd_394995] using wordTrace_append hprefix tailTrace_394995
  have hstable : (prefixWord ++ tailWord_394995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394995).length < 2 ^ (prefixWord ++ tailWord_394995).sum := by decide
  have hdescent : baseEnd_394995 < baseStart_394995 := by decide
  rcases family_descends (prefixWord ++ tailWord_394995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394996 : List Nat := [2, 6, 1, 1, 1, 2, 2, 2, 1, 1, 4]
def baseStart_394996 : Nat := 118140960795 + 394996 * 2 ^ 59
def prefixEnd_394996 : Nat := 4983230072969 + 3 ^ 40 * 394996 * 2
def baseEnd_394996 : Nat := 202822804603441810033453

theorem tailTrace_394996 : CollatzResearch.WordTrace tailWord_394996 prefixEnd_394996 202822804603441810033453 := by
  unfold tailWord_394996
  simp only [CollatzResearch.WordTrace]
  refine ⟨7203343838502213395574421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9604458451336284527432561 7203343838502213395574421)
  ·
    refine ⟨337656742429791252917551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 7203343838502213395574421 337656742429791252917551)
    ·
      refine ⟨506485113644686879376327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337656742429791252917551 506485113644686879376327)
      ·
        refine ⟨759727670467030319064491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 506485113644686879376327 759727670467030319064491)
        ·
          refine ⟨1139591505700545478596737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 759727670467030319064491 1139591505700545478596737)
          ·
            refine ⟨854693629275409108947553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1139591505700545478596737 854693629275409108947553)
            ·
              refine ⟨641020221956556831710665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 854693629275409108947553 641020221956556831710665)
              ·
                refine ⟨480765166467417623782999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 641020221956556831710665 480765166467417623782999)
                ·
                  refine ⟨721147749701126435674499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 480765166467417623782999 721147749701126435674499)
                  ·
                    refine ⟨1081721624551689653511749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 721147749701126435674499 1081721624551689653511749)
                    ·
                      refine ⟨202822804603441810033453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1081721624551689653511749 202822804603441810033453)
                      ·
                        rfl

theorem cell23_394996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_394996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_394996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_394996 prefixEnd_394996 := by exact prefixLift 394996
  have htrace : WordTrace (prefixWord ++ tailWord_394996) baseStart_394996 baseEnd_394996 := by
    simpa [prefixWord, tailWord_394996, baseEnd_394996] using wordTrace_append hprefix tailTrace_394996
  have hstable : (prefixWord ++ tailWord_394996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394996).length < 2 ^ (prefixWord ++ tailWord_394996).sum := by decide
  have hdescent : baseEnd_394996 < baseStart_394996 := by decide
  rcases family_descends (prefixWord ++ tailWord_394996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395012 : List Nat := [2, 3, 2, 2, 1, 2, 1, 2, 4, 1, 3]
def baseStart_395012 : Nat := 118140960795 + 395012 * 2 ^ 59
def prefixEnd_395012 : Nat := 4983230072969 + 3 ^ 40 * 395012 * 2
def baseEnd_395012 : Nat := 202831020293913747433379

theorem tailTrace_395012 : CollatzResearch.WordTrace tailWord_395012 prefixEnd_395012 202831020293913747433379 := by
  unfold tailWord_395012
  simp only [CollatzResearch.WordTrace]
  refine ⟨7203635622473230761865645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9604847496630974349154193 7203635622473230761865645)
  ·
    refine ⟨2701363358427461535699617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7203635622473230761865645 2701363358427461535699617)
    ·
      refine ⟨2026022518820596151774713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2701363358427461535699617 2026022518820596151774713)
      ·
        refine ⟨1519516889115447113831035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2026022518820596151774713 1519516889115447113831035)
        ·
          refine ⟨2279275333673170670746553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1519516889115447113831035 2279275333673170670746553)
          ·
            refine ⟨1709456500254878003059915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2279275333673170670746553 1709456500254878003059915)
            ·
              refine ⟨2564184750382317004589873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1709456500254878003059915 2564184750382317004589873)
              ·
                refine ⟨1923138562786737753442405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2564184750382317004589873 1923138562786737753442405)
                ·
                  refine ⟨360588480522513328770451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1923138562786737753442405 360588480522513328770451)
                  ·
                    refine ⟨540882720783769993155677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 360588480522513328770451 540882720783769993155677)
                    ·
                      refine ⟨202831020293913747433379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 540882720783769993155677 202831020293913747433379)
                      ·
                        rfl

theorem cell23_395012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_395012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_395012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_395012 prefixEnd_395012 := by exact prefixLift 395012
  have htrace : WordTrace (prefixWord ++ tailWord_395012) baseStart_395012 baseEnd_395012 := by
    simpa [prefixWord, tailWord_395012, baseEnd_395012] using wordTrace_append hprefix tailTrace_395012
  have hstable : (prefixWord ++ tailWord_395012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395012).length < 2 ^ (prefixWord ++ tailWord_395012).sum := by decide
  have hdescent : baseEnd_395012 < baseStart_395012 := by decide
  rcases family_descends (prefixWord ++ tailWord_395012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395035 : List Nat := [1, 1, 1, 1, 1, 1, 4, 4, 3, 4, 2]
def baseStart_395035 : Nat := 118140960795 + 395035 * 2 ^ 59
def prefixEnd_395035 : Nat := 4983230072969 + 3 ^ 40 * 395035 * 2
def baseEnd_395035 : Nat := 202842830348967157445773

theorem tailTrace_395035 : CollatzResearch.WordTrace tailWord_395035 prefixEnd_395035 202842830348967157445773 := by
  unfold tailWord_395035
  simp only [CollatzResearch.WordTrace]
  refine ⟨14408110123863136451818559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9605406749242090967879039 14408110123863136451818559)
  ·
    refine ⟨21612165185794704677727839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14408110123863136451818559 21612165185794704677727839)
    ·
      refine ⟨32418247778692057016591759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21612165185794704677727839 32418247778692057016591759)
      ·
        refine ⟨48627371668038085524887639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32418247778692057016591759 48627371668038085524887639)
        ·
          refine ⟨72941057502057128287331459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48627371668038085524887639 72941057502057128287331459)
          ·
            refine ⟨109411586253085692430997189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72941057502057128287331459 109411586253085692430997189)
            ·
              refine ⟨20514672422453567330811973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 109411586253085692430997189 20514672422453567330811973)
              ·
                refine ⟨3846501079210043874527245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20514672422453567330811973 3846501079210043874527245)
                ·
                  refine ⟨1442437904703766452947717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3846501079210043874527245 1442437904703766452947717)
                  ·
                    refine ⟨270457107131956209927697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1442437904703766452947717 270457107131956209927697)
                    ·
                      refine ⟨202842830348967157445773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 270457107131956209927697 202842830348967157445773)
                      ·
                        rfl

theorem cell23_395035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 3, 4, 2].length) (baseStart_395035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_395035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_395035 prefixEnd_395035 := by exact prefixLift 395035
  have htrace : WordTrace (prefixWord ++ tailWord_395035) baseStart_395035 baseEnd_395035 := by
    simpa [prefixWord, tailWord_395035, baseEnd_395035] using wordTrace_append hprefix tailTrace_395035
  have hstable : (prefixWord ++ tailWord_395035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395035).length < 2 ^ (prefixWord ++ tailWord_395035).sum := by decide
  have hdescent : baseEnd_395035 < baseStart_395035 := by decide
  rcases family_descends (prefixWord ++ tailWord_395035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395069 : List Nat := [1, 4, 1, 4, 1, 2, 1, 2, 1, 4, 2]
def baseStart_395069 : Nat := 118140960795 + 395069 * 2 ^ 59
def prefixEnd_395069 : Nat := 4983230072969 + 3 ^ 40 * 395069 * 2
def baseEnd_395069 : Nat := 202860288691220024420617

theorem tailTrace_395069 : CollatzResearch.WordTrace tailWord_395069 prefixEnd_395069 202860288691220024420617 := by
  unfold tailWord_395069
  simp only [CollatzResearch.WordTrace]
  refine ⟨14409350205739960258556261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9606233470493306839037507 14409350205739960258556261)
  ·
    refine ⟨2701753163576242548479299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14409350205739960258556261 2701753163576242548479299)
    ·
      refine ⟨4052629745364363822718949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2701753163576242548479299 4052629745364363822718949)
      ·
        refine ⟨759868077255818216759803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4052629745364363822718949 759868077255818216759803)
        ·
          refine ⟨1139802115883727325139705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 759868077255818216759803 1139802115883727325139705)
          ·
            refine ⟨854851586912795493854779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1139802115883727325139705 854851586912795493854779)
            ·
              refine ⟨1282277380369193240782169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 854851586912795493854779 1282277380369193240782169)
              ·
                refine ⟨961708035276894930586627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1282277380369193240782169 961708035276894930586627)
                ·
                  refine ⟨1442562052915342395879941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 961708035276894930586627 1442562052915342395879941)
                  ·
                    refine ⟨270480384921626699227489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1442562052915342395879941 270480384921626699227489)
                    ·
                      refine ⟨202860288691220024420617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 270480384921626699227489 202860288691220024420617)
                      ·
                        rfl

theorem cell23_395069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_395069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_395069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_395069 prefixEnd_395069 := by exact prefixLift 395069
  have htrace : WordTrace (prefixWord ++ tailWord_395069) baseStart_395069 baseEnd_395069 := by
    simpa [prefixWord, tailWord_395069, baseEnd_395069] using wordTrace_append hprefix tailTrace_395069
  have hstable : (prefixWord ++ tailWord_395069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395069).length < 2 ^ (prefixWord ++ tailWord_395069).sum := by decide
  have hdescent : baseEnd_395069 < baseStart_395069 := by decide
  rcases family_descends (prefixWord ++ tailWord_395069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395088 : List Nat := [2, 1, 1, 1, 1, 4, 1, 2, 3, 7]
def baseStart_395088 : Nat := 118140960795 + 395088 * 2 ^ 59
def prefixEnd_395088 : Nat := 4983230072969 + 3 ^ 40 * 395088 * 2
def baseEnd_395088 : Nat := 67623348274551816694343

theorem tailTrace_395088 : CollatzResearch.WordTrace tailWord_395088 prefixEnd_395088 67623348274551816694343 := by
  unfold tailWord_395088
  simp only [CollatzResearch.WordTrace]
  refine ⟨7205021596335563251748959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9606695461780751002331945 7205021596335563251748959)
  ·
    refine ⟨10807532394503344877623439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7205021596335563251748959 10807532394503344877623439)
    ·
      refine ⟨16211298591755017316435159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10807532394503344877623439 16211298591755017316435159)
      ·
        refine ⟨24316947887632525974652739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16211298591755017316435159 24316947887632525974652739)
        ·
          refine ⟨36475421831448788961979109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24316947887632525974652739 36475421831448788961979109)
          ·
            refine ⟨6839141593396647930371083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36475421831448788961979109 6839141593396647930371083)
            ·
              refine ⟨10258712390094971895556625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6839141593396647930371083 10258712390094971895556625)
              ·
                refine ⟨7694034292571228921667469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10258712390094971895556625 7694034292571228921667469)
                ·
                  refine ⟨2885262859714210845625301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7694034292571228921667469 2885262859714210845625301)
                  ·
                    refine ⟨67623348274551816694343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2885262859714210845625301 67623348274551816694343)
                    ·
                      rfl

theorem cell23_395088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 3, 7].length) (baseStart_395088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_395088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_395088 prefixEnd_395088 := by exact prefixLift 395088
  have htrace : WordTrace (prefixWord ++ tailWord_395088) baseStart_395088 baseEnd_395088 := by
    simpa [prefixWord, tailWord_395088, baseEnd_395088] using wordTrace_append hprefix tailTrace_395088
  have hstable : (prefixWord ++ tailWord_395088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395088).length < 2 ^ (prefixWord ++ tailWord_395088).sum := by decide
  have hdescent : baseEnd_395088 < baseStart_395088 := by decide
  rcases family_descends (prefixWord ++ tailWord_395088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395112 : List Nat := [2, 1, 4, 2, 1, 1, 1, 2, 2, 5, 2]
def baseStart_395112 : Nat := 118140960795 + 395112 * 2 ^ 59
def prefixEnd_395112 : Nat := 4983230072969 + 3 ^ 40 * 395112 * 2
def baseEnd_395112 : Nat := 202882368359363356182919

theorem tailTrace_395112 : CollatzResearch.WordTrace tailWord_395112 prefixEnd_395112 202882368359363356182919 := by
  unfold tailWord_395112
  simp only [CollatzResearch.WordTrace]
  refine ⟨7205459272292089301185795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9607279029722785734914393 7205459272292089301185795)
  ·
    refine ⟨10808188908438133951778693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7205459272292089301185795 10808188908438133951778693)
    ·
      refine ⟨2026535420332150115958505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10808188908438133951778693 2026535420332150115958505)
      ·
        refine ⟨1519901565249112586968879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2026535420332150115958505 1519901565249112586968879)
        ·
          refine ⟨2279852347873668880453319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1519901565249112586968879 2279852347873668880453319)
          ·
            refine ⟨3419778521810503320679979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2279852347873668880453319 3419778521810503320679979)
            ·
              refine ⟨5129667782715754981019969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3419778521810503320679979 5129667782715754981019969)
              ·
                refine ⟨3847250837036816235764977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5129667782715754981019969 3847250837036816235764977)
                ·
                  refine ⟨2885438127777612176823733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3847250837036816235764977 2885438127777612176823733)
                  ·
                    refine ⟨270509824479151141577225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2885438127777612176823733 270509824479151141577225)
                    ·
                      refine ⟨202882368359363356182919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 270509824479151141577225 202882368359363356182919)
                      ·
                        rfl

theorem cell23_395112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 2, 5, 2].length) (baseStart_395112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_395112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_395112 prefixEnd_395112 := by exact prefixLift 395112
  have htrace : WordTrace (prefixWord ++ tailWord_395112) baseStart_395112 baseEnd_395112 := by
    simpa [prefixWord, tailWord_395112, baseEnd_395112] using wordTrace_append hprefix tailTrace_395112
  have hstable : (prefixWord ++ tailWord_395112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395112).length < 2 ^ (prefixWord ++ tailWord_395112).sum := by decide
  have hdescent : baseEnd_395112 < baseStart_395112 := by decide
  rcases family_descends (prefixWord ++ tailWord_395112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395126 : List Nat := [5, 1, 1, 3, 2, 1, 2, 3, 5]
def baseStart_395126 : Nat := 118140960795 + 395126 * 2 ^ 59
def prefixEnd_395126 : Nat := 4983230072969 + 3 ^ 40 * 395126 * 2
def baseEnd_395126 : Nat := 22543284120947366823095

theorem tailTrace_395126 : CollatzResearch.WordTrace tailWord_395126 prefixEnd_395126 22543284120947366823095 := by
  unfold tailWord_395126
  simp only [CollatzResearch.WordTrace]
  refine ⟨900714322908341187086327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9607619444355639328920821 900714322908341187086327)
  ·
    refine ⟨1351071484362511780629491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 900714322908341187086327 1351071484362511780629491)
    ·
      refine ⟨2026607226543767670944237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1351071484362511780629491 2026607226543767670944237)
      ·
        refine ⟨759977709953912876604089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2026607226543767670944237 759977709953912876604089)
        ·
          refine ⟨569983282465434657453067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 759977709953912876604089 569983282465434657453067)
          ·
            refine ⟨854974923698151986179601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 569983282465434657453067 854974923698151986179601)
            ·
              refine ⟨641231192773613989634701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 854974923698151986179601 641231192773613989634701)
              ·
                refine ⟨240461697290105246113013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 641231192773613989634701 240461697290105246113013)
                ·
                  refine ⟨22543284120947366823095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 240461697290105246113013 22543284120947366823095)
                  ·
                    rfl

theorem cell23_395126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 3, 5].length) (baseStart_395126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_395126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_395126 prefixEnd_395126 := by exact prefixLift 395126
  have htrace : WordTrace (prefixWord ++ tailWord_395126) baseStart_395126 baseEnd_395126 := by
    simpa [prefixWord, tailWord_395126, baseEnd_395126] using wordTrace_append hprefix tailTrace_395126
  have hstable : (prefixWord ++ tailWord_395126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395126).length < 2 ^ (prefixWord ++ tailWord_395126).sum := by decide
  have hdescent : baseEnd_395126 < baseStart_395126 := by decide
  rcases family_descends (prefixWord ++ tailWord_395126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395135 : List Nat := [1, 1, 2, 2, 1, 1, 3, 1, 7, 4]
def baseStart_395135 : Nat := 118140960795 + 395135 * 2 ^ 59
def prefixEnd_395135 : Nat := 4983230072969 + 3 ^ 40 * 395135 * 2
def baseEnd_395135 : Nat := 67631392804805588731771

theorem tailTrace_395135 : CollatzResearch.WordTrace tailWord_395135 prefixEnd_395135 67631392804805588731771 := by
  unfold tailWord_395135
  simp only [CollatzResearch.WordTrace]
  refine ⟨14411757423500853530458859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9607838282333902353639239 14411757423500853530458859)
  ·
    refine ⟨21617636135251280295688289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14411757423500853530458859 21617636135251280295688289)
    ·
      refine ⟨16213227101438460221766217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21617636135251280295688289 16213227101438460221766217)
      ·
        refine ⟨12159920326078845166324663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16213227101438460221766217 12159920326078845166324663)
        ·
          refine ⟨18239880489118267749486995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12159920326078845166324663 18239880489118267749486995)
          ·
            refine ⟨27359820733677401624230493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18239880489118267749486995 27359820733677401624230493)
            ·
              refine ⟨10259932775129025609086435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27359820733677401624230493 10259932775129025609086435)
              ·
                refine ⟨15389899162693538413629653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10259932775129025609086435 15389899162693538413629653)
                ·
                  refine ⟨360700761625629806569445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15389899162693538413629653 360700761625629806569445)
                  ·
                    refine ⟨67631392804805588731771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 360700761625629806569445 67631392804805588731771)
                    ·
                      rfl

theorem cell23_395135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 7, 4].length) (baseStart_395135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_395135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_395135 prefixEnd_395135 := by exact prefixLift 395135
  have htrace : WordTrace (prefixWord ++ tailWord_395135) baseStart_395135 baseEnd_395135 := by
    simpa [prefixWord, tailWord_395135, baseEnd_395135] using wordTrace_append hprefix tailTrace_395135
  have hstable : (prefixWord ++ tailWord_395135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395135).length < 2 ^ (prefixWord ++ tailWord_395135).sum := by decide
  have hdescent : baseEnd_395135 < baseStart_395135 := by decide
  rcases family_descends (prefixWord ++ tailWord_395135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395162 : List Nat := [3, 1, 1, 4, 2, 1, 1, 2, 1, 4, 3]
def baseStart_395162 : Nat := 118140960795 + 395162 * 2 ^ 59
def prefixEnd_395162 : Nat := 4983230072969 + 3 ^ 40 * 395162 * 2
def baseEnd_395162 : Nat := 202908042392088160557689

theorem tailTrace_395162 : CollatzResearch.WordTrace tailWord_395162 prefixEnd_395162 202908042392088160557689 := by
  unfold tailWord_395162
  simp only [CollatzResearch.WordTrace]
  refine ⟨3603185548600759285422935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9608494796268691427794493 3603185548600759285422935)
  ·
    refine ⟨5404778322901138928134403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3603185548600759285422935 5404778322901138928134403)
    ·
      refine ⟨8107167484351708392201605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5404778322901138928134403 8107167484351708392201605)
      ·
        refine ⟨1520093903315945323537801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8107167484351708392201605 1520093903315945323537801)
        ·
          refine ⟨1140070427486958992653351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1520093903315945323537801 1140070427486958992653351)
          ·
            refine ⟨1710105641230438488980027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1140070427486958992653351 1710105641230438488980027)
            ·
              refine ⟨2565158461845657733470041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1710105641230438488980027 2565158461845657733470041)
              ·
                refine ⟨1923868846384243300102531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2565158461845657733470041 1923868846384243300102531)
                ·
                  refine ⟨2885803269576364950153797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1923868846384243300102531 2885803269576364950153797)
                  ·
                    refine ⟨541088113045568428153837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2885803269576364950153797 541088113045568428153837)
                    ·
                      refine ⟨202908042392088160557689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 541088113045568428153837 202908042392088160557689)
                      ·
                        rfl

theorem cell23_395162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_395162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_395162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_395162 prefixEnd_395162 := by exact prefixLift 395162
  have htrace : WordTrace (prefixWord ++ tailWord_395162) baseStart_395162 baseEnd_395162 := by
    simpa [prefixWord, tailWord_395162, baseEnd_395162] using wordTrace_append hprefix tailTrace_395162
  have hstable : (prefixWord ++ tailWord_395162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395162).length < 2 ^ (prefixWord ++ tailWord_395162).sum := by decide
  have hdescent : baseEnd_395162 < baseStart_395162 := by decide
  rcases family_descends (prefixWord ++ tailWord_395162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395196 : List Nat := [2, 2, 2, 5, 1, 1, 1, 2, 2, 2, 3]
def baseStart_395196 : Nat := 118140960795 + 395196 * 2 ^ 59
def prefixEnd_395196 : Nat := 4983230072969 + 3 ^ 40 * 395196 * 2
def baseEnd_395196 : Nat := 202925500734341027532533

theorem tailTrace_395196 : CollatzResearch.WordTrace tailWord_395196 prefixEnd_395196 202925500734341027532533 := by
  unfold tailWord_395196
  simp only [CollatzResearch.WordTrace]
  refine ⟨7206991138139930474214721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9609321517519907298952961 7206991138139930474214721)
  ·
    refine ⟨5405243353604947855661041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7206991138139930474214721 5405243353604947855661041)
    ·
      refine ⟨4053932515203710891745781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5405243353604947855661041 4053932515203710891745781)
      ·
        refine ⟨380056173300347896101167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4053932515203710891745781 380056173300347896101167)
        ·
          refine ⟨570084259950521844151751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 380056173300347896101167 570084259950521844151751)
          ·
            refine ⟨855126389925782766227627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 570084259950521844151751 855126389925782766227627)
            ·
              refine ⟨1282689584888674149341441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 855126389925782766227627 1282689584888674149341441)
              ·
                refine ⟨962017188666505612006081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1282689584888674149341441 962017188666505612006081)
                ·
                  refine ⟨721512891499879209004561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 962017188666505612006081 721512891499879209004561)
                  ·
                    refine ⟨541134668624909406753421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 721512891499879209004561 541134668624909406753421)
                    ·
                      refine ⟨202925500734341027532533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 541134668624909406753421 202925500734341027532533)
                      ·
                        rfl

theorem cell23_395196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_395196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_395196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_395196 prefixEnd_395196 := by exact prefixLift 395196
  have htrace : WordTrace (prefixWord ++ tailWord_395196) baseStart_395196 baseEnd_395196 := by
    simpa [prefixWord, tailWord_395196, baseEnd_395196] using wordTrace_append hprefix tailTrace_395196
  have hstable : (prefixWord ++ tailWord_395196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395196).length < 2 ^ (prefixWord ++ tailWord_395196).sum := by decide
  have hdescent : baseEnd_395196 < baseStart_395196 := by decide
  rcases family_descends (prefixWord ++ tailWord_395196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395229 : List Nat := [1, 4, 3, 1, 3, 1, 1, 1, 3, 5]
def baseStart_395229 : Nat := 118140960795 + 395229 * 2 ^ 59
def prefixEnd_395229 : Nat := 4983230072969 + 3 ^ 40 * 395229 * 2
def baseEnd_395229 : Nat := 67647481865313132806627

theorem tailTrace_395229 : CollatzResearch.WordTrace tailWord_395229 prefixEnd_395229 67647481865313132806627 := by
  unfold tailWord_395229
  simp only [CollatzResearch.WordTrace]
  refine ⟨14415185885160307584380741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9610123923440205056253827 14415185885160307584380741)
  ·
    refine ⟨2702847353467557672071389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14415185885160307584380741 2702847353467557672071389)
    ·
      refine ⟨1013567757550334127026771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2702847353467557672071389 1013567757550334127026771)
      ·
        refine ⟨1520351636325501190540157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1013567757550334127026771 1520351636325501190540157)
        ·
          refine ⟨570131863622062946452559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1520351636325501190540157 570131863622062946452559)
          ·
            refine ⟨855197795433094419678839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 570131863622062946452559 855197795433094419678839)
            ·
              refine ⟨1282796693149641629518259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 855197795433094419678839 1282796693149641629518259)
              ·
                refine ⟨1924195039724462444277389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1282796693149641629518259 1924195039724462444277389)
                ·
                  refine ⟨721573139896673416604021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1924195039724462444277389 721573139896673416604021)
                  ·
                    refine ⟨67647481865313132806627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 721573139896673416604021 67647481865313132806627)
                    ·
                      rfl

theorem cell23_395229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_395229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_395229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_395229 prefixEnd_395229 := by exact prefixLift 395229
  have htrace : WordTrace (prefixWord ++ tailWord_395229) baseStart_395229 baseEnd_395229 := by
    simpa [prefixWord, tailWord_395229, baseEnd_395229] using wordTrace_append hprefix tailTrace_395229
  have hstable : (prefixWord ++ tailWord_395229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395229).length < 2 ^ (prefixWord ++ tailWord_395229).sum := by decide
  have hdescent : baseEnd_395229 < baseStart_395229 := by decide
  rcases family_descends (prefixWord ++ tailWord_395229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395232 : List Nat := [2, 1, 1, 3, 1, 1, 1, 3, 2, 6, 2]
def baseStart_395232 : Nat := 118140960795 + 395232 * 2 ^ 59
def prefixEnd_395232 : Nat := 4983230072969 + 3 ^ 40 * 395232 * 2
def baseEnd_395232 : Nat := 202943986037902886682367

theorem tailTrace_395232 : CollatzResearch.WordTrace tailWord_395232 prefixEnd_395232 202943986037902886682367 := by
  unfold tailWord_395232
  simp only [CollatzResearch.WordTrace]
  refine ⟨7207647652074719548369975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9610196869432959397826633 7207647652074719548369975)
  ·
    refine ⟨10811471478112079322554963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7207647652074719548369975 10811471478112079322554963)
    ·
      refine ⟨16217207217168118983832445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10811471478112079322554963 16217207217168118983832445)
      ·
        refine ⟨6081452706438044618937167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16217207217168118983832445 6081452706438044618937167)
        ·
          refine ⟨9122179059657066928405751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6081452706438044618937167 9122179059657066928405751)
          ·
            refine ⟨13683268589485600392608627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9122179059657066928405751 13683268589485600392608627)
            ·
              refine ⟨20524902884228400588912941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13683268589485600392608627 20524902884228400588912941)
              ·
                refine ⟨7696838581585650220842353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20524902884228400588912941 7696838581585650220842353)
                ·
                  refine ⟨5772628936189237665631765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7696838581585650220842353 5772628936189237665631765)
                  ·
                    refine ⟨270591981383870515576489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5772628936189237665631765 270591981383870515576489)
                    ·
                      refine ⟨202943986037902886682367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 270591981383870515576489 202943986037902886682367)
                      ·
                        rfl

theorem cell23_395232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 2, 6, 2].length) (baseStart_395232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_395232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_395232 prefixEnd_395232 := by exact prefixLift 395232
  have htrace : WordTrace (prefixWord ++ tailWord_395232) baseStart_395232 baseEnd_395232 := by
    simpa [prefixWord, tailWord_395232, baseEnd_395232] using wordTrace_append hprefix tailTrace_395232
  have hstable : (prefixWord ++ tailWord_395232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395232).length < 2 ^ (prefixWord ++ tailWord_395232).sum := by decide
  have hdescent : baseEnd_395232 < baseStart_395232 := by decide
  rcases family_descends (prefixWord ++ tailWord_395232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395242 : List Nat := [3, 1, 3, 1, 2, 1, 3, 2, 1, 6]
def baseStart_395242 : Nat := 118140960795 + 395242 * 2 ^ 59
def prefixEnd_395242 : Nat := 4983230072969 + 3 ^ 40 * 395242 * 2
def baseEnd_395242 : Nat := 67649706948149282519107

theorem tailTrace_395242 : CollatzResearch.WordTrace tailWord_395242 prefixEnd_395242 67649706948149282519107 := by
  unfold tailWord_395242
  simp only [CollatzResearch.WordTrace]
  refine ⟨3603915008528302701150995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9610440022742140536402653 3603915008528302701150995)
  ·
    refine ⟨5405872512792454051726493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3603915008528302701150995 5405872512792454051726493)
    ·
      refine ⟨2027202192297170269397435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5405872512792454051726493 2027202192297170269397435)
      ·
        refine ⟨3040803288445755404096153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2027202192297170269397435 3040803288445755404096153)
        ·
          refine ⟨2280602466334316553072115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3040803288445755404096153 2280602466334316553072115)
          ·
            refine ⟨3420903699501474829608173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2280602466334316553072115 3420903699501474829608173)
            ·
              refine ⟨1282838887313053061103065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3420903699501474829608173 1282838887313053061103065)
              ·
                refine ⟨962129165484789795827299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1282838887313053061103065 962129165484789795827299)
                ·
                  refine ⟨1443193748227184693740949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 962129165484789795827299 1443193748227184693740949)
                  ·
                    refine ⟨67649706948149282519107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1443193748227184693740949 67649706948149282519107)
                    ·
                      rfl

theorem cell23_395242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 2, 1, 6].length) (baseStart_395242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_395242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_395242 prefixEnd_395242 := by exact prefixLift 395242
  have htrace : WordTrace (prefixWord ++ tailWord_395242) baseStart_395242 baseEnd_395242 := by
    simpa [prefixWord, tailWord_395242, baseEnd_395242] using wordTrace_append hprefix tailTrace_395242
  have hstable : (prefixWord ++ tailWord_395242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395242).length < 2 ^ (prefixWord ++ tailWord_395242).sum := by decide
  have hdescent : baseEnd_395242 < baseStart_395242 := by decide
  rcases family_descends (prefixWord ++ tailWord_395242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395246 : List Nat := [4, 1, 2, 1, 3, 2, 3, 1, 1, 5]
def baseStart_395246 : Nat := 118140960795 + 395246 * 2 ^ 59
def prefixEnd_395246 : Nat := 4983230072969 + 3 ^ 40 * 395246 * 2
def baseEnd_395246 : Nat := 67650391589021943969101

theorem tailTrace_395246 : CollatzResearch.WordTrace tailWord_395246 prefixEnd_395246 67650391589021943969101 := by
  unfold tailWord_395246
  simp only [CollatzResearch.WordTrace]
  refine ⟨1801975740762339935968699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9610537284065812991833061 1801975740762339935968699)
  ·
    refine ⟨2702963611143509903953049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1801975740762339935968699 2702963611143509903953049)
    ·
      refine ⟨2027222708357632427964787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2702963611143509903953049 2027222708357632427964787)
      ·
        refine ⟨3040834062536448641947181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2027222708357632427964787 3040834062536448641947181)
        ·
          refine ⟨1140312773451168240730193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3040834062536448641947181 1140312773451168240730193)
          ·
            refine ⟨855234580088376180547645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1140312773451168240730193 855234580088376180547645)
            ·
              refine ⟨320712967533141067705367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 855234580088376180547645 320712967533141067705367)
              ·
                refine ⟨481069451299711601558051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 320712967533141067705367 481069451299711601558051)
                ·
                  refine ⟨721604176949567402337077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 481069451299711601558051 721604176949567402337077)
                  ·
                    refine ⟨67650391589021943969101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 721604176949567402337077 67650391589021943969101)
                    ·
                      rfl

theorem cell23_395246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 3, 1, 1, 5].length) (baseStart_395246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_395246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_395246 prefixEnd_395246 := by exact prefixLift 395246
  have htrace : WordTrace (prefixWord ++ tailWord_395246) baseStart_395246 baseEnd_395246 := by
    simpa [prefixWord, tailWord_395246, baseEnd_395246] using wordTrace_append hprefix tailTrace_395246
  have hstable : (prefixWord ++ tailWord_395246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395246).length < 2 ^ (prefixWord ++ tailWord_395246).sum := by decide
  have hdescent : baseEnd_395246 < baseStart_395246 := by decide
  rcases family_descends (prefixWord ++ tailWord_395246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395299 : List Nat := [1, 1, 1, 4, 3, 1, 2, 2, 4, 1, 3]
def baseStart_395299 : Nat := 118140960795 + 395299 * 2 ^ 59
def prefixEnd_395299 : Nat := 4983230072969 + 3 ^ 40 * 395299 * 2
def baseEnd_395299 : Nat := 202978389241754124544559

theorem tailTrace_395299 : CollatzResearch.WordTrace tailWord_395299 prefixEnd_395299 202978389241754124544559 := by
  unfold tailWord_395299
  simp only [CollatzResearch.WordTrace]
  refine ⟨14417738994906709539428951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9611825996604473026285967 14417738994906709539428951)
  ·
    refine ⟨21626608492360064309143427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14417738994906709539428951 21626608492360064309143427)
    ·
      refine ⟨32439912738540096463715141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21626608492360064309143427 32439912738540096463715141)
      ·
        refine ⟨6082483638476268086946589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32439912738540096463715141 6082483638476268086946589)
        ·
          refine ⟨2280931364428600532604971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6082483638476268086946589 2280931364428600532604971)
          ·
            refine ⟨3421397046642900798907457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2280931364428600532604971 3421397046642900798907457)
            ·
              refine ⟨2566047784982175599180593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3421397046642900798907457 2566047784982175599180593)
              ·
                refine ⟨1924535838736631699385445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2566047784982175599180593 1924535838736631699385445)
                ·
                  refine ⟨360850469763118443634771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1924535838736631699385445 360850469763118443634771)
                  ·
                    refine ⟨541275704644677665452157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 360850469763118443634771 541275704644677665452157)
                    ·
                      refine ⟨202978389241754124544559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 541275704644677665452157 202978389241754124544559)
                      ·
                        rfl

theorem cell23_395299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 2, 4, 1, 3].length) (baseStart_395299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_395299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_395299 prefixEnd_395299 := by exact prefixLift 395299
  have htrace : WordTrace (prefixWord ++ tailWord_395299) baseStart_395299 baseEnd_395299 := by
    simpa [prefixWord, tailWord_395299, baseEnd_395299] using wordTrace_append hprefix tailTrace_395299
  have hstable : (prefixWord ++ tailWord_395299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395299).length < 2 ^ (prefixWord ++ tailWord_395299).sum := by decide
  have hdescent : baseEnd_395299 < baseStart_395299 := by decide
  rcases family_descends (prefixWord ++ tailWord_395299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395300 : List Nat := [2, 3, 1, 4, 3, 1, 2, 1, 1, 1, 4]
def baseStart_395300 : Nat := 118140960795 + 395300 * 2 ^ 59
def prefixEnd_395300 : Nat := 4983230072969 + 3 ^ 40 * 395300 * 2
def baseEnd_395300 : Nat := 202978902722408620632055

theorem tailTrace_395300 : CollatzResearch.WordTrace tailWord_395300 prefixEnd_395300 202978902722408620632055 := by
  unfold tailWord_395300
  simp only [CollatzResearch.WordTrace]
  refine ⟨7208887733951543355107677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9611850311935391140143569 7208887733951543355107677)
  ·
    refine ⟨2703332900231828758165379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7208887733951543355107677 2703332900231828758165379)
    ·
      refine ⟨4054999350347743137248069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2703332900231828758165379 4054999350347743137248069)
      ·
        refine ⟨760312378190201838234013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4054999350347743137248069 760312378190201838234013)
        ·
          refine ⟨285117141821325689337755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 760312378190201838234013 285117141821325689337755)
          ·
            refine ⟨427675712731988534006633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 285117141821325689337755 427675712731988534006633)
            ·
              refine ⟨320756784548991400504975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 427675712731988534006633 320756784548991400504975)
              ·
                refine ⟨481135176823487100757463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 320756784548991400504975 481135176823487100757463)
                ·
                  refine ⟨721702765235230651136195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 481135176823487100757463 721702765235230651136195)
                  ·
                    refine ⟨1082554147852845976704293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 721702765235230651136195 1082554147852845976704293)
                    ·
                      refine ⟨202978902722408620632055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1082554147852845976704293 202978902722408620632055)
                      ·
                        rfl

theorem cell23_395300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_395300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_395300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_395300 prefixEnd_395300 := by exact prefixLift 395300
  have htrace : WordTrace (prefixWord ++ tailWord_395300) baseStart_395300 baseEnd_395300 := by
    simpa [prefixWord, tailWord_395300, baseEnd_395300] using wordTrace_append hprefix tailTrace_395300
  have hstable : (prefixWord ++ tailWord_395300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395300).length < 2 ^ (prefixWord ++ tailWord_395300).sum := by decide
  have hdescent : baseEnd_395300 < baseStart_395300 := by decide
  rcases family_descends (prefixWord ++ tailWord_395300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395303 : List Nat := [1, 1, 7, 1, 2, 1, 1, 3, 1, 2, 3]
def baseStart_395303 : Nat := 118140960795 + 395303 * 2 ^ 59
def prefixEnd_395303 : Nat := 4983230072969 + 3 ^ 40 * 395303 * 2
def baseEnd_395303 : Nat := 202980443164372108894541

theorem tailTrace_395303 : CollatzResearch.WordTrace tailWord_395303 prefixEnd_395303 202980443164372108894541 := by
  unfold tailWord_395303
  simp only [CollatzResearch.WordTrace]
  refine ⟨14417884886892218222574563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9611923257928145481716375 14417884886892218222574563)
  ·
    refine ⟨21626827330338327333861845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14417884886892218222574563 21626827330338327333861845)
    ·
      refine ⟨506878765554804546887387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 21626827330338327333861845 506878765554804546887387)
      ·
        refine ⟨760318148332206820331081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 506878765554804546887387 760318148332206820331081)
        ·
          refine ⟨570238611249155115248311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 760318148332206820331081 570238611249155115248311)
          ·
            refine ⟨855357916873732672872467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 570238611249155115248311 855357916873732672872467)
            ·
              refine ⟨1283036875310599009308701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 855357916873732672872467 1283036875310599009308701)
              ·
                refine ⟨481138828241474628490763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1283036875310599009308701 481138828241474628490763)
                ·
                  refine ⟨721708242362211942736145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 481138828241474628490763 721708242362211942736145)
                  ·
                    refine ⟨541281181771658957052109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 721708242362211942736145 541281181771658957052109)
                    ·
                      refine ⟨202980443164372108894541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 541281181771658957052109 202980443164372108894541)
                      ·
                        rfl

theorem cell23_395303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_395303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_395303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_395303 prefixEnd_395303 := by exact prefixLift 395303
  have htrace : WordTrace (prefixWord ++ tailWord_395303) baseStart_395303 baseEnd_395303 := by
    simpa [prefixWord, tailWord_395303, baseEnd_395303] using wordTrace_append hprefix tailTrace_395303
  have hstable : (prefixWord ++ tailWord_395303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395303).length < 2 ^ (prefixWord ++ tailWord_395303).sum := by decide
  have hdescent : baseEnd_395303 < baseStart_395303 := by decide
  rcases family_descends (prefixWord ++ tailWord_395303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395373 : List Nat := [1, 5, 1, 1, 2, 1, 2, 4, 2, 2, 2]
def baseStart_395373 : Nat := 118140960795 + 395373 * 2 ^ 59
def prefixEnd_395373 : Nat := 4983230072969 + 3 ^ 40 * 395373 * 2
def baseEnd_395373 : Nat := 203016386810186835019219

theorem tailTrace_395373 : CollatzResearch.WordTrace tailWord_395373 prefixEnd_395373 203016386810186835019219 := by
  unfold tailWord_395373
  simp only [CollatzResearch.WordTrace]
  refine ⟨14420437996638620177622773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9613625331092413451748515 14420437996638620177622773)
  ·
    refine ⟨1351916062184870641652135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14420437996638620177622773 1351916062184870641652135)
    ·
      refine ⟨2027874093277305962478203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1351916062184870641652135 2027874093277305962478203)
      ·
        refine ⟨3041811139915958943717305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2027874093277305962478203 3041811139915958943717305)
        ·
          refine ⟨2281358354936969207787979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3041811139915958943717305 2281358354936969207787979)
          ·
            refine ⟨3422037532405453811681969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2281358354936969207787979 3422037532405453811681969)
            ·
              refine ⟨2566528149304090358761477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3422037532405453811681969 2566528149304090358761477)
              ·
                refine ⟨481224027994516942267777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2566528149304090358761477 481224027994516942267777)
                ·
                  refine ⟨360918020995887706700833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 481224027994516942267777 360918020995887706700833)
                  ·
                    refine ⟨270688515746915780025625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 360918020995887706700833 270688515746915780025625)
                    ·
                      refine ⟨203016386810186835019219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 270688515746915780025625 203016386810186835019219)
                      ·
                        rfl

theorem cell23_395373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 4, 2, 2, 2].length) (baseStart_395373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_395373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_395373 prefixEnd_395373 := by exact prefixLift 395373
  have htrace : WordTrace (prefixWord ++ tailWord_395373) baseStart_395373 baseEnd_395373 := by
    simpa [prefixWord, tailWord_395373, baseEnd_395373] using wordTrace_append hprefix tailTrace_395373
  have hstable : (prefixWord ++ tailWord_395373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395373).length < 2 ^ (prefixWord ++ tailWord_395373).sum := by decide
  have hdescent : baseEnd_395373 < baseStart_395373 := by decide
  rcases family_descends (prefixWord ++ tailWord_395373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395392 : List Nat := [2, 1, 1, 2, 1, 3, 1, 1, 6, 5]
def baseStart_395392 : Nat := 118140960795 + 395392 * 2 ^ 59
def prefixEnd_395392 : Nat := 4983230072969 + 3 ^ 40 * 395392 * 2
def baseEnd_395392 : Nat := 67675380980874086893877

theorem tailTrace_395392 : CollatzResearch.WordTrace tailWord_395392 prefixEnd_395392 67675380980874086893877 := by
  unfold tailWord_395392
  simp only [CollatzResearch.WordTrace]
  refine ⟨7210565491784893211282215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9614087322379857615042953 7210565491784893211282215)
  ·
    refine ⟨10815848237677339816923323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7210565491784893211282215 10815848237677339816923323)
    ·
      refine ⟨16223772356516009725384985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10815848237677339816923323 16223772356516009725384985)
      ·
        refine ⟨12167829267387007294038739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16223772356516009725384985 12167829267387007294038739)
        ·
          refine ⟨18251743901080510941058109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12167829267387007294038739 18251743901080510941058109)
          ·
            refine ⟨6844403962905191602896791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18251743901080510941058109 6844403962905191602896791)
            ·
              refine ⟨10266605944357787404345187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6844403962905191602896791 10266605944357787404345187)
              ·
                refine ⟨15399908916536681106517781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10266605944357787404345187 15399908916536681106517781)
                ·
                  refine ⟨721870730462656926868021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 15399908916536681106517781 721870730462656926868021)
                  ·
                    refine ⟨67675380980874086893877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 721870730462656926868021 67675380980874086893877)
                    ·
                      rfl

theorem cell23_395392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 6, 5].length) (baseStart_395392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_395392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_395392 prefixEnd_395392 := by exact prefixLift 395392
  have htrace : WordTrace (prefixWord ++ tailWord_395392) baseStart_395392 baseEnd_395392 := by
    simpa [prefixWord, tailWord_395392, baseEnd_395392] using wordTrace_append hprefix tailTrace_395392
  have hstable : (prefixWord ++ tailWord_395392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395392).length < 2 ^ (prefixWord ++ tailWord_395392).sum := by decide
  have hdescent : baseEnd_395392 < baseStart_395392 := by decide
  rcases family_descends (prefixWord ++ tailWord_395392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395426 : List Nat := [3, 3, 1, 3, 1, 1, 2, 2, 2, 5]
def baseStart_395426 : Nat := 118140960795 + 395426 * 2 ^ 59
def prefixEnd_395426 : Nat := 4983230072969 + 3 ^ 40 * 395426 * 2
def baseEnd_395426 : Nat := 67681200428291709218825

theorem tailTrace_395426 : CollatzResearch.WordTrace tailWord_395426 prefixEnd_395426 67681200428291709218825 := by
  unfold tailWord_395426
  simp only [CollatzResearch.WordTrace]
  refine ⟨3605592766361652557325533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9614914043631073486201421 3605592766361652557325533)
  ·
    refine ⟨1352097287385619708997075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3605592766361652557325533 1352097287385619708997075)
    ·
      refine ⟨2028145931078429563495613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1352097287385619708997075 2028145931078429563495613)
      ·
        refine ⟨760554724154411086310855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2028145931078429563495613 760554724154411086310855)
        ·
          refine ⟨1140832086231616629466283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 760554724154411086310855 1140832086231616629466283)
          ·
            refine ⟨1711248129347424944199425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1140832086231616629466283 1711248129347424944199425)
            ·
              refine ⟨1283436097010568708149569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1711248129347424944199425 1283436097010568708149569)
              ·
                refine ⟨962577072757926531112177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1283436097010568708149569 962577072757926531112177)
                ·
                  refine ⟨721932804568444898334133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 962577072757926531112177 721932804568444898334133)
                  ·
                    refine ⟨67681200428291709218825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 721932804568444898334133 67681200428291709218825)
                    ·
                      rfl

theorem cell23_395426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 2, 2, 5].length) (baseStart_395426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_395426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_395426 prefixEnd_395426 := by exact prefixLift 395426
  have htrace : WordTrace (prefixWord ++ tailWord_395426) baseStart_395426 baseEnd_395426 := by
    simpa [prefixWord, tailWord_395426, baseEnd_395426] using wordTrace_append hprefix tailTrace_395426
  have hstable : (prefixWord ++ tailWord_395426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395426).length < 2 ^ (prefixWord ++ tailWord_395426).sum := by decide
  have hdescent : baseEnd_395426 < baseStart_395426 := by decide
  rcases family_descends (prefixWord ++ tailWord_395426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395429 : List Nat := [1, 3, 1, 2, 1, 3, 1, 4, 2, 1, 4]
def baseStart_395429 : Nat := 118140960795 + 395429 * 2 ^ 59
def prefixEnd_395429 : Nat := 4983230072969 + 3 ^ 40 * 395429 * 2
def baseEnd_395429 : Nat := 203045141726838615918961

theorem tailTrace_395429 : CollatzResearch.WordTrace tailWord_395429 prefixEnd_395429 203045141726838615918961 := by
  unfold tailWord_395429
  simp only [CollatzResearch.WordTrace]
  refine ⟨14422480484435741741661341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9614986989623827827774227 14422480484435741741661341)
  ·
    refine ⟨5408430181663403153123003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14422480484435741741661341 5408430181663403153123003)
    ·
      refine ⟨8112645272495104729684505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5408430181663403153123003 8112645272495104729684505)
      ·
        refine ⟨6084483954371328547263379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8112645272495104729684505 6084483954371328547263379)
        ·
          refine ⟨9126725931556992820895069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6084483954371328547263379 9126725931556992820895069)
          ·
            refine ⟨3422522224333872307835651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9126725931556992820895069 3422522224333872307835651)
            ·
              refine ⟨5133783336500808461753477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3422522224333872307835651 5133783336500808461753477)
              ·
                refine ⟨962584375593901586578777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5133783336500808461753477 962584375593901586578777)
                ·
                  refine ⟨721938281695426189934083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 962584375593901586578777 721938281695426189934083)
                  ·
                    refine ⟨1082907422543139284901125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 721938281695426189934083 1082907422543139284901125)
                    ·
                      refine ⟨203045141726838615918961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1082907422543139284901125 203045141726838615918961)
                      ·
                        rfl

theorem cell23_395429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 4, 2, 1, 4].length) (baseStart_395429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_395429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_395429 prefixEnd_395429 := by exact prefixLift 395429
  have htrace : WordTrace (prefixWord ++ tailWord_395429) baseStart_395429 baseEnd_395429 := by
    simpa [prefixWord, tailWord_395429, baseEnd_395429] using wordTrace_append hprefix tailTrace_395429
  have hstable : (prefixWord ++ tailWord_395429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395429).length < 2 ^ (prefixWord ++ tailWord_395429).sum := by decide
  have hdescent : baseEnd_395429 < baseStart_395429 := by decide
  rcases family_descends (prefixWord ++ tailWord_395429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395439 : List Nat := [1, 1, 2, 1, 2, 3, 1, 5, 3, 4]
def baseStart_395439 : Nat := 118140960795 + 395439 * 2 ^ 59
def prefixEnd_395439 : Nat := 4983230072969 + 3 ^ 40 * 395439 * 2
def baseEnd_395439 : Nat := 67683425511127858931305

theorem tailTrace_395439 : CollatzResearch.WordTrace tailWord_395439 prefixEnd_395439 67683425511127858931305 := by
  unfold tailWord_395439
  simp only [CollatzResearch.WordTrace]
  refine ⟨14422845214399513449525371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9615230142933008966350247 14422845214399513449525371)
  ·
    refine ⟨21634267821599270174288057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14422845214399513449525371 21634267821599270174288057)
    ·
      refine ⟨16225700866199452630716043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21634267821599270174288057 16225700866199452630716043)
      ·
        refine ⟨24338551299299178946074065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16225700866199452630716043 24338551299299178946074065)
        ·
          refine ⟨18253913474474384209555549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24338551299299178946074065 18253913474474384209555549)
          ·
            refine ⟨6845217552927894078583331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18253913474474384209555549 6845217552927894078583331)
            ·
              refine ⟨10267826329391841117874997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6845217552927894078583331 10267826329391841117874997)
              ·
                refine ⟨962608718380485104800781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10267826329391841117874997 962608718380485104800781)
                ·
                  refine ⟨360978269392681914300293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 962608718380485104800781 360978269392681914300293)
                  ·
                    refine ⟨67683425511127858931305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 360978269392681914300293 67683425511127858931305)
                    ·
                      rfl

theorem cell23_395439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 5, 3, 4].length) (baseStart_395439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_395439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_395439 prefixEnd_395439 := by exact prefixLift 395439
  have htrace : WordTrace (prefixWord ++ tailWord_395439) baseStart_395439 baseEnd_395439 := by
    simpa [prefixWord, tailWord_395439, baseEnd_395439] using wordTrace_append hprefix tailTrace_395439
  have hstable : (prefixWord ++ tailWord_395439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395439).length < 2 ^ (prefixWord ++ tailWord_395439).sum := by decide
  have hdescent : baseEnd_395439 < baseStart_395439 := by decide
  rcases family_descends (prefixWord ++ tailWord_395439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395449 : List Nat := [1, 2, 1, 4, 1, 2, 2, 2, 1, 4, 3]
def baseStart_395449 : Nat := 118140960795 + 395449 * 2 ^ 59
def prefixEnd_395449 : Nat := 4983230072969 + 3 ^ 40 * 395449 * 2
def baseEnd_395449 : Nat := 203055411339928537668869

theorem tailTrace_395449 : CollatzResearch.WordTrace tailWord_395449 prefixEnd_395449 203055411339928537668869 := by
  unfold tailWord_395449
  simp only [CollatzResearch.WordTrace]
  refine ⟨14423209944363285157389401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9615473296242190104926267 14423209944363285157389401)
  ·
    refine ⟨10817407458272463868042051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14423209944363285157389401 10817407458272463868042051)
    ·
      refine ⟨16226111187408695802063077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10817407458272463868042051 16226111187408695802063077)
      ·
        refine ⟨3042395847639130462886827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16226111187408695802063077 3042395847639130462886827)
        ·
          refine ⟨4563593771458695694330241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3042395847639130462886827 4563593771458695694330241)
          ·
            refine ⟨3422695328594021770747681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4563593771458695694330241 3422695328594021770747681)
            ·
              refine ⟨2567021496445516328060761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3422695328594021770747681 2567021496445516328060761)
              ·
                refine ⟨1925266122334137246045571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2567021496445516328060761 1925266122334137246045571)
                ·
                  refine ⟨2887899183501205869068357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1925266122334137246045571 2887899183501205869068357)
                  ·
                    refine ⟨541481096906476100450317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2887899183501205869068357 541481096906476100450317)
                    ·
                      refine ⟨203055411339928537668869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 541481096906476100450317 203055411339928537668869)
                      ·
                        rfl

theorem cell23_395449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 2, 1, 4, 3].length) (baseStart_395449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_395449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_395449 prefixEnd_395449 := by exact prefixLift 395449
  have htrace : WordTrace (prefixWord ++ tailWord_395449) baseStart_395449 baseEnd_395449 := by
    simpa [prefixWord, tailWord_395449, baseEnd_395449] using wordTrace_append hprefix tailTrace_395449
  have hstable : (prefixWord ++ tailWord_395449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395449).length < 2 ^ (prefixWord ++ tailWord_395449).sum := by decide
  have hdescent : baseEnd_395449 < baseStart_395449 := by decide
  rcases family_descends (prefixWord ++ tailWord_395449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395456 : List Nat := [2, 1, 1, 2, 5, 2, 1, 2, 3, 4]
def baseStart_395456 : Nat := 118140960795 + 395456 * 2 ^ 59
def prefixEnd_395456 : Nat := 4983230072969 + 3 ^ 40 * 395456 * 2
def baseEnd_395456 : Nat := 67686335234836670093779

theorem tailTrace_395456 : CollatzResearch.WordTrace tailWord_395456 prefixEnd_395456 67686335234836670093779 := by
  unfold tailWord_395456
  simp only [CollatzResearch.WordTrace]
  refine ⟨7211732627668962676447111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9615643503558616901929481 7211732627668962676447111)
  ·
    refine ⟨10817598941503444014670667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7211732627668962676447111 10817598941503444014670667)
    ·
      refine ⟨16226398412255166022006001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10817598941503444014670667 16226398412255166022006001)
      ·
        refine ⟨12169798809191374516504501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16226398412255166022006001 12169798809191374516504501)
        ·
          refine ⟨1140918638361691360922297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12169798809191374516504501 1140918638361691360922297)
          ·
            refine ⟨855688978771268520691723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1140918638361691360922297 855688978771268520691723)
            ·
              refine ⟨1283533468156902781037585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 855688978771268520691723 1283533468156902781037585)
              ·
                refine ⟨962650101117677085778189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1283533468156902781037585 962650101117677085778189)
                ·
                  refine ⟨360993787919128907166821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 962650101117677085778189 360993787919128907166821)
                  ·
                    refine ⟨67686335234836670093779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 360993787919128907166821 67686335234836670093779)
                    ·
                      rfl

theorem cell23_395456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 2, 3, 4].length) (baseStart_395456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_395456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_395456 prefixEnd_395456 := by exact prefixLift 395456
  have htrace : WordTrace (prefixWord ++ tailWord_395456) baseStart_395456 baseEnd_395456 := by
    simpa [prefixWord, tailWord_395456, baseEnd_395456] using wordTrace_append hprefix tailTrace_395456
  have hstable : (prefixWord ++ tailWord_395456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395456).length < 2 ^ (prefixWord ++ tailWord_395456).sum := by decide
  have hdescent : baseEnd_395456 < baseStart_395456 := by decide
  rcases family_descends (prefixWord ++ tailWord_395456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395472 : List Nat := [2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 6]
def baseStart_395472 : Nat := 118140960795 + 395472 * 2 ^ 59
def prefixEnd_395472 : Nat := 4983230072969 + 3 ^ 40 * 395472 * 2
def baseEnd_395472 : Nat := 203067221394981947681263

theorem tailTrace_395472 : CollatzResearch.WordTrace tailWord_395472 prefixEnd_395472 203067221394981947681263 := by
  unfold tailWord_395472
  simp only [CollatzResearch.WordTrace]
  refine ⟨7212024411639980042738335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9616032548853306723651113 7212024411639980042738335)
  ·
    refine ⟨10818036617459970064107503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7212024411639980042738335 10818036617459970064107503)
    ·
      refine ⟨16227054926189955096161255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10818036617459970064107503 16227054926189955096161255)
      ·
        refine ⟨24340582389284932644241883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16227054926189955096161255 24340582389284932644241883)
        ·
          refine ⟨36510873583927398966362825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24340582389284932644241883 36510873583927398966362825)
          ·
            refine ⟨27383155187945549224772119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36510873583927398966362825 27383155187945549224772119)
            ·
              refine ⟨41074732781918323837158179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27383155187945549224772119 41074732781918323837158179)
              ·
                refine ⟨61612099172877485755737269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41074732781918323837158179 61612099172877485755737269)
                ·
                  refine ⟨5776134297457264289600369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61612099172877485755737269 5776134297457264289600369)
                  ·
                    refine ⟨4332100723092948217200277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5776134297457264289600369 4332100723092948217200277)
                    ·
                      refine ⟨203067221394981947681263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4332100723092948217200277 203067221394981947681263)
                      ·
                        rfl

theorem cell23_395472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 6].length) (baseStart_395472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_395472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_395472 prefixEnd_395472 := by exact prefixLift 395472
  have htrace : WordTrace (prefixWord ++ tailWord_395472) baseStart_395472 baseEnd_395472 := by
    simpa [prefixWord, tailWord_395472, baseEnd_395472] using wordTrace_append hprefix tailTrace_395472
  have hstable : (prefixWord ++ tailWord_395472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395472).length < 2 ^ (prefixWord ++ tailWord_395472).sum := by decide
  have hdescent : baseEnd_395472 < baseStart_395472 := by decide
  rcases family_descends (prefixWord ++ tailWord_395472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395516 : List Nat := [2, 2, 2, 1, 4, 1, 1, 4, 1, 5]
def baseStart_395516 : Nat := 118140960795 + 395516 * 2 ^ 59
def prefixEnd_395516 : Nat := 4983230072969 + 3 ^ 40 * 395516 * 2
def baseEnd_395516 : Nat := 67696604847926591843687

theorem tailTrace_395516 : CollatzResearch.WordTrace tailWord_395516 prefixEnd_395516 67696604847926591843687 := by
  unfold tailWord_395516
  simp only [CollatzResearch.WordTrace]
  refine ⟨7212826817560277800039201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9617102423413703733385601 7212826817560277800039201)
  ·
    refine ⟨5409620113170208350029401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7212826817560277800039201 5409620113170208350029401)
    ·
      refine ⟨4057215084877656262522051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5409620113170208350029401 4057215084877656262522051)
      ·
        refine ⟨6085822627316484393783077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4057215084877656262522051 6085822627316484393783077)
        ·
          refine ⟨1141091742621840823834327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6085822627316484393783077 1141091742621840823834327)
          ·
            refine ⟨1711637613932761235751491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1141091742621840823834327 1711637613932761235751491)
            ·
              refine ⟨2567456420899141853627237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1711637613932761235751491 2567456420899141853627237)
              ·
                refine ⟨481398078918589097555107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2567456420899141853627237 481398078918589097555107)
                ·
                  refine ⟨722097118377883646332661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 481398078918589097555107 722097118377883646332661)
                  ·
                    refine ⟨67696604847926591843687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 722097118377883646332661 67696604847926591843687)
                    ·
                      rfl

theorem cell23_395516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 4, 1, 5].length) (baseStart_395516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_395516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_395516 prefixEnd_395516 := by exact prefixLift 395516
  have htrace : WordTrace (prefixWord ++ tailWord_395516) baseStart_395516 baseEnd_395516 := by
    simpa [prefixWord, tailWord_395516, baseEnd_395516] using wordTrace_append hprefix tailTrace_395516
  have hstable : (prefixWord ++ tailWord_395516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395516).length < 2 ^ (prefixWord ++ tailWord_395516).sum := by decide
  have hdescent : baseEnd_395516 < baseStart_395516 := by decide
  rcases family_descends (prefixWord ++ tailWord_395516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395530 : List Nat := [3, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3]
def baseStart_395530 : Nat := 118140960795 + 395530 * 2 ^ 59
def prefixEnd_395530 : Nat := 4983230072969 + 3 ^ 40 * 395530 * 2
def baseEnd_395530 : Nat := 203097003272942720755997

theorem tailTrace_395530 : CollatzResearch.WordTrace tailWord_395530 prefixEnd_395530 203097003272942720755997 := by
  unfold tailWord_395530
  simp only [CollatzResearch.WordTrace]
  refine ⟨3606541064267458997772011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9617442838046557327392029 3606541064267458997772011)
  ·
    refine ⟨5409811596401188496658017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3606541064267458997772011 5409811596401188496658017)
    ·
      refine ⟨4057358697300891372493513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5409811596401188496658017 4057358697300891372493513)
      ·
        refine ⟨3043019022975668529370135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4057358697300891372493513 3043019022975668529370135)
        ·
          refine ⟨4564528534463502794055203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3043019022975668529370135 4564528534463502794055203)
          ·
            refine ⟨6846792801695254191082805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4564528534463502794055203 6846792801695254191082805)
            ·
              refine ⟨641886825158930080414013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6846792801695254191082805 641886825158930080414013)
              ·
                refine ⟨240707559434598780155255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 641886825158930080414013 240707559434598780155255)
                ·
                  refine ⟨361061339151898170232883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 240707559434598780155255 361061339151898170232883)
                  ·
                    refine ⟨541592008727847255349325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 361061339151898170232883 541592008727847255349325)
                    ·
                      refine ⟨203097003272942720755997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 541592008727847255349325 203097003272942720755997)
                      ·
                        rfl

theorem cell23_395530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3].length) (baseStart_395530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_395530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_395530 prefixEnd_395530 := by exact prefixLift 395530
  have htrace : WordTrace (prefixWord ++ tailWord_395530) baseStart_395530 baseEnd_395530 := by
    simpa [prefixWord, tailWord_395530, baseEnd_395530] using wordTrace_append hprefix tailTrace_395530
  have hstable : (prefixWord ++ tailWord_395530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395530).length < 2 ^ (prefixWord ++ tailWord_395530).sum := by decide
  have hdescent : baseEnd_395530 < baseStart_395530 := by decide
  rcases family_descends (prefixWord ++ tailWord_395530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395556 : List Nat := [2, 3, 1, 3, 1, 2, 2, 2, 1, 1, 5]
def baseStart_395556 : Nat := 118140960795 + 395556 * 2 ^ 59
def prefixEnd_395556 : Nat := 4983230072969 + 3 ^ 40 * 395556 * 2
def baseEnd_395556 : Nat := 203110353769959619030877

theorem tailTrace_395556 : CollatzResearch.WordTrace tailWord_395556 prefixEnd_395556 203110353769959619030877 := by
  unfold tailWord_395556
  simp only [CollatzResearch.WordTrace]
  refine ⟨7213556277487821215767261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9618075036650428287689681 7213556277487821215767261)
  ·
    refine ⟨2705083604057932955912723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7213556277487821215767261 2705083604057932955912723)
    ·
      refine ⟨4057625406086899433869085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2705083604057932955912723 4057625406086899433869085)
      ·
        refine ⟨1521609527282587287700907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4057625406086899433869085 1521609527282587287700907)
        ·
          refine ⟨2282414290923880931551361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1521609527282587287700907 2282414290923880931551361)
          ·
            refine ⟨1711810718192910698663521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2282414290923880931551361 1711810718192910698663521)
            ·
              refine ⟨1283858038644683023997641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1711810718192910698663521 1283858038644683023997641)
              ·
                refine ⟨962893528983512267998231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1283858038644683023997641 962893528983512267998231)
                ·
                  refine ⟨1444340293475268401997347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 962893528983512267998231 1444340293475268401997347)
                  ·
                    refine ⟨2166510440212902602996021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1444340293475268401997347 2166510440212902602996021)
                    ·
                      refine ⟨203110353769959619030877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2166510440212902602996021 203110353769959619030877)
                      ·
                        rfl

theorem cell23_395556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_395556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_395556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_395556 prefixEnd_395556 := by exact prefixLift 395556
  have htrace : WordTrace (prefixWord ++ tailWord_395556) baseStart_395556 baseEnd_395556 := by
    simpa [prefixWord, tailWord_395556, baseEnd_395556] using wordTrace_append hprefix tailTrace_395556
  have hstable : (prefixWord ++ tailWord_395556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395556).length < 2 ^ (prefixWord ++ tailWord_395556).sum := by decide
  have hdescent : baseEnd_395556 < baseStart_395556 := by decide
  rcases family_descends (prefixWord ++ tailWord_395556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395570 : List Nat := [3, 2, 1, 1, 5, 2, 1, 2, 1, 1, 4]
def baseStart_395570 : Nat := 118140960795 + 395570 * 2 ^ 59
def prefixEnd_395570 : Nat := 4983230072969 + 3 ^ 40 * 395570 * 2
def baseEnd_395570 : Nat := 203117542499122564255813

theorem tailTrace_395570 : CollatzResearch.WordTrace tailWord_395570 prefixEnd_395570 203117542499122564255813 := by
  unfold tailWord_395570
  simp only [CollatzResearch.WordTrace]
  refine ⟨3606905794231230705636041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9618415451283281881696109 3606905794231230705636041)
  ·
    refine ⟨2705179345673423029227031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3606905794231230705636041 2705179345673423029227031)
    ·
      refine ⟨4057769018510134543840547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2705179345673423029227031 4057769018510134543840547)
      ·
        refine ⟨6086653527765201815760821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4057769018510134543840547 6086653527765201815760821)
        ·
          refine ⟨570623768227987670227577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6086653527765201815760821 570623768227987670227577)
          ·
            refine ⟨427967826170990752670683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 570623768227987670227577 427967826170990752670683)
            ·
              refine ⟨641951739256486129006025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 427967826170990752670683 641951739256486129006025)
              ·
                refine ⟨481463804442364596754519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 641951739256486129006025 481463804442364596754519)
                ·
                  refine ⟨722195706663546895131779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 481463804442364596754519 722195706663546895131779)
                  ·
                    refine ⟨1083293559995320342697669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 722195706663546895131779 1083293559995320342697669)
                    ·
                      refine ⟨203117542499122564255813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1083293559995320342697669 203117542499122564255813)
                      ·
                        rfl

theorem cell23_395570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 2, 1, 1, 4].length) (baseStart_395570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_395570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_395570 prefixEnd_395570 := by exact prefixLift 395570
  have htrace : WordTrace (prefixWord ++ tailWord_395570) baseStart_395570 baseEnd_395570 := by
    simpa [prefixWord, tailWord_395570, baseEnd_395570] using wordTrace_append hprefix tailTrace_395570
  have hstable : (prefixWord ++ tailWord_395570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395570).length < 2 ^ (prefixWord ++ tailWord_395570).sum := by decide
  have hdescent : baseEnd_395570 < baseStart_395570 := by decide
  rcases family_descends (prefixWord ++ tailWord_395570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395604 : List Nat := [2, 4, 1, 1, 2, 2, 4, 2, 1, 2, 2]
def baseStart_395604 : Nat := 118140960795 + 395604 * 2 ^ 59
def prefixEnd_395604 : Nat := 4983230072969 + 3 ^ 40 * 395604 * 2
def baseEnd_395604 : Nat := 203135000841375431230657

theorem tailTrace_395604 : CollatzResearch.WordTrace tailWord_395604 prefixEnd_395604 203135000841375431230657 := by
  unfold tailWord_395604
  simp only [CollatzResearch.WordTrace]
  refine ⟨7214431629400873314640933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9619242172534497752854577 7214431629400873314640933)
  ·
    refine ⟨1352705930512663746495175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7214431629400873314640933 1352705930512663746495175)
    ·
      refine ⟨2029058895768995619742763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1352705930512663746495175 2029058895768995619742763)
      ·
        refine ⟨3043588343653493429614145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2029058895768995619742763 3043588343653493429614145)
        ·
          refine ⟨2282691257740120072210609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3043588343653493429614145 2282691257740120072210609)
          ·
            refine ⟨1712018443305090054157957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2282691257740120072210609 1712018443305090054157957)
            ·
              refine ⟨321003458119704385154617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1712018443305090054157957 321003458119704385154617)
              ·
                refine ⟨240752593589778288865963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 321003458119704385154617 240752593589778288865963)
                ·
                  refine ⟨361128890384667433298945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 240752593589778288865963 361128890384667433298945)
                  ·
                    refine ⟨270846667788500574974209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 361128890384667433298945 270846667788500574974209)
                    ·
                      refine ⟨203135000841375431230657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 270846667788500574974209 203135000841375431230657)
                      ·
                        rfl

theorem cell23_395604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 4, 2, 1, 2, 2].length) (baseStart_395604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_395604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_395604 prefixEnd_395604 := by exact prefixLift 395604
  have htrace : WordTrace (prefixWord ++ tailWord_395604) baseStart_395604 baseEnd_395604 := by
    simpa [prefixWord, tailWord_395604, baseEnd_395604] using wordTrace_append hprefix tailTrace_395604
  have hstable : (prefixWord ++ tailWord_395604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395604).length < 2 ^ (prefixWord ++ tailWord_395604).sum := by decide
  have hdescent : baseEnd_395604 < baseStart_395604 := by decide
  rcases family_descends (prefixWord ++ tailWord_395604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395614 : List Nat := [4, 4, 2, 1, 1, 1, 2, 1, 1, 6]
def baseStart_395614 : Nat := 118140960795 + 395614 * 2 ^ 59
def prefixEnd_395614 : Nat := 4983230072969 + 3 ^ 40 * 395614 * 2
def baseEnd_395614 : Nat := 67713378549306797368537

theorem tailTrace_395614 : CollatzResearch.WordTrace tailWord_395614 prefixEnd_395614 67713378549306797368537 := by
  unfold tailWord_395614
  simp only [CollatzResearch.WordTrace]
  refine ⟨1803653498595689792143237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9619485325843678891430597 1803653498595689792143237)
  ·
    refine ⟨338185030986691836026857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1803653498595689792143237 338185030986691836026857)
    ·
      refine ⟨253638773240018877020143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 338185030986691836026857 253638773240018877020143)
      ·
        refine ⟨380458159860028315530215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253638773240018877020143 380458159860028315530215)
        ·
          refine ⟨570687239790042473295323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 380458159860028315530215 570687239790042473295323)
          ·
            refine ⟨856030859685063709942985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 570687239790042473295323 856030859685063709942985)
            ·
              refine ⟨642023144763797782457239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 856030859685063709942985 642023144763797782457239)
              ·
                refine ⟨963034717145696673685859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 642023144763797782457239 963034717145696673685859)
                ·
                  refine ⟨1444552075718545010528789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 963034717145696673685859 1444552075718545010528789)
                  ·
                    refine ⟨67713378549306797368537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1444552075718545010528789 67713378549306797368537)
                    ·
                      rfl

theorem cell23_395614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_395614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_395614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_395614 prefixEnd_395614 := by exact prefixLift 395614
  have htrace : WordTrace (prefixWord ++ tailWord_395614) baseStart_395614 baseEnd_395614 := by
    simpa [prefixWord, tailWord_395614, baseEnd_395614] using wordTrace_append hprefix tailTrace_395614
  have hstable : (prefixWord ++ tailWord_395614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395614).length < 2 ^ (prefixWord ++ tailWord_395614).sum := by decide
  have hdescent : baseEnd_395614 < baseStart_395614 := by decide
  rcases family_descends (prefixWord ++ tailWord_395614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395643 : List Nat := [1, 1, 1, 1, 1, 7, 2, 2, 1, 4, 2]
def baseStart_395643 : Nat := 118140960795 + 395643 * 2 ^ 59
def prefixEnd_395643 : Nat := 4983230072969 + 3 ^ 40 * 395643 * 2
def baseEnd_395643 : Nat := 203155026586900778642977

theorem tailTrace_395643 : CollatzResearch.WordTrace tailWord_395643 prefixEnd_395643 203155026586900778642977 := by
  unfold tailWord_395643
  simp only [CollatzResearch.WordTrace]
  refine ⟨14430285705660456289951583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9620190470440304193301055 14430285705660456289951583)
  ·
    refine ⟨21645428558490684434927375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14430285705660456289951583 21645428558490684434927375)
    ·
      refine ⟨32468142837736026652391063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21645428558490684434927375 32468142837736026652391063)
      ·
        refine ⟨48702214256604039978586595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32468142837736026652391063 48702214256604039978586595)
        ·
          refine ⟨73053321384906059967879893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48702214256604039978586595 73053321384906059967879893)
          ·
            refine ⟨1712187219958735780497185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 73053321384906059967879893 1712187219958735780497185)
            ·
              refine ⟨1284140414969051835372889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1712187219958735780497185 1284140414969051835372889)
              ·
                refine ⟨963105311226788876529667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1284140414969051835372889 963105311226788876529667)
                ·
                  refine ⟨1444657966840183314794501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 963105311226788876529667 1444657966840183314794501)
                  ·
                    refine ⟨270873368782534371523969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1444657966840183314794501 270873368782534371523969)
                    ·
                      refine ⟨203155026586900778642977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 270873368782534371523969 203155026586900778642977)
                      ·
                        rfl

theorem cell23_395643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 2, 1, 4, 2].length) (baseStart_395643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_395643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_395643 prefixEnd_395643 := by exact prefixLift 395643
  have htrace : WordTrace (prefixWord ++ tailWord_395643) baseStart_395643 baseEnd_395643 := by
    simpa [prefixWord, tailWord_395643, baseEnd_395643] using wordTrace_append hprefix tailTrace_395643
  have hstable : (prefixWord ++ tailWord_395643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395643).length < 2 ^ (prefixWord ++ tailWord_395643).sum := by decide
  have hdescent : baseEnd_395643 < baseStart_395643 := by decide
  rcases family_descends (prefixWord ++ tailWord_395643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395656 : List Nat := [2, 1, 3, 3, 1, 1, 1, 1, 4, 2, 4]
def baseStart_395656 : Nat := 118140960795 + 395656 * 2 ^ 59
def prefixEnd_395656 : Nat := 4983230072969 + 3 ^ 40 * 395656 * 2
def baseEnd_395656 : Nat := 203161701835409227780417

theorem tailTrace_395656 : CollatzResearch.WordTrace tailWord_395656 prefixEnd_395656 203161701835409227780417 := by
  unfold tailWord_395656
  simp only [CollatzResearch.WordTrace]
  refine ⟨7215379927306679755087411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9620506569742239673449881 7215379927306679755087411)
  ·
    refine ⟨10823069890960019632631117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7215379927306679755087411 10823069890960019632631117)
    ·
      refine ⟨4058651209110007362236669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10823069890960019632631117 4058651209110007362236669)
      ·
        refine ⟨1521994203416252760838751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4058651209110007362236669 1521994203416252760838751)
        ·
          refine ⟨2282991305124379141258127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1521994203416252760838751 2282991305124379141258127)
          ·
            refine ⟨3424486957686568711887191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2282991305124379141258127 3424486957686568711887191)
            ·
              refine ⟨5136730436529853067830787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3424486957686568711887191 5136730436529853067830787)
              ·
                refine ⟨7705095654794779601746181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5136730436529853067830787 7705095654794779601746181)
                ·
                  refine ⟨1444705435274021175327409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7705095654794779601746181 1444705435274021175327409)
                  ·
                    refine ⟨1083529076455515881495557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1444705435274021175327409 1083529076455515881495557)
                    ·
                      refine ⟨203161701835409227780417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1083529076455515881495557 203161701835409227780417)
                      ·
                        rfl

theorem cell23_395656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_395656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_395656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_395656 prefixEnd_395656 := by exact prefixLift 395656
  have htrace : WordTrace (prefixWord ++ tailWord_395656) baseStart_395656 baseEnd_395656 := by
    simpa [prefixWord, tailWord_395656, baseEnd_395656] using wordTrace_append hprefix tailTrace_395656
  have hstable : (prefixWord ++ tailWord_395656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395656).length < 2 ^ (prefixWord ++ tailWord_395656).sum := by decide
  have hdescent : baseEnd_395656 < baseStart_395656 := by decide
  rcases family_descends (prefixWord ++ tailWord_395656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395660 : List Nat := [2, 2, 1, 2, 1, 5, 1, 1, 4, 2, 2]
def baseStart_395660 : Nat := 118140960795 + 395660 * 2 ^ 59
def prefixEnd_395660 : Nat := 4983230072969 + 3 ^ 40 * 395660 * 2
def baseEnd_395660 : Nat := 203163755758027212130399

theorem tailTrace_395660 : CollatzResearch.WordTrace tailWord_395660 prefixEnd_395660 203163755758027212130399 := by
  unfold tailWord_395660
  simp only [CollatzResearch.WordTrace]
  refine ⟨7215452873299434096660217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9620603831065912128880289 7215452873299434096660217)
  ·
    refine ⟨5411589654974575572495163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7215452873299434096660217 5411589654974575572495163)
    ·
      refine ⟨8117384482461863358742745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5411589654974575572495163 8117384482461863358742745)
      ·
        refine ⟨6088038361846397519057059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8117384482461863358742745 6088038361846397519057059)
        ·
          refine ⟨9132057542769596278585589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6088038361846397519057059 9132057542769596278585589)
          ·
            refine ⟨856130394634649651117399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9132057542769596278585589 856130394634649651117399)
            ·
              refine ⟨1284195591951974476676099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 856130394634649651117399 1284195591951974476676099)
              ·
                refine ⟨1926293387927961715014149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1284195591951974476676099 1926293387927961715014149)
                ·
                  refine ⟨361180010236492821565153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1926293387927961715014149 361180010236492821565153)
                  ·
                    refine ⟨270885007677369616173865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 361180010236492821565153 270885007677369616173865)
                    ·
                      refine ⟨203163755758027212130399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 270885007677369616173865 203163755758027212130399)
                      ·
                        rfl

theorem cell23_395660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 1, 4, 2, 2].length) (baseStart_395660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_395660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_395660 prefixEnd_395660 := by exact prefixLift 395660
  have htrace : WordTrace (prefixWord ++ tailWord_395660) baseStart_395660 baseEnd_395660 := by
    simpa [prefixWord, tailWord_395660, baseEnd_395660] using wordTrace_append hprefix tailTrace_395660
  have hstable : (prefixWord ++ tailWord_395660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395660).length < 2 ^ (prefixWord ++ tailWord_395660).sum := by decide
  have hdescent : baseEnd_395660 < baseStart_395660 := by decide
  rcases family_descends (prefixWord ++ tailWord_395660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395677 : List Nat := [1, 4, 2, 1, 4, 2, 1, 1, 1, 4, 2]
def baseStart_395677 : Nat := 118140960795 + 395677 * 2 ^ 59
def prefixEnd_395677 : Nat := 4983230072969 + 3 ^ 40 * 395677 * 2
def baseEnd_395677 : Nat := 203172484929153645617821

theorem tailTrace_395677 : CollatzResearch.WordTrace tailWord_395677 prefixEnd_395677 203172484929153645617821 := by
  unfold tailWord_395677
  simp only [CollatzResearch.WordTrace]
  refine ⟨14431525787537280096689285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9621017191691520064459523 14431525787537280096689285)
  ·
    refine ⟨2705911085163240018129241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14431525787537280096689285 2705911085163240018129241)
    ·
      refine ⟨2029433313872430013596931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2705911085163240018129241 2029433313872430013596931)
      ·
        refine ⟨3044149970808645020395397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2029433313872430013596931 3044149970808645020395397)
        ·
          refine ⟨570778119526620941324137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3044149970808645020395397 570778119526620941324137)
          ·
            refine ⟨428083589644965705993103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 570778119526620941324137 428083589644965705993103)
            ·
              refine ⟨642125384467448558989655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 428083589644965705993103 642125384467448558989655)
              ·
                refine ⟨963188076701172838484483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 642125384467448558989655 963188076701172838484483)
                ·
                  refine ⟨1444782115051759257726725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 963188076701172838484483 1444782115051759257726725)
                  ·
                    refine ⟨270896646572204860823761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1444782115051759257726725 270896646572204860823761)
                    ·
                      refine ⟨203172484929153645617821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 270896646572204860823761 203172484929153645617821)
                      ·
                        rfl

theorem cell23_395677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 1, 1, 4, 2].length) (baseStart_395677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_395677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_395677 prefixEnd_395677 := by exact prefixLift 395677
  have htrace : WordTrace (prefixWord ++ tailWord_395677) baseStart_395677 baseEnd_395677 := by
    simpa [prefixWord, tailWord_395677, baseEnd_395677] using wordTrace_append hprefix tailTrace_395677
  have hstable : (prefixWord ++ tailWord_395677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395677).length < 2 ^ (prefixWord ++ tailWord_395677).sum := by decide
  have hdescent : baseEnd_395677 < baseStart_395677 := by decide
  rcases family_descends (prefixWord ++ tailWord_395677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395760 : List Nat := [2, 1, 1, 1, 3, 3, 2, 5, 1, 4]
def baseStart_395760 : Nat := 118140960795 + 395760 * 2 ^ 59
def prefixEnd_395760 : Nat := 4983230072969 + 3 ^ 40 * 395760 * 2
def baseEnd_395760 : Nat := 67738367941158940293313

theorem tailTrace_395760 : CollatzResearch.WordTrace tailWord_395760 prefixEnd_395760 67738367941158940293313 := by
  unfold tailWord_395760
  simp only [CollatzResearch.WordTrace]
  refine ⟨7217276523118292635980367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9623035364157723514640489 7217276523118292635980367)
  ·
    refine ⟨10825914784677438953970551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7217276523118292635980367 10825914784677438953970551)
    ·
      refine ⟨16238872177016158430955827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10825914784677438953970551 16238872177016158430955827)
      ·
        refine ⟨24358308265524237646433741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16238872177016158430955827 24358308265524237646433741)
        ·
          refine ⟨9134365599571589117412653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24358308265524237646433741 9134365599571589117412653)
          ·
            refine ⟨3425387099839345919029745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9134365599571589117412653 3425387099839345919029745)
            ·
              refine ⟨2569040324879509439272309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3425387099839345919029745 2569040324879509439272309)
              ·
                refine ⟨240847530457454009931779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2569040324879509439272309 240847530457454009931779)
                ·
                  refine ⟨361271295686181014897669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 240847530457454009931779 361271295686181014897669)
                  ·
                    refine ⟨67738367941158940293313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 361271295686181014897669 67738367941158940293313)
                    ·
                      rfl

theorem cell23_395760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 5, 1, 4].length) (baseStart_395760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_395760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_395760 prefixEnd_395760 := by exact prefixLift 395760
  have htrace : WordTrace (prefixWord ++ tailWord_395760) baseStart_395760 baseEnd_395760 := by
    simpa [prefixWord, tailWord_395760, baseEnd_395760] using wordTrace_append hprefix tailTrace_395760
  have hstable : (prefixWord ++ tailWord_395760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395760).length < 2 ^ (prefixWord ++ tailWord_395760).sum := by decide
  have hdescent : baseEnd_395760 < baseStart_395760 := by decide
  rcases family_descends (prefixWord ++ tailWord_395760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395773 : List Nat := [1, 4, 1, 1, 1, 3, 4, 2, 6]
def baseStart_395773 : Nat := 118140960795 + 395773 * 2 ^ 59
def prefixEnd_395773 : Nat := 4983230072969 + 3 ^ 40 * 395773 * 2
def baseEnd_395773 : Nat := 22580197674665030001931

theorem tailTrace_395773 : CollatzResearch.WordTrace tailWord_395773 prefixEnd_395773 22580197674665030001931 := by
  unfold tailWord_395773
  simp only [CollatzResearch.WordTrace]
  refine ⟨14435027195189488492183973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9623351463459658994789315 14435027195189488492183973)
  ·
    refine ⟨2706567599098029092284495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14435027195189488492183973 2706567599098029092284495)
    ·
      refine ⟨4059851398647043638426743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2706567599098029092284495 4059851398647043638426743)
      ·
        refine ⟨6089777097970565457640115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4059851398647043638426743 6089777097970565457640115)
        ·
          refine ⟨9134665646955848186460173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6089777097970565457640115 9134665646955848186460173)
          ·
            refine ⟨3425499617608443069922565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9134665646955848186460173 3425499617608443069922565)
            ·
              refine ⟨642281178301583075610481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3425499617608443069922565 642281178301583075610481)
              ·
                refine ⟨481710883726187306707861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 642281178301583075610481 481710883726187306707861)
                ·
                  refine ⟨22580197674665030001931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 481710883726187306707861 22580197674665030001931)
                  ·
                    rfl

theorem cell23_395773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 2, 6].length) (baseStart_395773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_395773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_395773 prefixEnd_395773 := by exact prefixLift 395773
  have htrace : WordTrace (prefixWord ++ tailWord_395773) baseStart_395773 baseEnd_395773 := by
    simpa [prefixWord, tailWord_395773, baseEnd_395773] using wordTrace_append hprefix tailTrace_395773
  have hstable : (prefixWord ++ tailWord_395773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395773).length < 2 ^ (prefixWord ++ tailWord_395773).sum := by decide
  have hdescent : baseEnd_395773 < baseStart_395773 := by decide
  rcases family_descends (prefixWord ++ tailWord_395773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395777 : List Nat := [1, 2, 4, 1, 3, 2, 1, 4, 1, 4]
def baseStart_395777 : Nat := 118140960795 + 395777 * 2 ^ 59
def prefixEnd_395777 : Nat := 4983230072969 + 3 ^ 40 * 395777 * 2
def baseEnd_395777 : Nat := 67741277664867751455787

theorem tailTrace_395777 : CollatzResearch.WordTrace tailWord_395777 prefixEnd_395777 67741277664867751455787 := by
  unfold tailWord_395777
  simp only [CollatzResearch.WordTrace]
  refine ⟨14435173087174997175329585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9623448724783331450219723 14435173087174997175329585)
  ·
    refine ⟨10826379815381247881497189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14435173087174997175329585 10826379815381247881497189)
    ·
      refine ⟨2029946215383983977780723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10826379815381247881497189 2029946215383983977780723)
      ·
        refine ⟨3044919323075975966671085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2029946215383983977780723 3044919323075975966671085)
        ·
          refine ⟨1141844746153490987501657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3044919323075975966671085 1141844746153490987501657)
          ·
            refine ⟨856383559615118240626243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1141844746153490987501657 856383559615118240626243)
            ·
              refine ⟨1284575339422677360939365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 856383559615118240626243 1284575339422677360939365)
              ·
                refine ⟨240857876141752005176131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1284575339422677360939365 240857876141752005176131)
                ·
                  refine ⟨361286814212628007764197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 240857876141752005176131 361286814212628007764197)
                  ·
                    refine ⟨67741277664867751455787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 361286814212628007764197 67741277664867751455787)
                    ·
                      rfl

theorem cell23_395777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 4, 1, 4].length) (baseStart_395777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_395777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_395777 prefixEnd_395777 := by exact prefixLift 395777
  have htrace : WordTrace (prefixWord ++ tailWord_395777) baseStart_395777 baseEnd_395777 := by
    simpa [prefixWord, tailWord_395777, baseEnd_395777] using wordTrace_append hprefix tailTrace_395777
  have hstable : (prefixWord ++ tailWord_395777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395777).length < 2 ^ (prefixWord ++ tailWord_395777).sum := by decide
  have hdescent : baseEnd_395777 < baseStart_395777 := by decide
  rcases family_descends (prefixWord ++ tailWord_395777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395800 : List Nat := [2, 1, 2, 3, 3, 1, 1, 1, 5, 1, 3]
def baseStart_395800 : Nat := 118140960795 + 395800 * 2 ^ 59
def prefixEnd_395800 : Nat := 4983230072969 + 3 ^ 40 * 395800 * 2
def baseEnd_395800 : Nat := 203235643049656664379755

theorem tailTrace_395800 : CollatzResearch.WordTrace tailWord_395800 prefixEnd_395800 203235643049656664379755 := by
  unfold tailWord_395800
  simp only [CollatzResearch.WordTrace]
  refine ⟨7218005983045836051708427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9624007977394448068944569 7218005983045836051708427)
  ·
    refine ⟨10827008974568754077562641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7218005983045836051708427 10827008974568754077562641)
    ·
      refine ⟨8120256730926565558171981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10827008974568754077562641 8120256730926565558171981)
      ·
        refine ⟨3045096274097462084314493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8120256730926565558171981 3045096274097462084314493)
        ·
          refine ⟨1141911102786548281617935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3045096274097462084314493 1141911102786548281617935)
          ·
            refine ⟨1712866654179822422426903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1141911102786548281617935 1712866654179822422426903)
            ·
              refine ⟨2569299981269733633640355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1712866654179822422426903 2569299981269733633640355)
              ·
                refine ⟨3853949971904600450460533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2569299981269733633640355 3853949971904600450460533)
                ·
                  refine ⟨361307809866056292230675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3853949971904600450460533 361307809866056292230675)
                  ·
                    refine ⟨541961714799084438346013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 361307809866056292230675 541961714799084438346013)
                    ·
                      refine ⟨203235643049656664379755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 541961714799084438346013 203235643049656664379755)
                      ·
                        rfl

theorem cell23_395800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 5, 1, 3].length) (baseStart_395800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_395800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_395800 prefixEnd_395800 := by exact prefixLift 395800
  have htrace : WordTrace (prefixWord ++ tailWord_395800) baseStart_395800 baseEnd_395800 := by
    simpa [prefixWord, tailWord_395800, baseEnd_395800] using wordTrace_append hprefix tailTrace_395800
  have hstable : (prefixWord ++ tailWord_395800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395800).length < 2 ^ (prefixWord ++ tailWord_395800).sum := by decide
  have hdescent : baseEnd_395800 < baseStart_395800 := by decide
  rcases family_descends (prefixWord ++ tailWord_395800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395823 : List Nat := [1, 1, 2, 1, 2, 1, 1, 1, 3, 8, 2]
def baseStart_395823 : Nat := 118140960795 + 395823 * 2 ^ 59
def prefixEnd_395823 : Nat := 4983230072969 + 3 ^ 40 * 395823 * 2
def baseEnd_395823 : Nat := 203247453104710074392149

theorem tailTrace_395823 : CollatzResearch.WordTrace tailWord_395823 prefixEnd_395823 203247453104710074392149 := by
  unfold tailWord_395823
  simp only [CollatzResearch.WordTrace]
  refine ⟨14436850845008347031504123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9624567230005564687669415 14436850845008347031504123)
  ·
    refine ⟨21655276267512520547256185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14436850845008347031504123 21655276267512520547256185)
    ·
      refine ⟨16241457200634390410442139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21655276267512520547256185 16241457200634390410442139)
      ·
        refine ⟨24362185800951585615663209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16241457200634390410442139 24362185800951585615663209)
        ·
          refine ⟨18271639350713689211747407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24362185800951585615663209 18271639350713689211747407)
          ·
            refine ⟨27407459026070533817621111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18271639350713689211747407 27407459026070533817621111)
            ·
              refine ⟨41111188539105800726431667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27407459026070533817621111 41111188539105800726431667)
              ·
                refine ⟨61666782808658701089647501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41111188539105800726431667 61666782808658701089647501)
                ·
                  refine ⟨23125043553247012908617813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61666782808658701089647501 23125043553247012908617813)
                  ·
                    refine ⟨270996604139613432522865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 23125043553247012908617813 270996604139613432522865)
                    ·
                      refine ⟨203247453104710074392149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 270996604139613432522865 203247453104710074392149)
                      ·
                        rfl

theorem cell23_395823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 8, 2].length) (baseStart_395823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_395823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_395823 prefixEnd_395823 := by exact prefixLift 395823
  have htrace : WordTrace (prefixWord ++ tailWord_395823) baseStart_395823 baseEnd_395823 := by
    simpa [prefixWord, tailWord_395823, baseEnd_395823] using wordTrace_append hprefix tailTrace_395823
  have hstable : (prefixWord ++ tailWord_395823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395823).length < 2 ^ (prefixWord ++ tailWord_395823).sum := by decide
  have hdescent : baseEnd_395823 < baseStart_395823 := by decide
  rcases family_descends (prefixWord ++ tailWord_395823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395843 : List Nat := [1, 1, 1, 3, 1, 2, 1, 3, 5, 2, 3]
def baseStart_395843 : Nat := 118140960795 + 395843 * 2 ^ 59
def prefixEnd_395843 : Nat := 4983230072969 + 3 ^ 40 * 395843 * 2
def baseEnd_395843 : Nat := 203257722717799996142057

theorem tailTrace_395843 : CollatzResearch.WordTrace tailWord_395843 prefixEnd_395843 203257722717799996142057 := by
  unfold tailWord_395843
  simp only [CollatzResearch.WordTrace]
  refine ⟨14437580304935890447232183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9625053536623926964821455 14437580304935890447232183)
  ·
    refine ⟨21656370457403835670848275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14437580304935890447232183 21656370457403835670848275)
    ·
      refine ⟨32484555686105753506272413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21656370457403835670848275 32484555686105753506272413)
      ·
        refine ⟨12181708382289657564852155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32484555686105753506272413 12181708382289657564852155)
        ·
          refine ⟨18272562573434486347278233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12181708382289657564852155 18272562573434486347278233)
          ·
            refine ⟨13704421930075864760458675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18272562573434486347278233 13704421930075864760458675)
            ·
              refine ⟨20556632895113797140688013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13704421930075864760458675 20556632895113797140688013)
              ·
                refine ⟨7708737335667673927758005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20556632895113797140688013 7708737335667673927758005)
                ·
                  refine ⟨722694125218844430727313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7708737335667673927758005 722694125218844430727313)
                  ·
                    refine ⟨542020593914133323045485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 722694125218844430727313 542020593914133323045485)
                    ·
                      refine ⟨203257722717799996142057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 542020593914133323045485 203257722717799996142057)
                      ·
                        rfl

theorem cell23_395843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 5, 2, 3].length) (baseStart_395843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_395843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_395843 prefixEnd_395843 := by exact prefixLift 395843
  have htrace : WordTrace (prefixWord ++ tailWord_395843) baseStart_395843 baseEnd_395843 := by
    simpa [prefixWord, tailWord_395843, baseEnd_395843] using wordTrace_append hprefix tailTrace_395843
  have hstable : (prefixWord ++ tailWord_395843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395843).length < 2 ^ (prefixWord ++ tailWord_395843).sum := by decide
  have hdescent : baseEnd_395843 < baseStart_395843 := by decide
  rcases family_descends (prefixWord ++ tailWord_395843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395850 : List Nat := [3, 1, 2, 1, 1, 6, 1, 1, 1, 6]
def baseStart_395850 : Nat := 118140960795 + 395850 * 2 ^ 59
def prefixEnd_395850 : Nat := 4983230072969 + 3 ^ 40 * 395850 * 2
def baseEnd_395850 : Nat := 67753772360793822918175

theorem tailTrace_395850 : CollatzResearch.WordTrace tailWord_395850 prefixEnd_395850 67753772360793822918175 := by
  unfold tailWord_395850
  simp only [CollatzResearch.WordTrace]
  refine ⟨3609458903977632660684251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9625223743940353761824669 3609458903977632660684251)
  ·
    refine ⟨5414188355966448991026377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3609458903977632660684251 5414188355966448991026377)
    ·
      refine ⟨4060641266974836743269783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5414188355966448991026377 4060641266974836743269783)
      ·
        refine ⟨6090961900462255114904675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4060641266974836743269783 6090961900462255114904675)
        ·
          refine ⟨9136442850693382672357013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6090961900462255114904675 9136442850693382672357013)
          ·
            refine ⟨428270758626252312766735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 9136442850693382672357013 428270758626252312766735)
            ·
              refine ⟨642406137939378469150103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 428270758626252312766735 642406137939378469150103)
              ·
                refine ⟨963609206909067703725155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 642406137939378469150103 963609206909067703725155)
                ·
                  refine ⟨1445413810363601555587733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 963609206909067703725155 1445413810363601555587733)
                  ·
                    refine ⟨67753772360793822918175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1445413810363601555587733 67753772360793822918175)
                    ·
                      rfl

theorem cell23_395850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 1, 1, 6].length) (baseStart_395850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_395850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_395850 prefixEnd_395850 := by exact prefixLift 395850
  have htrace : WordTrace (prefixWord ++ tailWord_395850) baseStart_395850 baseEnd_395850 := by
    simpa [prefixWord, tailWord_395850, baseEnd_395850] using wordTrace_append hprefix tailTrace_395850
  have hstable : (prefixWord ++ tailWord_395850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395850).length < 2 ^ (prefixWord ++ tailWord_395850).sum := by decide
  have hdescent : baseEnd_395850 < baseStart_395850 := by decide
  rcases family_descends (prefixWord ++ tailWord_395850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395857 : List Nat := [1, 2, 2, 1, 3, 3, 2, 2, 3, 2, 2]
def baseStart_395857 : Nat := 118140960795 + 395857 * 2 ^ 59
def prefixEnd_395857 : Nat := 4983230072969 + 3 ^ 40 * 395857 * 2
def baseEnd_395857 : Nat := 203264911446962941366993

theorem tailTrace_395857 : CollatzResearch.WordTrace tailWord_395857 prefixEnd_395857 203264911446962941366993 := by
  unfold tailWord_395857
  simp only [CollatzResearch.WordTrace]
  refine ⟨14438090926885170838241825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9625393951256780558827883 14438090926885170838241825)
  ·
    refine ⟨10828568195163878128681369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14438090926885170838241825 10828568195163878128681369)
    ·
      refine ⟨8121426146372908596511027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10828568195163878128681369 8121426146372908596511027)
      ·
        refine ⟨12182139219559362894766541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8121426146372908596511027 12182139219559362894766541)
        ·
          refine ⟨4568302207334761085537453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12182139219559362894766541 4568302207334761085537453)
          ·
            refine ⟨1713113327750535407076545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4568302207334761085537453 1713113327750535407076545)
            ·
              refine ⟨1284834995812901555307409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1713113327750535407076545 1284834995812901555307409)
              ·
                refine ⟨963626246859676166480557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1284834995812901555307409 963626246859676166480557)
                ·
                  refine ⟨361359842572378562430209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 963626246859676166480557 361359842572378562430209)
                  ·
                    refine ⟨271019881929283921822657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 361359842572378562430209 271019881929283921822657)
                    ·
                      refine ⟨203264911446962941366993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 271019881929283921822657 203264911446962941366993)
                      ·
                        rfl

theorem cell23_395857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 2, 3, 2, 2].length) (baseStart_395857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_395857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_395857 prefixEnd_395857 := by exact prefixLift 395857
  have htrace : WordTrace (prefixWord ++ tailWord_395857) baseStart_395857 baseEnd_395857 := by
    simpa [prefixWord, tailWord_395857, baseEnd_395857] using wordTrace_append hprefix tailTrace_395857
  have hstable : (prefixWord ++ tailWord_395857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395857).length < 2 ^ (prefixWord ++ tailWord_395857).sum := by decide
  have hdescent : baseEnd_395857 < baseStart_395857 := by decide
  rcases family_descends (prefixWord ++ tailWord_395857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395868 : List Nat := [2, 2, 4, 1, 4, 1, 1, 3, 1, 1, 3]
def baseStart_395868 : Nat := 118140960795 + 395868 * 2 ^ 59
def prefixEnd_395868 : Nat := 4983230072969 + 3 ^ 40 * 395868 * 2
def baseEnd_395868 : Nat := 203270559734162398329443

theorem tailTrace_395868 : CollatzResearch.WordTrace tailWord_395868 prefixEnd_395868 203270559734162398329443 := by
  unfold tailWord_395868
  simp only [CollatzResearch.WordTrace]
  refine ⟨7219246064922659858446129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9625661419896879811261505 7219246064922659858446129)
  ·
    refine ⟨5414434548691994893834597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7219246064922659858446129 5414434548691994893834597)
    ·
      refine ⟨1015206477879749042593987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5414434548691994893834597 1015206477879749042593987)
      ·
        refine ⟨1522809716819623563890981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1015206477879749042593987 1522809716819623563890981)
        ·
          refine ⟨285526821903679418229559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1522809716819623563890981 285526821903679418229559)
          ·
            refine ⟨428290232855519127344339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 285526821903679418229559 428290232855519127344339)
            ·
              refine ⟨642435349283278691016509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 428290232855519127344339 642435349283278691016509)
              ·
                refine ⟨240913255981229509131191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 642435349283278691016509 240913255981229509131191)
                ·
                  refine ⟨361369883971844263696787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 240913255981229509131191 361369883971844263696787)
                  ·
                    refine ⟨542054825957766395545181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 361369883971844263696787 542054825957766395545181)
                    ·
                      refine ⟨203270559734162398329443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 542054825957766395545181 203270559734162398329443)
                      ·
                        rfl

theorem cell23_395868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 3, 1, 1, 3].length) (baseStart_395868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_395868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_395868 prefixEnd_395868 := by exact prefixLift 395868
  have htrace : WordTrace (prefixWord ++ tailWord_395868) baseStart_395868 baseEnd_395868 := by
    simpa [prefixWord, tailWord_395868, baseEnd_395868] using wordTrace_append hprefix tailTrace_395868
  have hstable : (prefixWord ++ tailWord_395868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395868).length < 2 ^ (prefixWord ++ tailWord_395868).sum := by decide
  have hdescent : baseEnd_395868 < baseStart_395868 := by decide
  rcases family_descends (prefixWord ++ tailWord_395868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395880 : List Nat := [2, 1, 4, 3, 2, 2, 9]
def baseStart_395880 : Nat := 118140960795 + 395880 * 2 ^ 59
def prefixEnd_395880 : Nat := 4983230072969 + 3 ^ 40 * 395880 * 2
def baseEnd_395880 : Nat := 2509589154345880881227

theorem tailTrace_395880 : CollatzResearch.WordTrace tailWord_395880 prefixEnd_395880 2509589154345880881227 := by
  unfold tailWord_395880
  simp only [CollatzResearch.WordTrace]
  refine ⟨7219464902900922883164547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9625953203867897177552729 7219464902900922883164547)
  ·
    refine ⟨10829197354351384324746821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7219464902900922883164547 10829197354351384324746821)
    ·
      refine ⟨2030474503940884560890029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10829197354351384324746821 2030474503940884560890029)
      ·
        refine ⟨761427938977831710333761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2030474503940884560890029 761427938977831710333761)
        ·
          refine ⟨571070954233373782750321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 761427938977831710333761 571070954233373782750321)
          ·
            refine ⟨428303215675030337062741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 571070954233373782750321 428303215675030337062741)
            ·
              refine ⟨2509589154345880881227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 428303215675030337062741 2509589154345880881227)
              ·
                rfl

theorem cell23_395880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 9].length) (baseStart_395880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_395880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_395880 prefixEnd_395880 := by exact prefixLift 395880
  have htrace : WordTrace (prefixWord ++ tailWord_395880) baseStart_395880 baseEnd_395880 := by
    simpa [prefixWord, tailWord_395880, baseEnd_395880] using wordTrace_append hprefix tailTrace_395880
  have hstable : (prefixWord ++ tailWord_395880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395880).length < 2 ^ (prefixWord ++ tailWord_395880).sum := by decide
  have hdescent : baseEnd_395880 < baseStart_395880 := by decide
  rcases family_descends (prefixWord ++ tailWord_395880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395901 : List Nat := [1, 4, 1, 1, 6, 1, 2, 1, 2, 4]
def baseStart_395901 : Nat := 118140960795 + 395901 * 2 ^ 59
def prefixEnd_395901 : Nat := 4983230072969 + 3 ^ 40 * 395901 * 2
def baseEnd_395901 : Nat := 67762501531920256405597

theorem tailTrace_395901 : CollatzResearch.WordTrace tailWord_395901 prefixEnd_395901 67762501531920256405597 := by
  unfold tailWord_395901
  simp only [CollatzResearch.WordTrace]
  refine ⟨14439695738725766352843557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9626463825817177568562371 14439695738725766352843557)
  ·
    refine ⟨2707442951011081191158167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14439695738725766352843557 2707442951011081191158167)
    ·
      refine ⟨4061164426516621786737251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2707442951011081191158167 4061164426516621786737251)
      ·
        refine ⟨6091746639774932680105877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4061164426516621786737251 6091746639774932680105877)
        ·
          refine ⟨285550623739449969379963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 6091746639774932680105877 285550623739449969379963)
          ·
            refine ⟨428325935609174954069945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 285550623739449969379963 428325935609174954069945)
            ·
              refine ⟨321244451706881215552459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 428325935609174954069945 321244451706881215552459)
              ·
                refine ⟨481866677560321823328689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 321244451706881215552459 481866677560321823328689)
                ·
                  refine ⟨361400008170241367496517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 481866677560321823328689 361400008170241367496517)
                  ·
                    refine ⟨67762501531920256405597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 361400008170241367496517 67762501531920256405597)
                    ·
                      rfl

theorem cell23_395901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 2, 1, 2, 4].length) (baseStart_395901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_395901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_395901 prefixEnd_395901 := by exact prefixLift 395901
  have htrace : WordTrace (prefixWord ++ tailWord_395901) baseStart_395901 baseEnd_395901 := by
    simpa [prefixWord, tailWord_395901, baseEnd_395901] using wordTrace_append hprefix tailTrace_395901
  have hstable : (prefixWord ++ tailWord_395901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395901).length < 2 ^ (prefixWord ++ tailWord_395901).sum := by decide
  have hdescent : baseEnd_395901 < baseStart_395901 := by decide
  rcases family_descends (prefixWord ++ tailWord_395901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395964 : List Nat := [2, 2, 2, 3, 1, 1, 1, 5, 2, 2, 2]
def baseStart_395964 : Nat := 118140960795 + 395964 * 2 ^ 59
def prefixEnd_395964 : Nat := 4983230072969 + 3 ^ 40 * 395964 * 2
def baseEnd_395964 : Nat := 203319853876994022729001

theorem tailTrace_395964 : CollatzResearch.WordTrace tailWord_395964 prefixEnd_395964 203319853876994022729001 := by
  unfold tailWord_395964
  simp only [CollatzResearch.WordTrace]
  refine ⟨7220996768748764056193473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9627995691665018741591297 7220996768748764056193473)
  ·
    refine ⟨5415747576561573042145105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7220996768748764056193473 5415747576561573042145105)
    ·
      refine ⟨4061810682421179781608829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5415747576561573042145105 4061810682421179781608829)
      ·
        refine ⟨1523179005907942418103311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4061810682421179781608829 1523179005907942418103311)
        ·
          refine ⟨2284768508861913627154967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1523179005907942418103311 2284768508861913627154967)
          ·
            refine ⟨3427152763292870440732451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2284768508861913627154967 3427152763292870440732451)
            ·
              refine ⟨5140729144939305661098677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3427152763292870440732451 5140729144939305661098677)
              ·
                refine ⟨481943357338059905728001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5140729144939305661098677 481943357338059905728001)
                ·
                  refine ⟨361457518003544929296001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 481943357338059905728001 361457518003544929296001)
                  ·
                    refine ⟨271093138502658696972001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 361457518003544929296001 271093138502658696972001)
                    ·
                      refine ⟨203319853876994022729001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 271093138502658696972001 203319853876994022729001)
                      ·
                        rfl

theorem cell23_395964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 5, 2, 2, 2].length) (baseStart_395964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_395964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_395964 prefixEnd_395964 := by exact prefixLift 395964
  have htrace : WordTrace (prefixWord ++ tailWord_395964) baseStart_395964 baseEnd_395964 := by
    simpa [prefixWord, tailWord_395964, baseEnd_395964] using wordTrace_append hprefix tailTrace_395964
  have hstable : (prefixWord ++ tailWord_395964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395964).length < 2 ^ (prefixWord ++ tailWord_395964).sum := by decide
  have hdescent : baseEnd_395964 < baseStart_395964 := by decide
  rcases family_descends (prefixWord ++ tailWord_395964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396060 : List Nat := [2, 2, 3, 1, 1, 3, 2, 1, 8]
def baseStart_396060 : Nat := 118140960795 + 396060 * 2 ^ 59
def prefixEnd_396060 : Nat := 4983230072969 + 3 ^ 40 * 396060 * 2
def baseEnd_396060 : Nat := 22596572002202849680951

theorem tailTrace_396060 : CollatzResearch.WordTrace tailWord_396060 prefixEnd_396060 22596572002202849680951 := by
  unfold tailWord_396060
  simp only [CollatzResearch.WordTrace]
  refine ⟨7222747472574868253940817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9630329963433157671921089 7222747472574868253940817)
  ·
    refine ⟨5417060604431151190455613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7222747472574868253940817 5417060604431151190455613)
    ·
      refine ⟨2031397726661681696420855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5417060604431151190455613 2031397726661681696420855)
      ·
        refine ⟨3047096589992522544631283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2031397726661681696420855 3047096589992522544631283)
        ·
          refine ⟨4570644884988783816946925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3047096589992522544631283 4570644884988783816946925)
          ·
            refine ⟨1713991831870793931355097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4570644884988783816946925 1713991831870793931355097)
            ·
              refine ⟨1285493873903095448516323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1713991831870793931355097 1285493873903095448516323)
              ·
                refine ⟨1928240810854643172774485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1285493873903095448516323 1928240810854643172774485)
                ·
                  refine ⟨22596572002202849680951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1928240810854643172774485 22596572002202849680951)
                  ·
                    rfl

theorem cell23_396060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 1, 8].length) (baseStart_396060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_396060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_396060 prefixEnd_396060 := by exact prefixLift 396060
  have htrace : WordTrace (prefixWord ++ tailWord_396060) baseStart_396060 baseEnd_396060 := by
    simpa [prefixWord, tailWord_396060, baseEnd_396060] using wordTrace_append hprefix tailTrace_396060
  have hstable : (prefixWord ++ tailWord_396060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396060).length < 2 ^ (prefixWord ++ tailWord_396060).sum := by decide
  have hdescent : baseEnd_396060 < baseStart_396060 := by decide
  rcases family_descends (prefixWord ++ tailWord_396060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396064 : List Nat := [2, 1, 1, 5, 1, 4, 1, 1, 3, 4]
def baseStart_396064 : Nat := 118140960795 + 396064 * 2 ^ 59
def prefixEnd_396064 : Nat := 4983230072969 + 3 ^ 40 * 396064 * 2
def baseEnd_396064 : Nat := 67790400647481210492847

theorem tailTrace_396064 : CollatzResearch.WordTrace tailWord_396064 prefixEnd_396064 67790400647481210492847 := by
  unfold tailWord_396064
  simp only [CollatzResearch.WordTrace]
  refine ⟨7222820418567622595513623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9630427224756830127351497 7222820418567622595513623)
  ·
    refine ⟨10834230627851433893270435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7222820418567622595513623 10834230627851433893270435)
    ·
      refine ⟨16251345941777150839905653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10834230627851433893270435 16251345941777150839905653)
      ·
        refine ⟨1523563682041607891241155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16251345941777150839905653 1523563682041607891241155)
        ·
          refine ⟨2285345523062411836861733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1523563682041607891241155 2285345523062411836861733)
          ·
            refine ⟨428502285574202219411575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2285345523062411836861733 428502285574202219411575)
            ·
              refine ⟨642753428361303329117363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 428502285574202219411575 642753428361303329117363)
              ·
                refine ⟨964130142541954993676045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 642753428361303329117363 964130142541954993676045)
                ·
                  refine ⟨361548803453233122628517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 964130142541954993676045 361548803453233122628517)
                  ·
                    refine ⟨67790400647481210492847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 361548803453233122628517 67790400647481210492847)
                    ·
                      rfl

theorem cell23_396064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 1, 3, 4].length) (baseStart_396064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_396064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_396064 prefixEnd_396064 := by exact prefixLift 396064
  have htrace : WordTrace (prefixWord ++ tailWord_396064) baseStart_396064 baseEnd_396064 := by
    simpa [prefixWord, tailWord_396064, baseEnd_396064] using wordTrace_append hprefix tailTrace_396064
  have hstable : (prefixWord ++ tailWord_396064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396064).length < 2 ^ (prefixWord ++ tailWord_396064).sum := by decide
  have hdescent : baseEnd_396064 < baseStart_396064 := by decide
  rcases family_descends (prefixWord ++ tailWord_396064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396087 : List Nat := [1, 1, 3, 1, 2, 1, 4, 1, 5, 1, 3]
def baseStart_396087 : Nat := 118140960795 + 396087 * 2 ^ 59
def prefixEnd_396087 : Nat := 4983230072969 + 3 ^ 40 * 396087 * 2
def baseEnd_396087 : Nat := 203383011997497041490935

theorem tailTrace_396087 : CollatzResearch.WordTrace tailWord_396087 prefixEnd_396087 203383011997497041490935 := by
  unfold tailWord_396087
  simp only [CollatzResearch.WordTrace]
  refine ⟨14446479716051920119114515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9630986477367946746076343 14446479716051920119114515)
  ·
    refine ⟨21669719574077880178671773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14446479716051920119114515 21669719574077880178671773)
    ·
      refine ⟨8126144840279205067001915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21669719574077880178671773 8126144840279205067001915)
      ·
        refine ⟨12189217260418807600502873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8126144840279205067001915 12189217260418807600502873)
        ·
          refine ⟨9141912945314105700377155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12189217260418807600502873 9141912945314105700377155)
          ·
            refine ⟨13712869417971158550565733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9141912945314105700377155 13712869417971158550565733)
            ·
              refine ⟨2571163015869592228231075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13712869417971158550565733 2571163015869592228231075)
              ·
                refine ⟨3856744523804388342346613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2571163015869592228231075 3856744523804388342346613)
                ·
                  refine ⟨361569799106661407094995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3856744523804388342346613 361569799106661407094995)
                  ·
                    refine ⟨542354698659992110642493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 361569799106661407094995 542354698659992110642493)
                    ·
                      refine ⟨203383011997497041490935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 542354698659992110642493 203383011997497041490935)
                      ·
                        rfl

theorem cell23_396087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 5, 1, 3].length) (baseStart_396087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_396087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_396087 prefixEnd_396087 := by exact prefixLift 396087
  have htrace : WordTrace (prefixWord ++ tailWord_396087) baseStart_396087 baseEnd_396087 := by
    simpa [prefixWord, tailWord_396087, baseEnd_396087] using wordTrace_append hprefix tailTrace_396087
  have hstable : (prefixWord ++ tailWord_396087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396087).length < 2 ^ (prefixWord ++ tailWord_396087).sum := by decide
  have hdescent : baseEnd_396087 < baseStart_396087 := by decide
  rcases family_descends (prefixWord ++ tailWord_396087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396114 : List Nat := [3, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2]
def baseStart_396114 : Nat := 118140960795 + 396114 * 2 ^ 59
def prefixEnd_396114 : Nat := 4983230072969 + 3 ^ 40 * 396114 * 2
def baseEnd_396114 : Nat := 203396875975168435853311

theorem tailTrace_396114 : CollatzResearch.WordTrace tailWord_396114 prefixEnd_396114 203396875975168435853311 := by
  unfold tailWord_396114
  simp only [CollatzResearch.WordTrace]
  refine ⟨3611866121738525932586849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9631642991302735820231597 3611866121738525932586849)
  ·
    refine ⟨2708899591303894449440137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3611866121738525932586849 2708899591303894449440137)
    ·
      refine ⟨2031674693477920837080103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2708899591303894449440137 2031674693477920837080103)
      ·
        refine ⟨3047512040216881255620155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2031674693477920837080103 3047512040216881255620155)
        ·
          refine ⟨4571268060325321883430233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3047512040216881255620155 4571268060325321883430233)
          ·
            refine ⟨3428451045243991412572675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4571268060325321883430233 3428451045243991412572675)
            ·
              refine ⟨5142676567865987118859013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3428451045243991412572675 5142676567865987118859013)
              ·
                refine ⟨964251856474872584786065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5142676567865987118859013 964251856474872584786065)
                ·
                  refine ⟨723188892356154438589549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 964251856474872584786065 723188892356154438589549)
                  ·
                    refine ⟨271195834633557914471081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 723188892356154438589549 271195834633557914471081)
                    ·
                      refine ⟨203396875975168435853311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 271195834633557914471081 203396875975168435853311)
                      ·
                        rfl

theorem cell23_396114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2].length) (baseStart_396114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_396114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_396114 prefixEnd_396114 := by exact prefixLift 396114
  have htrace : WordTrace (prefixWord ++ tailWord_396114) baseStart_396114 baseEnd_396114 := by
    simpa [prefixWord, tailWord_396114, baseEnd_396114] using wordTrace_append hprefix tailTrace_396114
  have hstable : (prefixWord ++ tailWord_396114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396114).length < 2 ^ (prefixWord ++ tailWord_396114).sum := by decide
  have hdescent : baseEnd_396114 < baseStart_396114 := by decide
  rcases family_descends (prefixWord ++ tailWord_396114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396121 : List Nat := [1, 2, 1, 2, 2, 5, 1, 4, 1, 1, 3]
def baseStart_396121 : Nat := 118140960795 + 396121 * 2 ^ 59
def prefixEnd_396121 : Nat := 4983230072969 + 3 ^ 40 * 396121 * 2
def baseEnd_396121 : Nat := 203400470339749908465779

theorem tailTrace_396121 : CollatzResearch.WordTrace tailWord_396121 prefixEnd_396121 203400470339749908465779 := by
  unfold tailWord_396121
  simp only [CollatzResearch.WordTrace]
  refine ⟨14447719797928743925852217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9631813198619162617234811 14447719797928743925852217)
  ·
    refine ⟨10835789848446557944389163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14447719797928743925852217 10835789848446557944389163)
    ·
      refine ⟨16253684772669836916583745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10835789848446557944389163 16253684772669836916583745)
      ·
        refine ⟨12190263579502377687437809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16253684772669836916583745 12190263579502377687437809)
        ·
          refine ⟨9142697684626783265578357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12190263579502377687437809 9142697684626783265578357)
          ·
            refine ⟨857127907933760931147971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9142697684626783265578357 857127907933760931147971)
            ·
              refine ⟨1285691861900641396721957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 857127907933760931147971 1285691861900641396721957)
              ·
                refine ⟨241067224106370261885367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1285691861900641396721957 241067224106370261885367)
                ·
                  refine ⟨361600836159555392828051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 241067224106370261885367 361600836159555392828051)
                  ·
                    refine ⟨542401254239333089242077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 361600836159555392828051 542401254239333089242077)
                    ·
                      refine ⟨203400470339749908465779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 542401254239333089242077 203400470339749908465779)
                      ·
                        rfl

theorem cell23_396121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 4, 1, 1, 3].length) (baseStart_396121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_396121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_396121 prefixEnd_396121 := by exact prefixLift 396121
  have htrace : WordTrace (prefixWord ++ tailWord_396121) baseStart_396121 baseEnd_396121 := by
    simpa [prefixWord, tailWord_396121, baseEnd_396121] using wordTrace_append hprefix tailTrace_396121
  have hstable : (prefixWord ++ tailWord_396121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396121).length < 2 ^ (prefixWord ++ tailWord_396121).sum := by decide
  have hdescent : baseEnd_396121 < baseStart_396121 := by decide
  rcases family_descends (prefixWord ++ tailWord_396121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396144 : List Nat := [2, 1, 1, 1, 4, 1, 3, 1, 5, 2, 2]
def baseStart_396144 : Nat := 118140960795 + 396144 * 2 ^ 59
def prefixEnd_396144 : Nat := 4983230072969 + 3 ^ 40 * 396144 * 2
def baseEnd_396144 : Nat := 203412280394803318478173

theorem tailTrace_396144 : CollatzResearch.WordTrace tailWord_396144 prefixEnd_396144 203412280394803318478173 := by
  unfold tailWord_396144
  simp only [CollatzResearch.WordTrace]
  refine ⟨7224279338422709426969743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9632372451230279235959657 7224279338422709426969743)
  ·
    refine ⟨10836419007634064140454615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7224279338422709426969743 10836419007634064140454615)
    ·
      refine ⟨16254628511451096210681923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10836419007634064140454615 16254628511451096210681923)
      ·
        refine ⟨24381942767176644316022885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16254628511451096210681923 24381942767176644316022885)
        ·
          refine ⟨4571614268845620809254291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24381942767176644316022885 4571614268845620809254291)
          ·
            refine ⟨6857421403268431213881437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4571614268845620809254291 6857421403268431213881437)
            ·
              refine ⟨2571533026225661705205539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6857421403268431213881437 2571533026225661705205539)
              ·
                refine ⟨3857299539338492557808309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2571533026225661705205539 3857299539338492557808309)
                ·
                  refine ⟨361621831812983677294529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3857299539338492557808309 361621831812983677294529)
                  ·
                    refine ⟨271216373859737757970897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 361621831812983677294529 271216373859737757970897)
                    ·
                      refine ⟨203412280394803318478173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 271216373859737757970897 203412280394803318478173)
                      ·
                        rfl

theorem cell23_396144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 5, 2, 2].length) (baseStart_396144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_396144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_396144 prefixEnd_396144 := by exact prefixLift 396144
  have htrace : WordTrace (prefixWord ++ tailWord_396144) baseStart_396144 baseEnd_396144 := by
    simpa [prefixWord, tailWord_396144, baseEnd_396144] using wordTrace_append hprefix tailTrace_396144
  have hstable : (prefixWord ++ tailWord_396144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396144).length < 2 ^ (prefixWord ++ tailWord_396144).sum := by decide
  have hdescent : baseEnd_396144 < baseStart_396144 := by decide
  rcases family_descends (prefixWord ++ tailWord_396144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396147 : List Nat := [1, 1, 1, 2, 2, 1, 6, 1, 3, 2, 3]
def baseStart_396147 : Nat := 118140960795 + 396147 * 2 ^ 59
def prefixEnd_396147 : Nat := 4983230072969 + 3 ^ 40 * 396147 * 2
def baseEnd_396147 : Nat := 203413820836766806740659

theorem tailTrace_396147 : CollatzResearch.WordTrace tailWord_396147 prefixEnd_396147 203413820836766806740659 := by
  unfold tailWord_396147
  simp only [CollatzResearch.WordTrace]
  refine ⟨14448668095834550366298695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9632445397223033577532463 14448668095834550366298695)
  ·
    refine ⟨21673002143751825549448043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14448668095834550366298695 21673002143751825549448043)
    ·
      refine ⟨32509503215627738324172065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21673002143751825549448043 32509503215627738324172065)
      ·
        refine ⟨24382127411720803743129049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32509503215627738324172065 24382127411720803743129049)
        ·
          refine ⟨18286595558790602807346787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24382127411720803743129049 18286595558790602807346787)
          ·
            refine ⟨27429893338185904211020181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18286595558790602807346787 27429893338185904211020181)
            ·
              refine ⟨1285776250227464259891571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 27429893338185904211020181 1285776250227464259891571)
              ·
                refine ⟨1928664375341196389837357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1285776250227464259891571 1928664375341196389837357)
                ·
                  refine ⟨723249140752948646189009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1928664375341196389837357 723249140752948646189009)
                  ·
                    refine ⟨542436855564711484641757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 723249140752948646189009 542436855564711484641757)
                    ·
                      refine ⟨203413820836766806740659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 542436855564711484641757 203413820836766806740659)
                      ·
                        rfl

theorem cell23_396147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 1, 3, 2, 3].length) (baseStart_396147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_396147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_396147 prefixEnd_396147 := by exact prefixLift 396147
  have htrace : WordTrace (prefixWord ++ tailWord_396147) baseStart_396147 baseEnd_396147 := by
    simpa [prefixWord, tailWord_396147, baseEnd_396147] using wordTrace_append hprefix tailTrace_396147
  have hstable : (prefixWord ++ tailWord_396147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396147).length < 2 ^ (prefixWord ++ tailWord_396147).sum := by decide
  have hdescent : baseEnd_396147 < baseStart_396147 := by decide
  rcases family_descends (prefixWord ++ tailWord_396147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396157 : List Nat := [1, 4, 1, 1, 2, 1, 4, 2, 1, 2, 4]
def baseStart_396157 : Nat := 118140960795 + 396157 * 2 ^ 59
def prefixEnd_396157 : Nat := 4983230072969 + 3 ^ 40 * 396157 * 2
def baseEnd_396157 : Nat := 203418955643311767615613

theorem tailTrace_396157 : CollatzResearch.WordTrace tailWord_396157 prefixEnd_396157 203418955643311767615613 := by
  unfold tailWord_396157
  simp only [CollatzResearch.WordTrace]
  refine ⟨14449032825798322074162725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9632688550532214716108483 14449032825798322074162725)
  ·
    refine ⟨2709193654837185388905511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14449032825798322074162725 2709193654837185388905511)
    ·
      refine ⟨4063790482255778083358267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2709193654837185388905511 4063790482255778083358267)
      ·
        refine ⟨6095685723383667125037401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4063790482255778083358267 6095685723383667125037401)
        ·
          refine ⟨4571764292537750343778051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6095685723383667125037401 4571764292537750343778051)
          ·
            refine ⟨6857646438806625515667077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4571764292537750343778051 6857646438806625515667077)
            ·
              refine ⟨1285808707276242284187577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6857646438806625515667077 1285808707276242284187577)
              ·
                refine ⟨964356530457181713140683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1285808707276242284187577 964356530457181713140683)
                ·
                  refine ⟨1446534795685772569711025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 964356530457181713140683 1446534795685772569711025)
                  ·
                    refine ⟨1084901096764329427283269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1446534795685772569711025 1084901096764329427283269)
                    ·
                      refine ⟨203418955643311767615613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1084901096764329427283269 203418955643311767615613)
                      ·
                        rfl

theorem cell23_396157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 2, 1, 2, 4].length) (baseStart_396157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_396157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_396157 prefixEnd_396157 := by exact prefixLift 396157
  have htrace : WordTrace (prefixWord ++ tailWord_396157) baseStart_396157 baseEnd_396157 := by
    simpa [prefixWord, tailWord_396157, baseEnd_396157] using wordTrace_append hprefix tailTrace_396157
  have hstable : (prefixWord ++ tailWord_396157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396157).length < 2 ^ (prefixWord ++ tailWord_396157).sum := by decide
  have hdescent : baseEnd_396157 < baseStart_396157 := by decide
  rcases family_descends (prefixWord ++ tailWord_396157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396188 : List Nat := [2, 2, 3, 3, 2, 1, 3, 1, 2, 4]
def baseStart_396188 : Nat := 118140960795 + 396188 * 2 ^ 59
def prefixEnd_396188 : Nat := 4983230072969 + 3 ^ 40 * 396188 * 2
def baseEnd_396188 : Nat := 67811624514533715442657

theorem tailTrace_396188 : CollatzResearch.WordTrace tailWord_396188 prefixEnd_396188 67811624514533715442657 := by
  unfold tailWord_396188
  simp only [CollatzResearch.WordTrace]
  refine ⟨7225081744343007184270609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9633442325790676245694145 7225081744343007184270609)
  ·
    refine ⟨5418811308257255388202957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7225081744343007184270609 5418811308257255388202957)
    ·
      refine ⟨2032054240596470770576109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5418811308257255388202957 2032054240596470770576109)
      ·
        refine ⟨762020340223676538966041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2032054240596470770576109 762020340223676538966041)
        ·
          refine ⟨571515255167757404224531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 762020340223676538966041 571515255167757404224531)
          ·
            refine ⟨857272882751636106336797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 571515255167757404224531 857272882751636106336797)
            ·
              refine ⟨321477331031863539876299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 857272882751636106336797 321477331031863539876299)
              ·
                refine ⟨482215996547795309814449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 321477331031863539876299 482215996547795309814449)
                ·
                  refine ⟨361661997410846482360837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 482215996547795309814449 361661997410846482360837)
                  ·
                    refine ⟨67811624514533715442657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 361661997410846482360837 67811624514533715442657)
                    ·
                      rfl

theorem cell23_396188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 3, 1, 2, 4].length) (baseStart_396188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_396188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_396188 prefixEnd_396188 := by exact prefixLift 396188
  have htrace : WordTrace (prefixWord ++ tailWord_396188) baseStart_396188 baseEnd_396188 := by
    simpa [prefixWord, tailWord_396188, baseEnd_396188] using wordTrace_append hprefix tailTrace_396188
  have hstable : (prefixWord ++ tailWord_396188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396188).length < 2 ^ (prefixWord ++ tailWord_396188).sum := by decide
  have hdescent : baseEnd_396188 < baseStart_396188 := by decide
  rcases family_descends (prefixWord ++ tailWord_396188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396212 : List Nat := [2, 5, 2, 1, 1, 1, 3, 3, 1, 2, 2]
def baseStart_396212 : Nat := 118140960795 + 396212 * 2 ^ 59
def prefixEnd_396212 : Nat := 4983230072969 + 3 ^ 40 * 396212 * 2
def baseEnd_396212 : Nat := 203447197079309052427861

theorem tailTrace_396212 : CollatzResearch.WordTrace tailWord_396212 prefixEnd_396212 203447197079309052427861 := by
  unfold tailWord_396212
  simp only [CollatzResearch.WordTrace]
  refine ⟨7225519420299533233707445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9634025893732710978276593 7225519420299533233707445)
  ·
    refine ⟨677392445653081240660073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7225519420299533233707445 677392445653081240660073)
    ·
      refine ⟨508044334239810930495055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 677392445653081240660073 508044334239810930495055)
      ·
        refine ⟨762066501359716395742583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 508044334239810930495055 762066501359716395742583)
        ·
          refine ⟨1143099752039574593613875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 762066501359716395742583 1143099752039574593613875)
          ·
            refine ⟨1714649628059361890420813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1143099752039574593613875 1714649628059361890420813)
            ·
              refine ⟨642993610522260708907805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1714649628059361890420813 642993610522260708907805)
              ·
                refine ⟨241122603945847765840427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 642993610522260708907805 241122603945847765840427)
                ·
                  refine ⟨361683905918771648760641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 241122603945847765840427 361683905918771648760641)
                  ·
                    refine ⟨271262929439078736570481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 361683905918771648760641 271262929439078736570481)
                    ·
                      refine ⟨203447197079309052427861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 271262929439078736570481 203447197079309052427861)
                      ·
                        rfl

theorem cell23_396212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_396212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_396212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_396212 prefixEnd_396212 := by exact prefixLift 396212
  have htrace : WordTrace (prefixWord ++ tailWord_396212) baseStart_396212 baseEnd_396212 := by
    simpa [prefixWord, tailWord_396212, baseEnd_396212] using wordTrace_append hprefix tailTrace_396212
  have hstable : (prefixWord ++ tailWord_396212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396212).length < 2 ^ (prefixWord ++ tailWord_396212).sum := by decide
  have hdescent : baseEnd_396212 < baseStart_396212 := by decide
  rcases family_descends (prefixWord ++ tailWord_396212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396245 : List Nat := [1, 3, 2, 3, 3, 2, 2, 1, 2, 1, 3]
def baseStart_396245 : Nat := 118140960795 + 396245 * 2 ^ 59
def prefixEnd_396245 : Nat := 4983230072969 + 3 ^ 40 * 396245 * 2
def baseEnd_396245 : Nat := 203464141940907423315209

theorem tailTrace_396245 : CollatzResearch.WordTrace tailWord_396245 prefixEnd_396245 203464141940907423315209 := by
  unfold tailWord_396245
  simp only [CollatzResearch.WordTrace]
  refine ⟨14452242449479513103366189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9634828299653008735577459 14452242449479513103366189)
  ·
    refine ⟨5419590918554817413762321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14452242449479513103366189 5419590918554817413762321)
    ·
      refine ⟨4064693188916113060321741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5419590918554817413762321 4064693188916113060321741)
      ·
        refine ⟨1524259945843542397620653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4064693188916113060321741 1524259945843542397620653)
        ·
          refine ⟨571597479691328399107745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1524259945843542397620653 571597479691328399107745)
          ·
            refine ⟨428698109768496299330809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 571597479691328399107745 428698109768496299330809)
            ·
              refine ⟨321523582326372224498107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 428698109768496299330809 321523582326372224498107)
              ·
                refine ⟨482285373489558336747161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 321523582326372224498107 482285373489558336747161)
                ·
                  refine ⟨361714030117168752560371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 482285373489558336747161 361714030117168752560371)
                  ·
                    refine ⟨542571045175753128840557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 361714030117168752560371 542571045175753128840557)
                    ·
                      refine ⟨203464141940907423315209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 542571045175753128840557 203464141940907423315209)
                      ·
                        rfl

theorem cell23_396245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 2, 1, 2, 1, 3].length) (baseStart_396245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_396245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_396245 prefixEnd_396245 := by exact prefixLift 396245
  have htrace : WordTrace (prefixWord ++ tailWord_396245) baseStart_396245 baseEnd_396245 := by
    simpa [prefixWord, tailWord_396245, baseEnd_396245] using wordTrace_append hprefix tailTrace_396245
  have hstable : (prefixWord ++ tailWord_396245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396245).length < 2 ^ (prefixWord ++ tailWord_396245).sum := by decide
  have hdescent : baseEnd_396245 < baseStart_396245 := by decide
  rcases family_descends (prefixWord ++ tailWord_396245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396255 : List Nat := [1, 1, 2, 3, 6, 1, 1, 2, 1, 3, 2]
def baseStart_396255 : Nat := 118140960795 + 396255 * 2 ^ 59
def prefixEnd_396255 : Nat := 4983230072969 + 3 ^ 40 * 396255 * 2
def baseEnd_396255 : Nat := 203469276747452384190163

theorem tailTrace_396255 : CollatzResearch.WordTrace tailWord_396255 prefixEnd_396255 203469276747452384190163 := by
  unfold tailWord_396255
  simp only [CollatzResearch.WordTrace]
  refine ⟨14452607179443284811230219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9635071452962189874153479 14452607179443284811230219)
  ·
    refine ⟨21678910769164927216845329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14452607179443284811230219 21678910769164927216845329)
    ·
      refine ⟨16259183076873695412633997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21678910769164927216845329 16259183076873695412633997)
      ·
        refine ⟨6097193653827635779737749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16259183076873695412633997 6097193653827635779737749)
        ·
          refine ⟨285805952523170427175207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 6097193653827635779737749 285805952523170427175207)
          ·
            refine ⟨428708928784755640762811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 285805952523170427175207 428708928784755640762811)
            ·
              refine ⟨643063393177133461144217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 428708928784755640762811 643063393177133461144217)
              ·
                refine ⟨482297544882850095858163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 643063393177133461144217 482297544882850095858163)
                ·
                  refine ⟨723446317324275143787245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 482297544882850095858163 723446317324275143787245)
                  ·
                    refine ⟨271292368996603178920217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 723446317324275143787245 271292368996603178920217)
                    ·
                      refine ⟨203469276747452384190163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 271292368996603178920217 203469276747452384190163)
                      ·
                        rfl

theorem cell23_396255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 2, 1, 3, 2].length) (baseStart_396255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_396255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_396255 prefixEnd_396255 := by exact prefixLift 396255
  have htrace : WordTrace (prefixWord ++ tailWord_396255) baseStart_396255 baseEnd_396255 := by
    simpa [prefixWord, tailWord_396255, baseEnd_396255] using wordTrace_append hprefix tailTrace_396255
  have hstable : (prefixWord ++ tailWord_396255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396255).length < 2 ^ (prefixWord ++ tailWord_396255).sum := by decide
  have hdescent : baseEnd_396255 < baseStart_396255 := by decide
  rcases family_descends (prefixWord ++ tailWord_396255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396267 : List Nat := [1, 1, 1, 1, 2, 3, 1, 1, 6, 3, 3]
def baseStart_396267 : Nat := 118140960795 + 396267 * 2 ^ 59
def prefixEnd_396267 : Nat := 4983230072969 + 3 ^ 40 * 396267 * 2
def baseEnd_396267 : Nat := 203475438515306337240107

theorem tailTrace_396267 : CollatzResearch.WordTrace tailWord_396267 prefixEnd_396267 203475438515306337240107 := by
  unfold tailWord_396267
  simp only [CollatzResearch.WordTrace]
  refine ⟨14453044855399810860667055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9635363236933207240444703 14453044855399810860667055)
  ·
    refine ⟨21679567283099716291000583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14453044855399810860667055 21679567283099716291000583)
    ·
      refine ⟨32519350924649574436500875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21679567283099716291000583 32519350924649574436500875)
      ·
        refine ⟨48779026386974361654751313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32519350924649574436500875 48779026386974361654751313)
        ·
          refine ⟨36584269790230771241063485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48779026386974361654751313 36584269790230771241063485)
          ·
            refine ⟨13719101171336539215398807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36584269790230771241063485 13719101171336539215398807)
            ·
              refine ⟨20578651757004808823098211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13719101171336539215398807 20578651757004808823098211)
              ·
                refine ⟨30867977635507213234647317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20578651757004808823098211 30867977635507213234647317)
                ·
                  refine ⟨1446936451664400620374093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 30867977635507213234647317 1446936451664400620374093)
                  ·
                    refine ⟨542601169374150232640285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1446936451664400620374093 542601169374150232640285)
                    ·
                      refine ⟨203475438515306337240107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 542601169374150232640285 203475438515306337240107)
                      ·
                        rfl

theorem cell23_396267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 6, 3, 3].length) (baseStart_396267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_396267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_396267 prefixEnd_396267 := by exact prefixLift 396267
  have htrace : WordTrace (prefixWord ++ tailWord_396267) baseStart_396267 baseEnd_396267 := by
    simpa [prefixWord, tailWord_396267, baseEnd_396267] using wordTrace_append hprefix tailTrace_396267
  have hstable : (prefixWord ++ tailWord_396267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396267).length < 2 ^ (prefixWord ++ tailWord_396267).sum := by decide
  have hdescent : baseEnd_396267 < baseStart_396267 := by decide
  rcases family_descends (prefixWord ++ tailWord_396267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396307 : List Nat := [1, 1, 1, 2, 1, 4, 1, 4, 1, 3, 4]
def baseStart_396307 : Nat := 118140960795 + 396307 * 2 ^ 59
def prefixEnd_396307 : Nat := 4983230072969 + 3 ^ 40 * 396307 * 2
def baseEnd_396307 : Nat := 203495977741486180739923

theorem tailTrace_396307 : CollatzResearch.WordTrace tailWord_396307 prefixEnd_396307 203495977741486180739923 := by
  unfold tailWord_396307
  simp only [CollatzResearch.WordTrace]
  refine ⟨14454503775254897692123175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9636335850169931794748783 14454503775254897692123175)
  ·
    refine ⟨21681755662882346538184763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14454503775254897692123175 21681755662882346538184763)
    ·
      refine ⟨32522633494323519807277145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21681755662882346538184763 32522633494323519807277145)
      ·
        refine ⟨24391975120742639855457859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32522633494323519807277145 24391975120742639855457859)
        ·
          refine ⟨36587962681113959783186789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24391975120742639855457859 36587962681113959783186789)
          ·
            refine ⟨6860243002708867459347523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36587962681113959783186789 6860243002708867459347523)
            ·
              refine ⟨10290364504063301189021285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6860243002708867459347523 10290364504063301189021285)
              ·
                refine ⟨1929443344511868972941491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10290364504063301189021285 1929443344511868972941491)
                ·
                  refine ⟨2894165016767803459412237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1929443344511868972941491 2894165016767803459412237)
                  ·
                    refine ⟨1085311881287926297279589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2894165016767803459412237 1085311881287926297279589)
                    ·
                      refine ⟨203495977741486180739923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1085311881287926297279589 203495977741486180739923)
                      ·
                        rfl

theorem cell23_396307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 4, 1, 3, 4].length) (baseStart_396307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_396307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_396307 prefixEnd_396307 := by exact prefixLift 396307
  have htrace : WordTrace (prefixWord ++ tailWord_396307) baseStart_396307 baseEnd_396307 := by
    simpa [prefixWord, tailWord_396307, baseEnd_396307] using wordTrace_append hprefix tailTrace_396307
  have hstable : (prefixWord ++ tailWord_396307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396307).length < 2 ^ (prefixWord ++ tailWord_396307).sum := by decide
  have hdescent : baseEnd_396307 < baseStart_396307 := by decide
  rcases family_descends (prefixWord ++ tailWord_396307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396321 : List Nat := [1, 2, 3, 2, 3, 3, 1, 1, 2, 5]
def baseStart_396321 : Nat := 118140960795 + 396321 * 2 ^ 59
def prefixEnd_396321 : Nat := 4983230072969 + 3 ^ 40 * 396321 * 2
def baseEnd_396321 : Nat := 67834388823549708654953

theorem tailTrace_396321 : CollatzResearch.WordTrace tailWord_396321 prefixEnd_396321 67834388823549708654953 := by
  unfold tailWord_396321
  simp only [CollatzResearch.WordTrace]
  refine ⟨14455014397204178083132817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9636676264802785388755211 14455014397204178083132817)
  ·
    refine ⟨10841260797903133562349613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14455014397204178083132817 10841260797903133562349613)
    ·
      refine ⟨4065472799213675085881105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10841260797903133562349613 4065472799213675085881105)
      ·
        refine ⟨3049104599410256314410829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4065472799213675085881105 3049104599410256314410829)
        ·
          refine ⟨1143414224778846117904061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3049104599410256314410829 1143414224778846117904061)
          ·
            refine ⟨428780334292067294214023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1143414224778846117904061 428780334292067294214023)
            ·
              refine ⟨643170501438100941321035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 428780334292067294214023 643170501438100941321035)
              ·
                refine ⟨964755752157151411981553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 643170501438100941321035 964755752157151411981553)
                ·
                  refine ⟨723566814117863558986165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 964755752157151411981553 723566814117863558986165)
                  ·
                    refine ⟨67834388823549708654953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 723566814117863558986165 67834388823549708654953)
                    ·
                      rfl

theorem cell23_396321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 1, 2, 5].length) (baseStart_396321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_396321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_396321 prefixEnd_396321 := by exact prefixLift 396321
  have htrace : WordTrace (prefixWord ++ tailWord_396321) baseStart_396321 baseEnd_396321 := by
    simpa [prefixWord, tailWord_396321, baseEnd_396321] using wordTrace_append hprefix tailTrace_396321
  have hstable : (prefixWord ++ tailWord_396321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396321).length < 2 ^ (prefixWord ++ tailWord_396321).sum := by decide
  have hdescent : baseEnd_396321 < baseStart_396321 := by decide
  rcases family_descends (prefixWord ++ tailWord_396321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396337 : List Nat := [1, 2, 2, 3, 1, 2, 1, 1, 1, 3, 6]
def baseStart_396337 : Nat := 118140960795 + 396337 * 2 ^ 59
def prefixEnd_396337 : Nat := 4983230072969 + 3 ^ 40 * 396337 * 2
def baseEnd_396337 : Nat := 203511382161121063364785

theorem tailTrace_396337 : CollatzResearch.WordTrace tailWord_396337 prefixEnd_396337 203511382161121063364785 := by
  unfold tailWord_396337
  simp only [CollatzResearch.WordTrace]
  refine ⟨14455597965146212815715265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9637065310097475210476843 14455597965146212815715265)
  ·
    refine ⟨10841698473859659611786449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14455597965146212815715265 10841698473859659611786449)
    ·
      refine ⟨8131273855394744708839837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10841698473859659611786449 8131273855394744708839837)
      ·
        refine ⟨3049227695773029265814939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8131273855394744708839837 3049227695773029265814939)
        ·
          refine ⟨4573841543659543898722409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3049227695773029265814939 4573841543659543898722409)
          ·
            refine ⟨3430381157744657924041807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4573841543659543898722409 3430381157744657924041807)
            ·
              refine ⟨5145571736616986886062711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3430381157744657924041807 5145571736616986886062711)
              ·
                refine ⟨7718357604925480329094067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5145571736616986886062711 7718357604925480329094067)
                ·
                  refine ⟨11577536407388220493641101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7718357604925480329094067 11577536407388220493641101)
                  ·
                    refine ⟨4341576152770582685115413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11577536407388220493641101 4341576152770582685115413)
                    ·
                      refine ⟨203511382161121063364785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4341576152770582685115413 203511382161121063364785)
                      ·
                        rfl

theorem cell23_396337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_396337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_396337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_396337 prefixEnd_396337 := by exact prefixLift 396337
  have htrace : WordTrace (prefixWord ++ tailWord_396337) baseStart_396337 baseEnd_396337 := by
    simpa [prefixWord, tailWord_396337, baseEnd_396337] using wordTrace_append hprefix tailTrace_396337
  have hstable : (prefixWord ++ tailWord_396337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396337).length < 2 ^ (prefixWord ++ tailWord_396337).sum := by decide
  have hdescent : baseEnd_396337 < baseStart_396337 := by decide
  rcases family_descends (prefixWord ++ tailWord_396337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396408 : List Nat := [2, 1, 2, 1, 1, 1, 4, 6, 1, 1, 3]
def baseStart_396408 : Nat := 118140960795 + 396408 * 2 ^ 59
def prefixEnd_396408 : Nat := 4983230072969 + 3 ^ 40 * 396408 * 2
def baseEnd_396408 : Nat := 203547839287590285576959

theorem tailTrace_396408 : CollatzResearch.WordTrace tailWord_396408 prefixEnd_396408 203547839287590285576959 := by
  unfold tailWord_396408
  simp only [CollatzResearch.WordTrace]
  refine ⟨7229093773944495970774939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9638791698592661294366585 7229093773944495970774939)
  ·
    refine ⟨10843640660916743956162409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7229093773944495970774939 10843640660916743956162409)
    ·
      refine ⟨8132730495687557967121807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10843640660916743956162409 8132730495687557967121807)
      ·
        refine ⟨12199095743531336950682711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8132730495687557967121807 12199095743531336950682711)
        ·
          refine ⟨18298643615297005426024067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12199095743531336950682711 18298643615297005426024067)
          ·
            refine ⟨27447965422945508139036101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18298643615297005426024067 27447965422945508139036101)
            ·
              refine ⟨5146493516802282776069269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27447965422945508139036101 5146493516802282776069269)
              ·
                refine ⟨241241883600107005128247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5146493516802282776069269 241241883600107005128247)
                ·
                  refine ⟨361862825400160507692371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 241241883600107005128247 361862825400160507692371)
                  ·
                    refine ⟨542794238100240761538557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 361862825400160507692371 542794238100240761538557)
                    ·
                      refine ⟨203547839287590285576959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 542794238100240761538557 203547839287590285576959)
                      ·
                        rfl

theorem cell23_396408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 6, 1, 1, 3].length) (baseStart_396408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_396408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_396408 prefixEnd_396408 := by exact prefixLift 396408
  have htrace : WordTrace (prefixWord ++ tailWord_396408) baseStart_396408 baseEnd_396408 := by
    simpa [prefixWord, tailWord_396408, baseEnd_396408] using wordTrace_append hprefix tailTrace_396408
  have hstable : (prefixWord ++ tailWord_396408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396408).length < 2 ^ (prefixWord ++ tailWord_396408).sum := by decide
  have hdescent : baseEnd_396408 < baseStart_396408 := by decide
  rcases family_descends (prefixWord ++ tailWord_396408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396448 : List Nat := [2, 1, 1, 4, 2, 1, 5, 1, 1, 1, 4]
def baseStart_396448 : Nat := 118140960795 + 396448 * 2 ^ 59
def prefixEnd_396448 : Nat := 4983230072969 + 3 ^ 40 * 396448 * 2
def baseEnd_396448 : Nat := 203568378513770129076775

theorem tailTrace_396448 : CollatzResearch.WordTrace tailWord_396448 prefixEnd_396448 203568378513770129076775 := by
  unfold tailWord_396448
  simp only [CollatzResearch.WordTrace]
  refine ⟨7229823233872039386502999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9639764311829385848670665 7229823233872039386502999)
  ·
    refine ⟨10844734850808059079754499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7229823233872039386502999 10844734850808059079754499)
    ·
      refine ⟨16267102276212088619631749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10844734850808059079754499 16267102276212088619631749)
      ·
        refine ⟨3050081676789766616180953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16267102276212088619631749 3050081676789766616180953)
        ·
          refine ⟨2287561257592324962135715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3050081676789766616180953 2287561257592324962135715)
          ·
            refine ⟨3431341886388487443203573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2287561257592324962135715 3431341886388487443203573)
            ·
              refine ⟨321688301848920697800335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3431341886388487443203573 321688301848920697800335)
              ·
                refine ⟨482532452773381046700503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 321688301848920697800335 482532452773381046700503)
                ·
                  refine ⟨723798679160071570050755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 482532452773381046700503 723798679160071570050755)
                  ·
                    refine ⟨1085698018740107355076133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 723798679160071570050755 1085698018740107355076133)
                    ·
                      refine ⟨203568378513770129076775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1085698018740107355076133 203568378513770129076775)
                      ·
                        rfl

theorem cell23_396448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 5, 1, 1, 1, 4].length) (baseStart_396448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_396448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_396448 prefixEnd_396448 := by exact prefixLift 396448
  have htrace : WordTrace (prefixWord ++ tailWord_396448) baseStart_396448 baseEnd_396448 := by
    simpa [prefixWord, tailWord_396448, baseEnd_396448] using wordTrace_append hprefix tailTrace_396448
  have hstable : (prefixWord ++ tailWord_396448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396448).length < 2 ^ (prefixWord ++ tailWord_396448).sum := by decide
  have hdescent : baseEnd_396448 < baseStart_396448 := by decide
  rcases family_descends (prefixWord ++ tailWord_396448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396451 : List Nat := [1, 1, 1, 4, 1, 1, 1, 7, 1, 2, 3]
def baseStart_396451 : Nat := 118140960795 + 396451 * 2 ^ 59
def prefixEnd_396451 : Nat := 4983230072969 + 3 ^ 40 * 396451 * 2
def baseEnd_396451 : Nat := 203569918955733617339261

theorem tailTrace_396451 : CollatzResearch.WordTrace tailWord_396451 prefixEnd_396451 203569918955733617339261 := by
  unfold tailWord_396451
  simp only [CollatzResearch.WordTrace]
  refine ⟨14459755886733210285365207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9639837257822140190243471 14459755886733210285365207)
  ·
    refine ⟨21689633830099815428047811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14459755886733210285365207 21689633830099815428047811)
    ·
      refine ⟨32534450745149723142071717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21689633830099815428047811 32534450745149723142071717)
      ·
        refine ⟨6100209514715573089138447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32534450745149723142071717 6100209514715573089138447)
        ·
          refine ⟨9150314272073359633707671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6100209514715573089138447 9150314272073359633707671)
          ·
            refine ⟨13725471408110039450561507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9150314272073359633707671 13725471408110039450561507)
            ·
              refine ⟨20588207112165059175842261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13725471408110039450561507 20588207112165059175842261)
              ·
                refine ⟨482536104191368574433803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 20588207112165059175842261 482536104191368574433803)
                ·
                  refine ⟨723804156287052861650705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 482536104191368574433803 723804156287052861650705)
                  ·
                    refine ⟨542853117215289646238029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 723804156287052861650705 542853117215289646238029)
                    ·
                      refine ⟨203569918955733617339261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 542853117215289646238029 203569918955733617339261)
                      ·
                        rfl

theorem cell23_396451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 7, 1, 2, 3].length) (baseStart_396451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_396451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_396451 prefixEnd_396451 := by exact prefixLift 396451
  have htrace : WordTrace (prefixWord ++ tailWord_396451) baseStart_396451 baseEnd_396451 := by
    simpa [prefixWord, tailWord_396451, baseEnd_396451] using wordTrace_append hprefix tailTrace_396451
  have hstable : (prefixWord ++ tailWord_396451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396451).length < 2 ^ (prefixWord ++ tailWord_396451).sum := by decide
  have hdescent : baseEnd_396451 < baseStart_396451 := by decide
  rcases family_descends (prefixWord ++ tailWord_396451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396478 : List Nat := [4, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4]
def baseStart_396478 : Nat := 118140960795 + 396478 * 2 ^ 59
def prefixEnd_396478 : Nat := 4983230072969 + 3 ^ 40 * 396478 * 2
def baseEnd_396478 : Nat := 203583782933405011701637

theorem tailTrace_396478 : CollatzResearch.WordTrace tailWord_396478 prefixEnd_396478 203583782933405011701637 := by
  unfold tailWord_396478
  simp only [CollatzResearch.WordTrace]
  refine ⟨1807592582204424237074761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9640493771756929264398725 1807592582204424237074761)
  ·
    refine ⟨1355694436653318177806071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1807592582204424237074761 1355694436653318177806071)
    ·
      refine ⟨2033541654979977266709107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1355694436653318177806071 2033541654979977266709107)
      ·
        refine ⟨3050312482469965900063661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2033541654979977266709107 3050312482469965900063661)
        ·
          refine ⟨1143867180926237212523873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3050312482469965900063661 1143867180926237212523873)
          ·
            refine ⟨857900385694677909392905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1143867180926237212523873 857900385694677909392905)
            ·
              refine ⟨643425289271008432044679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 857900385694677909392905 643425289271008432044679)
              ·
                refine ⟨965137933906512648067019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 643425289271008432044679 965137933906512648067019)
                ·
                  refine ⟨1447706900859768972100529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 965137933906512648067019 1447706900859768972100529)
                  ·
                    refine ⟨1085780175644826729075397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1447706900859768972100529 1085780175644826729075397)
                    ·
                      refine ⟨203583782933405011701637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1085780175644826729075397 203583782933405011701637)
                      ·
                        rfl

theorem cell23_396478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4].length) (baseStart_396478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_396478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_396478 prefixEnd_396478 := by exact prefixLift 396478
  have htrace : WordTrace (prefixWord ++ tailWord_396478) baseStart_396478 baseEnd_396478 := by
    simpa [prefixWord, tailWord_396478, baseEnd_396478] using wordTrace_append hprefix tailTrace_396478
  have hstable : (prefixWord ++ tailWord_396478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396478).length < 2 ^ (prefixWord ++ tailWord_396478).sum := by decide
  have hdescent : baseEnd_396478 < baseStart_396478 := by decide
  rcases family_descends (prefixWord ++ tailWord_396478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396486 : List Nat := [6, 1, 2, 2, 1, 2, 1, 1, 2, 3, 2]
def baseStart_396486 : Nat := 118140960795 + 396486 * 2 ^ 59
def prefixEnd_396486 : Nat := 4983230072969 + 3 ^ 40 * 396486 * 2
def baseEnd_396486 : Nat := 203587890778640980401601

theorem tailTrace_396486 : CollatzResearch.WordTrace tailWord_396486 prefixEnd_396486 203587890778640980401601 := by
  unfold tailWord_396486
  simp only [CollatzResearch.WordTrace]
  refine ⟨451907263800200351965291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 9640688294404274175259541 451907263800200351965291)
  ·
    refine ⟨677860895700300527947937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 451907263800200351965291 677860895700300527947937)
    ·
      refine ⟨508395671775225395960953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 677860895700300527947937 508395671775225395960953)
      ·
        refine ⟨381296753831419046970715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 508395671775225395960953 381296753831419046970715)
        ·
          refine ⟨571945130747128570456073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 381296753831419046970715 571945130747128570456073)
          ·
            refine ⟨428958848060346427842055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 571945130747128570456073 428958848060346427842055)
            ·
              refine ⟨643438272090519641763083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 428958848060346427842055 643438272090519641763083)
              ·
                refine ⟨965157408135779462644625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 643438272090519641763083 965157408135779462644625)
                ·
                  refine ⟨723868056101834596983469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 965157408135779462644625 723868056101834596983469)
                  ·
                    refine ⟨271450521038187973868801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 723868056101834596983469 271450521038187973868801)
                    ·
                      refine ⟨203587890778640980401601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 271450521038187973868801 203587890778640980401601)
                      ·
                        rfl

theorem cell23_396486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_396486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_396486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_396486 prefixEnd_396486 := by exact prefixLift 396486
  have htrace : WordTrace (prefixWord ++ tailWord_396486) baseStart_396486 baseEnd_396486 := by
    simpa [prefixWord, tailWord_396486, baseEnd_396486] using wordTrace_append hprefix tailTrace_396486
  have hstable : (prefixWord ++ tailWord_396486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396486).length < 2 ^ (prefixWord ++ tailWord_396486).sum := by decide
  have hdescent : baseEnd_396486 < baseStart_396486 := by decide
  rcases family_descends (prefixWord ++ tailWord_396486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396498 : List Nat := [3, 2, 2, 2, 1, 1, 2, 2, 4, 1, 3]
def baseStart_396498 : Nat := 118140960795 + 396498 * 2 ^ 59
def prefixEnd_396498 : Nat := 4983230072969 + 3 ^ 40 * 396498 * 2
def baseEnd_396498 : Nat := 203594052546494933451545

theorem tailTrace_396498 : CollatzResearch.WordTrace tailWord_396498 prefixEnd_396498 203594052546494933451545 := by
  unfold tailWord_396498
  simp only [CollatzResearch.WordTrace]
  refine ⟨3615367529390734328081537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9640980078375291541550765 3615367529390734328081537)
  ·
    refine ⟨2711525647043050746061153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3615367529390734328081537 2711525647043050746061153)
    ·
      refine ⟨2033644235282288059545865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2711525647043050746061153 2033644235282288059545865)
      ·
        refine ⟨1525233176461716044659399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2033644235282288059545865 1525233176461716044659399)
        ·
          refine ⟨2287849764692574066989099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1525233176461716044659399 2287849764692574066989099)
          ·
            refine ⟨3431774647038861100483649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2287849764692574066989099 3431774647038861100483649)
            ·
              refine ⟨2573830985279145825362737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3431774647038861100483649 2573830985279145825362737)
              ·
                refine ⟨1930373238959359369022053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2573830985279145825362737 1930373238959359369022053)
                ·
                  refine ⟨361944982304879881691635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1930373238959359369022053 361944982304879881691635)
                  ·
                    refine ⟨542917473457319822537453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 361944982304879881691635 542917473457319822537453)
                    ·
                      refine ⟨203594052546494933451545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 542917473457319822537453 203594052546494933451545)
                      ·
                        rfl

theorem cell23_396498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_396498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_396498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_396498 prefixEnd_396498 := by exact prefixLift 396498
  have htrace : WordTrace (prefixWord ++ tailWord_396498) baseStart_396498 baseEnd_396498 := by
    simpa [prefixWord, tailWord_396498, baseEnd_396498] using wordTrace_append hprefix tailTrace_396498
  have hstable : (prefixWord ++ tailWord_396498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396498).length < 2 ^ (prefixWord ++ tailWord_396498).sum := by decide
  have hdescent : baseEnd_396498 < baseStart_396498 := by decide
  rcases family_descends (prefixWord ++ tailWord_396498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396502 : List Nat := [5, 2, 1, 2, 2, 1, 1, 3, 1, 2, 3]
def baseStart_396502 : Nat := 118140960795 + 396502 * 2 ^ 59
def prefixEnd_396502 : Nat := 4983230072969 + 3 ^ 40 * 396502 * 2
def baseEnd_396502 : Nat := 203596106469112917801527

theorem tailTrace_396502 : CollatzResearch.WordTrace tailWord_396502 prefixEnd_396502 203596106469112917801527 := by
  unfold tailWord_396502
  simp only [CollatzResearch.WordTrace]
  refine ⟨903851000596777874716985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9641077339698963996981173 903851000596777874716985)
  ·
    refine ⟨677888250447583406037739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 903851000596777874716985 677888250447583406037739)
    ·
      refine ⟨1016832375671375109056609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 677888250447583406037739 1016832375671375109056609)
      ·
        refine ⟨762624281753531331792457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1016832375671375109056609 762624281753531331792457)
        ·
          refine ⟨571968211315148498844343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 762624281753531331792457 571968211315148498844343)
          ·
            refine ⟨857952316972722748266515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 571968211315148498844343 857952316972722748266515)
            ·
              refine ⟨1286928475459084122399773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 857952316972722748266515 1286928475459084122399773)
              ·
                refine ⟨482598178297156545899915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1286928475459084122399773 482598178297156545899915)
                ·
                  refine ⟨723897267445734818849873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 482598178297156545899915 723897267445734818849873)
                  ·
                    refine ⟨542922950584301114137405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 723897267445734818849873 542922950584301114137405)
                    ·
                      refine ⟨203596106469112917801527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 542922950584301114137405 203596106469112917801527)
                      ·
                        rfl

theorem cell23_396502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_396502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_396502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_396502 prefixEnd_396502 := by exact prefixLift 396502
  have htrace : WordTrace (prefixWord ++ tailWord_396502) baseStart_396502 baseEnd_396502 := by
    simpa [prefixWord, tailWord_396502, baseEnd_396502] using wordTrace_append hprefix tailTrace_396502
  have hstable : (prefixWord ++ tailWord_396502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396502).length < 2 ^ (prefixWord ++ tailWord_396502).sum := by decide
  have hdescent : baseEnd_396502 < baseStart_396502 := by decide
  rcases family_descends (prefixWord ++ tailWord_396502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396542 : List Nat := [4, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2]
def baseStart_396542 : Nat := 118140960795 + 396542 * 2 ^ 59
def prefixEnd_396542 : Nat := 4983230072969 + 3 ^ 40 * 396542 * 2
def baseEnd_396542 : Nat := 203616645695292761301343

theorem tailTrace_396542 : CollatzResearch.WordTrace tailWord_396542 prefixEnd_396542 203616645695292761301343 := by
  unfold tailWord_396542
  simp only [CollatzResearch.WordTrace]
  refine ⟨1807884366175441603365985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9642049952935688551285253 1807884366175441603365985)
  ·
    refine ⟨1355913274631581202524489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1807884366175441603365985 1355913274631581202524489)
    ·
      refine ⟨1016934955973685901893367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1355913274631581202524489 1016934955973685901893367)
      ·
        refine ⟨1525402433960528852840051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1016934955973685901893367 1525402433960528852840051)
        ·
          refine ⟨2288103650940793279260077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1525402433960528852840051 2288103650940793279260077)
          ·
            refine ⟨858038869102797479722529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2288103650940793279260077 858038869102797479722529)
            ·
              refine ⟨643529151827098109791897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 858038869102797479722529 643529151827098109791897)
              ·
                refine ⟨482646863870323582343923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 643529151827098109791897 482646863870323582343923)
                ·
                  refine ⟨723970295805485373515885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 482646863870323582343923 723970295805485373515885)
                  ·
                    refine ⟨271488860927057015068457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 723970295805485373515885 271488860927057015068457)
                    ·
                      refine ⟨203616645695292761301343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 271488860927057015068457 203616645695292761301343)
                      ·
                        rfl

theorem cell23_396542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2].length) (baseStart_396542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_396542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_396542 prefixEnd_396542 := by exact prefixLift 396542
  have htrace : WordTrace (prefixWord ++ tailWord_396542) baseStart_396542 baseEnd_396542 := by
    simpa [prefixWord, tailWord_396542, baseEnd_396542] using wordTrace_append hprefix tailTrace_396542
  have hstable : (prefixWord ++ tailWord_396542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396542).length < 2 ^ (prefixWord ++ tailWord_396542).sum := by decide
  have hdescent : baseEnd_396542 < baseStart_396542 := by decide
  rcases family_descends (prefixWord ++ tailWord_396542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396589 : List Nat := [1, 5, 3, 1, 1, 2, 1, 3, 2, 2, 2]
def baseStart_396589 : Nat := 118140960795 + 396589 * 2 ^ 59
def prefixEnd_396589 : Nat := 4983230072969 + 3 ^ 40 * 396589 * 2
def baseEnd_396589 : Nat := 203640779286054077413627

theorem tailTrace_396589 : CollatzResearch.WordTrace tailWord_396589 prefixEnd_396589 203640779286054077413627 := by
  unfold tailWord_396589
  simp only [CollatzResearch.WordTrace]
  refine ⟨14464789160233259853888821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9643192773488839902592547 14464789160233259853888821)
  ·
    refine ⟨1356073983771868111302077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14464789160233259853888821 1356073983771868111302077)
    ·
      refine ⟨508527743914450541738279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1356073983771868111302077 508527743914450541738279)
      ·
        refine ⟨762791615871675812607419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 508527743914450541738279 762791615871675812607419)
        ·
          refine ⟨1144187423807513718911129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 762791615871675812607419 1144187423807513718911129)
          ·
            refine ⟨858140567855635289183347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1144187423807513718911129 858140567855635289183347)
            ·
              refine ⟨1287210851783452933775021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 858140567855635289183347 1287210851783452933775021)
              ·
                refine ⟨482704069418794850165633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1287210851783452933775021 482704069418794850165633)
                ·
                  refine ⟨362028052064096137624225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 482704069418794850165633 362028052064096137624225)
                  ·
                    refine ⟨271521039048072103218169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 362028052064096137624225 271521039048072103218169)
                    ·
                      refine ⟨203640779286054077413627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 271521039048072103218169 203640779286054077413627)
                      ·
                        rfl

theorem cell23_396589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_396589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_396589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_396589 prefixEnd_396589 := by exact prefixLift 396589
  have htrace : WordTrace (prefixWord ++ tailWord_396589) baseStart_396589 baseEnd_396589 := by
    simpa [prefixWord, tailWord_396589, baseEnd_396589] using wordTrace_append hprefix tailTrace_396589
  have hstable : (prefixWord ++ tailWord_396589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396589).length < 2 ^ (prefixWord ++ tailWord_396589).sum := by decide
  have hdescent : baseEnd_396589 < baseStart_396589 := by decide
  rcases family_descends (prefixWord ++ tailWord_396589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396628 : List Nat := [2, 4, 1, 1, 2, 1, 1, 4, 2, 1, 4]
def baseStart_396628 : Nat := 118140960795 + 396628 * 2 ^ 59
def prefixEnd_396628 : Nat := 4983230072969 + 3 ^ 40 * 396628 * 2
def baseEnd_396628 : Nat := 203660805031579424825947

theorem tailTrace_396628 : CollatzResearch.WordTrace tailWord_396628 prefixEnd_396628 203660805031579424825947 := by
  unfold tailWord_396628
  simp only [CollatzResearch.WordTrace]
  refine ⟨7233105803545984757279269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9644141071394646343039025 7233105803545984757279269)
  ·
    refine ⟨1356207338164872141989863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7233105803545984757279269 1356207338164872141989863)
    ·
      refine ⟨2034311007247308212984795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1356207338164872141989863 2034311007247308212984795)
      ·
        refine ⟨3051466510870962319477193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2034311007247308212984795 3051466510870962319477193)
        ·
          refine ⟨2288599883153221739607895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3051466510870962319477193 2288599883153221739607895)
          ·
            refine ⟨3432899824729832609411843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2288599883153221739607895 3432899824729832609411843)
            ·
              refine ⟨5149349737094748914117765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3432899824729832609411843 5149349737094748914117765)
              ·
                refine ⟨965503075705265421397081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5149349737094748914117765 965503075705265421397081)
                ·
                  refine ⟨724127306778949066047811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 965503075705265421397081 724127306778949066047811)
                  ·
                    refine ⟨1086190960168423599071717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 724127306778949066047811 1086190960168423599071717)
                    ·
                      refine ⟨203660805031579424825947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1086190960168423599071717 203660805031579424825947)
                      ·
                        rfl

theorem cell23_396628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_396628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_396628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_396628 prefixEnd_396628 := by exact prefixLift 396628
  have htrace : WordTrace (prefixWord ++ tailWord_396628) baseStart_396628 baseEnd_396628 := by
    simpa [prefixWord, tailWord_396628, baseEnd_396628] using wordTrace_append hprefix tailTrace_396628
  have hstable : (prefixWord ++ tailWord_396628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396628).length < 2 ^ (prefixWord ++ tailWord_396628).sum := by decide
  have hdescent : baseEnd_396628 < baseStart_396628 := by decide
  rcases family_descends (prefixWord ++ tailWord_396628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396728 : List Nat := [2, 1, 2, 1, 2, 2, 3, 2, 4, 4]
def baseStart_396728 : Nat := 118140960795 + 396728 * 2 ^ 59
def prefixEnd_396728 : Nat := 4983230072969 + 3 ^ 40 * 396728 * 2
def baseEnd_396728 : Nat := 67904051032343011191829

theorem tailTrace_396728 : CollatzResearch.WordTrace tailWord_396728 prefixEnd_396728 67904051032343011191829 := by
  unfold tailWord_396728
  simp only [CollatzResearch.WordTrace]
  refine ⟨7234929453364843296599419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9646572604486457728799225 7234929453364843296599419)
  ·
    refine ⟨10852394180047264944899129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7234929453364843296599419 10852394180047264944899129)
    ·
      refine ⟨8139295635035448708674347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10852394180047264944899129 8139295635035448708674347)
      ·
        refine ⟨12208943452553173063011521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8139295635035448708674347 12208943452553173063011521)
        ·
          refine ⟨9156707589414879797258641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12208943452553173063011521 9156707589414879797258641)
          ·
            refine ⟨6867530692061159847943981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9156707589414879797258641 6867530692061159847943981)
            ·
              refine ⟨2575324009522934942978993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6867530692061159847943981 2575324009522934942978993)
              ·
                refine ⟨1931493007142201207234245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2575324009522934942978993 1931493007142201207234245)
                ·
                  refine ⟨362154938839162726356421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1931493007142201207234245 362154938839162726356421)
                  ·
                    refine ⟨67904051032343011191829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 362154938839162726356421 67904051032343011191829)
                    ·
                      rfl

theorem cell23_396728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 2, 4, 4].length) (baseStart_396728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_396728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_396728 prefixEnd_396728 := by exact prefixLift 396728
  have htrace : WordTrace (prefixWord ++ tailWord_396728) baseStart_396728 baseEnd_396728 := by
    simpa [prefixWord, tailWord_396728, baseEnd_396728] using wordTrace_append hprefix tailTrace_396728
  have hstable : (prefixWord ++ tailWord_396728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396728).length < 2 ^ (prefixWord ++ tailWord_396728).sum := by decide
  have hdescent : baseEnd_396728 < baseStart_396728 := by decide
  rcases family_descends (prefixWord ++ tailWord_396728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396735 : List Nat := [1, 1, 2, 2, 2, 1, 1, 4, 5, 2, 2]
def baseStart_396735 : Nat := 118140960795 + 396735 * 2 ^ 59
def prefixEnd_396735 : Nat := 4983230072969 + 3 ^ 40 * 396735 * 2
def baseEnd_396735 : Nat := 203715747461610506187955

theorem tailTrace_396735 : CollatzResearch.WordTrace tailWord_396735 prefixEnd_396735 203715747461610506187955 := by
  unfold tailWord_396735
  simp only [CollatzResearch.WordTrace]
  refine ⟨14470114217704326788703659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9646742811802884525802439 14470114217704326788703659)
  ·
    refine ⟨21705171326556490183055489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14470114217704326788703659 21705171326556490183055489)
    ·
      refine ⟨16278878494917367637291617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21705171326556490183055489 16278878494917367637291617)
      ·
        refine ⟨12209158871188025727968713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16278878494917367637291617 12209158871188025727968713)
        ·
          refine ⟨9156869153391019295976535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12209158871188025727968713 9156869153391019295976535)
          ·
            refine ⟨13735303730086528943964803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9156869153391019295976535 13735303730086528943964803)
            ·
              refine ⟨20602955595129793415947205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13735303730086528943964803 20602955595129793415947205)
              ·
                refine ⟨3863054174086836265490101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20602955595129793415947205 3863054174086836265490101)
                ·
                  refine ⟨362161328820640899889697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3863054174086836265490101 362161328820640899889697)
                  ·
                    refine ⟨271620996615480674917273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 362161328820640899889697 271620996615480674917273)
                    ·
                      refine ⟨203715747461610506187955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 271620996615480674917273 203715747461610506187955)
                      ·
                        rfl

theorem cell23_396735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 5, 2, 2].length) (baseStart_396735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_396735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_396735 prefixEnd_396735 := by exact prefixLift 396735
  have htrace : WordTrace (prefixWord ++ tailWord_396735) baseStart_396735 baseEnd_396735 := by
    simpa [prefixWord, tailWord_396735, baseEnd_396735] using wordTrace_append hprefix tailTrace_396735
  have hstable : (prefixWord ++ tailWord_396735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396735).length < 2 ^ (prefixWord ++ tailWord_396735).sum := by decide
  have hdescent : baseEnd_396735 < baseStart_396735 := by decide
  rcases family_descends (prefixWord ++ tailWord_396735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396748 : List Nat := [2, 2, 1, 4, 2, 1, 1, 2, 1, 1, 6]
def baseStart_396748 : Nat := 118140960795 + 396748 * 2 ^ 59
def prefixEnd_396748 : Nat := 4983230072969 + 3 ^ 40 * 396748 * 2
def baseEnd_396748 : Nat := 203722422710118955325395

theorem tailTrace_396748 : CollatzResearch.WordTrace tailWord_396748 prefixEnd_396748 203722422710118955325395 := by
  unfold tailWord_396748
  simp only [CollatzResearch.WordTrace]
  refine ⟨7235294183328615004463449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9647058911104820005951265 7235294183328615004463449)
  ·
    refine ⟨5426470637496461253347587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7235294183328615004463449 5426470637496461253347587)
    ·
      refine ⟨8139705956244691880021381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5426470637496461253347587 8139705956244691880021381)
      ·
        refine ⟨1526194866795879727504009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8139705956244691880021381 1526194866795879727504009)
        ·
          refine ⟨1144646150096909795628007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1526194866795879727504009 1144646150096909795628007)
          ·
            refine ⟨1716969225145364693442011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1144646150096909795628007 1716969225145364693442011)
            ·
              refine ⟨2575453837718047040163017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1716969225145364693442011 2575453837718047040163017)
              ·
                refine ⟨1931590378288535280122263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2575453837718047040163017 1931590378288535280122263)
                ·
                  refine ⟨2897385567432802920183395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1931590378288535280122263 2897385567432802920183395)
                  ·
                    refine ⟨4346078351149204380275093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2897385567432802920183395 4346078351149204380275093)
                    ·
                      refine ⟨203722422710118955325395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4346078351149204380275093 203722422710118955325395)
                      ·
                        rfl

theorem cell23_396748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_396748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_396748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_396748 prefixEnd_396748 := by exact prefixLift 396748
  have htrace : WordTrace (prefixWord ++ tailWord_396748) baseStart_396748 baseEnd_396748 := by
    simpa [prefixWord, tailWord_396748, baseEnd_396748] using wordTrace_append hprefix tailTrace_396748
  have hstable : (prefixWord ++ tailWord_396748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396748).length < 2 ^ (prefixWord ++ tailWord_396748).sum := by decide
  have hdescent : baseEnd_396748 < baseStart_396748 := by decide
  rcases family_descends (prefixWord ++ tailWord_396748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396762 : List Nat := [3, 1, 1, 2, 3, 2, 4, 1, 2, 4]
def baseStart_396762 : Nat := 118140960795 + 396762 * 2 ^ 59
def prefixEnd_396762 : Nat := 4983230072969 + 3 ^ 40 * 396762 * 2
def baseEnd_396762 : Nat := 67909870479760633516777

theorem tailTrace_396762 : CollatzResearch.WordTrace tailWord_396762 prefixEnd_396762 67909870479760633516777 := by
  unfold tailWord_396762
  simp only [CollatzResearch.WordTrace]
  refine ⟨3617774747151627599984135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9647399325737673599957693 3617774747151627599984135)
  ·
    refine ⟨5426662120727441399976203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3617774747151627599984135 5426662120727441399976203)
    ·
      refine ⟨8139993181091162099964305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5426662120727441399976203 8139993181091162099964305)
      ·
        refine ⟨6104994885818371574973229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8139993181091162099964305 6104994885818371574973229)
        ·
          refine ⟨2289373082181889340614961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6104994885818371574973229 2289373082181889340614961)
          ·
            refine ⟨1717029811636417005461221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2289373082181889340614961 1717029811636417005461221)
            ·
              refine ⟨321943089681828188523979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1717029811636417005461221 321943089681828188523979)
              ·
                refine ⟨482914634522742282785969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 321943089681828188523979 482914634522742282785969)
                ·
                  refine ⟨362185975892056712089477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 482914634522742282785969 362185975892056712089477)
                  ·
                    refine ⟨67909870479760633516777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 362185975892056712089477 67909870479760633516777)
                    ·
                      rfl

theorem cell23_396762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 4, 1, 2, 4].length) (baseStart_396762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_396762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_396762 prefixEnd_396762 := by exact prefixLift 396762
  have htrace : WordTrace (prefixWord ++ tailWord_396762) baseStart_396762 baseEnd_396762 := by
    simpa [prefixWord, tailWord_396762, baseEnd_396762] using wordTrace_append hprefix tailTrace_396762
  have hstable : (prefixWord ++ tailWord_396762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396762).length < 2 ^ (prefixWord ++ tailWord_396762).sum := by decide
  have hdescent : baseEnd_396762 < baseStart_396762 := by decide
  rcases family_descends (prefixWord ++ tailWord_396762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396785 : List Nat := [1, 2, 2, 2, 3, 3, 1, 2, 1, 3, 3]
def baseStart_396785 : Nat := 118140960795 + 396785 * 2 ^ 59
def prefixEnd_396785 : Nat := 4983230072969 + 3 ^ 40 * 396785 * 2
def baseEnd_396785 : Nat := 203741421494335310562725

theorem tailTrace_396785 : CollatzResearch.WordTrace tailWord_396785 prefixEnd_396785 203741421494335310562725 := by
  unfold tailWord_396785
  simp only [CollatzResearch.WordTrace]
  refine ⟨14471937867523185328023809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9647958578348790218682539 14471937867523185328023809)
  ·
    refine ⟨10853953400642388996017857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14471937867523185328023809 10853953400642388996017857)
    ·
      refine ⟨8140465050481791747013393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10853953400642388996017857 8140465050481791747013393)
      ·
        refine ⟨6105348787861343810260045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8140465050481791747013393 6105348787861343810260045)
        ·
          refine ⟨2289505795448003928847517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6105348787861343810260045 2289505795448003928847517)
          ·
            refine ⟨858564673293001473317819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2289505795448003928847517 858564673293001473317819)
            ·
              refine ⟨1287847009939502209976729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 858564673293001473317819 1287847009939502209976729)
              ·
                refine ⟨965885257454626657482547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1287847009939502209976729 965885257454626657482547)
                ·
                  refine ⟨1448827886181939986223821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 965885257454626657482547 1448827886181939986223821)
                  ·
                    refine ⟨543310457318227494833933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1448827886181939986223821 543310457318227494833933)
                    ·
                      refine ⟨203741421494335310562725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 543310457318227494833933 203741421494335310562725)
                      ·
                        rfl

theorem cell23_396785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 2, 1, 3, 3].length) (baseStart_396785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_396785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_396785 prefixEnd_396785 := by exact prefixLift 396785
  have htrace : WordTrace (prefixWord ++ tailWord_396785) baseStart_396785 baseEnd_396785 := by
    simpa [prefixWord, tailWord_396785, baseEnd_396785] using wordTrace_append hprefix tailTrace_396785
  have hstable : (prefixWord ++ tailWord_396785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396785).length < 2 ^ (prefixWord ++ tailWord_396785).sum := by decide
  have hdescent : baseEnd_396785 < baseStart_396785 := by decide
  rcases family_descends (prefixWord ++ tailWord_396785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396808 : List Nat := [2, 1, 3, 2, 1, 1, 3, 1, 2, 3, 4]
def baseStart_396808 : Nat := 118140960795 + 396808 * 2 ^ 59
def prefixEnd_396808 : Nat := 4983230072969 + 3 ^ 40 * 396808 * 2
def baseEnd_396808 : Nat := 203753231549388720575119

theorem tailTrace_396808 : CollatzResearch.WordTrace tailWord_396808 prefixEnd_396808 203753231549388720575119 := by
  unfold tailWord_396808
  simp only [CollatzResearch.WordTrace]
  refine ⟨7236388373219930128055539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9648517830959906837407385 7236388373219930128055539)
  ·
    refine ⟨10854582559829895192083309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7236388373219930128055539 10854582559829895192083309)
    ·
      refine ⟨4070468459936210697031241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10854582559829895192083309 4070468459936210697031241)
      ·
        refine ⟨3052851344952158022773431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4070468459936210697031241 3052851344952158022773431)
        ·
          refine ⟨4579277017428237034160147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3052851344952158022773431 4579277017428237034160147)
          ·
            refine ⟨6868915526142355551240221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4579277017428237034160147 6868915526142355551240221)
            ·
              refine ⟨2575843322303383331715083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6868915526142355551240221 2575843322303383331715083)
              ·
                refine ⟨3863764983455074997572625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2575843322303383331715083 3863764983455074997572625)
                ·
                  refine ⟨2897823737591306248179469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3863764983455074997572625 2897823737591306248179469)
                  ·
                    refine ⟨1086683901596739843067301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2897823737591306248179469 1086683901596739843067301)
                    ·
                      refine ⟨203753231549388720575119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1086683901596739843067301 203753231549388720575119)
                      ·
                        rfl

theorem cell23_396808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_396808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_396808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_396808 prefixEnd_396808 := by exact prefixLift 396808
  have htrace : WordTrace (prefixWord ++ tailWord_396808) baseStart_396808 baseEnd_396808 := by
    simpa [prefixWord, tailWord_396808, baseEnd_396808] using wordTrace_append hprefix tailTrace_396808
  have hstable : (prefixWord ++ tailWord_396808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396808).length < 2 ^ (prefixWord ++ tailWord_396808).sum := by decide
  have hdescent : baseEnd_396808 < baseStart_396808 := by decide
  rcases family_descends (prefixWord ++ tailWord_396808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396842 : List Nat := [3, 1, 4, 1, 1, 1, 1, 4, 1, 4, 2]
def baseStart_396842 : Nat := 118140960795 + 396842 * 2 ^ 59
def prefixEnd_396842 : Nat := 4983230072969 + 3 ^ 40 * 396842 * 2
def baseEnd_396842 : Nat := 203770689891641587549963

theorem tailTrace_396842 : CollatzResearch.WordTrace tailWord_396842 prefixEnd_396842 203770689891641587549963 := by
  unfold tailWord_396842
  simp only [CollatzResearch.WordTrace]
  refine ⟨3618504207079171015712195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9649344552211122708565853 3618504207079171015712195)
  ·
    refine ⟨5427756310618756523568293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3618504207079171015712195 5427756310618756523568293)
    ·
      refine ⟨1017704308241016848169055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5427756310618756523568293 1017704308241016848169055)
      ·
        refine ⟨1526556462361525272253583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1017704308241016848169055 1526556462361525272253583)
        ·
          refine ⟨2289834693542287908380375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1526556462361525272253583 2289834693542287908380375)
          ·
            refine ⟨3434752040313431862570563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2289834693542287908380375 3434752040313431862570563)
            ·
              refine ⟨5152128060470147793855845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3434752040313431862570563 5152128060470147793855845)
              ·
                refine ⟨966024011338152711347971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5152128060470147793855845 966024011338152711347971)
                ·
                  refine ⟨1449036017007229067021957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 966024011338152711347971 1449036017007229067021957)
                  ·
                    refine ⟨271694253188855450066617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1449036017007229067021957 271694253188855450066617)
                    ·
                      refine ⟨203770689891641587549963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 271694253188855450066617 203770689891641587549963)
                      ·
                        rfl

theorem cell23_396842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 4, 1, 4, 2].length) (baseStart_396842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_396842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_396842 prefixEnd_396842 := by exact prefixLift 396842
  have htrace : WordTrace (prefixWord ++ tailWord_396842) baseStart_396842 baseEnd_396842 := by
    simpa [prefixWord, tailWord_396842, baseEnd_396842] using wordTrace_append hprefix tailTrace_396842
  have hstable : (prefixWord ++ tailWord_396842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396842).length < 2 ^ (prefixWord ++ tailWord_396842).sum := by decide
  have hdescent : baseEnd_396842 < baseStart_396842 := by decide
  rcases family_descends (prefixWord ++ tailWord_396842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396846 : List Nat := [4, 1, 3, 1, 2, 1, 4, 1, 1, 3, 2]
def baseStart_396846 : Nat := 118140960795 + 396846 * 2 ^ 59
def prefixEnd_396846 : Nat := 4983230072969 + 3 ^ 40 * 396846 * 2
def baseEnd_396846 : Nat := 203772743814259571899945

theorem tailTrace_396846 : CollatzResearch.WordTrace tailWord_396846 prefixEnd_396846 203772743814259571899945 := by
  unfold tailWord_396846
  simp only [CollatzResearch.WordTrace]
  refine ⟨1809270340037774093249299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9649441813534795163996261 1809270340037774093249299)
  ·
    refine ⟨2713905510056661139873949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1809270340037774093249299 2713905510056661139873949)
    ·
      refine ⟨1017714566271247927452731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2713905510056661139873949 1017714566271247927452731)
      ·
        refine ⟨1526571849406871891179097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1017714566271247927452731 1526571849406871891179097)
        ·
          refine ⟨1144928887055153918384323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1526571849406871891179097 1144928887055153918384323)
          ·
            refine ⟨1717393330582730877576485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1144928887055153918384323 1717393330582730877576485)
            ·
              refine ⟨322011249484262039545591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1717393330582730877576485 322011249484262039545591)
              ·
                refine ⟨483016874226393059318387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 322011249484262039545591 483016874226393059318387)
                ·
                  refine ⟨724525311339589588977581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 483016874226393059318387 724525311339589588977581)
                  ·
                    refine ⟨271696991752346095866593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 724525311339589588977581 271696991752346095866593)
                    ·
                      refine ⟨203772743814259571899945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 271696991752346095866593 203772743814259571899945)
                      ·
                        rfl

theorem cell23_396846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 4, 1, 1, 3, 2].length) (baseStart_396846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_396846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_396846 prefixEnd_396846 := by exact prefixLift 396846
  have htrace : WordTrace (prefixWord ++ tailWord_396846) baseStart_396846 baseEnd_396846 := by
    simpa [prefixWord, tailWord_396846, baseEnd_396846] using wordTrace_append hprefix tailTrace_396846
  have hstable : (prefixWord ++ tailWord_396846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396846).length < 2 ^ (prefixWord ++ tailWord_396846).sum := by decide
  have hdescent : baseEnd_396846 < baseStart_396846 := by decide
  rcases family_descends (prefixWord ++ tailWord_396846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396865 : List Nat := [1, 2, 5, 1, 1, 1, 4, 1, 7]
def baseStart_396865 : Nat := 118140960795 + 396865 * 2 ^ 59
def prefixEnd_396865 : Nat := 4983230072969 + 3 ^ 40 * 396865 * 2
def baseEnd_396865 : Nat := 22642499994077221951373

theorem tailTrace_396865 : CollatzResearch.WordTrace tailWord_396865 prefixEnd_396865 22642499994077221951373 := by
  unfold tailWord_396865
  simp only [CollatzResearch.WordTrace]
  refine ⟨14474855707233358990936049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9649903804822239327290699 14474855707233358990936049)
  ·
    refine ⟨10856141780425019243202037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14474855707233358990936049 10856141780425019243202037)
    ·
      refine ⟨1017763291914845554050191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10856141780425019243202037 1017763291914845554050191)
      ·
        refine ⟨1526644937872268331075287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1017763291914845554050191 1526644937872268331075287)
        ·
          refine ⟨2289967406808402496612931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1526644937872268331075287 2289967406808402496612931)
          ·
            refine ⟨3434951110212603744919397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2289967406808402496612931 3434951110212603744919397)
            ·
              refine ⟨644053333164863202172387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3434951110212603744919397 644053333164863202172387)
              ·
                refine ⟨966079999747294803258581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 644053333164863202172387 966079999747294803258581)
                ·
                  refine ⟨22642499994077221951373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 966079999747294803258581 22642499994077221951373)
                  ·
                    rfl

theorem cell23_396865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 1, 7].length) (baseStart_396865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_396865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_396865 prefixEnd_396865 := by exact prefixLift 396865
  have htrace : WordTrace (prefixWord ++ tailWord_396865) baseStart_396865 baseEnd_396865 := by
    simpa [prefixWord, tailWord_396865, baseEnd_396865] using wordTrace_append hprefix tailTrace_396865
  have hstable : (prefixWord ++ tailWord_396865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396865).length < 2 ^ (prefixWord ++ tailWord_396865).sum := by decide
  have hdescent : baseEnd_396865 < baseStart_396865 := by decide
  rcases family_descends (prefixWord ++ tailWord_396865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396876 : List Nat := [2, 2, 1, 3, 1, 4, 3, 1, 2, 2, 2]
def baseStart_396876 : Nat := 118140960795 + 396876 * 2 ^ 59
def prefixEnd_396876 : Nat := 4983230072969 + 3 ^ 40 * 396876 * 2
def baseEnd_396876 : Nat := 203788148233894454524807

theorem tailTrace_396876 : CollatzResearch.WordTrace tailWord_396876 prefixEnd_396876 203788148233894454524807 := by
  unfold tailWord_396876
  simp only [CollatzResearch.WordTrace]
  refine ⟨7237628455096753934793241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9650171273462338579724321 7237628455096753934793241)
  ·
    refine ⟨5428221341322565451094931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7237628455096753934793241 5428221341322565451094931)
    ·
      refine ⟨8142332011983848176642397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5428221341322565451094931 8142332011983848176642397)
      ·
        refine ⟨3053374504493943066240899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8142332011983848176642397 3053374504493943066240899)
        ·
          refine ⟨4580061756740914599361349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3053374504493943066240899 4580061756740914599361349)
          ·
            refine ⟨858761579388921487380253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4580061756740914599361349 858761579388921487380253)
            ·
              refine ⟨322035592270845557767595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 858761579388921487380253 322035592270845557767595)
              ·
                refine ⟨483053388406268336651393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 322035592270845557767595 483053388406268336651393)
                ·
                  refine ⟨362290041304701252488545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 483053388406268336651393 362290041304701252488545)
                  ·
                    refine ⟨271717530978525939366409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 362290041304701252488545 271717530978525939366409)
                    ·
                      refine ⟨203788148233894454524807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 271717530978525939366409 203788148233894454524807)
                      ·
                        rfl

theorem cell23_396876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 3, 1, 2, 2, 2].length) (baseStart_396876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_396876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_396876 prefixEnd_396876 := by exact prefixLift 396876
  have htrace : WordTrace (prefixWord ++ tailWord_396876) baseStart_396876 baseEnd_396876 := by
    simpa [prefixWord, tailWord_396876, baseEnd_396876] using wordTrace_append hprefix tailTrace_396876
  have hstable : (prefixWord ++ tailWord_396876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396876).length < 2 ^ (prefixWord ++ tailWord_396876).sum := by decide
  have hdescent : baseEnd_396876 < baseStart_396876 := by decide
  rcases family_descends (prefixWord ++ tailWord_396876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396888 : List Nat := [2, 1, 2, 2, 1, 2, 1, 2, 3, 2, 5]
def baseStart_396888 : Nat := 118140960795 + 396888 * 2 ^ 59
def prefixEnd_396888 : Nat := 4983230072969 + 3 ^ 40 * 396888 * 2
def baseEnd_396888 : Nat := 203794310001748407574751

theorem tailTrace_396888 : CollatzResearch.WordTrace tailWord_396888 prefixEnd_396888 203794310001748407574751 := by
  unfold tailWord_396888
  simp only [CollatzResearch.WordTrace]
  refine ⟨7237847293075016959511659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9650463057433355946015545 7237847293075016959511659)
  ·
    refine ⟨10856770939612525439267489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7237847293075016959511659 10856770939612525439267489)
    ·
      refine ⟨8142578204709394079450617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10856770939612525439267489 8142578204709394079450617)
      ·
        refine ⟨6106933653532045559587963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8142578204709394079450617 6106933653532045559587963)
        ·
          refine ⟨9160400480298068339381945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6106933653532045559587963 9160400480298068339381945)
          ·
            refine ⟨6870300360223551254536459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9160400480298068339381945 6870300360223551254536459)
            ·
              refine ⟨10305450540335326881804689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6870300360223551254536459 10305450540335326881804689)
              ·
                refine ⟨7729087905251495161353517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10305450540335326881804689 7729087905251495161353517)
                ·
                  refine ⟨2898407964469310685507569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7729087905251495161353517 2898407964469310685507569)
                  ·
                    refine ⟨2173805973351983014130677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2898407964469310685507569 2173805973351983014130677)
                    ·
                      refine ⟨203794310001748407574751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2173805973351983014130677 203794310001748407574751)
                      ·
                        rfl

theorem cell23_396888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 3, 2, 5].length) (baseStart_396888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_396888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_396888 prefixEnd_396888 := by exact prefixLift 396888
  have htrace : WordTrace (prefixWord ++ tailWord_396888) baseStart_396888 baseEnd_396888 := by
    simpa [prefixWord, tailWord_396888, baseEnd_396888] using wordTrace_append hprefix tailTrace_396888
  have hstable : (prefixWord ++ tailWord_396888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396888).length < 2 ^ (prefixWord ++ tailWord_396888).sum := by decide
  have hdescent : baseEnd_396888 < baseStart_396888 := by decide
  rcases family_descends (prefixWord ++ tailWord_396888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396952 : List Nat := [2, 1, 2, 4, 1, 2, 1, 3, 2, 2, 3]
def baseStart_396952 : Nat := 118140960795 + 396952 * 2 ^ 59
def prefixEnd_396952 : Nat := 4983230072969 + 3 ^ 40 * 396952 * 2
def baseEnd_396952 : Nat := 203827172763636157174457

theorem tailTrace_396952 : CollatzResearch.WordTrace tailWord_396952 prefixEnd_396952 203827172763636157174457 := by
  unfold tailWord_396952
  simp only [CollatzResearch.WordTrace]
  refine ⟨7239014428959086424676555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9652019238612115232902073 7239014428959086424676555)
  ·
    refine ⟨10858521643438629637014833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7239014428959086424676555 10858521643438629637014833)
    ·
      refine ⟨8143891232578972227761125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10858521643438629637014833 8143891232578972227761125)
      ·
        refine ⟨1526979606108557292705211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8143891232578972227761125 1526979606108557292705211)
        ·
          refine ⟨2290469409162835939057817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1526979606108557292705211 2290469409162835939057817)
          ·
            refine ⟨1717852056872126954293363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2290469409162835939057817 1717852056872126954293363)
            ·
              refine ⟨2576778085308190431440045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1717852056872126954293363 2576778085308190431440045)
              ·
                refine ⟨966291781990571411790017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2576778085308190431440045 966291781990571411790017)
                ·
                  refine ⟨724718836492928558842513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 966291781990571411790017 724718836492928558842513)
                  ·
                    refine ⟨543539127369696419131885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 724718836492928558842513 543539127369696419131885)
                    ·
                      refine ⟨203827172763636157174457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 543539127369696419131885 203827172763636157174457)
                      ·
                        rfl

theorem cell23_396952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_396952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_396952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_396952 prefixEnd_396952 := by exact prefixLift 396952
  have htrace : WordTrace (prefixWord ++ tailWord_396952) baseStart_396952 baseEnd_396952 := by
    simpa [prefixWord, tailWord_396952, baseEnd_396952] using wordTrace_append hprefix tailTrace_396952
  have hstable : (prefixWord ++ tailWord_396952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396952).length < 2 ^ (prefixWord ++ tailWord_396952).sum := by decide
  have hdescent : baseEnd_396952 < baseStart_396952 := by decide
  rcases family_descends (prefixWord ++ tailWord_396952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396985 : List Nat := [1, 2, 1, 4, 1, 1, 3, 2, 3, 5]
def baseStart_396985 : Nat := 118140960795 + 396985 * 2 ^ 59
def prefixEnd_396985 : Nat := 4983230072969 + 3 ^ 40 * 396985 * 2
def baseEnd_396985 : Nat := 67948039208411509353935

theorem tailTrace_396985 : CollatzResearch.WordTrace tailWord_396985 prefixEnd_396985 67948039208411509353935 := by
  unfold tailWord_396985
  simp only [CollatzResearch.WordTrace]
  refine ⟨14479232466798619485304409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9652821644532412990202939 14479232466798619485304409)
  ·
    refine ⟨10859424350098964613978307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14479232466798619485304409 10859424350098964613978307)
    ·
      refine ⟨16289136525148446920967461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10859424350098964613978307 16289136525148446920967461)
      ·
        refine ⟨3054213098465333797681399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16289136525148446920967461 3054213098465333797681399)
        ·
          refine ⟨4581319647698000696522099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3054213098465333797681399 4581319647698000696522099)
          ·
            refine ⟨6871979471547001044783149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4581319647698000696522099 6871979471547001044783149)
            ·
              refine ⟨2576992301830125391793681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6871979471547001044783149 2576992301830125391793681)
              ·
                refine ⟨1932744226372594043845261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2576992301830125391793681 1932744226372594043845261)
                ·
                  refine ⟨724779084889722766441973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1932744226372594043845261 724779084889722766441973)
                  ·
                    refine ⟨67948039208411509353935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 724779084889722766441973 67948039208411509353935)
                    ·
                      rfl

theorem cell23_396985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 2, 3, 5].length) (baseStart_396985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_396985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_396985 prefixEnd_396985 := by exact prefixLift 396985
  have htrace : WordTrace (prefixWord ++ tailWord_396985) baseStart_396985 baseEnd_396985 := by
    simpa [prefixWord, tailWord_396985, baseEnd_396985] using wordTrace_append hprefix tailTrace_396985
  have hstable : (prefixWord ++ tailWord_396985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396985).length < 2 ^ (prefixWord ++ tailWord_396985).sum := by decide
  have hdescent : baseEnd_396985 < baseStart_396985 := by decide
  rcases family_descends (prefixWord ++ tailWord_396985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396992 : List Nat := [2, 1, 1, 2, 4, 1, 2, 2, 1, 5, 2]
def baseStart_396992 : Nat := 118140960795 + 396992 * 2 ^ 59
def prefixEnd_396992 : Nat := 4983230072969 + 3 ^ 40 * 396992 * 2
def baseEnd_396992 : Nat := 203847711989816000674273

theorem tailTrace_396992 : CollatzResearch.WordTrace tailWord_396992 prefixEnd_396992 203847711989816000674273 := by
  unfold tailWord_396992
  simp only [CollatzResearch.WordTrace]
  refine ⟨7239743888886629840404615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9652991851848839787206153 7239743888886629840404615)
  ·
    refine ⟨10859615833329944760606923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7239743888886629840404615 10859615833329944760606923)
    ·
      refine ⟨16289423749994917140910385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10859615833329944760606923 16289423749994917140910385)
      ·
        refine ⟨12217067812496187855682789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16289423749994917140910385 12217067812496187855682789)
        ·
          refine ⟨2290700214843035222940523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12217067812496187855682789 2290700214843035222940523)
          ·
            refine ⟨3436050322264552834410785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2290700214843035222940523 3436050322264552834410785)
            ·
              refine ⟨2577037741698414625808089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3436050322264552834410785 2577037741698414625808089)
              ·
                refine ⟨1932778306273810969356067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2577037741698414625808089 1932778306273810969356067)
                ·
                  refine ⟨2899167459410716454034101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1932778306273810969356067 2899167459410716454034101)
                  ·
                    refine ⟨271796949319754667565697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2899167459410716454034101 271796949319754667565697)
                    ·
                      refine ⟨203847711989816000674273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 271796949319754667565697 203847711989816000674273)
                      ·
                        rfl

theorem cell23_396992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 2, 1, 5, 2].length) (baseStart_396992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_396992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_396992 prefixEnd_396992 := by exact prefixLift 396992
  have htrace : WordTrace (prefixWord ++ tailWord_396992) baseStart_396992 baseEnd_396992 := by
    simpa [prefixWord, tailWord_396992, baseEnd_396992] using wordTrace_append hprefix tailTrace_396992
  have hstable : (prefixWord ++ tailWord_396992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396992).length < 2 ^ (prefixWord ++ tailWord_396992).sum := by decide
  have hdescent : baseEnd_396992 < baseStart_396992 := by decide
  rcases family_descends (prefixWord ++ tailWord_396992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397009 : List Nat := [1, 2, 2, 1, 2, 4, 3, 1, 2, 3, 2]
def baseStart_397009 : Nat := 118140960795 + 397009 * 2 ^ 59
def prefixEnd_397009 : Nat := 4983230072969 + 3 ^ 40 * 397009 * 2
def baseEnd_397009 : Nat := 203856441160942434161695

theorem tailTrace_397009 : CollatzResearch.WordTrace tailWord_397009 prefixEnd_397009 203856441160942434161695 := by
  unfold tailWord_397009
  simp only [CollatzResearch.WordTrace]
  refine ⟨14480107818711671584178081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9653405212474447722785387 14480107818711671584178081)
  ·
    refine ⟨10860080864033753688133561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14480107818711671584178081 10860080864033753688133561)
    ·
      refine ⟨8145060648025315266100171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10860080864033753688133561 8145060648025315266100171)
      ·
        refine ⟨12217590972037972899150257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8145060648025315266100171 12217590972037972899150257)
        ·
          refine ⟨9163193229028479674362693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12217590972037972899150257 9163193229028479674362693)
          ·
            refine ⟨1718098730442839938943005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9163193229028479674362693 1718098730442839938943005)
            ·
              refine ⟨644287023916064977103627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1718098730442839938943005 644287023916064977103627)
              ·
                refine ⟨966430535874097465655441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 644287023916064977103627 966430535874097465655441)
                ·
                  refine ⟨724822901905573099241581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 966430535874097465655441 724822901905573099241581)
                  ·
                    refine ⟨271808588214589912215593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 724822901905573099241581 271808588214589912215593)
                    ·
                      refine ⟨203856441160942434161695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 271808588214589912215593 203856441160942434161695)
                      ·
                        rfl

theorem cell23_397009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 1, 2, 3, 2].length) (baseStart_397009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_397009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_397009 prefixEnd_397009 := by exact prefixLift 397009
  have htrace : WordTrace (prefixWord ++ tailWord_397009) baseStart_397009 baseEnd_397009 := by
    simpa [prefixWord, tailWord_397009, baseEnd_397009] using wordTrace_append hprefix tailTrace_397009
  have hstable : (prefixWord ++ tailWord_397009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397009).length < 2 ^ (prefixWord ++ tailWord_397009).sum := by decide
  have hdescent : baseEnd_397009 < baseStart_397009 := by decide
  rcases family_descends (prefixWord ++ tailWord_397009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397015 : List Nat := [1, 1, 3, 2, 1, 3, 1, 4, 1, 6]
def baseStart_397015 : Nat := 118140960795 + 397015 * 2 ^ 59
def prefixEnd_397015 : Nat := 4983230072969 + 3 ^ 40 * 397015 * 2
def baseEnd_397015 : Nat := 67953174014956470228889

theorem tailTrace_397015 : CollatzResearch.WordTrace tailWord_397015 prefixEnd_397015 67953174014956470228889 := by
  unfold tailWord_397015
  simp only [CollatzResearch.WordTrace]
  refine ⟨14480326656689934608896499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9653551104459956405930999 14480326656689934608896499)
  ·
    refine ⟨21720489985034901913344749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14480326656689934608896499 21720489985034901913344749)
    ·
      refine ⟨8145183744388088217504281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21720489985034901913344749 8145183744388088217504281)
      ·
        refine ⟨6108887808291066163128211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8145183744388088217504281 6108887808291066163128211)
        ·
          refine ⟨9163331712436599244692317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6108887808291066163128211 9163331712436599244692317)
          ·
            refine ⟨3436249392163724716759619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9163331712436599244692317 3436249392163724716759619)
            ·
              refine ⟨5154374088245587075139429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3436249392163724716759619 5154374088245587075139429)
              ·
                refine ⟨966445141546047576588643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5154374088245587075139429 966445141546047576588643)
                ·
                  refine ⟨1449667712319071364882965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 966445141546047576588643 1449667712319071364882965)
                  ·
                    refine ⟨67953174014956470228889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1449667712319071364882965 67953174014956470228889)
                    ·
                      rfl

theorem cell23_397015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 4, 1, 6].length) (baseStart_397015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_397015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_397015 prefixEnd_397015 := by exact prefixLift 397015
  have htrace : WordTrace (prefixWord ++ tailWord_397015) baseStart_397015 baseEnd_397015 := by
    simpa [prefixWord, tailWord_397015, baseEnd_397015] using wordTrace_append hprefix tailTrace_397015
  have hstable : (prefixWord ++ tailWord_397015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397015).length < 2 ^ (prefixWord ++ tailWord_397015).sum := by decide
  have hdescent : baseEnd_397015 < baseStart_397015 := by decide
  rcases family_descends (prefixWord ++ tailWord_397015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397016 : List Nat := [2, 1, 2, 2, 3, 1, 4, 3, 1, 1, 3]
def baseStart_397016 : Nat := 118140960795 + 397016 * 2 ^ 59
def prefixEnd_397016 : Nat := 4983230072969 + 3 ^ 40 * 397016 * 2
def baseEnd_397016 : Nat := 203860035525523906774163

theorem tailTrace_397016 : CollatzResearch.WordTrace tailWord_397016 prefixEnd_397016 203860035525523906774163 := by
  unfold tailWord_397016
  simp only [CollatzResearch.WordTrace]
  refine ⟨7240181564843155889841451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9653575419790874519788601 7240181564843155889841451)
  ·
    refine ⟨10860272347264733834762177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7240181564843155889841451 10860272347264733834762177)
    ·
      refine ⟨8145204260448550376071633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10860272347264733834762177 8145204260448550376071633)
      ·
        refine ⟨6108903195336412782053725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8145204260448550376071633 6108903195336412782053725)
        ·
          refine ⟨2290838698251154793270147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6108903195336412782053725 2290838698251154793270147)
          ·
            refine ⟨3436258047376732189905221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2290838698251154793270147 3436258047376732189905221)
            ·
              refine ⟨644298383883137285607229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3436258047376732189905221 644298383883137285607229)
              ·
                refine ⟨241611893956176482102711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 644298383883137285607229 241611893956176482102711)
                ·
                  refine ⟨362417840934264723154067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 241611893956176482102711 362417840934264723154067)
                  ·
                    refine ⟨543626761401397084731101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 362417840934264723154067 543626761401397084731101)
                    ·
                      refine ⟨203860035525523906774163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 543626761401397084731101 203860035525523906774163)
                      ·
                        rfl

theorem cell23_397016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 3, 1, 1, 3].length) (baseStart_397016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_397016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_397016 prefixEnd_397016 := by exact prefixLift 397016
  have htrace : WordTrace (prefixWord ++ tailWord_397016) baseStart_397016 baseEnd_397016 := by
    simpa [prefixWord, tailWord_397016, baseEnd_397016] using wordTrace_append hprefix tailTrace_397016
  have hstable : (prefixWord ++ tailWord_397016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397016).length < 2 ^ (prefixWord ++ tailWord_397016).sum := by decide
  have hdescent : baseEnd_397016 < baseStart_397016 := by decide
  rcases family_descends (prefixWord ++ tailWord_397016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397035 : List Nat := [1, 1, 1, 1, 2, 4, 2, 2, 3, 2, 4]
def baseStart_397035 : Nat := 118140960795 + 397035 * 2 ^ 59
def prefixEnd_397035 : Nat := 4983230072969 + 3 ^ 40 * 397035 * 2
def baseEnd_397035 : Nat := 203869791657959332436575

theorem tailTrace_397035 : CollatzResearch.WordTrace tailWord_397035 prefixEnd_397035 203869791657959332436575 := by
  unfold tailWord_397035
  simp only [CollatzResearch.WordTrace]
  refine ⟨14481056116617478024624559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9654037411078318683083039 14481056116617478024624559)
  ·
    refine ⟨21721584174926217036936839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14481056116617478024624559 21721584174926217036936839)
    ·
      refine ⟨32582376262389325555405259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21721584174926217036936839 32582376262389325555405259)
      ·
        refine ⟨48873564393583988333107889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32582376262389325555405259 48873564393583988333107889)
        ·
          refine ⟨36655173295187991249830917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48873564393583988333107889 36655173295187991249830917)
          ·
            refine ⟨6872844992847748359343297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36655173295187991249830917 6872844992847748359343297)
            ·
              refine ⟨5154633744635811269507473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6872844992847748359343297 5154633744635811269507473)
              ·
                refine ⟨3865975308476858452130605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5154633744635811269507473 3865975308476858452130605)
                ·
                  refine ⟨1449740740678821919548977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3865975308476858452130605 1449740740678821919548977)
                  ·
                    refine ⟨1087305555509116439661733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1449740740678821919548977 1087305555509116439661733)
                    ·
                      refine ⟨203869791657959332436575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1087305555509116439661733 203869791657959332436575)
                      ·
                        rfl

theorem cell23_397035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 3, 2, 4].length) (baseStart_397035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_397035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_397035 prefixEnd_397035 := by exact prefixLift 397035
  have htrace : WordTrace (prefixWord ++ tailWord_397035) baseStart_397035 baseEnd_397035 := by
    simpa [prefixWord, tailWord_397035, baseEnd_397035] using wordTrace_append hprefix tailTrace_397035
  have hstable : (prefixWord ++ tailWord_397035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397035).length < 2 ^ (prefixWord ++ tailWord_397035).sum := by decide
  have hdescent : baseEnd_397035 < baseStart_397035 := by decide
  rcases family_descends (prefixWord ++ tailWord_397035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
