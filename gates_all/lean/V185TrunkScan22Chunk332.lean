import V185TrunkScan22Chunk331

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2961899 : List Nat := [1, 1, 1, 1, 2, 3, 3, 6, 1, 3]
def baseStart_2961899 : Nat := 118140960795 + 2961899 * 2 ^ 59
def prefixEnd_2961899 : Nat := 4983230072969 + 3 ^ 40 * 2961899 * 2
def baseEnd_2961899 : Nat := 1013918558047608193493987

theorem tailTrace_2961899 : CollatzResearch.WordTrace tailWord_2961899 prefixEnd_2961899 1013918558047608193493987 := by
  unfold tailWord_2961899
  simp only [CollatzResearch.WordTrace]
  refine ⟨108029331496553249921368751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72019554331035499947579167 108029331496553249921368751)
  ·
    refine ⟨162043997244829874882053127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108029331496553249921368751 162043997244829874882053127)
    ·
      refine ⟨243065995867244812323079691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162043997244829874882053127 243065995867244812323079691)
      ·
        refine ⟨364598993800867218484619537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243065995867244812323079691 364598993800867218484619537)
        ·
          refine ⟨273449245350650413863464653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 364598993800867218484619537 273449245350650413863464653)
          ·
            refine ⟨102543467006493905198799245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 273449245350650413863464653 102543467006493905198799245)
            ·
              refine ⟨38453800127435214449549717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102543467006493905198799245 38453800127435214449549717)
              ·
                refine ⟨1802521880973525677322643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 38453800127435214449549717 1802521880973525677322643)
                ·
                  refine ⟨2703782821460288515983965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1802521880973525677322643 2703782821460288515983965)
                  ·
                    refine ⟨1013918558047608193493987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2703782821460288515983965 1013918558047608193493987)
                    ·
                      rfl

theorem cell22_2961899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 6, 1, 3].length) (baseStart_2961899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2961899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2961899 prefixEnd_2961899 := by exact prefixLift 2961899
  have htrace : WordTrace (prefixWord ++ tailWord_2961899) baseStart_2961899 baseEnd_2961899 := by
    simpa [prefixWord, tailWord_2961899, baseEnd_2961899] using wordTrace_append hprefix tailTrace_2961899
  have hstable : (prefixWord ++ tailWord_2961899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2961899).length < 2 ^ (prefixWord ++ tailWord_2961899).sum := by decide
  have hdescent : baseEnd_2961899 < baseStart_2961899 := by decide
  rcases family_descends (prefixWord ++ tailWord_2961899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2961957 : List Nat := [1, 3, 1, 2, 2, 1, 5, 1, 6]
def baseStart_2961957 : Nat := 118140960795 + 2961957 * 2 ^ 59
def prefixEnd_2961957 : Nat := 4983230072969 + 3 ^ 40 * 2961957 * 2
def baseEnd_2961957 : Nat := 337979470877638458514603

theorem tailTrace_2961957 : CollatzResearch.WordTrace tailWord_2961957 prefixEnd_2961957 337979470877638458514603 := by
  unfold tailWord_2961957
  simp only [CollatzResearch.WordTrace]
  refine ⟨108031446930343125826980125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72020964620228750551320083 108031446930343125826980125)
  ·
    refine ⟨40511792598878672185117547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108031446930343125826980125 40511792598878672185117547)
    ·
      refine ⟨60767688898318008277676321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40511792598878672185117547 60767688898318008277676321)
      ·
        refine ⟨45575766673738506208257241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60767688898318008277676321 45575766673738506208257241)
        ·
          refine ⟨34181825005303879656192931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45575766673738506208257241 34181825005303879656192931)
          ·
            refine ⟨51272737507955819484289397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34181825005303879656192931 51272737507955819484289397)
            ·
              refine ⟨4806819141370858076652131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51272737507955819484289397 4806819141370858076652131)
              ·
                refine ⟨7210228712056287114978197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4806819141370858076652131 7210228712056287114978197)
                ·
                  refine ⟨337979470877638458514603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7210228712056287114978197 337979470877638458514603)
                  ·
                    rfl

theorem cell22_2961957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 1, 6].length) (baseStart_2961957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2961957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2961957 prefixEnd_2961957 := by exact prefixLift 2961957
  have htrace : WordTrace (prefixWord ++ tailWord_2961957) baseStart_2961957 baseEnd_2961957 := by
    simpa [prefixWord, tailWord_2961957, baseEnd_2961957] using wordTrace_append hprefix tailTrace_2961957
  have hstable : (prefixWord ++ tailWord_2961957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2961957).length < 2 ^ (prefixWord ++ tailWord_2961957).sum := by decide
  have hdescent : baseEnd_2961957 < baseStart_2961957 := by decide
  rcases family_descends (prefixWord ++ tailWord_2961957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2962004 : List Nat := [2, 4, 1, 1, 1, 3, 2, 2, 2, 4]
def baseStart_2962004 : Nat := 118140960795 + 2962004 * 2 ^ 59
def prefixEnd_2962004 : Nat := 4983230072969 + 3 ^ 40 * 2962004 * 2
def baseEnd_2962004 : Nat := 1013954501693422919618665

theorem tailTrace_2962004 : CollatzResearch.WordTrace tailWord_2962004 prefixEnd_2962004 1013954501693422919618665 := by
  unfold tailWord_2962004
  simp only [CollatzResearch.WordTrace]
  refine ⟨54016580580586426426970533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72022107440781901902627377 54016580580586426426970533)
  ·
    refine ⟨10128108858859954955056975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54016580580586426426970533 10128108858859954955056975)
    ·
      refine ⟨15192163288289932432585463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10128108858859954955056975 15192163288289932432585463)
      ·
        refine ⟨22788244932434898648878195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15192163288289932432585463 22788244932434898648878195)
        ·
          refine ⟨34182367398652347973317293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22788244932434898648878195 34182367398652347973317293)
          ·
            refine ⟨12818387774494630489993985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34182367398652347973317293 12818387774494630489993985)
            ·
              refine ⟨9613790830870972867495489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12818387774494630489993985 9613790830870972867495489)
              ·
                refine ⟨7210343123153229650621617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9613790830870972867495489 7210343123153229650621617)
                ·
                  refine ⟨5407757342364922237966213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7210343123153229650621617 5407757342364922237966213)
                  ·
                    refine ⟨1013954501693422919618665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5407757342364922237966213 1013954501693422919618665)
                    ·
                      rfl

theorem cell22_2962004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_2962004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2962004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2962004 prefixEnd_2962004 := by exact prefixLift 2962004
  have htrace : WordTrace (prefixWord ++ tailWord_2962004) baseStart_2962004 baseEnd_2962004 := by
    simpa [prefixWord, tailWord_2962004, baseEnd_2962004] using wordTrace_append hprefix tailTrace_2962004
  have hstable : (prefixWord ++ tailWord_2962004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2962004).length < 2 ^ (prefixWord ++ tailWord_2962004).sum := by decide
  have hdescent : baseEnd_2962004 < baseStart_2962004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2962004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2962038 : List Nat := [5, 1, 1, 2, 3, 2, 1, 1, 2, 4]
def baseStart_2962038 : Nat := 118140960795 + 2962038 * 2 ^ 59
def prefixEnd_2962038 : Nat := 4983230072969 + 3 ^ 40 * 2962038 * 2
def baseEnd_2962038 : Nat := 1013966140588258164268561

theorem tailTrace_2962038 : CollatzResearch.WordTrace tailWord_2962038 prefixEnd_2962038 1013966140588258164268561 := by
  unfold tailWord_2962038
  simp only [CollatzResearch.WordTrace]
  refine ⟨6752150077690604791292423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72022934162033117773785845 6752150077690604791292423)
  ·
    refine ⟨10128225116535907186938635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6752150077690604791292423 10128225116535907186938635)
    ·
      refine ⟨15192337674803860780407953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10128225116535907186938635 15192337674803860780407953)
      ·
        refine ⟨11394253256102895585305965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15192337674803860780407953 11394253256102895585305965)
        ·
          refine ⟨4272844971038585844489737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11394253256102895585305965 4272844971038585844489737)
          ·
            refine ⟨3204633728278939383367303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4272844971038585844489737 3204633728278939383367303)
            ·
              refine ⟨4806950592418409075050955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3204633728278939383367303 4806950592418409075050955)
              ·
                refine ⟨7210425888627613612576433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4806950592418409075050955 7210425888627613612576433)
                ·
                  refine ⟨5407819416470710209432325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7210425888627613612576433 5407819416470710209432325)
                  ·
                    refine ⟨1013966140588258164268561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5407819416470710209432325 1013966140588258164268561)
                    ·
                      rfl

theorem cell22_2962038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 1, 2, 4].length) (baseStart_2962038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2962038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2962038 prefixEnd_2962038 := by exact prefixLift 2962038
  have htrace : WordTrace (prefixWord ++ tailWord_2962038) baseStart_2962038 baseEnd_2962038 := by
    simpa [prefixWord, tailWord_2962038, baseEnd_2962038] using wordTrace_append hprefix tailTrace_2962038
  have hstable : (prefixWord ++ tailWord_2962038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2962038).length < 2 ^ (prefixWord ++ tailWord_2962038).sum := by decide
  have hdescent : baseEnd_2962038 < baseStart_2962038 := by decide
  rcases family_descends (prefixWord ++ tailWord_2962038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2962051 : List Nat := [1, 1, 1, 3, 3, 1, 3, 5, 1, 3]
def baseStart_2962051 : Nat := 118140960795 + 2962051 * 2 ^ 59
def prefixEnd_2962051 : Nat := 4983230072969 + 3 ^ 40 * 2962051 * 2
def baseEnd_2962051 : Nat := 1013970590753930463693521

theorem tailTrace_2962051 : CollatzResearch.WordTrace tailWord_2962051 prefixEnd_2962051 1013970590753930463693521 := by
  unfold tailWord_2962051
  simp only [CollatzResearch.WordTrace]
  refine ⟨108034875392002579880902007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72023250261335053253934671 108034875392002579880902007)
  ·
    refine ⟨162052313088003869821353011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108034875392002579880902007 162052313088003869821353011)
    ·
      refine ⟨243078469632005804732029517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162052313088003869821353011 243078469632005804732029517)
      ·
        refine ⟨91154426112002176774511069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 243078469632005804732029517 91154426112002176774511069)
        ·
          refine ⟨34182909792000816290441651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91154426112002176774511069 34182909792000816290441651)
          ·
            refine ⟨51274364688001224435662477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34182909792000816290441651 51274364688001224435662477)
            ·
              refine ⟨19227886758000459163373429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51274364688001224435662477 19227886758000459163373429)
              ·
                refine ⟨1802614383562543046566259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19227886758000459163373429 1802614383562543046566259)
                ·
                  refine ⟨2703921575343814569849389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1802614383562543046566259 2703921575343814569849389)
                  ·
                    refine ⟨1013970590753930463693521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2703921575343814569849389 1013970590753930463693521)
                    ·
                      rfl

theorem cell22_2962051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 5, 1, 3].length) (baseStart_2962051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2962051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2962051 prefixEnd_2962051 := by exact prefixLift 2962051
  have htrace : WordTrace (prefixWord ++ tailWord_2962051) baseStart_2962051 baseEnd_2962051 := by
    simpa [prefixWord, tailWord_2962051, baseEnd_2962051] using wordTrace_append hprefix tailTrace_2962051
  have hstable : (prefixWord ++ tailWord_2962051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2962051).length < 2 ^ (prefixWord ++ tailWord_2962051).sum := by decide
  have hdescent : baseEnd_2962051 < baseStart_2962051 := by decide
  rcases family_descends (prefixWord ++ tailWord_2962051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2962068 : List Nat := [2, 4, 2, 2, 1, 2, 2, 1, 3, 3]
def baseStart_2962068 : Nat := 118140960795 + 2962068 * 2 ^ 59
def prefixEnd_2962068 : Nat := 4983230072969 + 3 ^ 40 * 2962068 * 2
def baseEnd_2962068 : Nat := 1013976410201348086018469

theorem tailTrace_2962068 : CollatzResearch.WordTrace tailWord_2962068 prefixEnd_2962068 1013976410201348086018469 := by
  unfold tailWord_2962068
  simp only [CollatzResearch.WordTrace]
  refine ⟨54017747716470495892135429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72023663621960661189513905 54017747716470495892135429)
  ·
    refine ⟨10128327696838217979775393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54017747716470495892135429 10128327696838217979775393)
    ·
      refine ⟨7596245772628663484831545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10128327696838217979775393 7596245772628663484831545)
      ·
        refine ⟨5697184329471497613623659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7596245772628663484831545 5697184329471497613623659)
        ·
          refine ⟨8545776494207246420435489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5697184329471497613623659 8545776494207246420435489)
          ·
            refine ⟨6409332370655434815326617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8545776494207246420435489 6409332370655434815326617)
            ·
              refine ⟨4806999277991576111494963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6409332370655434815326617 4806999277991576111494963)
              ·
                refine ⟨7210498916987364167242445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4806999277991576111494963 7210498916987364167242445)
                ·
                  refine ⟨2703937093870261562715917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7210498916987364167242445 2703937093870261562715917)
                  ·
                    refine ⟨1013976410201348086018469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2703937093870261562715917 1013976410201348086018469)
                    ·
                      rfl

theorem cell22_2962068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_2962068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2962068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2962068 prefixEnd_2962068 := by exact prefixLift 2962068
  have htrace : WordTrace (prefixWord ++ tailWord_2962068) baseStart_2962068 baseEnd_2962068 := by
    simpa [prefixWord, tailWord_2962068, baseEnd_2962068] using wordTrace_append hprefix tailTrace_2962068
  have hstable : (prefixWord ++ tailWord_2962068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2962068).length < 2 ^ (prefixWord ++ tailWord_2962068).sum := by decide
  have hdescent : baseEnd_2962068 < baseStart_2962068 := by decide
  rcases family_descends (prefixWord ++ tailWord_2962068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2962126 : List Nat := [4, 1, 1, 1, 3, 4, 1, 1, 6]
def baseStart_2962126 : Nat := 118140960795 + 2962126 * 2 ^ 59
def prefixEnd_2962126 : Nat := 4983230072969 + 3 ^ 40 * 2962126 * 2
def baseEnd_2962126 : Nat := 337998754928885089356097

theorem tailTrace_2962126 : CollatzResearch.WordTrace tailWord_2962126 prefixEnd_2962126 337998754928885089356097 := by
  unfold tailWord_2962126
  simp only [CollatzResearch.WordTrace]
  refine ⟨13504701358341358461235279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72025073911153911793254821 13504701358341358461235279)
  ·
    refine ⟨20257052037512037691852919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13504701358341358461235279 20257052037512037691852919)
    ·
      refine ⟨30385578056268056537779379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20257052037512037691852919 30385578056268056537779379)
      ·
        refine ⟨45578367084402084806669069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30385578056268056537779379 45578367084402084806669069)
        ·
          refine ⟨17091887656650781802500901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45578367084402084806669069 17091887656650781802500901)
          ·
            refine ⟨3204728935622021587968919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17091887656650781802500901 3204728935622021587968919)
            ·
              refine ⟨4807093403433032381953379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3204728935622021587968919 4807093403433032381953379)
              ·
                refine ⟨7210640105149548572930069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4807093403433032381953379 7210640105149548572930069)
                ·
                  refine ⟨337998754928885089356097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7210640105149548572930069 337998754928885089356097)
                  ·
                    rfl

theorem cell22_2962126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 1, 6].length) (baseStart_2962126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2962126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2962126 prefixEnd_2962126 := by exact prefixLift 2962126
  have htrace : WordTrace (prefixWord ++ tailWord_2962126) baseStart_2962126 baseEnd_2962126 := by
    simpa [prefixWord, tailWord_2962126, baseEnd_2962126] using wordTrace_append hprefix tailTrace_2962126
  have hstable : (prefixWord ++ tailWord_2962126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2962126).length < 2 ^ (prefixWord ++ tailWord_2962126).sum := by decide
  have hdescent : baseEnd_2962126 < baseStart_2962126 := by decide
  rcases family_descends (prefixWord ++ tailWord_2962126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2962184 : List Nat := [2, 1, 3, 2, 2, 2, 1, 1, 2, 6]
def baseStart_2962184 : Nat := 118140960795 + 2962184 * 2 ^ 59
def prefixEnd_2962184 : Nat := 4983230072969 + 3 ^ 40 * 2962184 * 2
def baseEnd_2962184 : Nat := 1014016119371962450118113

theorem tailTrace_2962184 : CollatzResearch.WordTrace tailWord_2962184 prefixEnd_2962184 1014016119371962450118113 := by
  unfold tailWord_2962184
  simp only [CollatzResearch.WordTrace]
  refine ⟨54019863150260371797746803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72026484200347162396995737 54019863150260371797746803)
  ·
    refine ⟨81029794725390557696620205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54019863150260371797746803 81029794725390557696620205)
    ·
      refine ⟨30386173022021459136232577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81029794725390557696620205 30386173022021459136232577)
      ·
        refine ⟨22789629766516094352174433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30386173022021459136232577 22789629766516094352174433)
        ·
          refine ⟨17092222324887070764130825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22789629766516094352174433 17092222324887070764130825)
          ·
            refine ⟨12819166743665303073098119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17092222324887070764130825 12819166743665303073098119)
            ·
              refine ⟨19228750115497954609647179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12819166743665303073098119 19228750115497954609647179)
              ·
                refine ⟨28843125173246931914470769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19228750115497954609647179 28843125173246931914470769)
                ·
                  refine ⟨21632343879935198935853077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28843125173246931914470769 21632343879935198935853077)
                  ·
                    refine ⟨1014016119371962450118113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21632343879935198935853077 1014016119371962450118113)
                    ·
                      rfl

theorem cell22_2962184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 2, 6].length) (baseStart_2962184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2962184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2962184 prefixEnd_2962184 := by exact prefixLift 2962184
  have htrace : WordTrace (prefixWord ++ tailWord_2962184) baseStart_2962184 baseEnd_2962184 := by
    simpa [prefixWord, tailWord_2962184, baseEnd_2962184] using wordTrace_append hprefix tailTrace_2962184
  have hstable : (prefixWord ++ tailWord_2962184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2962184).length < 2 ^ (prefixWord ++ tailWord_2962184).sum := by decide
  have hdescent : baseEnd_2962184 < baseStart_2962184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2962184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2962186 : List Nat := [3, 1, 2, 2, 1, 2, 2, 3, 3, 3]
def baseStart_2962186 : Nat := 118140960795 + 2962186 * 2 ^ 59
def prefixEnd_2962186 : Nat := 4983230072969 + 3 ^ 40 * 2962186 * 2
def baseEnd_2962186 : Nat := 1014016804012835111568107

theorem tailTrace_2962186 : CollatzResearch.WordTrace tailWord_2962186 prefixEnd_2962186 1014016804012835111568107 := by
  unfold tailWord_2962186
  simp only [CollatzResearch.WordTrace]
  refine ⟨27009949811628374484266603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72026532831008998624710941 27009949811628374484266603)
  ·
    refine ⟨40514924717442561726399905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27009949811628374484266603 40514924717442561726399905)
    ·
      refine ⟨30386193538081921294799929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40514924717442561726399905 30386193538081921294799929)
      ·
        refine ⟨22789645153561440971099947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30386193538081921294799929 22789645153561440971099947)
        ·
          refine ⟨34184467730342161456649921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22789645153561440971099947 34184467730342161456649921)
          ·
            refine ⟨25638350797756621092487441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34184467730342161456649921 25638350797756621092487441)
            ·
              refine ⟨19228763098317465819365581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25638350797756621092487441 19228763098317465819365581)
              ·
                refine ⟨7210786161869049682262093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19228763098317465819365581 7210786161869049682262093)
                ·
                  refine ⟨2704044810700893630848285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7210786161869049682262093 2704044810700893630848285)
                  ·
                    refine ⟨1014016804012835111568107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2704044810700893630848285 1014016804012835111568107)
                    ·
                      rfl

theorem cell22_2962186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 3, 3, 3].length) (baseStart_2962186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2962186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2962186 prefixEnd_2962186 := by exact prefixLift 2962186
  have htrace : WordTrace (prefixWord ++ tailWord_2962186) baseStart_2962186 baseEnd_2962186 := by
    simpa [prefixWord, tailWord_2962186, baseEnd_2962186] using wordTrace_append hprefix tailTrace_2962186
  have hstable : (prefixWord ++ tailWord_2962186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2962186).length < 2 ^ (prefixWord ++ tailWord_2962186).sum := by decide
  have hdescent : baseEnd_2962186 < baseStart_2962186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2962186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2962263 : List Nat := [1, 1, 3, 2, 4, 2, 2, 2, 1, 4]
def baseStart_2962263 : Nat := 118140960795 + 2962263 * 2 ^ 59
def prefixEnd_2962263 : Nat := 4983230072969 + 3 ^ 40 * 2962263 * 2
def baseEnd_2962263 : Nat := 1014043162686432577392871

theorem tailTrace_2962263 : CollatzResearch.WordTrace tailWord_2962263 prefixEnd_2962263 1014043162686432577392871 := by
  unfold tailWord_2962263
  simp only [CollatzResearch.WordTrace]
  refine ⟨108042607667234540087619443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72028405111489693391746295 108042607667234540087619443)
  ·
    refine ⟨162063911500851810131429165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108042607667234540087619443 162063911500851810131429165)
    ·
      refine ⟨60773966812819428799285937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162063911500851810131429165 60773966812819428799285937)
      ·
        refine ⟨45580475109614571599464453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60773966812819428799285937 45580475109614571599464453)
        ·
          refine ⟨8546339083052732174899585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45580475109614571599464453 8546339083052732174899585)
          ·
            refine ⟨6409754312289549131174689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8546339083052732174899585 6409754312289549131174689)
            ·
              refine ⟨4807315734217161848381017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6409754312289549131174689 4807315734217161848381017)
              ·
                refine ⟨3605486800662871386285763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4807315734217161848381017 3605486800662871386285763)
                ·
                  refine ⟨5408230200994307079428645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3605486800662871386285763 5408230200994307079428645)
                  ·
                    refine ⟨1014043162686432577392871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5408230200994307079428645 1014043162686432577392871)
                    ·
                      rfl

theorem cell22_2962263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 2, 1, 4].length) (baseStart_2962263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2962263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2962263 prefixEnd_2962263 := by exact prefixLift 2962263
  have htrace : WordTrace (prefixWord ++ tailWord_2962263) baseStart_2962263 baseEnd_2962263 := by
    simpa [prefixWord, tailWord_2962263, baseEnd_2962263] using wordTrace_append hprefix tailTrace_2962263
  have hstable : (prefixWord ++ tailWord_2962263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2962263).length < 2 ^ (prefixWord ++ tailWord_2962263).sum := by decide
  have hdescent : baseEnd_2962263 < baseStart_2962263 := by decide
  rcases family_descends (prefixWord ++ tailWord_2962263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2962289 : List Nat := [1, 2, 2, 2, 1, 4, 10]
def baseStart_2962289 : Nat := 118140960795 + 2962289 * 2 ^ 59
def prefixEnd_2962289 : Nat := 4983230072969 + 3 ^ 40 * 2962289 * 2
def baseEnd_2962289 : Nat := 37557483815473228749733

theorem tailTrace_2962289 : CollatzResearch.WordTrace tailWord_2962289 prefixEnd_2962289 37557483815473228749733 := by
  unfold tailWord_2962289
  simp only [CollatzResearch.WordTrace]
  refine ⟨108043555965140346528065921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72029037310093564352043947 108043555965140346528065921)
  ·
    refine ⟨81032666973855259896049441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108043555965140346528065921 81032666973855259896049441)
    ·
      refine ⟨60774500230391444922037081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81032666973855259896049441 60774500230391444922037081)
      ·
        refine ⟨45580875172793583691527811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60774500230391444922037081 45580875172793583691527811)
        ·
          refine ⟨68371312759190375537291717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45580875172793583691527811 68371312759190375537291717)
          ·
            refine ⟨12819621142348195413242197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68371312759190375537291717 12819621142348195413242197)
            ·
              refine ⟨37557483815473228749733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 12819621142348195413242197 37557483815473228749733)
              ·
                rfl

theorem cell22_2962289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 10].length) (baseStart_2962289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2962289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2962289 prefixEnd_2962289 := by exact prefixLift 2962289
  have htrace : WordTrace (prefixWord ++ tailWord_2962289) baseStart_2962289 baseEnd_2962289 := by
    simpa [prefixWord, tailWord_2962289, baseEnd_2962289] using wordTrace_append hprefix tailTrace_2962289
  have hstable : (prefixWord ++ tailWord_2962289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2962289).length < 2 ^ (prefixWord ++ tailWord_2962289).sum := by decide
  have hdescent : baseEnd_2962289 < baseStart_2962289 := by decide
  rcases family_descends (prefixWord ++ tailWord_2962289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2962293 : List Nat := [1, 3, 4, 1, 1, 2, 2, 1, 4, 3]
def baseStart_2962293 : Nat := 118140960795 + 2962293 * 2 ^ 59
def prefixEnd_2962293 : Nat := 4983230072969 + 3 ^ 40 * 2962293 * 2
def baseEnd_2962293 : Nat := 1014053432299522499142779

theorem tailTrace_2962293 : CollatzResearch.WordTrace tailWord_2962293 prefixEnd_2962293 1014053432299522499142779 := by
  unfold tailWord_2962293
  simp only [CollatzResearch.WordTrace]
  refine ⟨108043701857125855211211533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72029134571417236807474355 108043701857125855211211533)
  ·
    refine ⟨40516388196422195704204325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108043701857125855211211533 40516388196422195704204325)
    ·
      refine ⟨7596822786829161694538311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40516388196422195704204325 7596822786829161694538311)
      ·
        refine ⟨11395234180243742541807467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7596822786829161694538311 11395234180243742541807467)
        ·
          refine ⟨17092851270365613812711201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11395234180243742541807467 17092851270365613812711201)
          ·
            refine ⟨12819638452774210359533401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17092851270365613812711201 12819638452774210359533401)
            ·
              refine ⟨9614728839580657769650051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12819638452774210359533401 9614728839580657769650051)
              ·
                refine ⟨14422093259370986654475077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9614728839580657769650051 14422093259370986654475077)
                ·
                  refine ⟨2704142486132059997714077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14422093259370986654475077 2704142486132059997714077)
                  ·
                    refine ⟨1014053432299522499142779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2704142486132059997714077 1014053432299522499142779)
                    ·
                      rfl

theorem cell22_2962293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_2962293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2962293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2962293 prefixEnd_2962293 := by exact prefixLift 2962293
  have htrace : WordTrace (prefixWord ++ tailWord_2962293) baseStart_2962293 baseEnd_2962293 := by
    simpa [prefixWord, tailWord_2962293, baseEnd_2962293] using wordTrace_append hprefix tailTrace_2962293
  have hstable : (prefixWord ++ tailWord_2962293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2962293).length < 2 ^ (prefixWord ++ tailWord_2962293).sum := by decide
  have hdescent : baseEnd_2962293 < baseStart_2962293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2962293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2962304 : List Nat := [2, 1, 1, 2, 1, 2, 2, 2, 2, 7]
def baseStart_2962304 : Nat := 118140960795 + 2962304 * 2 ^ 59
def prefixEnd_2962304 : Nat := 4983230072969 + 3 ^ 40 * 2962304 * 2
def baseEnd_2962304 : Nat := 1014057197824322137117745

theorem tailTrace_2962304 : CollatzResearch.WordTrace tailWord_2962304 prefixEnd_2962304 1014057197824322137117745 := by
  unfold tailWord_2962304
  simp only [CollatzResearch.WordTrace]
  refine ⟨54022051530043002044930983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72029402040057336059907977 54022051530043002044930983)
  ·
    refine ⟨81033077295064503067396475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54022051530043002044930983 81033077295064503067396475)
    ·
      refine ⟨121549615942596754601094713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81033077295064503067396475 121549615942596754601094713)
      ·
        refine ⟨91162211956947565950821035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121549615942596754601094713 91162211956947565950821035)
        ·
          refine ⟨136743317935421348926231553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91162211956947565950821035 136743317935421348926231553)
          ·
            refine ⟨102557488451566011694673665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136743317935421348926231553 102557488451566011694673665)
            ·
              refine ⟨76918116338674508771005249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102557488451566011694673665 76918116338674508771005249)
              ·
                refine ⟨57688587254005881578253937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76918116338674508771005249 57688587254005881578253937)
                ·
                  refine ⟨43266440440504411183690453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57688587254005881578253937 43266440440504411183690453)
                  ·
                    refine ⟨1014057197824322137117745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43266440440504411183690453 1014057197824322137117745)
                    ·
                      rfl

theorem cell22_2962304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 2, 7].length) (baseStart_2962304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2962304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2962304 prefixEnd_2962304 := by exact prefixLift 2962304
  have htrace : WordTrace (prefixWord ++ tailWord_2962304) baseStart_2962304 baseEnd_2962304 := by
    simpa [prefixWord, tailWord_2962304, baseEnd_2962304] using wordTrace_append hprefix tailTrace_2962304
  have hstable : (prefixWord ++ tailWord_2962304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2962304).length < 2 ^ (prefixWord ++ tailWord_2962304).sum := by decide
  have hdescent : baseEnd_2962304 < baseStart_2962304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2962304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2962321 : List Nat := [1, 2, 2, 1, 1, 1, 3, 3, 5, 3]
def baseStart_2962321 : Nat := 118140960795 + 2962321 * 2 ^ 59
def prefixEnd_2962321 : Nat := 4983230072969 + 3 ^ 40 * 2962321 * 2
def baseEnd_2962321 : Nat := 1014063017271739759442693

theorem tailTrace_2962321 : CollatzResearch.WordTrace tailWord_2962321 prefixEnd_2962321 1014063017271739759442693 := by
  unfold tailWord_2962321
  simp only [CollatzResearch.WordTrace]
  refine ⟨108044723101024415993230817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72029815400682943995487211 108044723101024415993230817)
  ·
    refine ⟨81033542325768311994923113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108044723101024415993230817 81033542325768311994923113)
    ·
      refine ⟨60775156744326233996192335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81033542325768311994923113 60775156744326233996192335)
      ·
        refine ⟨91162735116489350994288503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60775156744326233996192335 91162735116489350994288503)
        ·
          refine ⟨136744102674734026491432755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91162735116489350994288503 136744102674734026491432755)
          ·
            refine ⟨205116154012101039737149133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136744102674734026491432755 205116154012101039737149133)
            ·
              refine ⟨76918557754537889901430925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 205116154012101039737149133 76918557754537889901430925)
              ·
                refine ⟨28844459157951708713036597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76918557754537889901430925 28844459157951708713036597)
                ·
                  refine ⟨2704168046057972691847181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28844459157951708713036597 2704168046057972691847181)
                  ·
                    refine ⟨1014063017271739759442693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2704168046057972691847181 1014063017271739759442693)
                    ·
                      rfl

theorem cell22_2962321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 5, 3].length) (baseStart_2962321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2962321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2962321 prefixEnd_2962321 := by exact prefixLift 2962321
  have htrace : WordTrace (prefixWord ++ tailWord_2962321) baseStart_2962321 baseEnd_2962321 := by
    simpa [prefixWord, tailWord_2962321, baseEnd_2962321] using wordTrace_append hprefix tailTrace_2962321
  have hstable : (prefixWord ++ tailWord_2962321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2962321).length < 2 ^ (prefixWord ++ tailWord_2962321).sum := by decide
  have hdescent : baseEnd_2962321 < baseStart_2962321 := by decide
  rcases family_descends (prefixWord ++ tailWord_2962321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2962372 : List Nat := [2, 3, 3, 3, 1, 1, 1, 2, 3, 3]
def baseStart_2962372 : Nat := 118140960795 + 2962372 * 2 ^ 59
def prefixEnd_2962372 : Nat := 4983230072969 + 3 ^ 40 * 2962372 * 2
def baseEnd_2962372 : Nat := 1014080475613992626417537

theorem tailTrace_2962372 : CollatzResearch.WordTrace tailWord_2962372 prefixEnd_2962372 1014080475613992626417537 := by
  unfold tailWord_2962372
  simp only [CollatzResearch.WordTrace]
  refine ⟨54023291611919825851668685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72031055482559767802224913 54023291611919825851668685)
  ·
    refine ⟨20258734354469934694375757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54023291611919825851668685 20258734354469934694375757)
    ·
      refine ⟨7597025382926225510390909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20258734354469934694375757 7597025382926225510390909)
      ·
        refine ⟨2848884518597334566396591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7597025382926225510390909 2848884518597334566396591)
        ·
          refine ⟨4273326777896001849594887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2848884518597334566396591 4273326777896001849594887)
          ·
            refine ⟨6409990166844002774392331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4273326777896001849594887 6409990166844002774392331)
            ·
              refine ⟨9614985250266004161588497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6409990166844002774392331 9614985250266004161588497)
              ·
                refine ⟨7211238937699503121191373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9614985250266004161588497 7211238937699503121191373)
                ·
                  refine ⟨2704214601637313670446765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7211238937699503121191373 2704214601637313670446765)
                  ·
                    refine ⟨1014080475613992626417537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2704214601637313670446765 1014080475613992626417537)
                    ·
                      rfl

theorem cell22_2962372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_2962372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2962372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2962372 prefixEnd_2962372 := by exact prefixLift 2962372
  have htrace : WordTrace (prefixWord ++ tailWord_2962372) baseStart_2962372 baseEnd_2962372 := by
    simpa [prefixWord, tailWord_2962372, baseEnd_2962372] using wordTrace_append hprefix tailTrace_2962372
  have hstable : (prefixWord ++ tailWord_2962372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2962372).length < 2 ^ (prefixWord ++ tailWord_2962372).sum := by decide
  have hdescent : baseEnd_2962372 < baseStart_2962372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2962372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2962402 : List Nat := [3, 3, 3, 1, 1, 3, 1, 2, 5]
def baseStart_2962402 : Nat := 118140960795 + 2962402 * 2 ^ 59
def prefixEnd_2962402 : Nat := 4983230072969 + 3 ^ 40 * 2962402 * 2
def baseEnd_2962402 : Nat := 338030248409027516055815

theorem tailTrace_2962402 : CollatzResearch.WordTrace tailWord_2962402 prefixEnd_2962402 338030248409027516055815 := by
  unfold tailWord_2962402
  simp only [CollatzResearch.WordTrace]
  refine ⟨27011919353432741706732365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72031784942487311217952973 27011919353432741706732365)
  ·
    refine ⟨10129469757537278140024637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27011919353432741706732365 10129469757537278140024637)
    ·
      refine ⟨3798551159076479302509239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10129469757537278140024637 3798551159076479302509239)
      ·
        refine ⟨5697826738614718953763859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3798551159076479302509239 5697826738614718953763859)
        ·
          refine ⟨8546740107922078430645789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5697826738614718953763859 8546740107922078430645789)
          ·
            refine ⟨3205027540470779411492171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8546740107922078430645789 3205027540470779411492171)
            ·
              refine ⟨4807541310706169117238257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3205027540470779411492171 4807541310706169117238257)
              ·
                refine ⟨3605655983029626837928693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4807541310706169117238257 3605655983029626837928693)
                ·
                  refine ⟨338030248409027516055815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3605655983029626837928693 338030248409027516055815)
                  ·
                    rfl

theorem cell22_2962402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 2, 5].length) (baseStart_2962402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2962402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2962402 prefixEnd_2962402 := by exact prefixLift 2962402
  have htrace : WordTrace (prefixWord ++ tailWord_2962402) baseStart_2962402 baseEnd_2962402 := by
    simpa [prefixWord, tailWord_2962402, baseEnd_2962402] using wordTrace_append hprefix tailTrace_2962402
  have hstable : (prefixWord ++ tailWord_2962402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2962402).length < 2 ^ (prefixWord ++ tailWord_2962402).sum := by decide
  have hdescent : baseEnd_2962402 < baseStart_2962402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2962402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2962428 : List Nat := [2, 2, 2, 1, 2, 3, 3, 1, 1, 5]
def baseStart_2962428 : Nat := 118140960795 + 2962428 * 2 ^ 59
def prefixEnd_2962428 : Nat := 4983230072969 + 3 ^ 40 * 2962428 * 2
def baseEnd_2962428 : Nat := 1014099645558427147017365

theorem tailTrace_2962428 : CollatzResearch.WordTrace tailWord_2962428 prefixEnd_2962428 1014099645558427147017365 := by
  unfold tailWord_2962428
  simp only [CollatzResearch.WordTrace]
  refine ⟨54024312855818386633687969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72032417141091182178250625 54024312855818386633687969)
  ·
    refine ⟨40518234641863789975265977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54024312855818386633687969 40518234641863789975265977)
    ·
      refine ⟨30388675981397842481449483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40518234641863789975265977 30388675981397842481449483)
      ·
        refine ⟨45583013972096763722174225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30388675981397842481449483 45583013972096763722174225)
        ·
          refine ⟨34187260479072572791630669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45583013972096763722174225 34187260479072572791630669)
          ·
            refine ⟨12820222679652214796861501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34187260479072572791630669 12820222679652214796861501)
            ·
              refine ⟨4807583504869580548823063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12820222679652214796861501 4807583504869580548823063)
              ·
                refine ⟨7211375257304370823234595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4807583504869580548823063 7211375257304370823234595)
                ·
                  refine ⟨10817062885956556234851893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7211375257304370823234595 10817062885956556234851893)
                  ·
                    refine ⟨1014099645558427147017365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10817062885956556234851893 1014099645558427147017365)
                    ·
                      rfl

theorem cell22_2962428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 1, 1, 5].length) (baseStart_2962428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2962428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2962428 prefixEnd_2962428 := by exact prefixLift 2962428
  have htrace : WordTrace (prefixWord ++ tailWord_2962428) baseStart_2962428 baseEnd_2962428 := by
    simpa [prefixWord, tailWord_2962428, baseEnd_2962428] using wordTrace_append hprefix tailTrace_2962428
  have hstable : (prefixWord ++ tailWord_2962428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2962428).length < 2 ^ (prefixWord ++ tailWord_2962428).sum := by decide
  have hdescent : baseEnd_2962428 < baseStart_2962428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2962428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2962460 : List Nat := [2, 2, 3, 1, 4, 1, 1, 2, 2, 4]
def baseStart_2962460 : Nat := 118140960795 + 2962460 * 2 ^ 59
def prefixEnd_2962460 : Nat := 4983230072969 + 3 ^ 40 * 2962460 * 2
def baseEnd_2962460 : Nat := 1014110599812389730217267

theorem tailTrace_2962460 : CollatzResearch.WordTrace tailWord_2962460 prefixEnd_2962460 1014110599812389730217267 := by
  unfold tailWord_2962460
  simp only [CollatzResearch.WordTrace]
  refine ⟨54024896423760421366270417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72033195231680561821693889 54024896423760421366270417)
  ·
    refine ⟨40518672317820316024702813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54024896423760421366270417 40518672317820316024702813)
    ·
      refine ⟨15194502119182618509263555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40518672317820316024702813 15194502119182618509263555)
      ·
        refine ⟨22791753178773927763895333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15194502119182618509263555 22791753178773927763895333)
        ·
          refine ⟨4273453721020111455730375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22791753178773927763895333 4273453721020111455730375)
          ·
            refine ⟨6410180581530167183595563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4273453721020111455730375 6410180581530167183595563)
            ·
              refine ⟨9615270872295250775393345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6410180581530167183595563 9615270872295250775393345)
              ·
                refine ⟨7211453154221438081545009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9615270872295250775393345 7211453154221438081545009)
                ·
                  refine ⟨5408589865666078561158757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7211453154221438081545009 5408589865666078561158757)
                  ·
                    refine ⟨1014110599812389730217267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5408589865666078561158757 1014110599812389730217267)
                    ·
                      rfl

theorem cell22_2962460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_2962460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2962460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2962460 prefixEnd_2962460 := by exact prefixLift 2962460
  have htrace : WordTrace (prefixWord ++ tailWord_2962460) baseStart_2962460 baseEnd_2962460 := by
    simpa [prefixWord, tailWord_2962460, baseEnd_2962460] using wordTrace_append hprefix tailTrace_2962460
  have hstable : (prefixWord ++ tailWord_2962460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2962460).length < 2 ^ (prefixWord ++ tailWord_2962460).sum := by decide
  have hdescent : baseEnd_2962460 < baseStart_2962460 := by decide
  rcases family_descends (prefixWord ++ tailWord_2962460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2962464 : List Nat := [2, 1, 1, 7, 1, 1, 3, 2, 4]
def baseStart_2962464 : Nat := 118140960795 + 2962464 * 2 ^ 59
def prefixEnd_2962464 : Nat := 4983230072969 + 3 ^ 40 * 2962464 * 2
def baseEnd_2962464 : Nat := 338037323031378351039085

theorem tailTrace_2962464 : CollatzResearch.WordTrace tailWord_2962464 prefixEnd_2962464 338037323031378351039085 := by
  unfold tailWord_2962464
  simp only [CollatzResearch.WordTrace]
  refine ⟨54024969369753175707843223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72033292493004234277124297 54024969369753175707843223)
  ·
    refine ⟨81037454054629763561764835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54024969369753175707843223 81037454054629763561764835)
    ·
      refine ⟨121556181081944645342647253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81037454054629763561764835 121556181081944645342647253)
      ·
        refine ⟨2848972994108077625218295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 121556181081944645342647253 2848972994108077625218295)
        ·
          refine ⟨4273459491162116437827443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2848972994108077625218295 4273459491162116437827443)
          ·
            refine ⟨6410189236743174656741165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4273459491162116437827443 6410189236743174656741165)
            ·
              refine ⟨2403820963778690496277937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6410189236743174656741165 2403820963778690496277937)
              ·
                refine ⟨1802865722834017872208453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2403820963778690496277937 1802865722834017872208453)
                ·
                  refine ⟨338037323031378351039085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1802865722834017872208453 338037323031378351039085)
                  ·
                    rfl

theorem cell22_2962464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 3, 2, 4].length) (baseStart_2962464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2962464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2962464 prefixEnd_2962464 := by exact prefixLift 2962464
  have htrace : WordTrace (prefixWord ++ tailWord_2962464) baseStart_2962464 baseEnd_2962464 := by
    simpa [prefixWord, tailWord_2962464, baseEnd_2962464] using wordTrace_append hprefix tailTrace_2962464
  have hstable : (prefixWord ++ tailWord_2962464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2962464).length < 2 ^ (prefixWord ++ tailWord_2962464).sum := by decide
  have hdescent : baseEnd_2962464 < baseStart_2962464 := by decide
  rcases family_descends (prefixWord ++ tailWord_2962464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2962533 : List Nat := [1, 3, 1, 3, 2, 1, 1, 1, 5, 4]
def baseStart_2962533 : Nat := 118140960795 + 2962533 * 2 ^ 59
def prefixEnd_2962533 : Nat := 4983230072969 + 3 ^ 40 * 2962533 * 2
def baseEnd_2962533 : Nat := 1014135589204241873142043

theorem tailTrace_2962533 : CollatzResearch.WordTrace tailWord_2962533 prefixEnd_2962533 1014135589204241873142043 := by
  unfold tailWord_2962533
  simp only [CollatzResearch.WordTrace]
  refine ⟨108052455376256376199948253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72034970250837584133298835 108052455376256376199948253)
  ·
    refine ⟨40519670766096141074980595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108052455376256376199948253 40519670766096141074980595)
    ·
      refine ⟨60779506149144211612470893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40519670766096141074980595 60779506149144211612470893)
      ·
        refine ⟨22792314805929079354676585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60779506149144211612470893 22792314805929079354676585)
        ·
          refine ⟨17094236104446809516007439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22792314805929079354676585 17094236104446809516007439)
          ·
            refine ⟨25641354156670214274011159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17094236104446809516007439 25641354156670214274011159)
            ·
              refine ⟨38462031235005321411016739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25641354156670214274011159 38462031235005321411016739)
              ·
                refine ⟨57693046852507982116525109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38462031235005321411016739 57693046852507982116525109)
                ·
                  refine ⟨5408723142422623323424229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57693046852507982116525109 5408723142422623323424229)
                  ·
                    refine ⟨1014135589204241873142043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5408723142422623323424229 1014135589204241873142043)
                    ·
                      rfl

theorem cell22_2962533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 5, 4].length) (baseStart_2962533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2962533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2962533 prefixEnd_2962533 := by exact prefixLift 2962533
  have htrace : WordTrace (prefixWord ++ tailWord_2962533) baseStart_2962533 baseEnd_2962533 := by
    simpa [prefixWord, tailWord_2962533, baseEnd_2962533] using wordTrace_append hprefix tailTrace_2962533
  have hstable : (prefixWord ++ tailWord_2962533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2962533).length < 2 ^ (prefixWord ++ tailWord_2962533).sum := by decide
  have hdescent : baseEnd_2962533 < baseStart_2962533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2962533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2962550 : List Nat := [5, 1, 1, 2, 1, 1, 1, 3, 3, 4]
def baseStart_2962550 : Nat := 118140960795 + 2962550 * 2 ^ 59
def prefixEnd_2962550 : Nat := 4983230072969 + 3 ^ 40 * 2962550 * 2
def baseEnd_2962550 : Nat := 1014141408651659495466991

theorem tailTrace_2962550 : CollatzResearch.WordTrace tailWord_2962550 prefixEnd_2962550 1014141408651659495466991 := by
  unfold tailWord_2962550
  simp only [CollatzResearch.WordTrace]
  refine ⟨6753317213574674256457319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72035383611463192068878069 6753317213574674256457319)
  ·
    refine ⟨10129975820362011384685979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6753317213574674256457319 10129975820362011384685979)
    ·
      refine ⟨15194963730543017077028969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10129975820362011384685979 15194963730543017077028969)
      ·
        refine ⟨11396222797907262807771727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15194963730543017077028969 11396222797907262807771727)
        ·
          refine ⟨17094334196860894211657591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11396222797907262807771727 17094334196860894211657591)
          ·
            refine ⟨25641501295291341317486387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17094334196860894211657591 25641501295291341317486387)
            ·
              refine ⟨38462251942937011976229581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25641501295291341317486387 38462251942937011976229581)
              ·
                refine ⟨14423344478601379491086093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38462251942937011976229581 14423344478601379491086093)
                ·
                  refine ⟨5408754179475517309157285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14423344478601379491086093 5408754179475517309157285)
                  ·
                    refine ⟨1014141408651659495466991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5408754179475517309157285 1014141408651659495466991)
                    ·
                      rfl

theorem cell22_2962550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_2962550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2962550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2962550 prefixEnd_2962550 := by exact prefixLift 2962550
  have htrace : WordTrace (prefixWord ++ tailWord_2962550) baseStart_2962550 baseEnd_2962550 := by
    simpa [prefixWord, tailWord_2962550, baseEnd_2962550] using wordTrace_append hprefix tailTrace_2962550
  have hstable : (prefixWord ++ tailWord_2962550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2962550).length < 2 ^ (prefixWord ++ tailWord_2962550).sum := by decide
  have hdescent : baseEnd_2962550 < baseStart_2962550 := by decide
  rcases family_descends (prefixWord ++ tailWord_2962550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2962563 : List Nat := [1, 1, 1, 3, 3, 2, 1, 4, 1, 5]
def baseStart_2962563 : Nat := 118140960795 + 2962563 * 2 ^ 59
def prefixEnd_2962563 : Nat := 4983230072969 + 3 ^ 40 * 2962563 * 2
def baseEnd_2962563 : Nat := 1014145858817331794891951

theorem tailTrace_2962563 : CollatzResearch.WordTrace tailWord_2962563 prefixEnd_2962563 1014145858817331794891951 := by
  unfold tailWord_2962563
  simp only [CollatzResearch.WordTrace]
  refine ⟨108053549566147691323540343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72035699710765127549026895 108053549566147691323540343)
  ·
    refine ⟨162080324349221536985310515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108053549566147691323540343 162080324349221536985310515)
    ·
      refine ⟨243120486523832305477965773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162080324349221536985310515 243120486523832305477965773)
      ·
        refine ⟨91170182446437114554237165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 243120486523832305477965773 91170182446437114554237165)
        ·
          refine ⟨34188818417413917957838937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91170182446437114554237165 34188818417413917957838937)
          ·
            refine ⟨25641613813060438468379203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34188818417413917957838937 25641613813060438468379203)
            ·
              refine ⟨38462420719590657702568805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25641613813060438468379203 38462420719590657702568805)
              ·
                refine ⟨7211703884923248319231651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38462420719590657702568805 7211703884923248319231651)
                ·
                  refine ⟨10817555827384872478847477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7211703884923248319231651 10817555827384872478847477)
                  ·
                    refine ⟨1014145858817331794891951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10817555827384872478847477 1014145858817331794891951)
                    ·
                      rfl

theorem cell22_2962563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 4, 1, 5].length) (baseStart_2962563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2962563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2962563 prefixEnd_2962563 := by exact prefixLift 2962563
  have htrace : WordTrace (prefixWord ++ tailWord_2962563) baseStart_2962563 baseEnd_2962563 := by
    simpa [prefixWord, tailWord_2962563, baseEnd_2962563] using wordTrace_append hprefix tailTrace_2962563
  have hstable : (prefixWord ++ tailWord_2962563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2962563).length < 2 ^ (prefixWord ++ tailWord_2962563).sum := by decide
  have hdescent : baseEnd_2962563 < baseStart_2962563 := by decide
  rcases family_descends (prefixWord ++ tailWord_2962563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2962593 : List Nat := [1, 2, 3, 3, 1, 1, 2, 9]
def baseStart_2962593 : Nat := 118140960795 + 2962593 * 2 ^ 59
def prefixEnd_2962593 : Nat := 4983230072969 + 3 ^ 40 * 2962593 * 2
def baseEnd_2962593 : Nat := 112684014270046857404651

theorem tailTrace_2962593 : CollatzResearch.WordTrace tailWord_2962593 prefixEnd_2962593 112684014270046857404651 := by
  unfold tailWord_2962593
  simp only [CollatzResearch.WordTrace]
  refine ⟨108054643756039006447132433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72036429170692670964754955 108054643756039006447132433)
  ·
    refine ⟨81040982817029254835349325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108054643756039006447132433 81040982817029254835349325)
    ·
      refine ⟨30390368556385970563255997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81040982817029254835349325 30390368556385970563255997)
      ·
        refine ⟨11396388208644738961220999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30390368556385970563255997 11396388208644738961220999)
        ·
          refine ⟨17094582312967108441831499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11396388208644738961220999 17094582312967108441831499)
          ·
            refine ⟨25641873469450662662747249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17094582312967108441831499 25641873469450662662747249)
            ·
              refine ⟨19231405102087996997060437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25641873469450662662747249 19231405102087996997060437)
              ·
                refine ⟨112684014270046857404651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19231405102087996997060437 112684014270046857404651)
                ·
                  rfl

theorem cell22_2962593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 9].length) (baseStart_2962593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2962593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2962593 prefixEnd_2962593 := by exact prefixLift 2962593
  have htrace : WordTrace (prefixWord ++ tailWord_2962593) baseStart_2962593 baseEnd_2962593 := by
    simpa [prefixWord, tailWord_2962593, baseEnd_2962593] using wordTrace_append hprefix tailTrace_2962593
  have hstable : (prefixWord ++ tailWord_2962593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2962593).length < 2 ^ (prefixWord ++ tailWord_2962593).sum := by decide
  have hdescent : baseEnd_2962593 < baseStart_2962593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2962593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2962610 : List Nat := [3, 2, 1, 1, 1, 4, 4, 6]
def baseStart_2962610 : Nat := 118140960795 + 2962610 * 2 ^ 59
def prefixEnd_2962610 : Nat := 4983230072969 + 3 ^ 40 * 2962610 * 2
def baseEnd_2962610 : Nat := 112684660875315482107423

theorem tailTrace_2962610 : CollatzResearch.WordTrace tailWord_2962610 prefixEnd_2962610 112684660875315482107423 := by
  unfold tailWord_2962610
  simp only [CollatzResearch.WordTrace]
  refine ⟨27013815949244354587625321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72036842531318278900334189 27013815949244354587625321)
  ·
    refine ⟨20260361961933265940718991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27013815949244354587625321 20260361961933265940718991)
    ·
      refine ⟨30390542942899898911078487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20260361961933265940718991 30390542942899898911078487)
      ·
        refine ⟨45585814414349848366617731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30390542942899898911078487 45585814414349848366617731)
        ·
          refine ⟨68378721621524772549926597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45585814414349848366617731 68378721621524772549926597)
          ·
            refine ⟨12821010304035894853111237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68378721621524772549926597 12821010304035894853111237)
            ·
              refine ⟨2403939432006730284958357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12821010304035894853111237 2403939432006730284958357)
              ·
                refine ⟨112684660875315482107423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2403939432006730284958357 112684660875315482107423)
                ·
                  rfl

theorem cell22_2962610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 4, 6].length) (baseStart_2962610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2962610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2962610 prefixEnd_2962610 := by exact prefixLift 2962610
  have htrace : WordTrace (prefixWord ++ tailWord_2962610) baseStart_2962610 baseEnd_2962610 := by
    simpa [prefixWord, tailWord_2962610, baseEnd_2962610] using wordTrace_append hprefix tailTrace_2962610
  have hstable : (prefixWord ++ tailWord_2962610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2962610).length < 2 ^ (prefixWord ++ tailWord_2962610).sum := by decide
  have hdescent : baseEnd_2962610 < baseStart_2962610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2962610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2962715 : List Nat := [1, 1, 1, 1, 1, 1, 5, 2, 6, 3]
def baseStart_2962715 : Nat := 118140960795 + 2962715 * 2 ^ 59
def prefixEnd_2962715 : Nat := 4983230072969 + 3 ^ 40 * 2962715 * 2
def baseEnd_2962715 : Nat := 1014197891523654065091485

theorem tailTrace_2962715 : CollatzResearch.WordTrace tailWord_2962715 prefixEnd_2962715 1014197891523654065091485 := by
  unfold tailWord_2962715
  simp only [CollatzResearch.WordTrace]
  refine ⟨108059093461597021283073599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72039395641064680855382399 108059093461597021283073599)
  ·
    refine ⟨162088640192395531924610399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108059093461597021283073599 162088640192395531924610399)
    ·
      refine ⟨243132960288593297886915599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162088640192395531924610399 243132960288593297886915599)
      ·
        refine ⟨364699440432889946830373399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243132960288593297886915599 364699440432889946830373399)
        ·
          refine ⟨547049160649334920245560099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 364699440432889946830373399 547049160649334920245560099)
          ·
            refine ⟨820573740974002380368340149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 547049160649334920245560099 820573740974002380368340149)
            ·
              refine ⟨76928788216312723159531889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 820573740974002380368340149 76928788216312723159531889)
              ·
                refine ⟨57696591162234542369648917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76928788216312723159531889 57696591162234542369648917)
                ·
                  refine ⟨2704527710729744173577293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 57696591162234542369648917 2704527710729744173577293)
                  ·
                    refine ⟨1014197891523654065091485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2704527710729744173577293 1014197891523654065091485)
                    ·
                      rfl

theorem cell22_2962715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 6, 3].length) (baseStart_2962715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2962715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2962715 prefixEnd_2962715 := by exact prefixLift 2962715
  have htrace : WordTrace (prefixWord ++ tailWord_2962715) baseStart_2962715 baseEnd_2962715 := by
    simpa [prefixWord, tailWord_2962715, baseEnd_2962715] using wordTrace_append hprefix tailTrace_2962715
  have hstable : (prefixWord ++ tailWord_2962715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2962715).length < 2 ^ (prefixWord ++ tailWord_2962715).sum := by decide
  have hdescent : baseEnd_2962715 < baseStart_2962715 := by decide
  rcases family_descends (prefixWord ++ tailWord_2962715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2962717 : List Nat := [1, 4, 2, 3, 1, 2, 1, 2, 6]
def baseStart_2962717 : Nat := 118140960795 + 2962717 * 2 ^ 59
def prefixEnd_2962717 : Nat := 4983230072969 + 3 ^ 40 * 2962717 * 2
def baseEnd_2962717 : Nat := 338066192054842242180493

theorem tailTrace_2962717 : CollatzResearch.WordTrace tailWord_2962717 prefixEnd_2962717 338066192054842242180493 := by
  unfold tailWord_2962717
  simp only [CollatzResearch.WordTrace]
  refine ⟨108059166407589775624646405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72039444271726517083097603 108059166407589775624646405)
  ·
    refine ⟨20261093701423082929621201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108059166407589775624646405 20261093701423082929621201)
    ·
      refine ⟨15195820276067312197215901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20261093701423082929621201 15195820276067312197215901)
      ·
        refine ⟨5698432603525242073955963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15195820276067312197215901 5698432603525242073955963)
        ·
          refine ⟨8547648905287863110933945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5698432603525242073955963 8547648905287863110933945)
          ·
            refine ⟨6410736678965897333200459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8547648905287863110933945 6410736678965897333200459)
            ·
              refine ⟨9616105018448845999800689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6410736678965897333200459 9616105018448845999800689)
              ·
                refine ⟨7212078763836634499850517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9616105018448845999800689 7212078763836634499850517)
                ·
                  refine ⟨338066192054842242180493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7212078763836634499850517 338066192054842242180493)
                  ·
                    rfl

theorem cell22_2962717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 2, 6].length) (baseStart_2962717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2962717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2962717 prefixEnd_2962717 := by exact prefixLift 2962717
  have htrace : WordTrace (prefixWord ++ tailWord_2962717) baseStart_2962717 baseEnd_2962717 := by
    simpa [prefixWord, tailWord_2962717, baseEnd_2962717] using wordTrace_append hprefix tailTrace_2962717
  have hstable : (prefixWord ++ tailWord_2962717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2962717).length < 2 ^ (prefixWord ++ tailWord_2962717).sum := by decide
  have hdescent : baseEnd_2962717 < baseStart_2962717 := by decide
  rcases family_descends (prefixWord ++ tailWord_2962717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2962777 : List Nat := [1, 2, 1, 2, 2, 2, 4, 2, 3, 3]
def baseStart_2962777 : Nat := 118140960795 + 2962777 * 2 ^ 59
def prefixEnd_2962777 : Nat := 4983230072969 + 3 ^ 40 * 2962777 * 2
def baseEnd_2962777 : Nat := 1014219115390706570041295

theorem tailTrace_2962777 : CollatzResearch.WordTrace tailWord_2962777 prefixEnd_2962777 1014219115390706570041295 := by
  unfold tailWord_2962777
  simp only [CollatzResearch.WordTrace]
  refine ⟨108061354787372405871830585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72040903191581603914553723 108061354787372405871830585)
  ·
    refine ⟨81046016090529304403872939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108061354787372405871830585 81046016090529304403872939)
    ·
      refine ⟨121569024135793956605809409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81046016090529304403872939 121569024135793956605809409)
      ·
        refine ⟨91176768101845467454357057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121569024135793956605809409 91176768101845467454357057)
        ·
          refine ⟨68382576076384100590767793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91176768101845467454357057 68382576076384100590767793)
          ·
            refine ⟨51286932057288075443075845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68382576076384100590767793 51286932057288075443075845)
            ·
              refine ⟨9616299760741514145576721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51286932057288075443075845 9616299760741514145576721)
              ·
                refine ⟨7212224820556135609182541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9616299760741514145576721 7212224820556135609182541)
                ·
                  refine ⟨2704584307708550853443453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7212224820556135609182541 2704584307708550853443453)
                  ·
                    refine ⟨1014219115390706570041295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2704584307708550853443453 1014219115390706570041295)
                    ·
                      rfl

theorem cell22_2962777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 2, 3, 3].length) (baseStart_2962777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2962777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2962777 prefixEnd_2962777 := by exact prefixLift 2962777
  have htrace : WordTrace (prefixWord ++ tailWord_2962777) baseStart_2962777 baseEnd_2962777 := by
    simpa [prefixWord, tailWord_2962777, baseEnd_2962777] using wordTrace_append hprefix tailTrace_2962777
  have hstable : (prefixWord ++ tailWord_2962777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2962777).length < 2 ^ (prefixWord ++ tailWord_2962777).sum := by decide
  have hdescent : baseEnd_2962777 < baseStart_2962777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2962777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2962811 : List Nat := [1, 1, 1, 1, 1, 6, 5, 2, 1, 3]
def baseStart_2962811 : Nat := 118140960795 + 2962811 * 2 ^ 59
def prefixEnd_2962811 : Nat := 4983230072969 + 3 ^ 40 * 2962811 * 2
def baseEnd_2962811 : Nat := 1014230754285541814691191

theorem tailTrace_2962811 : CollatzResearch.WordTrace tailWord_2962811 prefixEnd_2962811 1014230754285541814691191 := by
  unfold tailWord_2962811
  simp only [CollatzResearch.WordTrace]
  refine ⟨108062594869249229678568287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72041729912832819785712191 108062594869249229678568287)
  ·
    refine ⟨162093892303873844517852431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108062594869249229678568287 162093892303873844517852431)
    ·
      refine ⟨243140838455810766776778647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162093892303873844517852431 243140838455810766776778647)
      ·
        refine ⟨364711257683716150165167971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243140838455810766776778647 364711257683716150165167971)
        ·
          refine ⟨547066886525574225247751957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 364711257683716150165167971 547066886525574225247751957)
          ·
            refine ⟨25643760305886291808488373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 547066886525574225247751957 25643760305886291808488373)
            ·
              refine ⟨2404102528676839857045785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25643760305886291808488373 2404102528676839857045785)
              ·
                refine ⟨1803076896507629892784339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2404102528676839857045785 1803076896507629892784339)
                ·
                  refine ⟨2704615344761444839176509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1803076896507629892784339 2704615344761444839176509)
                  ·
                    refine ⟨1014230754285541814691191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2704615344761444839176509 1014230754285541814691191)
                    ·
                      rfl

theorem cell22_2962811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 5, 2, 1, 3].length) (baseStart_2962811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2962811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2962811 prefixEnd_2962811 := by exact prefixLift 2962811
  have htrace : WordTrace (prefixWord ++ tailWord_2962811) baseStart_2962811 baseEnd_2962811 := by
    simpa [prefixWord, tailWord_2962811, baseEnd_2962811] using wordTrace_append hprefix tailTrace_2962811
  have hstable : (prefixWord ++ tailWord_2962811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2962811).length < 2 ^ (prefixWord ++ tailWord_2962811).sum := by decide
  have hdescent : baseEnd_2962811 < baseStart_2962811 := by decide
  rcases family_descends (prefixWord ++ tailWord_2962811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2962824 : List Nat := [2, 1, 3, 3, 1, 2, 4, 1, 5]
def baseStart_2962824 : Nat := 118140960795 + 2962824 * 2 ^ 59
def prefixEnd_2962824 : Nat := 4983230072969 + 3 ^ 40 * 2962824 * 2
def baseEnd_2962824 : Nat := 338078401483738038038717

theorem tailTrace_2962824 : CollatzResearch.WordTrace tailWord_2962824 prefixEnd_2962824 338078401483738038038717 := by
  unfold tailWord_2962824
  simp only [CollatzResearch.WordTrace]
  refine ⟨54031534509101066449395763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72042046012134755265861017 54031534509101066449395763)
  ·
    refine ⟨81047301763651599674093645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54031534509101066449395763 81047301763651599674093645)
    ·
      refine ⟨30392738161369349877785117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81047301763651599674093645 30392738161369349877785117)
      ·
        refine ⟨11397276810513506204169419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30392738161369349877785117 11397276810513506204169419)
        ·
          refine ⟨17095915215770259306254129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11397276810513506204169419 17095915215770259306254129)
          ·
            refine ⟨12821936411827694479690597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17095915215770259306254129 12821936411827694479690597)
            ·
              refine ⟨2404113077217692714941987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12821936411827694479690597 2404113077217692714941987)
              ·
                refine ⟨3606169615826539072412981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2404113077217692714941987 3606169615826539072412981)
                ·
                  refine ⟨338078401483738038038717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3606169615826539072412981 338078401483738038038717)
                  ·
                    rfl

theorem cell22_2962824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 4, 1, 5].length) (baseStart_2962824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2962824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2962824 prefixEnd_2962824 := by exact prefixLift 2962824
  have htrace : WordTrace (prefixWord ++ tailWord_2962824) baseStart_2962824 baseEnd_2962824 := by
    simpa [prefixWord, tailWord_2962824, baseEnd_2962824] using wordTrace_append hprefix tailTrace_2962824
  have hstable : (prefixWord ++ tailWord_2962824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2962824).length < 2 ^ (prefixWord ++ tailWord_2962824).sum := by decide
  have hdescent : baseEnd_2962824 < baseStart_2962824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2962824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2962867 : List Nat := [1, 1, 1, 2, 3, 1, 1, 5, 4, 3]
def baseStart_2962867 : Nat := 118140960795 + 2962867 * 2 ^ 59
def prefixEnd_2962867 : Nat := 4983230072969 + 3 ^ 40 * 2962867 * 2
def baseEnd_2962867 : Nat := 1014249924229976335291019

theorem tailTrace_2962867 : CollatzResearch.WordTrace tailWord_2962867 prefixEnd_2962867 1014249924229976335291019 := by
  unfold tailWord_2962867
  simp only [CollatzResearch.WordTrace]
  refine ⟨108064637357046351242606855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72043091571364234161737903 108064637357046351242606855)
  ·
    refine ⟨162096956035569526863910283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108064637357046351242606855 162096956035569526863910283)
    ·
      refine ⟨243145434053354290295865425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162096956035569526863910283 243145434053354290295865425)
      ·
        refine ⟨182359075540015717721899069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243145434053354290295865425 182359075540015717721899069)
        ·
          refine ⟨68384653327505894145712151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 182359075540015717721899069 68384653327505894145712151)
          ·
            refine ⟨102576979991258841218568227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68384653327505894145712151 102576979991258841218568227)
            ·
              refine ⟨153865469986888261827852341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102576979991258841218568227 153865469986888261827852341)
              ·
                refine ⟨14424887811270774546361157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 153865469986888261827852341 14424887811270774546361157)
                ·
                  refine ⟨2704666464613270227442717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14424887811270774546361157 2704666464613270227442717)
                  ·
                    refine ⟨1014249924229976335291019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2704666464613270227442717 1014249924229976335291019)
                    ·
                      rfl

theorem cell22_2962867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 5, 4, 3].length) (baseStart_2962867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2962867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2962867 prefixEnd_2962867 := by exact prefixLift 2962867
  have htrace : WordTrace (prefixWord ++ tailWord_2962867) baseStart_2962867 baseEnd_2962867 := by
    simpa [prefixWord, tailWord_2962867, baseEnd_2962867] using wordTrace_append hprefix tailTrace_2962867
  have hstable : (prefixWord ++ tailWord_2962867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2962867).length < 2 ^ (prefixWord ++ tailWord_2962867).sum := by decide
  have hdescent : baseEnd_2962867 < baseStart_2962867 := by decide
  rcases family_descends (prefixWord ++ tailWord_2962867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2962884 : List Nat := [2, 3, 3, 2, 1, 1, 1, 3, 1, 5]
def baseStart_2962884 : Nat := 118140960795 + 2962884 * 2 ^ 59
def prefixEnd_2962884 : Nat := 4983230072969 + 3 ^ 40 * 2962884 * 2
def baseEnd_2962884 : Nat := 1014255743677393957615967

theorem tailTrace_2962884 : CollatzResearch.WordTrace tailWord_2962884 prefixEnd_2962884 1014255743677393957615967 := by
  unfold tailWord_2962884
  simp only [CollatzResearch.WordTrace]
  refine ⟨54032628698992381572987853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72043504931989842097317137 54032628698992381572987853)
  ·
    refine ⟨20262235762122143089870445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54032628698992381572987853 20262235762122143089870445)
    ·
      refine ⟨7598338410795803658701417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20262235762122143089870445 7598338410795803658701417)
      ·
        refine ⟨5698753808096852744026063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7598338410795803658701417 5698753808096852744026063)
        ·
          refine ⟨8548130712145279116039095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5698753808096852744026063 8548130712145279116039095)
          ·
            refine ⟨12822196068217918674058643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8548130712145279116039095 12822196068217918674058643)
            ·
              refine ⟨19233294102326878011087965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12822196068217918674058643 19233294102326878011087965)
              ·
                refine ⟨7212485288372579254157987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19233294102326878011087965 7212485288372579254157987)
                ·
                  refine ⟨10818727932558868881236981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7212485288372579254157987 10818727932558868881236981)
                  ·
                    refine ⟨1014255743677393957615967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10818727932558868881236981 1014255743677393957615967)
                    ·
                      rfl

theorem cell22_2962884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_2962884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2962884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2962884 prefixEnd_2962884 := by exact prefixLift 2962884
  have htrace : WordTrace (prefixWord ++ tailWord_2962884) baseStart_2962884 baseEnd_2962884 := by
    simpa [prefixWord, tailWord_2962884, baseEnd_2962884] using wordTrace_append hprefix tailTrace_2962884
  have hstable : (prefixWord ++ tailWord_2962884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2962884).length < 2 ^ (prefixWord ++ tailWord_2962884).sum := by decide
  have hdescent : baseEnd_2962884 < baseStart_2962884 := by decide
  rcases family_descends (prefixWord ++ tailWord_2962884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2962929 : List Nat := [1, 2, 2, 2, 3, 2, 1, 3, 3, 3]
def baseStart_2962929 : Nat := 118140960795 + 2962929 * 2 ^ 59
def prefixEnd_2962929 : Nat := 4983230072969 + 3 ^ 40 * 2962929 * 2
def baseEnd_2962929 : Nat := 1014271148097028840240829

theorem tailTrace_2962929 : CollatzResearch.WordTrace tailWord_2962929 prefixEnd_2962929 1014271148097028840240829 := by
  unfold tailWord_2962929
  simp only [CollatzResearch.WordTrace]
  refine ⟨108066898682821735831363841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72044599121881157220909227 108066898682821735831363841)
  ·
    refine ⟨81050174012116301873522881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108066898682821735831363841 81050174012116301873522881)
    ·
      refine ⟨60787630509087226405142161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81050174012116301873522881 60787630509087226405142161)
      ·
        refine ⟨45590722881815419803856621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60787630509087226405142161 45590722881815419803856621)
        ·
          refine ⟨17096521080680782426446233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45590722881815419803856621 17096521080680782426446233)
          ·
            refine ⟨12822390810510586819834675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17096521080680782426446233 12822390810510586819834675)
            ·
              refine ⟨19233586215765880229752013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12822390810510586819834675 19233586215765880229752013)
              ·
                refine ⟨7212594830912205086157005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19233586215765880229752013 7212594830912205086157005)
                ·
                  refine ⟨2704723061592076907308877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7212594830912205086157005 2704723061592076907308877)
                  ·
                    refine ⟨1014271148097028840240829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2704723061592076907308877 1014271148097028840240829)
                    ·
                      rfl

theorem cell22_2962929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 3, 3, 3].length) (baseStart_2962929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2962929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2962929 prefixEnd_2962929 := by exact prefixLift 2962929
  have htrace : WordTrace (prefixWord ++ tailWord_2962929) baseStart_2962929 baseEnd_2962929 := by
    simpa [prefixWord, tailWord_2962929, baseEnd_2962929] using wordTrace_append hprefix tailTrace_2962929
  have hstable : (prefixWord ++ tailWord_2962929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2962929).length < 2 ^ (prefixWord ++ tailWord_2962929).sum := by decide
  have hdescent : baseEnd_2962929 < baseStart_2962929 := by decide
  rcases family_descends (prefixWord ++ tailWord_2962929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2962948 : List Nat := [2, 3, 2, 3, 3, 1, 2, 6]
def baseStart_2962948 : Nat := 118140960795 + 2962948 * 2 ^ 59
def prefixEnd_2962948 : Nat := 4983230072969 + 3 ^ 40 * 2962948 * 2
def baseEnd_2962948 : Nat := 112697516909479902668419

theorem tailTrace_2962948 : CollatzResearch.WordTrace tailWord_2962948 prefixEnd_2962948 112697516909479902668419 := by
  unfold tailWord_2962948
  simp only [CollatzResearch.WordTrace]
  refine ⟨54033795834876451038152749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72045061113168601384203665 54033795834876451038152749)
  ·
    refine ⟨20262673438078669139307281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54033795834876451038152749 20262673438078669139307281)
    ·
      refine ⟨15197005078559001854480461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20262673438078669139307281 15197005078559001854480461)
      ·
        refine ⟨5698876904459625695430173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15197005078559001854480461 5698876904459625695430173)
        ·
          refine ⟨2137078839172359635786315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5698876904459625695430173 2137078839172359635786315)
          ·
            refine ⟨3205618258758539453679473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2137078839172359635786315 3205618258758539453679473)
            ·
              refine ⟨2404213694068904590259605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3205618258758539453679473 2404213694068904590259605)
              ·
                refine ⟨112697516909479902668419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2404213694068904590259605 112697516909479902668419)
                ·
                  rfl

theorem cell22_2962948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 2, 6].length) (baseStart_2962948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2962948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2962948 prefixEnd_2962948 := by exact prefixLift 2962948
  have htrace : WordTrace (prefixWord ++ tailWord_2962948) baseStart_2962948 baseEnd_2962948 := by
    simpa [prefixWord, tailWord_2962948, baseEnd_2962948] using wordTrace_append hprefix tailTrace_2962948
  have hstable : (prefixWord ++ tailWord_2962948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2962948).length < 2 ^ (prefixWord ++ tailWord_2962948).sum := by decide
  have hdescent : baseEnd_2962948 < baseStart_2962948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2962948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2962963 : List Nat := [1, 1, 1, 2, 1, 8, 1, 3, 1, 3]
def baseStart_2962963 : Nat := 118140960795 + 2962963 * 2 ^ 59
def prefixEnd_2962963 : Nat := 4983230072969 + 3 ^ 40 * 2962963 * 2
def baseEnd_2962963 : Nat := 1014282786991864084890725

theorem tailTrace_2962963 : CollatzResearch.WordTrace tailWord_2962963 prefixEnd_2962963 1014282786991864084890725 := by
  unfold tailWord_2962963
  simp only [CollatzResearch.WordTrace]
  refine ⟨108068138764698559638101543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72045425843132373092067695 108068138764698559638101543)
  ·
    refine ⟨162102208147047839457152315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108068138764698559638101543 162102208147047839457152315)
    ·
      refine ⟨243153312220571759185728473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162102208147047839457152315 243153312220571759185728473)
      ·
        refine ⟨182364984165428819389296355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243153312220571759185728473 182364984165428819389296355)
        ·
          refine ⟨273547476248143229083944533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182364984165428819389296355 273547476248143229083944533)
          ·
            refine ⟨3205634487282928465827475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 273547476248143229083944533 3205634487282928465827475)
            ·
              refine ⟨4808451730924392698741213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3205634487282928465827475 4808451730924392698741213)
              ·
                refine ⟨1803169399096647262027955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4808451730924392698741213 1803169399096647262027955)
                ·
                  refine ⟨2704754098644970893041933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1803169399096647262027955 2704754098644970893041933)
                  ·
                    refine ⟨1014282786991864084890725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2704754098644970893041933 1014282786991864084890725)
                    ·
                      rfl

theorem cell22_2962963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 3, 1, 3].length) (baseStart_2962963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2962963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2962963 prefixEnd_2962963 := by exact prefixLift 2962963
  have htrace : WordTrace (prefixWord ++ tailWord_2962963) baseStart_2962963 baseEnd_2962963 := by
    simpa [prefixWord, tailWord_2962963, baseEnd_2962963] using wordTrace_append hprefix tailTrace_2962963
  have hstable : (prefixWord ++ tailWord_2962963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2962963).length < 2 ^ (prefixWord ++ tailWord_2962963).sum := by decide
  have hdescent : baseEnd_2962963 < baseStart_2962963 := by decide
  rcases family_descends (prefixWord ++ tailWord_2962963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2963017 : List Nat := [1, 2, 1, 1, 2, 2, 1, 5, 1, 6]
def baseStart_2963017 : Nat := 118140960795 + 2963017 * 2 ^ 59
def prefixEnd_2963017 : Nat := 4983230072969 + 3 ^ 40 * 2963017 * 2
def baseEnd_2963017 : Nat := 1014301272295425944040559

theorem tailTrace_2963017 : CollatzResearch.WordTrace tailWord_2963017 prefixEnd_2963017 1014301272295425944040559 := by
  unfold tailWord_2963017
  simp only [CollatzResearch.WordTrace]
  refine ⟨108070108306502926860567305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72046738871001951240378203 108070108306502926860567305)
  ·
    refine ⟨81052581229877195145425479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108070108306502926860567305 81052581229877195145425479)
    ·
      refine ⟨121578871844815792718138219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81052581229877195145425479 121578871844815792718138219)
      ·
        refine ⟨182368307767223689077207329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121578871844815792718138219 182368307767223689077207329)
        ·
          refine ⟨136776230825417766807905497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182368307767223689077207329 136776230825417766807905497)
          ·
            refine ⟨102582173119063325105929123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136776230825417766807905497 102582173119063325105929123)
            ·
              refine ⟨153873259678594987658893685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102582173119063325105929123 153873259678594987658893685)
              ·
                refine ⟨14425618094868280093021283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 153873259678594987658893685 14425618094868280093021283)
                ·
                  refine ⟨21638427142302420139531925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14425618094868280093021283 21638427142302420139531925)
                  ·
                    refine ⟨1014301272295425944040559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21638427142302420139531925 1014301272295425944040559)
                    ·
                      rfl

theorem cell22_2963017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 5, 1, 6].length) (baseStart_2963017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2963017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2963017 prefixEnd_2963017 := by exact prefixLift 2963017
  have htrace : WordTrace (prefixWord ++ tailWord_2963017) baseStart_2963017 baseEnd_2963017 := by
    simpa [prefixWord, tailWord_2963017, baseEnd_2963017] using wordTrace_append hprefix tailTrace_2963017
  have hstable : (prefixWord ++ tailWord_2963017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2963017).length < 2 ^ (prefixWord ++ tailWord_2963017).sum := by decide
  have hdescent : baseEnd_2963017 < baseStart_2963017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2963017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2963109 : List Nat := [1, 3, 1, 2, 1, 2, 4, 1, 2, 5]
def baseStart_2963109 : Nat := 118140960795 + 2963109 * 2 ^ 59
def prefixEnd_2963109 : Nat := 4983230072969 + 3 ^ 40 * 2963109 * 2
def baseEnd_2963109 : Nat := 1014332765775568370740277

theorem tailTrace_2963109 : CollatzResearch.WordTrace tailWord_2963109 prefixEnd_2963109 1014332765775568370740277 := by
  unfold tailWord_2963109
  simp only [CollatzResearch.WordTrace]
  refine ⟨108073463822169626572916381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72048975881446417715277587 108073463822169626572916381)
  ·
    refine ⟨40527548933313609964843643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108073463822169626572916381 40527548933313609964843643)
    ·
      refine ⟨60791323399970414947265465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40527548933313609964843643 60791323399970414947265465)
      ·
        refine ⟨45593492549977811210449099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60791323399970414947265465 45593492549977811210449099)
        ·
          refine ⟨68390238824966716815673649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45593492549977811210449099 68390238824966716815673649)
          ·
            refine ⟨51292679118725037611755237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68390238824966716815673649 51292679118725037611755237)
            ·
              refine ⟨9617377334760944552204107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51292679118725037611755237 9617377334760944552204107)
              ·
                refine ⟨14426066002141416828306161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9617377334760944552204107 14426066002141416828306161)
                ·
                  refine ⟨10819549501606062621229621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14426066002141416828306161 10819549501606062621229621)
                  ·
                    refine ⟨1014332765775568370740277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10819549501606062621229621 1014332765775568370740277)
                    ·
                      rfl

theorem cell22_2963109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 1, 2, 5].length) (baseStart_2963109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2963109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2963109 prefixEnd_2963109 := by exact prefixLift 2963109
  have htrace : WordTrace (prefixWord ++ tailWord_2963109) baseStart_2963109 baseEnd_2963109 := by
    simpa [prefixWord, tailWord_2963109, baseEnd_2963109] using wordTrace_append hprefix tailTrace_2963109
  have hstable : (prefixWord ++ tailWord_2963109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2963109).length < 2 ^ (prefixWord ++ tailWord_2963109).sum := by decide
  have hdescent : baseEnd_2963109 < baseStart_2963109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2963109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2963149 : List Nat := [1, 6, 2, 1, 1, 2, 3, 2, 1, 3]
def baseStart_2963149 : Nat := 118140960795 + 2963149 * 2 ^ 59
def prefixEnd_2963149 : Nat := 4983230072969 + 3 ^ 40 * 2963149 * 2
def baseEnd_2963149 : Nat := 1014346458593021599740155

theorem tailTrace_2963149 : CollatzResearch.WordTrace tailWord_2963149 prefixEnd_2963149 1014346458593021599740155 := by
  unfold tailWord_2963149
  simp only [CollatzResearch.WordTrace]
  refine ⟨108074922742024713404372501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72049948494683142269581667 108074922742024713404372501)
  ·
    refine ⟨5066012003532408440829961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 108074922742024713404372501 5066012003532408440829961)
    ·
      refine ⟨3799509002649306330622471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5066012003532408440829961 3799509002649306330622471)
      ·
        refine ⟨5699263503973959495933707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3799509002649306330622471 5699263503973959495933707)
        ·
          refine ⟨8548895255960939243900561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5699263503973959495933707 8548895255960939243900561)
          ·
            refine ⟨6411671441970704432925421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8548895255960939243900561 6411671441970704432925421)
            ·
              refine ⟨2404376790739014162347033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6411671441970704432925421 2404376790739014162347033)
              ·
                refine ⟨1803282593054260621760275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2404376790739014162347033 1803282593054260621760275)
                ·
                  refine ⟨2704923889581390932640413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1803282593054260621760275 2704923889581390932640413)
                  ·
                    refine ⟨1014346458593021599740155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2704923889581390932640413 1014346458593021599740155)
                    ·
                      rfl

theorem cell22_2963149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_2963149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2963149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2963149 prefixEnd_2963149 := by exact prefixLift 2963149
  have htrace : WordTrace (prefixWord ++ tailWord_2963149) baseStart_2963149 baseEnd_2963149 := by
    simpa [prefixWord, tailWord_2963149, baseEnd_2963149] using wordTrace_append hprefix tailTrace_2963149
  have hstable : (prefixWord ++ tailWord_2963149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2963149).length < 2 ^ (prefixWord ++ tailWord_2963149).sum := by decide
  have hdescent : baseEnd_2963149 < baseStart_2963149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2963149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2963207 : List Nat := [1, 1, 4, 4, 2, 2, 2, 2, 4]
def baseStart_2963207 : Nat := 118140960795 + 2963207 * 2 ^ 59
def prefixEnd_2963207 : Nat := 4983230072969 + 3 ^ 40 * 2963207 * 2
def baseEnd_2963207 : Nat := 338122104392776260596659

theorem tailTrace_2963207 : CollatzResearch.WordTrace tailWord_2963207 prefixEnd_2963207 338122104392776260596659 := by
  unfold tailWord_2963207
  simp only [CollatzResearch.WordTrace]
  refine ⟨108077038175814589309983875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72051358783876392873322583 108077038175814589309983875)
  ·
    refine ⟨162115557263721883964975813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108077038175814589309983875 162115557263721883964975813)
    ·
      refine ⟨30396666986947853243432965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 162115557263721883964975813 30396666986947853243432965)
      ·
        refine ⟨5699375060052722483143681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30396666986947853243432965 5699375060052722483143681)
        ·
          refine ⟨4274531295039541862357761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5699375060052722483143681 4274531295039541862357761)
          ·
            refine ⟨3205898471279656396768321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4274531295039541862357761 3205898471279656396768321)
            ·
              refine ⟨2404423853459742297576241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3205898471279656396768321 2404423853459742297576241)
              ·
                refine ⟨1803317890094806723182181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2404423853459742297576241 1803317890094806723182181)
                ·
                  refine ⟨338122104392776260596659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1803317890094806723182181 338122104392776260596659)
                  ·
                    rfl

theorem cell22_2963207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 2, 2, 4].length) (baseStart_2963207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2963207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2963207 prefixEnd_2963207 := by exact prefixLift 2963207
  have htrace : WordTrace (prefixWord ++ tailWord_2963207) baseStart_2963207 baseEnd_2963207 := by
    simpa [prefixWord, tailWord_2963207, baseEnd_2963207] using wordTrace_append hprefix tailTrace_2963207
  have hstable : (prefixWord ++ tailWord_2963207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2963207).length < 2 ^ (prefixWord ++ tailWord_2963207).sum := by decide
  have hdescent : baseEnd_2963207 < baseStart_2963207 := by decide
  rcases family_descends (prefixWord ++ tailWord_2963207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2963218 : List Nat := [3, 2, 4, 1, 1, 1, 3, 7]
def baseStart_2963218 : Nat := 118140960795 + 2963218 * 2 ^ 59
def prefixEnd_2963218 : Nat := 4983230072969 + 3 ^ 40 * 2963218 * 2
def baseEnd_2963218 : Nat := 112707786522569824418327

theorem tailTrace_2963218 : CollatzResearch.WordTrace tailWord_2963218 prefixEnd_2963218 112707786522569824418327 := by
  unfold tailWord_2963218
  simp only [CollatzResearch.WordTrace]
  refine ⟨27019359844693684547158577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72051626252516492125756205 27019359844693684547158577)
  ·
    refine ⟨20264519883520263410368933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27019359844693684547158577 20264519883520263410368933)
    ·
      refine ⟨3799597478160049389444175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20264519883520263410368933 3799597478160049389444175)
      ·
        refine ⟨5699396217240074084166263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3799597478160049389444175 5699396217240074084166263)
        ·
          refine ⟨8549094325860111126249395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5699396217240074084166263 8549094325860111126249395)
          ·
            refine ⟨12823641488790166689374093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8549094325860111126249395 12823641488790166689374093)
            ·
              refine ⟨4808865558296312508515285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12823641488790166689374093 4808865558296312508515285)
              ·
                refine ⟨112707786522569824418327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4808865558296312508515285 112707786522569824418327)
                ·
                  rfl

theorem cell22_2963218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 7].length) (baseStart_2963218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2963218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2963218 prefixEnd_2963218 := by exact prefixLift 2963218
  have htrace : WordTrace (prefixWord ++ tailWord_2963218) baseStart_2963218 baseEnd_2963218 := by
    simpa [prefixWord, tailWord_2963218, baseEnd_2963218] using wordTrace_append hprefix tailTrace_2963218
  have hstable : (prefixWord ++ tailWord_2963218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2963218).length < 2 ^ (prefixWord ++ tailWord_2963218).sum := by decide
  have hdescent : baseEnd_2963218 < baseStart_2963218 := by decide
  rcases family_descends (prefixWord ++ tailWord_2963218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2963233 : List Nat := [1, 2, 3, 2, 1, 4, 1, 2, 3, 3]
def baseStart_2963233 : Nat := 118140960795 + 2963233 * 2 ^ 59
def prefixEnd_2963233 : Nat := 4983230072969 + 3 ^ 40 * 2963233 * 2
def baseEnd_2963233 : Nat := 1014375213509673380639897

theorem tailTrace_2963233 : CollatzResearch.WordTrace tailWord_2963233 prefixEnd_2963233 1014375213509673380639897 := by
  unfold tailWord_2963233
  simp only [CollatzResearch.WordTrace]
  refine ⟨108077986473720395750430353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72051990982480263833620235 108077986473720395750430353)
  ·
    refine ⟨81058489855290296812822765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108077986473720395750430353 81058489855290296812822765)
    ·
      refine ⟨30396933695733861304808537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81058489855290296812822765 30396933695733861304808537)
      ·
        refine ⟨22797700271800395978606403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30396933695733861304808537 22797700271800395978606403)
        ·
          refine ⟨34196550407700593967909605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22797700271800395978606403 34196550407700593967909605)
          ·
            refine ⟨6411853201443861368983051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34196550407700593967909605 6411853201443861368983051)
            ·
              refine ⟨9617779802165792053474577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6411853201443861368983051 9617779802165792053474577)
              ·
                refine ⟨7213334851624344040105933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9617779802165792053474577 7213334851624344040105933)
                ·
                  refine ⟨2705000569359129015039725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7213334851624344040105933 2705000569359129015039725)
                  ·
                    refine ⟨1014375213509673380639897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2705000569359129015039725 1014375213509673380639897)
                    ·
                      rfl

theorem cell22_2963233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 2, 3, 3].length) (baseStart_2963233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2963233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2963233 prefixEnd_2963233 := by exact prefixLift 2963233
  have htrace : WordTrace (prefixWord ++ tailWord_2963233) baseStart_2963233 baseEnd_2963233 := by
    simpa [prefixWord, tailWord_2963233, baseEnd_2963233] using wordTrace_append hprefix tailTrace_2963233
  have hstable : (prefixWord ++ tailWord_2963233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2963233).length < 2 ^ (prefixWord ++ tailWord_2963233).sum := by decide
  have hdescent : baseEnd_2963233 < baseStart_2963233 := by decide
  rcases family_descends (prefixWord ++ tailWord_2963233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2963250 : List Nat := [3, 2, 1, 1, 3, 2, 1, 5, 1, 3]
def baseStart_2963250 : Nat := 118140960795 + 2963250 * 2 ^ 59
def prefixEnd_2963250 : Nat := 4983230072969 + 3 ^ 40 * 2963250 * 2
def baseEnd_2963250 : Nat := 1014381032957091002964845

theorem tailTrace_2963250 : CollatzResearch.WordTrace tailWord_2963250 prefixEnd_2963250 1014381032957091002964845 := by
  unfold tailWord_2963250
  simp only [CollatzResearch.WordTrace]
  refine ⟨27019651628664701913449801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72052404343105871769199469 27019651628664701913449801)
  ·
    refine ⟨20264738721498526435087351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27019651628664701913449801 20264738721498526435087351)
    ·
      refine ⟨30397108082247789652631027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20264738721498526435087351 30397108082247789652631027)
      ·
        refine ⟨45595662123371684478946541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30397108082247789652631027 45595662123371684478946541)
        ·
          refine ⟨17098373296264381679604953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45595662123371684478946541 17098373296264381679604953)
          ·
            refine ⟨12823779972198286259703715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17098373296264381679604953 12823779972198286259703715)
            ·
              refine ⟨19235669958297429389555573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12823779972198286259703715 19235669958297429389555573)
              ·
                refine ⟨1803344058590384005270835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19235669958297429389555573 1803344058590384005270835)
                ·
                  refine ⟨2705016087885576007906253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1803344058590384005270835 2705016087885576007906253)
                  ·
                    refine ⟨1014381032957091002964845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2705016087885576007906253 1014381032957091002964845)
                    ·
                      rfl

theorem cell22_2963250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 5, 1, 3].length) (baseStart_2963250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2963250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2963250 prefixEnd_2963250 := by exact prefixLift 2963250
  have htrace : WordTrace (prefixWord ++ tailWord_2963250) baseStart_2963250 baseEnd_2963250 := by
    simpa [prefixWord, tailWord_2963250, baseEnd_2963250] using wordTrace_append hprefix tailTrace_2963250
  have hstable : (prefixWord ++ tailWord_2963250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2963250).length < 2 ^ (prefixWord ++ tailWord_2963250).sum := by decide
  have hdescent : baseEnd_2963250 < baseStart_2963250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2963250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2963310 : List Nat := [4, 1, 2, 3, 1, 1, 2, 3, 1, 4]
def baseStart_2963310 : Nat := 118140960795 + 2963310 * 2 ^ 59
def prefixEnd_2963310 : Nat := 4983230072969 + 3 ^ 40 * 2963310 * 2
def baseEnd_2963310 : Nat := 1014401572183270846464661

theorem tailTrace_2963310 : CollatzResearch.WordTrace tailWord_2963310 prefixEnd_2963310 1014401572183270846464661 := by
  unfold tailWord_2963310
  simp only [CollatzResearch.WordTrace]
  refine ⟨13510099361805179737622923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72053863262960958600655589 13510099361805179737622923)
  ·
    refine ⟨20265149042707769606434385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13510099361805179737622923 20265149042707769606434385)
    ·
      refine ⟨15198861782030827204825789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20265149042707769606434385 15198861782030827204825789)
      ·
        refine ⟨5699573168261560201809671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15198861782030827204825789 5699573168261560201809671)
        ·
          refine ⟨8549359752392340302714507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5699573168261560201809671 8549359752392340302714507)
          ·
            refine ⟨12824039628588510454071761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8549359752392340302714507 12824039628588510454071761)
            ·
              refine ⟨9618029721441382840553821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12824039628588510454071761 9618029721441382840553821)
              ·
                refine ⟨3606761145540518565207683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9618029721441382840553821 3606761145540518565207683)
                ·
                  refine ⟨5410141718310777847811525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3606761145540518565207683 5410141718310777847811525)
                  ·
                    refine ⟨1014401572183270846464661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5410141718310777847811525 1014401572183270846464661)
                    ·
                      rfl

theorem cell22_2963310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_2963310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2963310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2963310 prefixEnd_2963310 := by exact prefixLift 2963310
  have htrace : WordTrace (prefixWord ++ tailWord_2963310) baseStart_2963310 baseEnd_2963310 := by
    simpa [prefixWord, tailWord_2963310, baseEnd_2963310] using wordTrace_append hprefix tailTrace_2963310
  have hstable : (prefixWord ++ tailWord_2963310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2963310).length < 2 ^ (prefixWord ++ tailWord_2963310).sum := by decide
  have hdescent : baseEnd_2963310 < baseStart_2963310 := by decide
  rcases family_descends (prefixWord ++ tailWord_2963310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2963323 : List Nat := [1, 1, 1, 1, 1, 5, 1, 6, 2, 3]
def baseStart_2963323 : Nat := 118140960795 + 2963323 * 2 ^ 59
def prefixEnd_2963323 : Nat := 4983230072969 + 3 ^ 40 * 2963323 * 2
def baseEnd_2963323 : Nat := 1014406022348943145889621

theorem tailTrace_2963323 : CollatzResearch.WordTrace tailWord_2963323 prefixEnd_2963323 1014406022348943145889621 := by
  unfold tailWord_2963323
  simp only [CollatzResearch.WordTrace]
  refine ⟨108081269043394341121206623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72054179362262894080804415 108081269043394341121206623)
  ·
    refine ⟨162121903565091511681809935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108081269043394341121206623 162121903565091511681809935)
    ·
      refine ⟨243182855347637267522714903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162121903565091511681809935 243182855347637267522714903)
      ·
        refine ⟨364774283021455901284072355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243182855347637267522714903 364774283021455901284072355)
        ·
          refine ⟨547161424532183851926108533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 364774283021455901284072355 547161424532183851926108533)
          ·
            refine ⟨51296383549892236118072675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 547161424532183851926108533 51296383549892236118072675)
            ·
              refine ⟨76944575324838354177109013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51296383549892236118072675 76944575324838354177109013)
              ·
                refine ⟨3606776968351797852051985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 76944575324838354177109013 3606776968351797852051985)
                ·
                  refine ⟨2705082726263848389038989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3606776968351797852051985 2705082726263848389038989)
                  ·
                    refine ⟨1014406022348943145889621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2705082726263848389038989 1014406022348943145889621)
                    ·
                      rfl

theorem cell22_2963323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 6, 2, 3].length) (baseStart_2963323 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2963323 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2963323 prefixEnd_2963323 := by exact prefixLift 2963323
  have htrace : WordTrace (prefixWord ++ tailWord_2963323) baseStart_2963323 baseEnd_2963323 := by
    simpa [prefixWord, tailWord_2963323, baseEnd_2963323] using wordTrace_append hprefix tailTrace_2963323
  have hstable : (prefixWord ++ tailWord_2963323).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2963323).length < 2 ^ (prefixWord ++ tailWord_2963323).sum := by decide
  have hdescent : baseEnd_2963323 < baseStart_2963323 := by decide
  rcases family_descends (prefixWord ++ tailWord_2963323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2963490 : List Nat := [3, 3, 1, 1, 1, 2, 3, 2, 2, 4]
def baseStart_2963490 : Nat := 118140960795 + 2963490 * 2 ^ 59
def prefixEnd_2963490 : Nat := 4983230072969 + 3 ^ 40 * 2963490 * 2
def baseEnd_2963490 : Nat := 1014463189861810376964109

theorem tailTrace_2963490 : CollatzResearch.WordTrace tailWord_2963490 prefixEnd_2963490 1014463189861810376964109 := by
  unfold tailWord_2963490
  simp only [CollatzResearch.WordTrace]
  refine ⟨27021840008447332160633981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72058240022526219095023949 27021840008447332160633981)
  ·
    refine ⟨10133190003167749560237743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27021840008447332160633981 10133190003167749560237743)
    ·
      refine ⟨15199785004751624340356615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10133190003167749560237743 15199785004751624340356615)
      ·
        refine ⟨22799677507127436510534923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15199785004751624340356615 22799677507127436510534923)
        ·
          refine ⟨34199516260691154765802385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22799677507127436510534923 34199516260691154765802385)
          ·
            refine ⟨25649637195518366074351789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34199516260691154765802385 25649637195518366074351789)
            ·
              refine ⟨9618613948319387277881921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25649637195518366074351789 9618613948319387277881921)
              ·
                refine ⟨7213960461239540458411441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9618613948319387277881921 7213960461239540458411441)
                ·
                  refine ⟨5410470345929655343808581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7213960461239540458411441 5410470345929655343808581)
                  ·
                    refine ⟨1014463189861810376964109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5410470345929655343808581 1014463189861810376964109)
                    ·
                      rfl

theorem cell22_2963490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_2963490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2963490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2963490 prefixEnd_2963490 := by exact prefixLift 2963490
  have htrace : WordTrace (prefixWord ++ tailWord_2963490) baseStart_2963490 baseEnd_2963490 := by
    simpa [prefixWord, tailWord_2963490, baseEnd_2963490] using wordTrace_append hprefix tailTrace_2963490
  have hstable : (prefixWord ++ tailWord_2963490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2963490).length < 2 ^ (prefixWord ++ tailWord_2963490).sum := by decide
  have hdescent : baseEnd_2963490 < baseStart_2963490 := by decide
  rcases family_descends (prefixWord ++ tailWord_2963490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2963537 : List Nat := [1, 2, 2, 1, 3, 1, 1, 7, 1, 3]
def baseStart_2963537 : Nat := 118140960795 + 2963537 * 2 ^ 59
def prefixEnd_2963537 : Nat := 4983230072969 + 3 ^ 40 * 2963537 * 2
def baseEnd_2963537 : Nat := 1014479278922317921038965

theorem tailTrace_2963537 : CollatzResearch.WordTrace tailWord_2963537 prefixEnd_2963537 1014479278922317921038965 := by
  unfold tailWord_2963537
  simp only [CollatzResearch.WordTrace]
  refine ⟨108089074264619055669496865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72059382843079370446331243 108089074264619055669496865)
  ·
    refine ⟨81066805698464291752122649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108089074264619055669496865 81066805698464291752122649)
    ·
      refine ⟨60800104273848218814091987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81066805698464291752122649 60800104273848218814091987)
      ·
        refine ⟨91200156410772328221137981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60800104273848218814091987 91200156410772328221137981)
        ·
          refine ⟨34200058654039623082926743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91200156410772328221137981 34200058654039623082926743)
          ·
            refine ⟨51300087981059434624390115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34200058654039623082926743 51300087981059434624390115)
            ·
              refine ⟨76950131971589151936585173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51300087981059434624390115 76950131971589151936585173)
              ·
                refine ⟨1803518718084120748513715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 76950131971589151936585173 1803518718084120748513715)
                ·
                  refine ⟨2705278077126181122770573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1803518718084120748513715 2705278077126181122770573)
                  ·
                    refine ⟨1014479278922317921038965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2705278077126181122770573 1014479278922317921038965)
                    ·
                      rfl

theorem cell22_2963537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 7, 1, 3].length) (baseStart_2963537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2963537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2963537 prefixEnd_2963537 := by exact prefixLift 2963537
  have htrace : WordTrace (prefixWord ++ tailWord_2963537) baseStart_2963537 baseEnd_2963537 := by
    simpa [prefixWord, tailWord_2963537, baseEnd_2963537] using wordTrace_append hprefix tailTrace_2963537
  have hstable : (prefixWord ++ tailWord_2963537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2963537).length < 2 ^ (prefixWord ++ tailWord_2963537).sum := by decide
  have hdescent : baseEnd_2963537 < baseStart_2963537 := by decide
  rcases family_descends (prefixWord ++ tailWord_2963537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2963565 : List Nat := [1, 5, 1, 1, 2, 1, 3, 1, 2, 5]
def baseStart_2963565 : Nat := 118140960795 + 2963565 * 2 ^ 59
def prefixEnd_2963565 : Nat := 4983230072969 + 3 ^ 40 * 2963565 * 2
def baseEnd_2963565 : Nat := 1014488863894535181338879

theorem tailTrace_2963565 : CollatzResearch.WordTrace tailWord_2963565 prefixEnd_2963565 1014488863894535181338879 := by
  unfold tailWord_2963565
  simp only [CollatzResearch.WordTrace]
  refine ⟨108090095508517616451516149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72060063672345077634344099 108090095508517616451516149)
  ·
    refine ⟨10133446453923526542329639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 108090095508517616451516149 10133446453923526542329639)
    ·
      refine ⟨15200169680885289813494459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10133446453923526542329639 15200169680885289813494459)
      ·
        refine ⟨22800254521327934720241689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15200169680885289813494459 22800254521327934720241689)
        ·
          refine ⟨17100190890995951040181267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22800254521327934720241689 17100190890995951040181267)
          ·
            refine ⟨25650286336493926560271901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17100190890995951040181267 25650286336493926560271901)
            ·
              refine ⟨9618857376185222460101963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25650286336493926560271901 9618857376185222460101963)
              ·
                refine ⟨14428286064277833690152945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9618857376185222460101963 14428286064277833690152945)
                ·
                  refine ⟨10821214548208375267614709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14428286064277833690152945 10821214548208375267614709)
                  ·
                    refine ⟨1014488863894535181338879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10821214548208375267614709 1014488863894535181338879)
                    ·
                      rfl

theorem cell22_2963565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_2963565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2963565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2963565 prefixEnd_2963565 := by exact prefixLift 2963565
  have htrace : WordTrace (prefixWord ++ tailWord_2963565) baseStart_2963565 baseEnd_2963565 := by
    simpa [prefixWord, tailWord_2963565, baseEnd_2963565] using wordTrace_append hprefix tailTrace_2963565
  have hstable : (prefixWord ++ tailWord_2963565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2963565).length < 2 ^ (prefixWord ++ tailWord_2963565).sum := by decide
  have hdescent : baseEnd_2963565 < baseStart_2963565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2963565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2963580 : List Nat := [2, 2, 2, 1, 1, 4, 2, 1, 3, 4]
def baseStart_2963580 : Nat := 118140960795 + 2963580 * 2 ^ 59
def prefixEnd_2963580 : Nat := 4983230072969 + 3 ^ 40 * 2963580 * 2
def baseEnd_2963580 : Nat := 1014493998701080142213833

theorem tailTrace_2963580 : CollatzResearch.WordTrace tailWord_2963580 prefixEnd_2963580 1014493998701080142213833 := by
  unfold tailWord_2963580
  simp only [CollatzResearch.WordTrace]
  refine ⟨54045321301731637006656097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72060428402308849342208129 54045321301731637006656097)
  ·
    refine ⟨40533990976298727754992073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54045321301731637006656097 40533990976298727754992073)
    ·
      refine ⟨30400493232224045816244055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40533990976298727754992073 30400493232224045816244055)
      ·
        refine ⟨45600739848336068724366083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30400493232224045816244055 45600739848336068724366083)
        ·
          refine ⟨68401109772504103086549125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45600739848336068724366083 68401109772504103086549125)
          ·
            refine ⟨12825208082344519328727961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68401109772504103086549125 12825208082344519328727961)
            ·
              refine ⟨9618906061758389496545971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12825208082344519328727961 9618906061758389496545971)
              ·
                refine ⟨14428359092637584244818957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9618906061758389496545971 14428359092637584244818957)
                ·
                  refine ⟨5410634659739094091807109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14428359092637584244818957 5410634659739094091807109)
                  ·
                    refine ⟨1014493998701080142213833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5410634659739094091807109 1014493998701080142213833)
                    ·
                      rfl

theorem cell22_2963580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 1, 3, 4].length) (baseStart_2963580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2963580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2963580 prefixEnd_2963580 := by exact prefixLift 2963580
  have htrace : WordTrace (prefixWord ++ tailWord_2963580) baseStart_2963580 baseEnd_2963580 := by
    simpa [prefixWord, tailWord_2963580, baseEnd_2963580] using wordTrace_append hprefix tailTrace_2963580
  have hstable : (prefixWord ++ tailWord_2963580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2963580).length < 2 ^ (prefixWord ++ tailWord_2963580).sum := by decide
  have hdescent : baseEnd_2963580 < baseStart_2963580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2963580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2963612 : List Nat := [2, 2, 3, 2, 1, 1, 1, 6, 4]
def baseStart_2963612 : Nat := 118140960795 + 2963612 * 2 ^ 59
def prefixEnd_2963612 : Nat := 4983230072969 + 3 ^ 40 * 2963612 * 2
def baseEnd_2963612 : Nat := 338168317651680908471245

theorem tailTrace_2963612 : CollatzResearch.WordTrace tailWord_2963612 prefixEnd_2963612 338168317651680908471245 := by
  unfold tailWord_2963612
  simp only [CollatzResearch.WordTrace]
  refine ⟨54045904869673671739238545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72061206492898228985651393 54045904869673671739238545)
  ·
    refine ⟨40534428652255253804428909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54045904869673671739238545 40534428652255253804428909)
    ·
      refine ⟨15200410744595720176660841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40534428652255253804428909 15200410744595720176660841)
      ·
        refine ⟨11400308058446790132495631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15200410744595720176660841 11400308058446790132495631)
        ·
          refine ⟨17100462087670185198743447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11400308058446790132495631 17100462087670185198743447)
          ·
            refine ⟨25650693131505277798115171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17100462087670185198743447 25650693131505277798115171)
            ·
              refine ⟨38476039697257916697172757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25650693131505277798115171 38476039697257916697172757)
              ·
                refine ⟨1803564360808964845179973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 38476039697257916697172757 1803564360808964845179973)
                ·
                  refine ⟨338168317651680908471245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1803564360808964845179973 338168317651680908471245)
                  ·
                    rfl

theorem cell22_2963612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 6, 4].length) (baseStart_2963612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2963612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2963612 prefixEnd_2963612 := by exact prefixLift 2963612
  have htrace : WordTrace (prefixWord ++ tailWord_2963612) baseStart_2963612 baseEnd_2963612 := by
    simpa [prefixWord, tailWord_2963612, baseEnd_2963612] using wordTrace_append hprefix tailTrace_2963612
  have hstable : (prefixWord ++ tailWord_2963612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2963612).length < 2 ^ (prefixWord ++ tailWord_2963612).sum := by decide
  have hdescent : baseEnd_2963612 < baseStart_2963612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2963612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2963646 : List Nat := [4, 2, 1, 1, 4, 2, 1, 3, 4]
def baseStart_2963646 : Nat := 118140960795 + 2963646 * 2 ^ 59
def prefixEnd_2963646 : Nat := 4983230072969 + 3 ^ 40 * 2963646 * 2
def baseEnd_2963646 : Nat := 338172197283292656687877

theorem tailTrace_2963646 : CollatzResearch.WordTrace tailWord_2963646 prefixEnd_2963646 338172197283292656687877 := by
  unfold tailWord_2963646
  simp only [CollatzResearch.WordTrace]
  refine ⟨13511631227653020910651849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72062033214149444856809861 13511631227653020910651849)
  ·
    refine ⟨10133723420739765682988887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13511631227653020910651849 10133723420739765682988887)
    ·
      refine ⟨15200585131109648524483331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10133723420739765682988887 15200585131109648524483331)
      ·
        refine ⟨22800877696664472786724997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15200585131109648524483331 22800877696664472786724997)
        ·
          refine ⟨4275164568124588647510937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22800877696664472786724997 4275164568124588647510937)
          ·
            refine ⟨3206373426093441485633203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4275164568124588647510937 3206373426093441485633203)
            ·
              refine ⟨4809560139140162228449805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3206373426093441485633203 4809560139140162228449805)
              ·
                refine ⟨1803585052177560835668677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4809560139140162228449805 1803585052177560835668677)
                ·
                  refine ⟨338172197283292656687877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1803585052177560835668677 338172197283292656687877)
                  ·
                    rfl

theorem cell22_2963646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 3, 4].length) (baseStart_2963646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2963646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2963646 prefixEnd_2963646 := by exact prefixLift 2963646
  have htrace : WordTrace (prefixWord ++ tailWord_2963646) baseStart_2963646 baseEnd_2963646 := by
    simpa [prefixWord, tailWord_2963646, baseEnd_2963646] using wordTrace_append hprefix tailTrace_2963646
  have hstable : (prefixWord ++ tailWord_2963646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2963646).length < 2 ^ (prefixWord ++ tailWord_2963646).sum := by decide
  have hdescent : baseEnd_2963646 < baseStart_2963646 := by decide
  rcases family_descends (prefixWord ++ tailWord_2963646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2963775 : List Nat := [1, 1, 2, 2, 4, 1, 11]
def baseStart_2963775 : Nat := 118140960795 + 2963775 * 2 ^ 59
def prefixEnd_2963775 : Nat := 4983230072969 + 3 ^ 40 * 2963775 * 2
def baseEnd_2963775 : Nat := 37576324118006097540305

theorem tailTrace_2963775 : CollatzResearch.WordTrace tailWord_2963775 prefixEnd_2963775 37576324118006097540305 := by
  unfold tailWord_2963775
  simp only [CollatzResearch.WordTrace]
  refine ⟨108097754837756822316660779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72065169891837881544440519 108097754837756822316660779)
  ·
    refine ⟨162146632256635233474991169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108097754837756822316660779 162146632256635233474991169)
    ·
      refine ⟨121609974192476425106243377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162146632256635233474991169 121609974192476425106243377)
      ·
        refine ⟨91207480644357318829682533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121609974192476425106243377 91207480644357318829682533)
        ·
          refine ⟨17101402620816997280565475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91207480644357318829682533 17101402620816997280565475)
          ·
            refine ⟨25652103931225495920848213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17101402620816997280565475 25652103931225495920848213)
            ·
              refine ⟨37576324118006097540305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 25652103931225495920848213 37576324118006097540305)
              ·
                rfl

theorem cell22_2963775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 11].length) (baseStart_2963775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2963775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2963775 prefixEnd_2963775 := by exact prefixLift 2963775
  have htrace : WordTrace (prefixWord ++ tailWord_2963775) baseStart_2963775 baseEnd_2963775 := by
    simpa [prefixWord, tailWord_2963775, baseEnd_2963775] using wordTrace_append hprefix tailTrace_2963775
  have hstable : (prefixWord ++ tailWord_2963775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2963775).length < 2 ^ (prefixWord ++ tailWord_2963775).sum := by decide
  have hdescent : baseEnd_2963775 < baseStart_2963775 := by decide
  rcases family_descends (prefixWord ++ tailWord_2963775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2963779 : List Nat := [1, 1, 1, 3, 1, 3, 5, 2, 2, 3]
def baseStart_2963779 : Nat := 118140960795 + 2963779 * 2 ^ 59
def prefixEnd_2963779 : Nat := 4983230072969 + 3 ^ 40 * 2963779 * 2
def baseEnd_2963779 : Nat := 1014562120467909956488223

theorem tailTrace_2963779 : CollatzResearch.WordTrace tailWord_2963779 prefixEnd_2963779 1014562120467909956488223 := by
  unfold tailWord_2963779
  simp only [CollatzResearch.WordTrace]
  refine ⟨108097900729742330999806391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72065267153161553999870927 108097900729742330999806391)
  ·
    refine ⟨162146851094613496499709587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108097900729742330999806391 162146851094613496499709587)
    ·
      refine ⟨243220276641920244749564381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162146851094613496499709587 243220276641920244749564381)
      ·
        refine ⟨91207603740720091781086643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 243220276641920244749564381 91207603740720091781086643)
        ·
          refine ⟨136811405611080137671629965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91207603740720091781086643 136811405611080137671629965)
          ·
            refine ⟨51304277104155051626861237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136811405611080137671629965 51304277104155051626861237)
            ·
              refine ⟨4809775978514536090018241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51304277104155051626861237 4809775978514536090018241)
              ·
                refine ⟨3607331983885902067513681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4809775978514536090018241 3607331983885902067513681)
                ·
                  refine ⟨2705498987914426550635261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3607331983885902067513681 2705498987914426550635261)
                  ·
                    refine ⟨1014562120467909956488223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2705498987914426550635261 1014562120467909956488223)
                    ·
                      rfl

theorem cell22_2963779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 2, 2, 3].length) (baseStart_2963779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2963779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2963779 prefixEnd_2963779 := by exact prefixLift 2963779
  have htrace : WordTrace (prefixWord ++ tailWord_2963779) baseStart_2963779 baseEnd_2963779 := by
    simpa [prefixWord, tailWord_2963779, baseEnd_2963779] using wordTrace_append hprefix tailTrace_2963779
  have hstable : (prefixWord ++ tailWord_2963779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2963779).length < 2 ^ (prefixWord ++ tailWord_2963779).sum := by decide
  have hdescent : baseEnd_2963779 < baseStart_2963779 := by decide
  rcases family_descends (prefixWord ++ tailWord_2963779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2963837 : List Nat := [1, 4, 1, 1, 2, 3, 2, 1, 7]
def baseStart_2963837 : Nat := 118140960795 + 2963837 * 2 ^ 59
def prefixEnd_2963837 : Nat := 4983230072969 + 3 ^ 40 * 2963837 * 2
def baseEnd_2963837 : Nat := 338193991684405712846015

theorem tailTrace_2963837 : CollatzResearch.WordTrace tailWord_2963837 prefixEnd_2963837 338193991684405712846015 := by
  unfold tailWord_2963837
  simp only [CollatzResearch.WordTrace]
  refine ⟨108100016163532206905417765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72066677442354804603611843 108100016163532206905417765)
  ·
    refine ⟨20268753030662288794765831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108100016163532206905417765 20268753030662288794765831)
    ·
      refine ⟨30403129545993433192148747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20268753030662288794765831 30403129545993433192148747)
      ·
        refine ⟨45604694318990149788223121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30403129545993433192148747 45604694318990149788223121)
        ·
          refine ⟨34203520739242612341167341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45604694318990149788223121 34203520739242612341167341)
          ·
            refine ⟨12826320277215979627937753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34203520739242612341167341 12826320277215979627937753)
            ·
              refine ⟨9619740207911984720953315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12826320277215979627937753 9619740207911984720953315)
              ·
                refine ⟨14429610311867977081429973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9619740207911984720953315 14429610311867977081429973)
                ·
                  refine ⟨338193991684405712846015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14429610311867977081429973 338193991684405712846015)
                  ·
                    rfl

theorem cell22_2963837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 1, 7].length) (baseStart_2963837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2963837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2963837 prefixEnd_2963837 := by exact prefixLift 2963837
  have htrace : WordTrace (prefixWord ++ tailWord_2963837) baseStart_2963837 baseEnd_2963837 := by
    simpa [prefixWord, tailWord_2963837, baseEnd_2963837] using wordTrace_append hprefix tailTrace_2963837
  have hstable : (prefixWord ++ tailWord_2963837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2963837).length < 2 ^ (prefixWord ++ tailWord_2963837).sum := by decide
  have hdescent : baseEnd_2963837 < baseStart_2963837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2963837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2963841 : List Nat := [1, 2, 4, 3, 1, 1, 3, 1, 3, 3]
def baseStart_2963841 : Nat := 118140960795 + 2963841 * 2 ^ 59
def prefixEnd_2963841 : Nat := 4983230072969 + 3 ^ 40 * 2963841 * 2
def baseEnd_2963841 : Nat := 1014583344334962461438033

theorem tailTrace_2963841 : CollatzResearch.WordTrace tailWord_2963841 prefixEnd_2963841 1014583344334962461438033 := by
  unfold tailWord_2963841
  simp only [CollatzResearch.WordTrace]
  refine ⟨108100162055517715588563377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72066774703678477059042251 108100162055517715588563377)
  ·
    refine ⟨81075121541638286691422533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108100162055517715588563377 81075121541638286691422533)
    ·
      refine ⟨15201585289057178754641725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81075121541638286691422533 15201585289057178754641725)
      ·
        refine ⟨5700594483396442032990647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15201585289057178754641725 5700594483396442032990647)
        ·
          refine ⟨8550891725094663049485971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5700594483396442032990647 8550891725094663049485971)
          ·
            refine ⟨12826337587641994574228957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8550891725094663049485971 12826337587641994574228957)
            ·
              refine ⟨4809876595365747965335859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12826337587641994574228957 4809876595365747965335859)
              ·
                refine ⟨7214814893048621948003789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4809876595365747965335859 7214814893048621948003789)
                ·
                  refine ⟨2705555584893233230501421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7214814893048621948003789 2705555584893233230501421)
                  ·
                    refine ⟨1014583344334962461438033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2705555584893233230501421 1014583344334962461438033)
                    ·
                      rfl

theorem cell22_2963841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 1, 3, 3].length) (baseStart_2963841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2963841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2963841 prefixEnd_2963841 := by exact prefixLift 2963841
  have htrace : WordTrace (prefixWord ++ tailWord_2963841) baseStart_2963841 baseEnd_2963841 := by
    simpa [prefixWord, tailWord_2963841, baseEnd_2963841] using wordTrace_append hprefix tailTrace_2963841
  have hstable : (prefixWord ++ tailWord_2963841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2963841).length < 2 ^ (prefixWord ++ tailWord_2963841).sum := by decide
  have hdescent : baseEnd_2963841 < baseStart_2963841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2963841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2963892 : List Nat := [2, 5, 2, 2, 1, 1, 1, 4, 1, 3]
def baseStart_2963892 : Nat := 118140960795 + 2963892 * 2 ^ 59
def prefixEnd_2963892 : Nat := 4983230072969 + 3 ^ 40 * 2963892 * 2
def baseEnd_2963892 : Nat := 1014600802677215328412877

theorem tailTrace_2963892 : CollatzResearch.WordTrace tailWord_2963892 prefixEnd_2963892 1014600802677215328412877 := by
  unfold tailWord_2963892
  simp only [CollatzResearch.WordTrace]
  refine ⟨54051011089166475649334965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72068014785555300865779953 54051011089166475649334965)
  ·
    refine ⟨5067282289609357092125153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54051011089166475649334965 5067282289609357092125153)
    ·
      refine ⟨3800461717207017819093865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5067282289609357092125153 3800461717207017819093865)
      ·
        refine ⟨2850346287905263364320399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3800461717207017819093865 2850346287905263364320399)
        ·
          refine ⟨4275519431857895046480599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2850346287905263364320399 4275519431857895046480599)
          ·
            refine ⟨6413279147786842569720899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4275519431857895046480599 6413279147786842569720899)
            ·
              refine ⟨9619918721680263854581349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6413279147786842569720899 9619918721680263854581349)
              ·
                refine ⟨1803734760315049472734003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9619918721680263854581349 1803734760315049472734003)
                ·
                  refine ⟨2705602140472574209101005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1803734760315049472734003 2705602140472574209101005)
                  ·
                    refine ⟨1014600802677215328412877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2705602140472574209101005 1014600802677215328412877)
                    ·
                      rfl

theorem cell22_2963892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_2963892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2963892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2963892 prefixEnd_2963892 := by exact prefixLift 2963892
  have htrace : WordTrace (prefixWord ++ tailWord_2963892) baseStart_2963892 baseEnd_2963892 := by
    simpa [prefixWord, tailWord_2963892, baseEnd_2963892] using wordTrace_append hprefix tailTrace_2963892
  have hstable : (prefixWord ++ tailWord_2963892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2963892).length < 2 ^ (prefixWord ++ tailWord_2963892).sum := by decide
  have hdescent : baseEnd_2963892 < baseStart_2963892 := by decide
  rcases family_descends (prefixWord ++ tailWord_2963892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2963914 : List Nat := [3, 1, 2, 1, 2, 2, 4, 1, 1, 5]
def baseStart_2963914 : Nat := 118140960795 + 2963914 * 2 ^ 59
def prefixEnd_2963914 : Nat := 4983230072969 + 3 ^ 40 * 2963914 * 2
def baseEnd_2963914 : Nat := 1014608333726814604362809

theorem tailTrace_2963914 : CollatzResearch.WordTrace tailWord_2963914 prefixEnd_2963914 1014608333726814604362809 := by
  unfold tailWord_2963914
  simp only [CollatzResearch.WordTrace]
  refine ⟨27025706146063312263992699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72068549722835499370647197 27025706146063312263992699)
  ·
    refine ⟨40538559219094968395989049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27025706146063312263992699 40538559219094968395989049)
    ·
      refine ⟨30403919414321226296991787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40538559219094968395989049 30403919414321226296991787)
      ·
        refine ⟨45605879121481839445487681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30403919414321226296991787 45605879121481839445487681)
        ·
          refine ⟨34204409341111379584115761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45605879121481839445487681 34204409341111379584115761)
          ·
            refine ⟨25653307005833534688086821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34204409341111379584115761 25653307005833534688086821)
            ·
              refine ⟨4809995063593787754016279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25653307005833534688086821 4809995063593787754016279)
              ·
                refine ⟨7214992595390681631024419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4809995063593787754016279 7214992595390681631024419)
                ·
                  refine ⟨10822488893086022446536629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7214992595390681631024419 10822488893086022446536629)
                  ·
                    refine ⟨1014608333726814604362809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10822488893086022446536629 1014608333726814604362809)
                    ·
                      rfl

theorem cell22_2963914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 1, 1, 5].length) (baseStart_2963914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2963914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2963914 prefixEnd_2963914 := by exact prefixLift 2963914
  have htrace : WordTrace (prefixWord ++ tailWord_2963914) baseStart_2963914 baseEnd_2963914 := by
    simpa [prefixWord, tailWord_2963914, baseEnd_2963914] using wordTrace_append hprefix tailTrace_2963914
  have hstable : (prefixWord ++ tailWord_2963914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2963914).length < 2 ^ (prefixWord ++ tailWord_2963914).sum := by decide
  have hdescent : baseEnd_2963914 < baseStart_2963914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2963914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964019 : List Nat := [1, 1, 1, 2, 4, 2, 2, 2, 3, 4]
def baseStart_2964019 : Nat := 118140960795 + 2964019 * 2 ^ 59
def prefixEnd_2964019 : Nat := 4983230072969 + 3 ^ 40 * 2964019 * 2
def baseEnd_2964019 : Nat := 1014644277372629330487487

theorem tailTrace_2964019 : CollatzResearch.WordTrace tailWord_2964019 prefixEnd_2964019 1014644277372629330487487 := by
  unfold tailWord_2964019
  simp only [CollatzResearch.WordTrace]
  refine ⟨108106654248872851988543111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72071102832581901325695407 108106654248872851988543111)
  ·
    refine ⟨162159981373309277982814667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108106654248872851988543111 162159981373309277982814667)
    ·
      refine ⟨243239972059963916974222001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162159981373309277982814667 243239972059963916974222001)
      ·
        refine ⟨182429979044972937730666501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243239972059963916974222001 182429979044972937730666501)
        ·
          refine ⟨34205621070932425824499969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 182429979044972937730666501 34205621070932425824499969)
          ·
            refine ⟨25654215803199319368374977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34205621070932425824499969 25654215803199319368374977)
            ·
              refine ⟨19240661852399489526281233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25654215803199319368374977 19240661852399489526281233)
              ·
                refine ⟨14430496389299617144710925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19240661852399489526281233 14430496389299617144710925)
                ·
                  refine ⟨5411436145987356429266597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14430496389299617144710925 5411436145987356429266597)
                  ·
                    refine ⟨1014644277372629330487487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5411436145987356429266597 1014644277372629330487487)
                    ·
                      rfl

theorem cell22_2964019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 2, 3, 4].length) (baseStart_2964019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2964019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2964019 prefixEnd_2964019 := by exact prefixLift 2964019
  have htrace : WordTrace (prefixWord ++ tailWord_2964019) baseStart_2964019 baseEnd_2964019 := by
    simpa [prefixWord, tailWord_2964019, baseEnd_2964019] using wordTrace_append hprefix tailTrace_2964019
  have hstable : (prefixWord ++ tailWord_2964019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964019).length < 2 ^ (prefixWord ++ tailWord_2964019).sum := by decide
  have hdescent : baseEnd_2964019 < baseStart_2964019 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964049 : List Nat := [1, 2, 2, 1, 3, 3, 1, 1, 3, 5]
def baseStart_2964049 : Nat := 118140960795 + 2964049 * 2 ^ 59
def prefixEnd_2964049 : Nat := 4983230072969 + 3 ^ 40 * 2964049 * 2
def baseEnd_2964049 : Nat := 1014654546985719252237395

theorem tailTrace_2964049 : CollatzResearch.WordTrace tailWord_2964049 prefixEnd_2964049 1014654546985719252237395 := by
  unfold tailWord_2964049
  simp only [CollatzResearch.WordTrace]
  refine ⟨108107748438764167112135201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72071832292509444741423467 108107748438764167112135201)
  ·
    refine ⟨81080811329073125334101401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108107748438764167112135201 81080811329073125334101401)
    ·
      refine ⟨60810608496804844000576051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81080811329073125334101401 60810608496804844000576051)
      ·
        refine ⟨91215912745207266000864077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60810608496804844000576051 91215912745207266000864077)
        ·
          refine ⟨34205967279452724750324029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91215912745207266000864077 34205967279452724750324029)
          ·
            refine ⟨12827237729794771781371511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34205967279452724750324029 12827237729794771781371511)
            ·
              refine ⟨19240856594692157672057267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12827237729794771781371511 19240856594692157672057267)
              ·
                refine ⟨28861284892038236508085901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19240856594692157672057267 28861284892038236508085901)
                ·
                  refine ⟨10822981834514338690532213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28861284892038236508085901 10822981834514338690532213)
                  ·
                    refine ⟨1014654546985719252237395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10822981834514338690532213 1014654546985719252237395)
                    ·
                      rfl

theorem cell22_2964049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 3, 5].length) (baseStart_2964049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2964049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2964049 prefixEnd_2964049 := by exact prefixLift 2964049
  have htrace : WordTrace (prefixWord ++ tailWord_2964049) baseStart_2964049 baseEnd_2964049 := by
    simpa [prefixWord, tailWord_2964049, baseEnd_2964049] using wordTrace_append hprefix tailTrace_2964049
  have hstable : (prefixWord ++ tailWord_2964049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964049).length < 2 ^ (prefixWord ++ tailWord_2964049).sum := by decide
  have hdescent : baseEnd_2964049 < baseStart_2964049 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964079 : List Nat := [1, 1, 2, 1, 3, 2, 5, 7]
def baseStart_2964079 : Nat := 118140960795 + 2964079 * 2 ^ 59
def prefixEnd_2964079 : Nat := 4983230072969 + 3 ^ 40 * 2964079 * 2
def baseEnd_2964079 : Nat := 112740535177645463776367

theorem tailTrace_2964079 : CollatzResearch.WordTrace tailWord_2964079 prefixEnd_2964079 112740535177645463776367 := by
  unfold tailWord_2964079
  simp only [CollatzResearch.WordTrace]
  refine ⟨108108842628655482235727291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72072561752436988157151527 108108842628655482235727291)
  ·
    refine ⟨162163263942983223353590937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108108842628655482235727291 162163263942983223353590937)
    ·
      refine ⟨121622447957237417515193203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162163263942983223353590937 121622447957237417515193203)
      ·
        refine ⟨182433671935856126272789805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121622447957237417515193203 182433671935856126272789805)
        ·
          refine ⟨68412626975946047352296177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 182433671935856126272789805 68412626975946047352296177)
          ·
            refine ⟨51309470231959535514222133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68412626975946047352296177 51309470231959535514222133)
            ·
              refine ⟨4810262834246206454458325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51309470231959535514222133 4810262834246206454458325)
              ·
                refine ⟨112740535177645463776367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4810262834246206454458325 112740535177645463776367)
                ·
                  rfl

theorem cell22_2964079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 7].length) (baseStart_2964079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2964079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2964079 prefixEnd_2964079 := by exact prefixLift 2964079
  have htrace : WordTrace (prefixWord ++ tailWord_2964079) baseStart_2964079 baseEnd_2964079 := by
    simpa [prefixWord, tailWord_2964079, baseEnd_2964079] using wordTrace_append hprefix tailTrace_2964079
  have hstable : (prefixWord ++ tailWord_2964079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964079).length < 2 ^ (prefixWord ++ tailWord_2964079).sum := by decide
  have hdescent : baseEnd_2964079 < baseStart_2964079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964096 : List Nat := [2, 1, 1, 2, 1, 6, 3, 6]
def baseStart_2964096 : Nat := 118140960795 + 2964096 * 2 ^ 59
def prefixEnd_2964096 : Nat := 4983230072969 + 3 ^ 40 * 2964096 * 2
def baseEnd_2964096 : Nat := 112741181782914088479139

theorem tailTrace_2964096 : CollatzResearch.WordTrace tailWord_2964096 prefixEnd_2964096 112741181782914088479139 := by
  unfold tailWord_2964096
  simp only [CollatzResearch.WordTrace]
  refine ⟨54054731334796947069548071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72072975113062596092730761 54054731334796947069548071)
  ·
    refine ⟨81082097002195420604322107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54054731334796947069548071 81082097002195420604322107)
    ·
      refine ⟨121623145503293130906483161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81082097002195420604322107 121623145503293130906483161)
      ·
        refine ⟨91217359127469848179862371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121623145503293130906483161 91217359127469848179862371)
        ·
          refine ⟨136826038691204772269793557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91217359127469848179862371 136826038691204772269793557)
          ·
            refine ⟨6413720563650223700146573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 136826038691204772269793557 6413720563650223700146573)
            ·
              refine ⟨2405145211368833887554965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6413720563650223700146573 2405145211368833887554965)
              ·
                refine ⟨112741181782914088479139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2405145211368833887554965 112741181782914088479139)
                ·
                  rfl

theorem cell22_2964096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 3, 6].length) (baseStart_2964096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2964096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2964096 prefixEnd_2964096 := by exact prefixLift 2964096
  have htrace : WordTrace (prefixWord ++ tailWord_2964096) baseStart_2964096 baseEnd_2964096 := by
    simpa [prefixWord, tailWord_2964096, baseEnd_2964096] using wordTrace_append hprefix tailTrace_2964096
  have hstable : (prefixWord ++ tailWord_2964096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964096).length < 2 ^ (prefixWord ++ tailWord_2964096).sum := by decide
  have hdescent : baseEnd_2964096 < baseStart_2964096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964222 : List Nat := [4, 2, 2, 1, 2, 2, 3, 1, 1, 4]
def baseStart_2964222 : Nat := 118140960795 + 2964222 * 2 ^ 59
def prefixEnd_2964222 : Nat := 4983230072969 + 3 ^ 40 * 2964222 * 2
def baseEnd_2964222 : Nat := 1014713768421204467661865

theorem tailTrace_2964222 : CollatzResearch.WordTrace tailWord_2964222 prefixEnd_2964222 1014713768421204467661865 := by
  unfold tailWord_2964222
  simp only [CollatzResearch.WordTrace]
  refine ⟨13514257283392177207272865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72076038844758278438788613 13514257283392177207272865)
  ·
    refine ⟨10135692962544132905454649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13514257283392177207272865 10135692962544132905454649)
    ·
      refine ⟨7601769721908099679090987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10135692962544132905454649 7601769721908099679090987)
      ·
        refine ⟨11402654582862149518636481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7601769721908099679090987 11402654582862149518636481)
        ·
          refine ⟨8551990937146612138977361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11402654582862149518636481 8551990937146612138977361)
          ·
            refine ⟨6413993202859959104233021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8551990937146612138977361 6413993202859959104233021)
            ·
              refine ⟨2405247451072484664087383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6413993202859959104233021 2405247451072484664087383)
              ·
                refine ⟨3607871176608726996131075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2405247451072484664087383 3607871176608726996131075)
                ·
                  refine ⟨5411806764913090494196613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3607871176608726996131075 5411806764913090494196613)
                  ·
                    refine ⟨1014713768421204467661865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5411806764913090494196613 1014713768421204467661865)
                    ·
                      rfl

theorem cell22_2964222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_2964222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2964222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2964222 prefixEnd_2964222 := by exact prefixLift 2964222
  have htrace : WordTrace (prefixWord ++ tailWord_2964222) baseStart_2964222 baseEnd_2964222 := by
    simpa [prefixWord, tailWord_2964222, baseEnd_2964222] using wordTrace_append hprefix tailTrace_2964222
  have hstable : (prefixWord ++ tailWord_2964222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964222).length < 2 ^ (prefixWord ++ tailWord_2964222).sum := by decide
  have hdescent : baseEnd_2964222 < baseStart_2964222 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964231 : List Nat := [1, 1, 4, 4, 1, 11]
def baseStart_2964231 : Nat := 118140960795 + 2964231 * 2 ^ 59
def prefixEnd_2964231 : Nat := 4983230072969 + 3 ^ 40 * 2964231 * 2
def baseEnd_2964231 : Nat := 12527368509939894372677

theorem tailTrace_2964231 : CollatzResearch.WordTrace tailWord_2964231 prefixEnd_2964231 12527368509939894372677 := by
  unfold tailWord_2964231
  simp only [CollatzResearch.WordTrace]
  refine ⟨108114386524104812195260547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72076257682736541463507031 108114386524104812195260547)
  ·
    refine ⟨162171579786157218292890821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108114386524104812195260547 162171579786157218292890821)
    ·
      refine ⟨30407171209904478429917029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 162171579786157218292890821 30407171209904478429917029)
      ·
        refine ⟨5701344601857089705609443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30407171209904478429917029 5701344601857089705609443)
        ·
          refine ⟨8552016902785634558414165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5701344601857089705609443 8552016902785634558414165)
          ·
            refine ⟨12527368509939894372677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8552016902785634558414165 12527368509939894372677)
            ·
              rfl

theorem cell22_2964231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 11].length) (baseStart_2964231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2964231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2964231 prefixEnd_2964231 := by exact prefixLift 2964231
  have htrace : WordTrace (prefixWord ++ tailWord_2964231) baseStart_2964231 baseEnd_2964231 := by
    simpa [prefixWord, tailWord_2964231, baseEnd_2964231] using wordTrace_append hprefix tailTrace_2964231
  have hstable : (prefixWord ++ tailWord_2964231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964231).length < 2 ^ (prefixWord ++ tailWord_2964231).sum := by decide
  have hdescent : baseEnd_2964231 < baseStart_2964231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964261 : List Nat := [1, 3, 1, 2, 3, 1, 1, 2, 2, 6]
def baseStart_2964261 : Nat := 118140960795 + 2964261 * 2 ^ 59
def prefixEnd_2964261 : Nat := 4983230072969 + 3 ^ 40 * 2964261 * 2
def baseEnd_2964261 : Nat := 1014727118918221365936745

theorem tailTrace_2964261 : CollatzResearch.WordTrace tailWord_2964261 prefixEnd_2964261 1014727118918221365936745 := by
  unfold tailWord_2964261
  simp only [CollatzResearch.WordTrace]
  refine ⟨108115480713996127318852637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72076987142664084879235091 108115480713996127318852637)
  ·
    refine ⟨40543305267748547744569739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108115480713996127318852637 40543305267748547744569739)
    ·
      refine ⟨60814957901622821616854609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40543305267748547744569739 60814957901622821616854609)
      ·
        refine ⟨45611218426217116212640957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60814957901622821616854609 45611218426217116212640957)
        ·
          refine ⟨17104206909831418579740359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45611218426217116212640957 17104206909831418579740359)
          ·
            refine ⟨25656310364747127869610539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17104206909831418579740359 25656310364747127869610539)
            ·
              refine ⟨38484465547120691804415809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25656310364747127869610539 38484465547120691804415809)
              ·
                refine ⟨28863349160340518853311857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38484465547120691804415809 28863349160340518853311857)
                ·
                  refine ⟨21647511870255389139983893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28863349160340518853311857 21647511870255389139983893)
                  ·
                    refine ⟨1014727118918221365936745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21647511870255389139983893 1014727118918221365936745)
                    ·
                      rfl

theorem cell22_2964261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 2, 6].length) (baseStart_2964261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2964261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2964261 prefixEnd_2964261 := by exact prefixLift 2964261
  have htrace : WordTrace (prefixWord ++ tailWord_2964261) baseStart_2964261 baseEnd_2964261 := by
    simpa [prefixWord, tailWord_2964261, baseEnd_2964261] using wordTrace_append hprefix tailTrace_2964261
  have hstable : (prefixWord ++ tailWord_2964261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964261).length < 2 ^ (prefixWord ++ tailWord_2964261).sum := by decide
  have hdescent : baseEnd_2964261 < baseStart_2964261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964291 : List Nat := [1, 1, 1, 3, 1, 4, 1, 1, 4, 5]
def baseStart_2964291 : Nat := 118140960795 + 2964291 * 2 ^ 59
def prefixEnd_2964291 : Nat := 4983230072969 + 3 ^ 40 * 2964291 * 2
def baseEnd_2964291 : Nat := 1014737388531311287686653

theorem tailTrace_2964291 : CollatzResearch.WordTrace tailWord_2964291 prefixEnd_2964291 1014737388531311287686653 := by
  unfold tailWord_2964291
  simp only [CollatzResearch.WordTrace]
  refine ⟨108116574903887442442444727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72077716602591628294963151 108116574903887442442444727)
  ·
    refine ⟨162174862355831163663667091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108116574903887442442444727 162174862355831163663667091)
    ·
      refine ⟨243262293533746745495500637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162174862355831163663667091 243262293533746745495500637)
      ·
        refine ⟨91223360075155029560812739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 243262293533746745495500637 91223360075155029560812739)
        ·
          refine ⟨136835040112732544341219109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91223360075155029560812739 136835040112732544341219109)
          ·
            refine ⟨25656570021137352063978583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 136835040112732544341219109 25656570021137352063978583)
            ·
              refine ⟨38484855031706028095967875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25656570021137352063978583 38484855031706028095967875)
              ·
                refine ⟨57727282547559042143951813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38484855031706028095967875 57727282547559042143951813)
                ·
                  refine ⟨10823865477667320401990965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57727282547559042143951813 10823865477667320401990965)
                  ·
                    refine ⟨1014737388531311287686653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10823865477667320401990965 1014737388531311287686653)
                    ·
                      rfl

theorem cell22_2964291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 4, 5].length) (baseStart_2964291 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2964291 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2964291 prefixEnd_2964291 := by exact prefixLift 2964291
  have htrace : WordTrace (prefixWord ++ tailWord_2964291) baseStart_2964291 baseEnd_2964291 := by
    simpa [prefixWord, tailWord_2964291, baseEnd_2964291] using wordTrace_append hprefix tailTrace_2964291
  have hstable : (prefixWord ++ tailWord_2964291).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964291).length < 2 ^ (prefixWord ++ tailWord_2964291).sum := by decide
  have hdescent : baseEnd_2964291 < baseStart_2964291 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964321 : List Nat := [1, 2, 3, 1, 1, 1, 2, 3, 8]
def baseStart_2964321 : Nat := 118140960795 + 2964321 * 2 ^ 59
def prefixEnd_2964321 : Nat := 4983230072969 + 3 ^ 40 * 2964321 * 2
def baseEnd_2964321 : Nat := 338249219381467069812187

theorem tailTrace_2964321 : CollatzResearch.WordTrace tailWord_2964321 prefixEnd_2964321 338249219381467069812187 := by
  unfold tailWord_2964321
  simp only [CollatzResearch.WordTrace]
  refine ⟨108117669093778757566036817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72078446062519171710691211 108117669093778757566036817)
  ·
    refine ⟨81088251820334068174527613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108117669093778757566036817 81088251820334068174527613)
    ·
      refine ⟨30408094432625275565447855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81088251820334068174527613 30408094432625275565447855)
      ·
        refine ⟨45612141648937913348171783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30408094432625275565447855 45612141648937913348171783)
        ·
          refine ⟨68418212473406870022257675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45612141648937913348171783 68418212473406870022257675)
          ·
            refine ⟨102627318710110305033386513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68418212473406870022257675 102627318710110305033386513)
            ·
              refine ⟨76970489032582728775039885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102627318710110305033386513 76970489032582728775039885)
              ·
                refine ⟨28863933387218523290639957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76970489032582728775039885 28863933387218523290639957)
                ·
                  refine ⟨338249219381467069812187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28863933387218523290639957 338249219381467069812187)
                  ·
                    rfl

theorem cell22_2964321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 8].length) (baseStart_2964321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2964321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2964321 prefixEnd_2964321 := by exact prefixLift 2964321
  have htrace : WordTrace (prefixWord ++ tailWord_2964321) baseStart_2964321 baseEnd_2964321 := by
    simpa [prefixWord, tailWord_2964321, baseEnd_2964321] using wordTrace_append hprefix tailTrace_2964321
  have hstable : (prefixWord ++ tailWord_2964321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964321).length < 2 ^ (prefixWord ++ tailWord_2964321).sum := by decide
  have hdescent : baseEnd_2964321 < baseStart_2964321 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964374 : List Nat := [5, 3, 1, 1, 1, 2, 1, 1, 3, 4]
def baseStart_2964374 : Nat := 118140960795 + 2964374 * 2 ^ 59
def prefixEnd_2964374 : Nat := 4983230072969 + 3 ^ 40 * 2964374 * 2
def baseEnd_2964374 : Nat := 1014765801127526737861399

theorem tailTrace_2964374 : CollatzResearch.WordTrace tailWord_2964374 prefixEnd_2964374 1014765801127526737861399 := by
  unfold tailWord_2964374
  simp only [CollatzResearch.WordTrace]
  refine ⟨6757475135161671726107261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72079734775057831745144117 6757475135161671726107261)
  ·
    refine ⟨2534053175685626897290223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6757475135161671726107261 2534053175685626897290223)
    ·
      refine ⟨3801079763528440345935335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2534053175685626897290223 3801079763528440345935335)
      ·
        refine ⟨5701619645292660518903003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3801079763528440345935335 5701619645292660518903003)
        ·
          refine ⟨8552429467938990778354505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5701619645292660518903003 8552429467938990778354505)
          ·
            refine ⟨6414322100954243083765879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8552429467938990778354505 6414322100954243083765879)
            ·
              refine ⟨9621483151431364625648819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6414322100954243083765879 9621483151431364625648819)
              ·
                refine ⟨14432224727147046938473229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9621483151431364625648819 14432224727147046938473229)
                ·
                  refine ⟨5412084272680142601927461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14432224727147046938473229 5412084272680142601927461)
                  ·
                    refine ⟨1014765801127526737861399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5412084272680142601927461 1014765801127526737861399)
                    ·
                      rfl

theorem cell22_2964374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_2964374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2964374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2964374 prefixEnd_2964374 := by exact prefixLift 2964374
  have htrace : WordTrace (prefixWord ++ tailWord_2964374) baseStart_2964374 baseEnd_2964374 := by
    simpa [prefixWord, tailWord_2964374, baseEnd_2964374] using wordTrace_append hprefix tailTrace_2964374
  have hstable : (prefixWord ++ tailWord_2964374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964374).length < 2 ^ (prefixWord ++ tailWord_2964374).sum := by decide
  have hdescent : baseEnd_2964374 < baseStart_2964374 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964383 : List Nat := [1, 1, 2, 5, 2, 1, 2, 8]
def baseStart_2964383 : Nat := 118140960795 + 2964383 * 2 ^ 59
def prefixEnd_2964383 : Nat := 4983230072969 + 3 ^ 40 * 2964383 * 2
def baseEnd_2964383 : Nat := 112752098001272634931819

theorem tailTrace_2964383 : CollatzResearch.WordTrace tailWord_2964383 prefixEnd_2964383 112752098001272634931819 := by
  unfold tailWord_2964383
  simp only [CollatzResearch.WordTrace]
  refine ⟨108119930419554142154793803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72079953613036094769862535 108119930419554142154793803)
  ·
    refine ⟨162179895629331213232190705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108119930419554142154793803 162179895629331213232190705)
    ·
      refine ⟨121634921721998409924143029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162179895629331213232190705 121634921721998409924143029)
      ·
        refine ⟨11403273911437350930388409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 121634921721998409924143029 11403273911437350930388409)
        ·
          refine ⟨8552455433578013197791307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11403273911437350930388409 8552455433578013197791307)
          ·
            refine ⟨12828683150367019796686961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8552455433578013197791307 12828683150367019796686961)
            ·
              refine ⟨9621512362775264847515221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12828683150367019796686961 9621512362775264847515221)
              ·
                refine ⟨112752098001272634931819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9621512362775264847515221 112752098001272634931819)
                ·
                  rfl

theorem cell22_2964383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 8].length) (baseStart_2964383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2964383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2964383 prefixEnd_2964383 := by exact prefixLift 2964383
  have htrace : WordTrace (prefixWord ++ tailWord_2964383) baseStart_2964383 baseEnd_2964383 := by
    simpa [prefixWord, tailWord_2964383, baseEnd_2964383] using wordTrace_append hprefix tailTrace_2964383
  have hstable : (prefixWord ++ tailWord_2964383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964383).length < 2 ^ (prefixWord ++ tailWord_2964383).sum := by decide
  have hdescent : baseEnd_2964383 < baseStart_2964383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964385 : List Nat := [1, 2, 3, 4, 1, 1, 1, 3, 2, 4]
def baseStart_2964385 : Nat := 118140960795 + 2964385 * 2 ^ 59
def prefixEnd_2964385 : Nat := 4983230072969 + 3 ^ 40 * 2964385 * 2
def baseEnd_2964385 : Nat := 1014769566652326375836365

theorem tailTrace_2964385 : CollatzResearch.WordTrace tailWord_2964385 prefixEnd_2964385 1014769566652326375836365 := by
  unfold tailWord_2964385
  simp only [CollatzResearch.WordTrace]
  refine ⟨108120003365546896496366609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72080002243697930997577739 108120003365546896496366609)
  ·
    refine ⟨81090002524160172372274957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108120003365546896496366609 81090002524160172372274957)
    ·
      refine ⟨30408750946560064639603109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81090002524160172372274957 30408750946560064639603109)
      ·
        refine ⟨5701640802480012119925583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30408750946560064639603109 5701640802480012119925583)
        ·
          refine ⟨8552461203720018179888375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5701640802480012119925583 8552461203720018179888375)
          ·
            refine ⟨12828691805580027269832563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8552461203720018179888375 12828691805580027269832563)
            ·
              refine ⟨19243037708370040904748845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12828691805580027269832563 19243037708370040904748845)
              ·
                refine ⟨7216139140638765339280817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19243037708370040904748845 7216139140638765339280817)
                ·
                  refine ⟨5412104355479074004460613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7216139140638765339280817 5412104355479074004460613)
                  ·
                    refine ⟨1014769566652326375836365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5412104355479074004460613 1014769566652326375836365)
                    ·
                      rfl

theorem cell22_2964385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 3, 2, 4].length) (baseStart_2964385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2964385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2964385 prefixEnd_2964385 := by exact prefixLift 2964385
  have htrace : WordTrace (prefixWord ++ tailWord_2964385) baseStart_2964385 baseEnd_2964385 := by
    simpa [prefixWord, tailWord_2964385, baseEnd_2964385] using wordTrace_append hprefix tailTrace_2964385
  have hstable : (prefixWord ++ tailWord_2964385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964385).length < 2 ^ (prefixWord ++ tailWord_2964385).sum := by decide
  have hdescent : baseEnd_2964385 < baseStart_2964385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964404 : List Nat := [2, 5, 2, 1, 1, 1, 1, 4, 2, 3]
def baseStart_2964404 : Nat := 118140960795 + 2964404 * 2 ^ 59
def prefixEnd_2964404 : Nat := 4983230072969 + 3 ^ 40 * 2964404 * 2
def baseEnd_2964404 : Nat := 1014776070740616659611307

theorem tailTrace_2964404 : CollatzResearch.WordTrace tailWord_2964404 prefixEnd_2964404 1014776070740616659611307 := by
  unfold tailWord_2964404
  simp only [CollatzResearch.WordTrace]
  refine ⟨54060348176239031370654133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72080464234985375160872177 54060348176239031370654133)
  ·
    refine ⟨5068157641522409190998825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54060348176239031370654133 5068157641522409190998825)
    ·
      refine ⟨3801118231141806893249119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5068157641522409190998825 3801118231141806893249119)
      ·
        refine ⟨5701677346712710339873679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3801118231141806893249119 5701677346712710339873679)
        ·
          refine ⟨8552516020069065509810519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5701677346712710339873679 8552516020069065509810519)
          ·
            refine ⟨12828774030103598264715779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8552516020069065509810519 12828774030103598264715779)
            ·
              refine ⟨19243161045155397397073669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12828774030103598264715779 19243161045155397397073669)
              ·
                refine ⟨3608092695966637011951313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19243161045155397397073669 3608092695966637011951313)
                ·
                  refine ⟨2706069521974977758963485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3608092695966637011951313 2706069521974977758963485)
                  ·
                    refine ⟨1014776070740616659611307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2706069521974977758963485 1014776070740616659611307)
                    ·
                      rfl

theorem cell22_2964404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_2964404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2964404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2964404 prefixEnd_2964404 := by exact prefixLift 2964404
  have htrace : WordTrace (prefixWord ++ tailWord_2964404) baseStart_2964404 baseEnd_2964404 := by
    simpa [prefixWord, tailWord_2964404, baseEnd_2964404] using wordTrace_append hprefix tailTrace_2964404
  have hstable : (prefixWord ++ tailWord_2964404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964404).length < 2 ^ (prefixWord ++ tailWord_2964404).sum := by decide
  have hdescent : baseEnd_2964404 < baseStart_2964404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964490 : List Nat := [3, 1, 2, 2, 3, 1, 2, 2, 6]
def baseStart_2964490 : Nat := 118140960795 + 2964490 * 2 ^ 59
def prefixEnd_2964490 : Nat := 4983230072969 + 3 ^ 40 * 2964490 * 2
def baseEnd_2964490 : Nat := 338268503432713700653681

theorem tailTrace_2964490 : CollatzResearch.WordTrace tailWord_2964490 prefixEnd_2964490 338268503432713700653681 := by
  unfold tailWord_2964490
  simp only [CollatzResearch.WordTrace]
  refine ⟨27030958257541624857234731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72082555353444332952625949 27030958257541624857234731)
  ·
    refine ⟨40546437386312437285852097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27030958257541624857234731 40546437386312437285852097)
    ·
      refine ⟨30409828039734327964389073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40546437386312437285852097 30409828039734327964389073)
      ·
        refine ⟨22807371029800745973291805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30409828039734327964389073 22807371029800745973291805)
        ·
          refine ⟨8552764136175279739984427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22807371029800745973291805 8552764136175279739984427)
          ·
            refine ⟨12829146204262919609976641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8552764136175279739984427 12829146204262919609976641)
            ·
              refine ⟨9621859653197189707482481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12829146204262919609976641 9621859653197189707482481)
              ·
                refine ⟨7216394739897892280611861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9621859653197189707482481 7216394739897892280611861)
                ·
                  refine ⟨338268503432713700653681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7216394739897892280611861 338268503432713700653681)
                  ·
                    rfl

theorem cell22_2964490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 2, 6].length) (baseStart_2964490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2964490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2964490 prefixEnd_2964490 := by exact prefixLift 2964490
  have htrace : WordTrace (prefixWord ++ tailWord_2964490) baseStart_2964490 baseEnd_2964490 := by
    simpa [prefixWord, tailWord_2964490, baseEnd_2964490] using wordTrace_append hprefix tailTrace_2964490
  have hstable : (prefixWord ++ tailWord_2964490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964490).length < 2 ^ (prefixWord ++ tailWord_2964490).sum := by decide
  have hdescent : baseEnd_2964490 < baseStart_2964490 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964492 : List Nat := [2, 2, 1, 2, 3, 3, 2, 2, 1, 4]
def baseStart_2964492 : Nat := 118140960795 + 2964492 * 2 ^ 59
def prefixEnd_2964492 : Nat := 4983230072969 + 3 ^ 40 * 2964492 * 2
def baseEnd_2964492 : Nat := 1014806194939013763411037

theorem tailTrace_2964492 : CollatzResearch.WordTrace tailWord_2964492 prefixEnd_2964492 1014806194939013763411037 := by
  unfold tailWord_2964492
  simp only [CollatzResearch.WordTrace]
  refine ⟨54061952988079626885255865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72082603984106169180341153 54061952988079626885255865)
  ·
    refine ⟨40546464741059720163941899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54061952988079626885255865 40546464741059720163941899)
    ·
      refine ⟨60819697111589580245912849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40546464741059720163941899 60819697111589580245912849)
      ·
        refine ⟨45614772833692185184434637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60819697111589580245912849 45614772833692185184434637)
        ·
          refine ⟨17105539812634569444162989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45614772833692185184434637 17105539812634569444162989)
          ·
            refine ⟨6414577429737963541561121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17105539812634569444162989 6414577429737963541561121)
            ·
              refine ⟨4810933072303472656170841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6414577429737963541561121 4810933072303472656170841)
              ·
                refine ⟨3608199804227604492128131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4810933072303472656170841 3608199804227604492128131)
                ·
                  refine ⟨5412299706341406738192197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3608199804227604492128131 5412299706341406738192197)
                  ·
                    refine ⟨1014806194939013763411037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5412299706341406738192197 1014806194939013763411037)
                    ·
                      rfl

theorem cell22_2964492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 2, 1, 4].length) (baseStart_2964492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2964492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2964492 prefixEnd_2964492 := by exact prefixLift 2964492
  have htrace : WordTrace (prefixWord ++ tailWord_2964492) baseStart_2964492 baseEnd_2964492 := by
    simpa [prefixWord, tailWord_2964492, baseEnd_2964492] using wordTrace_append hprefix tailTrace_2964492
  have hstable : (prefixWord ++ tailWord_2964492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964492).length < 2 ^ (prefixWord ++ tailWord_2964492).sum := by decide
  have hdescent : baseEnd_2964492 < baseStart_2964492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964505 : List Nat := [1, 2, 1, 2, 1, 1, 5, 2, 4, 3]
def baseStart_2964505 : Nat := 118140960795 + 2964505 * 2 ^ 59
def prefixEnd_2964505 : Nat := 4983230072969 + 3 ^ 40 * 2964505 * 2
def baseEnd_2964505 : Nat := 1014810645104686062835997

theorem tailTrace_2964505 : CollatzResearch.WordTrace tailWord_2964505 prefixEnd_2964505 1014810645104686062835997 := by
  unfold tailWord_2964505
  simp only [CollatzResearch.WordTrace]
  refine ⟨108124380125112156990734969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72082920083408104660489979 108124380125112156990734969)
  ·
    refine ⟨81093285093834117743051227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108124380125112156990734969 81093285093834117743051227)
    ·
      refine ⟨121639927640751176614576841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81093285093834117743051227 121639927640751176614576841)
      ·
        refine ⟨91229945730563382460932631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121639927640751176614576841 91229945730563382460932631)
        ·
          refine ⟨136844918595845073691398947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91229945730563382460932631 136844918595845073691398947)
          ·
            refine ⟨205267377893767610537098421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136844918595845073691398947 205267377893767610537098421)
            ·
              refine ⟨19243816677540713487852977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 205267377893767610537098421 19243816677540713487852977)
              ·
                refine ⟨14432862508155535115889733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19243816677540713487852977 14432862508155535115889733)
                ·
                  refine ⟨2706161720279162834229325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14432862508155535115889733 2706161720279162834229325)
                  ·
                    refine ⟨1014810645104686062835997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2706161720279162834229325 1014810645104686062835997)
                    ·
                      rfl

theorem cell22_2964505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 2, 4, 3].length) (baseStart_2964505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2964505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2964505 prefixEnd_2964505 := by exact prefixLift 2964505
  have htrace : WordTrace (prefixWord ++ tailWord_2964505) baseStart_2964505 baseEnd_2964505 := by
    simpa [prefixWord, tailWord_2964505, baseEnd_2964505] using wordTrace_append hprefix tailTrace_2964505
  have hstable : (prefixWord ++ tailWord_2964505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964505).length < 2 ^ (prefixWord ++ tailWord_2964505).sum := by decide
  have hdescent : baseEnd_2964505 < baseStart_2964505 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964655 : List Nat := [1, 1, 2, 1, 2, 3, 3, 2, 1, 6]
def baseStart_2964655 : Nat := 118140960795 + 2964655 * 2 ^ 59
def prefixEnd_2964655 : Nat := 4983230072969 + 3 ^ 40 * 2964655 * 2
def baseEnd_2964655 : Nat := 1014861993170135671585537

theorem tailTrace_2964655 : CollatzResearch.WordTrace tailWord_2964655 prefixEnd_2964655 1014861993170135671585537 := by
  unfold tailWord_2964655
  simp only [CollatzResearch.WordTrace]
  refine ⟨108129851074568732608695419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72086567383045821739130279 108129851074568732608695419)
  ·
    refine ⟨162194776611853098913043129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108129851074568732608695419 162194776611853098913043129)
    ·
      refine ⟨121646082458889824184782347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162194776611853098913043129 121646082458889824184782347)
      ·
        refine ⟨182469123688334736277173521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121646082458889824184782347 182469123688334736277173521)
        ·
          refine ⟨136851842766251052207880141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182469123688334736277173521 136851842766251052207880141)
          ·
            refine ⟨51319441037344144577955053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136851842766251052207880141 51319441037344144577955053)
            ·
              refine ⟨19244790389004054216733145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51319441037344144577955053 19244790389004054216733145)
              ·
                refine ⟨14433592791753040662549859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19244790389004054216733145 14433592791753040662549859)
                ·
                  refine ⟨21650389187629560993824789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14433592791753040662549859 21650389187629560993824789)
                  ·
                    refine ⟨1014861993170135671585537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21650389187629560993824789 1014861993170135671585537)
                    ·
                      rfl

theorem cell22_2964655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 2, 1, 6].length) (baseStart_2964655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2964655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2964655 prefixEnd_2964655 := by exact prefixLift 2964655
  have htrace : WordTrace (prefixWord ++ tailWord_2964655) baseStart_2964655 baseEnd_2964655 := by
    simpa [prefixWord, tailWord_2964655, baseEnd_2964655] using wordTrace_append hprefix tailTrace_2964655
  have hstable : (prefixWord ++ tailWord_2964655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964655).length < 2 ^ (prefixWord ++ tailWord_2964655).sum := by decide
  have hdescent : baseEnd_2964655 < baseStart_2964655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964796 : List Nat := [2, 2, 2, 2, 1, 3, 4, 1, 1, 4]
def baseStart_2964796 : Nat := 118140960795 + 2964796 * 2 ^ 59
def prefixEnd_2964796 : Nat := 4983230072969 + 3 ^ 40 * 2964796 * 2
def baseEnd_2964796 : Nat := 1014910260351658303810105

theorem tailTrace_2964796 : CollatzResearch.WordTrace tailWord_2964796 prefixEnd_2964796 1014910260351658303810105 := by
  unfold tailWord_2964796
  simp only [CollatzResearch.WordTrace]
  refine ⟨54067496883528956844789121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72089995844705275793052161 54067496883528956844789121)
  ·
    refine ⟨40550622662646717633591841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54067496883528956844789121 40550622662646717633591841)
    ·
      refine ⟨30412966996985038225193881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40550622662646717633591841 30412966996985038225193881)
      ·
        refine ⟨22809725247738778668895411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30412966996985038225193881 22809725247738778668895411)
        ·
          refine ⟨34214587871608168003343117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22809725247738778668895411 34214587871608168003343117)
          ·
            refine ⟨12830470451853063001253669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34214587871608168003343117 12830470451853063001253669)
            ·
              refine ⟨2405713209722449312735063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12830470451853063001253669 2405713209722449312735063)
              ·
                refine ⟨3608569814583673969102595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2405713209722449312735063 3608569814583673969102595)
                ·
                  refine ⟨5412854721875510953653893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3608569814583673969102595 5412854721875510953653893)
                  ·
                    refine ⟨1014910260351658303810105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5412854721875510953653893 1014910260351658303810105)
                    ·
                      rfl

theorem cell22_2964796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 4, 1, 1, 4].length) (baseStart_2964796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2964796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2964796 prefixEnd_2964796 := by exact prefixLift 2964796
  have htrace : WordTrace (prefixWord ++ tailWord_2964796) baseStart_2964796 baseEnd_2964796 := by
    simpa [prefixWord, tailWord_2964796, baseEnd_2964796] using wordTrace_append hprefix tailTrace_2964796
  have hstable : (prefixWord ++ tailWord_2964796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964796).length < 2 ^ (prefixWord ++ tailWord_2964796).sum := by decide
  have hdescent : baseEnd_2964796 < baseStart_2964796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964837 : List Nat := [1, 3, 1, 3, 1, 2, 1, 1, 2, 7]
def baseStart_2964837 : Nat := 118140960795 + 2964837 * 2 ^ 59
def prefixEnd_2964837 : Nat := 4983230072969 + 3 ^ 40 * 2964837 * 2
def baseEnd_2964837 : Nat := 1014924295489547863534979

theorem tailTrace_2964837 : CollatzResearch.WordTrace tailWord_2964837 prefixEnd_2964837 1014924295489547863534979 := by
  unfold tailWord_2964837
  simp only [CollatzResearch.WordTrace]
  refine ⟨108136489159909377691820765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72090992773272918461213843 108136489159909377691820765)
  ·
    refine ⟨40551183434966016634432787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108136489159909377691820765 40551183434966016634432787)
    ·
      refine ⟨60826775152449024951649181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40551183434966016634432787 60826775152449024951649181)
      ·
        refine ⟨22810040682168384356868443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60826775152449024951649181 22810040682168384356868443)
        ·
          refine ⟨34215061023252576535302665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22810040682168384356868443 34215061023252576535302665)
          ·
            refine ⟨25661295767439432401476999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34215061023252576535302665 25661295767439432401476999)
            ·
              refine ⟨38491943651159148602215499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25661295767439432401476999 38491943651159148602215499)
              ·
                refine ⟨57737915476738722903323249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38491943651159148602215499 57737915476738722903323249)
                ·
                  refine ⟨43303436607554042177492437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57737915476738722903323249 43303436607554042177492437)
                  ·
                    refine ⟨1014924295489547863534979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43303436607554042177492437 1014924295489547863534979)
                    ·
                      rfl

theorem cell22_2964837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 7].length) (baseStart_2964837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2964837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2964837 prefixEnd_2964837 := by exact prefixLift 2964837
  have htrace : WordTrace (prefixWord ++ tailWord_2964837) baseStart_2964837 baseEnd_2964837 := by
    simpa [prefixWord, tailWord_2964837, baseEnd_2964837] using wordTrace_append hprefix tailTrace_2964837
  have hstable : (prefixWord ++ tailWord_2964837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964837).length < 2 ^ (prefixWord ++ tailWord_2964837).sum := by decide
  have hdescent : baseEnd_2964837 < baseStart_2964837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964839 : List Nat := [1, 1, 5, 1, 4, 1, 1, 8]
def baseStart_2964839 : Nat := 118140960795 + 2964839 * 2 ^ 59
def prefixEnd_2964839 : Nat := 4983230072969 + 3 ^ 40 * 2964839 * 2
def baseEnd_2964839 : Nat := 112769442236713391664997

theorem tailTrace_2964839 : CollatzResearch.WordTrace tailWord_2964839 prefixEnd_2964839 112769442236713391664997 := by
  unfold tailWord_2964839
  simp only [CollatzResearch.WordTrace]
  refine ⟨108136562105902132033393571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72091041403934754688929047 108136562105902132033393571)
  ·
    refine ⟨162204843158853198050090357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108136562105902132033393571 162204843158853198050090357)
    ·
      refine ⟨15206704046142487317195971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 162204843158853198050090357 15206704046142487317195971)
      ·
        refine ⟨22810056069213730975793957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15206704046142487317195971 22810056069213730975793957)
        ·
          refine ⟨4276885512977574557961367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22810056069213730975793957 4276885512977574557961367)
          ·
            refine ⟨6415328269466361836942051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4276885512977574557961367 6415328269466361836942051)
            ·
              refine ⟨9622992404199542755413077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6415328269466361836942051 9622992404199542755413077)
              ·
                refine ⟨112769442236713391664997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9622992404199542755413077 112769442236713391664997)
                ·
                  rfl

theorem cell22_2964839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 8].length) (baseStart_2964839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2964839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2964839 prefixEnd_2964839 := by exact prefixLift 2964839
  have htrace : WordTrace (prefixWord ++ tailWord_2964839) baseStart_2964839 baseEnd_2964839 := by
    simpa [prefixWord, tailWord_2964839, baseEnd_2964839] using wordTrace_append hprefix tailTrace_2964839
  have hstable : (prefixWord ++ tailWord_2964839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964839).length < 2 ^ (prefixWord ++ tailWord_2964839).sum := by decide
  have hdescent : baseEnd_2964839 < baseStart_2964839 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964862 : List Nat := [4, 2, 3, 2, 1, 1, 3, 2, 4]
def baseStart_2964862 : Nat := 118140960795 + 2964862 * 2 ^ 59
def prefixEnd_2964862 : Nat := 4983230072969 + 3 ^ 40 * 2964862 * 2
def baseEnd_2964862 : Nat := 338310951166818710553301

theorem tailTrace_2964862 : CollatzResearch.WordTrace tailWord_2964862 prefixEnd_2964862 338310951166818710553301 := by
  unfold tailWord_2964862
  simp only [CollatzResearch.WordTrace]
  refine ⟨13517175123102350870185105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72091600656545871307653893 13517175123102350870185105)
  ·
    refine ⟨10137881342326763152638829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13517175123102350870185105 10137881342326763152638829)
    ·
      refine ⟨3801705503372536182239561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10137881342326763152638829 3801705503372536182239561)
      ·
        refine ⟨2851279127529402136679671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3801705503372536182239561 2851279127529402136679671)
        ·
          refine ⟨4276918691294103205019507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2851279127529402136679671 4276918691294103205019507)
          ·
            refine ⟨6415378036941154807529261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4276918691294103205019507 6415378036941154807529261)
            ·
              refine ⟨2405766763852933052823473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6415378036941154807529261 2405766763852933052823473)
              ·
                refine ⟨1804325072889699789617605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2405766763852933052823473 1804325072889699789617605)
                ·
                  refine ⟨338310951166818710553301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1804325072889699789617605 338310951166818710553301)
                  ·
                    rfl

theorem cell22_2964862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 3, 2, 4].length) (baseStart_2964862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2964862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2964862 prefixEnd_2964862 := by exact prefixLift 2964862
  have htrace : WordTrace (prefixWord ++ tailWord_2964862) baseStart_2964862 baseEnd_2964862 := by
    simpa [prefixWord, tailWord_2964862, baseEnd_2964862] using wordTrace_append hprefix tailTrace_2964862
  have hstable : (prefixWord ++ tailWord_2964862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964862).length < 2 ^ (prefixWord ++ tailWord_2964862).sum := by decide
  have hdescent : baseEnd_2964862 < baseStart_2964862 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964871 : List Nat := [1, 1, 4, 2, 2, 2, 3, 1, 3, 3]
def baseStart_2964871 : Nat := 118140960795 + 2964871 * 2 ^ 59
def prefixEnd_2964871 : Nat := 4983230072969 + 3 ^ 40 * 2964871 * 2
def baseEnd_2964871 : Nat := 1014935934384383108184875

theorem tailTrace_2964871 : CollatzResearch.WordTrace tailWord_2964871 prefixEnd_2964871 1014935934384383108184875 := by
  unfold tailWord_2964871
  simp only [CollatzResearch.WordTrace]
  refine ⟨108137729241786201498558467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72091819494524134332372311 108137729241786201498558467)
  ·
    refine ⟨162206593862679302247837701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108137729241786201498558467 162206593862679302247837701)
    ·
      refine ⟨30413736349252369171469569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 162206593862679302247837701 30413736349252369171469569)
      ·
        refine ⟨22810302261939276878602177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30413736349252369171469569 22810302261939276878602177)
        ·
          refine ⟨17107726696454457658951633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22810302261939276878602177 17107726696454457658951633)
          ·
            refine ⟨12830795022340843244213725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17107726696454457658951633 12830795022340843244213725)
            ·
              refine ⟨4811548133377816216580147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12830795022340843244213725 4811548133377816216580147)
              ·
                refine ⟨7217322200066724324870221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4811548133377816216580147 7217322200066724324870221)
                ·
                  refine ⟨2706495825025021621826333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7217322200066724324870221 2706495825025021621826333)
                  ·
                    refine ⟨1014935934384383108184875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2706495825025021621826333 1014935934384383108184875)
                    ·
                      rfl

theorem cell22_2964871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 1, 3, 3].length) (baseStart_2964871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2964871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2964871 prefixEnd_2964871 := by exact prefixLift 2964871
  have htrace : WordTrace (prefixWord ++ tailWord_2964871) baseStart_2964871 baseEnd_2964871 := by
    simpa [prefixWord, tailWord_2964871, baseEnd_2964871] using wordTrace_append hprefix tailTrace_2964871
  have hstable : (prefixWord ++ tailWord_2964871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964871).length < 2 ^ (prefixWord ++ tailWord_2964871).sum := by decide
  have hdescent : baseEnd_2964871 < baseStart_2964871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964912 : List Nat := [2, 1, 1, 1, 2, 1, 1, 3, 10]
def baseStart_2964912 : Nat := 118140960795 + 2964912 * 2 ^ 59
def prefixEnd_2964912 : Nat := 4983230072969 + 3 ^ 40 * 2964912 * 2
def baseEnd_2964912 : Nat := 338316656507424222636583

theorem tailTrace_2964912 : CollatzResearch.WordTrace tailWord_2964912 prefixEnd_2964912 338316656507424222636583 := by
  unfold tailWord_2964912
  simp only [CollatzResearch.WordTrace]
  refine ⟨54069612317318832750400495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72092816423091777000533993 54069612317318832750400495)
  ·
    refine ⟨81104418475978249125600743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54069612317318832750400495 81104418475978249125600743)
    ·
      refine ⟨121656627713967373688401115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81104418475978249125600743 121656627713967373688401115)
      ·
        refine ⟨182484941570951060532601673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121656627713967373688401115 182484941570951060532601673)
        ·
          refine ⟨136863706178213295399451255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182484941570951060532601673 136863706178213295399451255)
          ·
            refine ⟨205295559267319943099176883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136863706178213295399451255 205295559267319943099176883)
            ·
              refine ⟨307943338900979914648765325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205295559267319943099176883 307943338900979914648765325)
              ·
                refine ⟨115478752087867467993286997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 307943338900979914648765325 115478752087867467993286997)
                ·
                  refine ⟨338316656507424222636583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 115478752087867467993286997 338316656507424222636583)
                  ·
                    rfl

theorem cell22_2964912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 10].length) (baseStart_2964912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2964912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2964912 prefixEnd_2964912 := by exact prefixLift 2964912
  have htrace : WordTrace (prefixWord ++ tailWord_2964912) baseStart_2964912 baseEnd_2964912 := by
    simpa [prefixWord, tailWord_2964912, baseEnd_2964912] using wordTrace_append hprefix tailTrace_2964912
  have hstable : (prefixWord ++ tailWord_2964912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964912).length < 2 ^ (prefixWord ++ tailWord_2964912).sum := by decide
  have hdescent : baseEnd_2964912 < baseStart_2964912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964959 : List Nat := [1, 1, 2, 3, 3, 1, 3, 1, 1, 6]
def baseStart_2964959 : Nat := 118140960795 + 2964959 * 2 ^ 59
def prefixEnd_2964959 : Nat := 4983230072969 + 3 ^ 40 * 2964959 * 2
def baseEnd_2964959 : Nat := 1014966058582780211984605

theorem tailTrace_2964959 : CollatzResearch.WordTrace tailWord_2964959 prefixEnd_2964959 1014966058582780211984605 := by
  unfold tailWord_2964959
  simp only [CollatzResearch.WordTrace]
  refine ⟨108140938865467392527761931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72093959243644928351841287 108140938865467392527761931)
  ·
    refine ⟨162211408298201088791642897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108140938865467392527761931 162211408298201088791642897)
    ·
      refine ⟨121658556223650816593732173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162211408298201088791642897 121658556223650816593732173)
      ·
        refine ⟨45621958583869056222649565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121658556223650816593732173 45621958583869056222649565)
        ·
          refine ⟨17108234468950896083493587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45621958583869056222649565 17108234468950896083493587)
          ·
            refine ⟨25662351703426344125240381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17108234468950896083493587 25662351703426344125240381)
            ·
              refine ⟨9623381888784879046965143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25662351703426344125240381 9623381888784879046965143)
              ·
                refine ⟨14435072833177318570447715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9623381888784879046965143 14435072833177318570447715)
                ·
                  refine ⟨21652609249765977855671573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14435072833177318570447715 21652609249765977855671573)
                  ·
                    refine ⟨1014966058582780211984605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21652609249765977855671573 1014966058582780211984605)
                    ·
                      rfl

theorem cell22_2964959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 1, 1, 6].length) (baseStart_2964959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2964959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2964959 prefixEnd_2964959 := by exact prefixLift 2964959
  have htrace : WordTrace (prefixWord ++ tailWord_2964959) baseStart_2964959 baseEnd_2964959 := by
    simpa [prefixWord, tailWord_2964959, baseEnd_2964959] using wordTrace_append hprefix tailTrace_2964959
  have hstable : (prefixWord ++ tailWord_2964959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964959).length < 2 ^ (prefixWord ++ tailWord_2964959).sum := by decide
  have hdescent : baseEnd_2964959 < baseStart_2964959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964963 : List Nat := [1, 1, 1, 6, 2, 2, 2, 3, 4]
def baseStart_2964963 : Nat := 118140960795 + 2964963 * 2 ^ 59
def prefixEnd_2964963 : Nat := 4983230072969 + 3 ^ 40 * 2964963 * 2
def baseEnd_2964963 : Nat := 338322475954841844961531

theorem tailTrace_2964963 : CollatzResearch.WordTrace tailWord_2964963 prefixEnd_2964963 338322475954841844961531 := by
  unfold tailWord_2964963
  simp only [CollatzResearch.WordTrace]
  refine ⟨108141084757452901210907543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72094056504968600807271695 108141084757452901210907543)
  ·
    refine ⟨162211627136179351816361315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108141084757452901210907543 162211627136179351816361315)
    ·
      refine ⟨243317440704269027724541973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162211627136179351816361315 243317440704269027724541973)
      ·
        refine ⟨11405505033012610674587905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 243317440704269027724541973 11405505033012610674587905)
        ·
          refine ⟨8554128774759458005940929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11405505033012610674587905 8554128774759458005940929)
          ·
            refine ⟨6415596581069593504455697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8554128774759458005940929 6415596581069593504455697)
            ·
              refine ⟨4811697435802195128341773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6415596581069593504455697 4811697435802195128341773)
              ·
                refine ⟨1804386538425823173128165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4811697435802195128341773 1804386538425823173128165)
                ·
                  refine ⟨338322475954841844961531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1804386538425823173128165 338322475954841844961531)
                  ·
                    rfl

theorem cell22_2964963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 3, 4].length) (baseStart_2964963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2964963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2964963 prefixEnd_2964963 := by exact prefixLift 2964963
  have htrace : WordTrace (prefixWord ++ tailWord_2964963) baseStart_2964963 baseEnd_2964963 := by
    simpa [prefixWord, tailWord_2964963, baseEnd_2964963] using wordTrace_append hprefix tailTrace_2964963
  have hstable : (prefixWord ++ tailWord_2964963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964963).length < 2 ^ (prefixWord ++ tailWord_2964963).sum := by decide
  have hdescent : baseEnd_2964963 < baseStart_2964963 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964965 : List Nat := [1, 3, 1, 5, 1, 3, 2, 1, 1, 4]
def baseStart_2964965 : Nat := 118140960795 + 2964965 * 2 ^ 59
def prefixEnd_2964965 : Nat := 4983230072969 + 3 ^ 40 * 2964965 * 2
def baseEnd_2964965 : Nat := 1014968112505398196334587

theorem tailTrace_2964965 : CollatzResearch.WordTrace tailWord_2964965 prefixEnd_2964965 1014968112505398196334587 := by
  unfold tailWord_2964965
  simp only [CollatzResearch.WordTrace]
  refine ⟨108141157703445655552480349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72094105135630437034986899 108141157703445655552480349)
  ·
    refine ⟨40552934138792120832180131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108141157703445655552480349 40552934138792120832180131)
    ·
      refine ⟨60829401208188181248270197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40552934138792120832180131 60829401208188181248270197)
      ·
        refine ⟨5702756363267641992025331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 60829401208188181248270197 5702756363267641992025331)
        ·
          refine ⟨8554134544901462988037997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5702756363267641992025331 8554134544901462988037997)
          ·
            refine ⟨3207800454338048620514249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8554134544901462988037997 3207800454338048620514249)
            ·
              refine ⟨2405850340753536465385687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3207800454338048620514249 2405850340753536465385687)
              ·
                refine ⟨3608775511130304698078531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2405850340753536465385687 3608775511130304698078531)
                ·
                  refine ⟨5413163266695457047117797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3608775511130304698078531 5413163266695457047117797)
                  ·
                    refine ⟨1014968112505398196334587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5413163266695457047117797 1014968112505398196334587)
                    ·
                      rfl

theorem cell22_2964965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 2, 1, 1, 4].length) (baseStart_2964965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2964965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2964965 prefixEnd_2964965 := by exact prefixLift 2964965
  have htrace : WordTrace (prefixWord ++ tailWord_2964965) baseStart_2964965 baseEnd_2964965 := by
    simpa [prefixWord, tailWord_2964965, baseEnd_2964965] using wordTrace_append hprefix tailTrace_2964965
  have hstable : (prefixWord ++ tailWord_2964965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964965).length < 2 ^ (prefixWord ++ tailWord_2964965).sum := by decide
  have hdescent : baseEnd_2964965 < baseStart_2964965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964974 : List Nat := [4, 1, 2, 1, 2, 1, 11]
def baseStart_2964974 : Nat := 118140960795 + 2964974 * 2 ^ 59
def prefixEnd_2964974 : Nat := 4983230072969 + 3 ^ 40 * 2964974 * 2
def baseEnd_2964974 : Nat := 37591525681086117513317

theorem tailTrace_2964974 : CollatzResearch.WordTrace tailWord_2964974 prefixEnd_2964974 37591525681086117513317 := by
  unfold tailWord_2964974
  simp only [CollatzResearch.WordTrace]
  refine ⟨13517685745051631261194747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72094323973608700059705317 13517685745051631261194747)
  ·
    refine ⟨20276528617577446891792121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13517685745051631261194747 20276528617577446891792121)
    ·
      refine ⟨15207396463183085168844091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20276528617577446891792121 15207396463183085168844091)
      ·
        refine ⟨22811094694774627753266137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15207396463183085168844091 22811094694774627753266137)
        ·
          refine ⟨17108321021080970814949603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22811094694774627753266137 17108321021080970814949603)
          ·
            refine ⟨25662481531621456222424405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17108321021080970814949603 25662481531621456222424405)
            ·
              refine ⟨37591525681086117513317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 25662481531621456222424405 37591525681086117513317)
              ·
                rfl

theorem cell22_2964974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 11].length) (baseStart_2964974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2964974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2964974 prefixEnd_2964974 := by exact prefixLift 2964974
  have htrace : WordTrace (prefixWord ++ tailWord_2964974) baseStart_2964974 baseEnd_2964974 := by
    simpa [prefixWord, tailWord_2964974, baseEnd_2964974] using wordTrace_append hprefix tailTrace_2964974
  have hstable : (prefixWord ++ tailWord_2964974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964974).length < 2 ^ (prefixWord ++ tailWord_2964974).sum := by decide
  have hdescent : baseEnd_2964974 < baseStart_2964974 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2964978 : List Nat := [3, 2, 1, 4, 1, 2, 1, 1, 4, 3]
def baseStart_2964978 : Nat := 118140960795 + 2964978 * 2 ^ 59
def prefixEnd_2964978 : Nat := 4983230072969 + 3 ^ 40 * 2964978 * 2
def baseEnd_2964978 : Nat := 1014972562671070495759547

theorem tailTrace_2964978 : CollatzResearch.WordTrace tailWord_2964978 prefixEnd_2964978 1014972562671070495759547 := by
  unfold tailWord_2964978
  simp only [CollatzResearch.WordTrace]
  refine ⟨27035407963099639693175897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72094421234932372515135725 27035407963099639693175897)
  ·
    refine ⟨20276555972324729769881923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27035407963099639693175897 20276555972324729769881923)
    ·
      refine ⟨30414833958487094654822885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20276555972324729769881923 30414833958487094654822885)
      ·
        refine ⟨5702781367216330247779291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30414833958487094654822885 5702781367216330247779291)
        ·
          refine ⟨8554172050824495371668937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5702781367216330247779291 8554172050824495371668937)
          ·
            refine ⟨6415629038118371528751703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8554172050824495371668937 6415629038118371528751703)
            ·
              refine ⟨9623443557177557293127555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6415629038118371528751703 9623443557177557293127555)
              ·
                refine ⟨14435165335766335939691333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9623443557177557293127555 14435165335766335939691333)
                ·
                  refine ⟨2706593500456187988692125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14435165335766335939691333 2706593500456187988692125)
                  ·
                    refine ⟨1014972562671070495759547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2706593500456187988692125 1014972562671070495759547)
                    ·
                      rfl

theorem cell22_2964978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 1, 4, 3].length) (baseStart_2964978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2964978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2964978 prefixEnd_2964978 := by exact prefixLift 2964978
  have htrace : WordTrace (prefixWord ++ tailWord_2964978) baseStart_2964978 baseEnd_2964978 := by
    simpa [prefixWord, tailWord_2964978, baseEnd_2964978] using wordTrace_append hprefix tailTrace_2964978
  have hstable : (prefixWord ++ tailWord_2964978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2964978).length < 2 ^ (prefixWord ++ tailWord_2964978).sum := by decide
  have hdescent : baseEnd_2964978 < baseStart_2964978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2964978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2965053 : List Nat := [1, 4, 1, 3, 3, 1, 1, 3, 5]
def baseStart_2965053 : Nat := 118140960795 + 2965053 * 2 ^ 59
def prefixEnd_2965053 : Nat := 4983230072969 + 3 ^ 40 * 2965053 * 2
def baseEnd_2965053 : Nat := 338332745567931766711439

theorem tailTrace_2965053 : CollatzResearch.WordTrace tailWord_2965053 prefixEnd_2965053 338332745567931766711439 := by
  unfold tailWord_2965053
  simp only [CollatzResearch.WordTrace]
  refine ⟨108144367327126846581683813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72096244884751231054455875 108144367327126846581683813)
  ·
    refine ⟨20277068873836283734065715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108144367327126846581683813 20277068873836283734065715)
    ·
      refine ⟨30415603310754425601098573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20277068873836283734065715 30415603310754425601098573)
      ·
        refine ⟨11405851241532909600411965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30415603310754425601098573 11405851241532909600411965)
        ·
          refine ⟨4277194215574841100154487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11405851241532909600411965 4277194215574841100154487)
          ·
            refine ⟨6415791323362261650231731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4277194215574841100154487 6415791323362261650231731)
            ·
              refine ⟨9623686985043392475347597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6415791323362261650231731 9623686985043392475347597)
              ·
                refine ⟨3608882619391272178255349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9623686985043392475347597 3608882619391272178255349)
                ·
                  refine ⟨338332745567931766711439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3608882619391272178255349 338332745567931766711439)
                  ·
                    rfl

theorem cell22_2965053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 3, 5].length) (baseStart_2965053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2965053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2965053 prefixEnd_2965053 := by exact prefixLift 2965053
  have htrace : WordTrace (prefixWord ++ tailWord_2965053) baseStart_2965053 baseEnd_2965053 := by
    simpa [prefixWord, tailWord_2965053, baseEnd_2965053] using wordTrace_append hprefix tailTrace_2965053
  have hstable : (prefixWord ++ tailWord_2965053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2965053).length < 2 ^ (prefixWord ++ tailWord_2965053).sum := by decide
  have hdescent : baseEnd_2965053 < baseStart_2965053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2965053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2965066 : List Nat := [3, 1, 2, 1, 1, 3, 3, 1, 3, 4]
def baseStart_2965066 : Nat := 118140960795 + 2965066 * 2 ^ 59
def prefixEnd_2965066 : Nat := 4983230072969 + 3 ^ 40 * 2965066 * 2
def baseEnd_2965066 : Nat := 1015002686869467599559277

theorem tailTrace_2965066 : CollatzResearch.WordTrace tailWord_2965066 prefixEnd_2965066 1015002686869467599559277 := by
  unfold tailWord_2965066
  simp only [CollatzResearch.WordTrace]
  refine ⟨27036210369019937450476763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72096560984053166534604701 27036210369019937450476763)
  ·
    refine ⟨40554315553529906175715145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27036210369019937450476763 40554315553529906175715145)
    ·
      refine ⟨30415736665147429631786359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40554315553529906175715145 30415736665147429631786359)
      ·
        refine ⟨45623604997721144447679539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30415736665147429631786359 45623604997721144447679539)
        ·
          refine ⟨68435407496581716671519309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45623604997721144447679539 68435407496581716671519309)
          ·
            refine ⟨25663277811218143751819741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68435407496581716671519309 25663277811218143751819741)
            ·
              refine ⟨9623729179206803906932403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25663277811218143751819741 9623729179206803906932403)
              ·
                refine ⟨14435593768810205860398605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9623729179206803906932403 14435593768810205860398605)
                ·
                  refine ⟨5413347663303827197649477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14435593768810205860398605 5413347663303827197649477)
                  ·
                    refine ⟨1015002686869467599559277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5413347663303827197649477 1015002686869467599559277)
                    ·
                      rfl

theorem cell22_2965066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 1, 3, 4].length) (baseStart_2965066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2965066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2965066 prefixEnd_2965066 := by exact prefixLift 2965066
  have htrace : WordTrace (prefixWord ++ tailWord_2965066) baseStart_2965066 baseEnd_2965066 := by
    simpa [prefixWord, tailWord_2965066, baseEnd_2965066] using wordTrace_append hprefix tailTrace_2965066
  have hstable : (prefixWord ++ tailWord_2965066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2965066).length < 2 ^ (prefixWord ++ tailWord_2965066).sum := by decide
  have hdescent : baseEnd_2965066 < baseStart_2965066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2965066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2965113 : List Nat := [1, 2, 1, 3, 3, 1, 1, 5, 2, 3]
def baseStart_2965113 : Nat := 118140960795 + 2965113 * 2 ^ 59
def prefixEnd_2965113 : Nat := 4983230072969 + 3 ^ 40 * 2965113 * 2
def baseEnd_2965113 : Nat := 1015018775929975143634133

theorem tailTrace_2965113 : CollatzResearch.WordTrace tailWord_2965113 prefixEnd_2965113 1015018775929975143634133 := by
  unfold tailWord_2965113
  simp only [CollatzResearch.WordTrace]
  refine ⟨108146555706909476828867993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72097703804606317885911995 108146555706909476828867993)
  ·
    refine ⟨81109916780182107621650995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108146555706909476828867993 81109916780182107621650995)
    ·
      refine ⟨121664875170273161432476493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81109916780182107621650995 121664875170273161432476493)
      ·
        refine ⟨45624328188852435537178685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121664875170273161432476493 45624328188852435537178685)
        ·
          refine ⟨17109123070819663326442007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45624328188852435537178685 17109123070819663326442007)
          ·
            refine ⟨25663684606229494989663011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17109123070819663326442007 25663684606229494989663011)
            ·
              refine ⟨38495526909344242484494517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25663684606229494989663011 38495526909344242484494517)
              ·
                refine ⟨3608955647751022732921361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38495526909344242484494517 3608955647751022732921361)
                ·
                  refine ⟨2706716735813267049691021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3608955647751022732921361 2706716735813267049691021)
                  ·
                    refine ⟨1015018775929975143634133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2706716735813267049691021 1015018775929975143634133)
                    ·
                      rfl

theorem cell22_2965113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 5, 2, 3].length) (baseStart_2965113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2965113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2965113 prefixEnd_2965113 := by exact prefixLift 2965113
  have htrace : WordTrace (prefixWord ++ tailWord_2965113) baseStart_2965113 baseEnd_2965113 := by
    simpa [prefixWord, tailWord_2965113, baseEnd_2965113] using wordTrace_append hprefix tailTrace_2965113
  have hstable : (prefixWord ++ tailWord_2965113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2965113).length < 2 ^ (prefixWord ++ tailWord_2965113).sum := by decide
  have hdescent : baseEnd_2965113 < baseStart_2965113 := by decide
  rcases family_descends (prefixWord ++ tailWord_2965113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2965252 : List Nat := [2, 3, 2, 2, 1, 3, 3, 1, 1, 4]
def baseStart_2965252 : Nat := 118140960795 + 2965252 * 2 ^ 59
def prefixEnd_2965252 : Nat := 4983230072969 + 3 ^ 40 * 2965252 * 2
def baseEnd_2965252 : Nat := 1015066358470625114408707

theorem tailTrace_2965252 : CollatzResearch.WordTrace tailWord_2965252 prefixEnd_2965252 1015066358470625114408707 := by
  unfold tailWord_2965252
  simp only [CollatzResearch.WordTrace]
  refine ⟨54075812726702951784089005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72101083635603935712118673 54075812726702951784089005)
  ·
    refine ⟨20278429772513606919033377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54075812726702951784089005 20278429772513606919033377)
    ·
      refine ⟨15208822329385205189275033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20278429772513606919033377 15208822329385205189275033)
      ·
        refine ⟨11406616747038903891956275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15208822329385205189275033 11406616747038903891956275)
        ·
          refine ⟨17109925120558355837934413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11406616747038903891956275 17109925120558355837934413)
          ·
            refine ⟨6416221920209383439225405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17109925120558355837934413 6416221920209383439225405)
            ·
              refine ⟨2406083220078518789709527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6416221920209383439225405 2406083220078518789709527)
              ·
                refine ⟨3609124830117778184564291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2406083220078518789709527 3609124830117778184564291)
                ·
                  refine ⟨5413687245176667276846437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3609124830117778184564291 5413687245176667276846437)
                  ·
                    refine ⟨1015066358470625114408707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5413687245176667276846437 1015066358470625114408707)
                    ·
                      rfl

theorem cell22_2965252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 3, 1, 1, 4].length) (baseStart_2965252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2965252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2965252 prefixEnd_2965252 := by exact prefixLift 2965252
  have htrace : WordTrace (prefixWord ++ tailWord_2965252) baseStart_2965252 baseEnd_2965252 := by
    simpa [prefixWord, tailWord_2965252, baseEnd_2965252] using wordTrace_append hprefix tailTrace_2965252
  have hstable : (prefixWord ++ tailWord_2965252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2965252).length < 2 ^ (prefixWord ++ tailWord_2965252).sum := by decide
  have hdescent : baseEnd_2965252 < baseStart_2965252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2965252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2965291 : List Nat := [1, 1, 1, 1, 2, 1, 2, 2, 3, 8]
def baseStart_2965291 : Nat := 118140960795 + 2965291 * 2 ^ 59
def prefixEnd_2965291 : Nat := 4983230072969 + 3 ^ 40 * 2965291 * 2
def baseEnd_2965291 : Nat := 1015079708967642012683587

theorem tailTrace_2965291 : CollatzResearch.WordTrace tailWord_2965291 prefixEnd_2965291 1015079708967642012683587 := by
  unfold tailWord_2965291
  simp only [CollatzResearch.WordTrace]
  refine ⟨108153047900264613228847727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72102031933509742152565151 108153047900264613228847727)
  ·
    refine ⟨162229571850396919843271591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108153047900264613228847727 162229571850396919843271591)
    ·
      refine ⟨243344357775595379764907387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162229571850396919843271591 243344357775595379764907387)
      ·
        refine ⟨365016536663393069647361081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243344357775595379764907387 365016536663393069647361081)
        ·
          refine ⟨273762402497544802235520811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 365016536663393069647361081 273762402497544802235520811)
          ·
            refine ⟨410643603746317203353281217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 273762402497544802235520811 410643603746317203353281217)
            ·
              refine ⟨307982702809737902514960913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 410643603746317203353281217 307982702809737902514960913)
              ·
                refine ⟨230987027107303426886220685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 307982702809737902514960913 230987027107303426886220685)
                ·
                  refine ⟨86620135165238785082332757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 230987027107303426886220685 86620135165238785082332757)
                  ·
                    refine ⟨1015079708967642012683587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 86620135165238785082332757 1015079708967642012683587)
                    ·
                      rfl

theorem cell22_2965291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 8].length) (baseStart_2965291 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2965291 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2965291 prefixEnd_2965291 := by exact prefixLift 2965291
  have htrace : WordTrace (prefixWord ++ tailWord_2965291) baseStart_2965291 baseEnd_2965291 := by
    simpa [prefixWord, tailWord_2965291, baseEnd_2965291] using wordTrace_append hprefix tailTrace_2965291
  have hstable : (prefixWord ++ tailWord_2965291).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2965291).length < 2 ^ (prefixWord ++ tailWord_2965291).sum := by decide
  have hdescent : baseEnd_2965291 < baseStart_2965291 := by decide
  rcases family_descends (prefixWord ++ tailWord_2965291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2965338 : List Nat := [3, 1, 1, 2, 1, 3, 1, 3, 2, 5]
def baseStart_2965338 : Nat := 118140960795 + 2965338 * 2 ^ 59
def prefixEnd_2965338 : Nat := 4983230072969 + 3 ^ 40 * 2965338 * 2
def baseEnd_2965338 : Nat := 1015095798028149556758443

theorem tailTrace_2965338 : CollatzResearch.WordTrace tailWord_2965338 prefixEnd_2965338 1015095798028149556758443 := by
  unfold tailWord_2965338
  simp only [CollatzResearch.WordTrace]
  refine ⟨27038690532773585063952167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72103174754062893503872445 27038690532773585063952167)
  ·
    refine ⟨40558035799160377595928251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27038690532773585063952167 40558035799160377595928251)
    ·
      refine ⟨60837053698740566393892377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40558035799160377595928251 60837053698740566393892377)
      ·
        refine ⟨45627790274055424795419283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60837053698740566393892377 45627790274055424795419283)
        ·
          refine ⟨68441685411083137193128925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45627790274055424795419283 68441685411083137193128925)
          ·
            refine ⟨25665632029156176447423347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68441685411083137193128925 25665632029156176447423347)
            ·
              refine ⟨38498448043734264671135021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25665632029156176447423347 38498448043734264671135021)
              ·
                refine ⟨14436918016400349251675633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38498448043734264671135021 14436918016400349251675633)
                ·
                  refine ⟨10827688512300261938756725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14436918016400349251675633 10827688512300261938756725)
                  ·
                    refine ⟨1015095798028149556758443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10827688512300261938756725 1015095798028149556758443)
                    ·
                      rfl

theorem cell22_2965338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 3, 2, 5].length) (baseStart_2965338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2965338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2965338 prefixEnd_2965338 := by exact prefixLift 2965338
  have htrace : WordTrace (prefixWord ++ tailWord_2965338) baseStart_2965338 baseEnd_2965338 := by
    simpa [prefixWord, tailWord_2965338, baseEnd_2965338] using wordTrace_append hprefix tailTrace_2965338
  have hstable : (prefixWord ++ tailWord_2965338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2965338).length < 2 ^ (prefixWord ++ tailWord_2965338).sum := by decide
  have hdescent : baseEnd_2965338 < baseStart_2965338 := by decide
  rcases family_descends (prefixWord ++ tailWord_2965338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2965353 : List Nat := [1, 2, 1, 1, 1, 3, 1, 5, 3, 4]
def baseStart_2965353 : Nat := 118140960795 + 2965353 * 2 ^ 59
def prefixEnd_2965353 : Nat := 4983230072969 + 3 ^ 40 * 2965353 * 2
def baseEnd_2965353 : Nat := 1015100932834694517633397

theorem tailTrace_2965353 : CollatzResearch.WordTrace tailWord_2965353 prefixEnd_2965353 1015100932834694517633397 := by
  unfold tailWord_2965353
  simp only [CollatzResearch.WordTrace]
  refine ⟨108155309226039997817604713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72103539484026665211736475 108155309226039997817604713)
  ·
    refine ⟨81116481919529998363203535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108155309226039997817604713 81116481919529998363203535)
    ·
      refine ⟨121674722879294997544805303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81116481919529998363203535 121674722879294997544805303)
      ·
        refine ⟨182512084318942496317207955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121674722879294997544805303 182512084318942496317207955)
        ·
          refine ⟨273768126478413744475811933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182512084318942496317207955 273768126478413744475811933)
          ·
            refine ⟨102663047429405154178429475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 273768126478413744475811933 102663047429405154178429475)
            ·
              refine ⟨153994571144107731267644213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102663047429405154178429475 153994571144107731267644213)
              ·
                refine ⟨14436991044760099806341645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 153994571144107731267644213 14436991044760099806341645)
                ·
                  refine ⟨5413871641785037427378117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14436991044760099806341645 5413871641785037427378117)
                  ·
                    refine ⟨1015100932834694517633397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5413871641785037427378117 1015100932834694517633397)
                    ·
                      rfl

theorem cell22_2965353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 5, 3, 4].length) (baseStart_2965353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2965353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2965353 prefixEnd_2965353 := by exact prefixLift 2965353
  have htrace : WordTrace (prefixWord ++ tailWord_2965353) baseStart_2965353 baseEnd_2965353 := by
    simpa [prefixWord, tailWord_2965353, baseEnd_2965353] using wordTrace_append hprefix tailTrace_2965353
  have hstable : (prefixWord ++ tailWord_2965353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2965353).length < 2 ^ (prefixWord ++ tailWord_2965353).sum := by decide
  have hdescent : baseEnd_2965353 < baseStart_2965353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2965353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2965370 : List Nat := [3, 1, 1, 1, 1, 1, 6, 3, 1, 4]
def baseStart_2965370 : Nat := 118140960795 + 2965370 * 2 ^ 59
def prefixEnd_2965370 : Nat := 4983230072969 + 3 ^ 40 * 2965370 * 2
def baseEnd_2965370 : Nat := 1015106752282112139958345

theorem tailTrace_2965370 : CollatzResearch.WordTrace tailWord_2965370 prefixEnd_2965370 1015106752282112139958345 := by
  unfold tailWord_2965370
  simp only [CollatzResearch.WordTrace]
  refine ⟨27038982316744602430243391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72103952844652273147315709 27038982316744602430243391)
  ·
    refine ⟨40558473475116903645365087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27038982316744602430243391 40558473475116903645365087)
    ·
      refine ⟨60837710212675355468047631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40558473475116903645365087 60837710212675355468047631)
      ·
        refine ⟨91256565319013033202071447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60837710212675355468047631 91256565319013033202071447)
        ·
          refine ⟨136884847978519549803107171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91256565319013033202071447 136884847978519549803107171)
          ·
            refine ⟨205327271967779324704660757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136884847978519549803107171 205327271967779324704660757)
            ·
              refine ⟨9624715873489655845530973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 205327271967779324704660757 9624715873489655845530973)
              ·
                refine ⟨3609268452558620942074115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9624715873489655845530973 3609268452558620942074115)
                ·
                  refine ⟨5413902678837931413111173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3609268452558620942074115 5413902678837931413111173)
                  ·
                    refine ⟨1015106752282112139958345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5413902678837931413111173 1015106752282112139958345)
                    ·
                      rfl

theorem cell22_2965370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 3, 1, 4].length) (baseStart_2965370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2965370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2965370 prefixEnd_2965370 := by exact prefixLift 2965370
  have htrace : WordTrace (prefixWord ++ tailWord_2965370) baseStart_2965370 baseEnd_2965370 := by
    simpa [prefixWord, tailWord_2965370, baseEnd_2965370] using wordTrace_append hprefix tailTrace_2965370
  have hstable : (prefixWord ++ tailWord_2965370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2965370).length < 2 ^ (prefixWord ++ tailWord_2965370).sum := by decide
  have hdescent : baseEnd_2965370 < baseStart_2965370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2965370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2965404 : List Nat := [2, 2, 3, 3, 1, 3, 1, 2, 1, 4]
def baseStart_2965404 : Nat := 118140960795 + 2965404 * 2 ^ 59
def prefixEnd_2965404 : Nat := 4983230072969 + 3 ^ 40 * 2965404 * 2
def baseEnd_2965404 : Nat := 1015118391176947384608241

theorem tailTrace_2965404 : CollatzResearch.WordTrace tailWord_2965404 prefixEnd_2965404 1015118391176947384608241 := by
  unfold tailWord_2965404
  simp only [CollatzResearch.WordTrace]
  refine ⟨54078584674427616763855633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72104779565903489018474177 54078584674427616763855633)
  ·
    refine ⟨40558938505820712572891725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54078584674427616763855633 40558938505820712572891725)
    ·
      refine ⟨15209601939682767214834397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40558938505820712572891725 15209601939682767214834397)
      ·
        refine ⟨5703600727381037705562899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15209601939682767214834397 5703600727381037705562899)
        ·
          refine ⟨8555401091071556558344349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5703600727381037705562899 8555401091071556558344349)
          ·
            refine ⟨3208275409151833709379131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8555401091071556558344349 3208275409151833709379131)
            ·
              refine ⟨4812413113727750564068697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3208275409151833709379131 4812413113727750564068697)
              ·
                refine ⟨3609309835295812923051523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4812413113727750564068697 3609309835295812923051523)
                ·
                  refine ⟨5413964752943719384577285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3609309835295812923051523 5413964752943719384577285)
                  ·
                    refine ⟨1015118391176947384608241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5413964752943719384577285 1015118391176947384608241)
                    ·
                      rfl

theorem cell22_2965404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 2, 1, 4].length) (baseStart_2965404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2965404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2965404 prefixEnd_2965404 := by exact prefixLift 2965404
  have htrace : WordTrace (prefixWord ++ tailWord_2965404) baseStart_2965404 baseEnd_2965404 := by
    simpa [prefixWord, tailWord_2965404, baseEnd_2965404] using wordTrace_append hprefix tailTrace_2965404
  have hstable : (prefixWord ++ tailWord_2965404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2965404).length < 2 ^ (prefixWord ++ tailWord_2965404).sum := by decide
  have hdescent : baseEnd_2965404 < baseStart_2965404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2965404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2965460 : List Nat := [2, 4, 1, 2, 1, 1, 1, 2, 2, 6]
def baseStart_2965460 : Nat := 118140960795 + 2965460 * 2 ^ 59
def prefixEnd_2965460 : Nat := 4983230072969 + 3 ^ 40 * 2965460 * 2
def baseEnd_2965460 : Nat := 1015137561121381905208069

theorem tailTrace_2965460 : CollatzResearch.WordTrace tailWord_2965460 prefixEnd_2965460 1015137561121381905208069 := by
  unfold tailWord_2965460
  simp only [CollatzResearch.WordTrace]
  refine ⟨54079605918326177545874917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72106141224434903394499889 54079605918326177545874917)
  ·
    refine ⟨10139926109686158289851547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54079605918326177545874917 10139926109686158289851547)
    ·
      refine ⟨15209889164529237434777321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10139926109686158289851547 15209889164529237434777321)
      ·
        refine ⟨11407416873396928076082991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15209889164529237434777321 11407416873396928076082991)
        ·
          refine ⟨17111125310095392114124487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11407416873396928076082991 17111125310095392114124487)
          ·
            refine ⟨25666687965143088171186731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17111125310095392114124487 25666687965143088171186731)
            ·
              refine ⟨38500031947714632256780097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25666687965143088171186731 38500031947714632256780097)
              ·
                refine ⟨28875023960785974192585073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38500031947714632256780097 28875023960785974192585073)
                ·
                  refine ⟨21656267970589480644438805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28875023960785974192585073 21656267970589480644438805)
                  ·
                    refine ⟨1015137561121381905208069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21656267970589480644438805 1015137561121381905208069)
                    ·
                      rfl

theorem cell22_2965460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_2965460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2965460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2965460 prefixEnd_2965460 := by exact prefixLift 2965460
  have htrace : WordTrace (prefixWord ++ tailWord_2965460) baseStart_2965460 baseEnd_2965460 := by
    simpa [prefixWord, tailWord_2965460, baseEnd_2965460] using wordTrace_append hprefix tailTrace_2965460
  have hstable : (prefixWord ++ tailWord_2965460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2965460).length < 2 ^ (prefixWord ++ tailWord_2965460).sum := by decide
  have hdescent : baseEnd_2965460 < baseStart_2965460 := by decide
  rcases family_descends (prefixWord ++ tailWord_2965460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2965535 : List Nat := [1, 1, 2, 4, 1, 2, 2, 1, 3, 5]
def baseStart_2965535 : Nat := 118140960795 + 2965535 * 2 ^ 59
def prefixEnd_2965535 : Nat := 4983230072969 + 3 ^ 40 * 2965535 * 2
def baseEnd_2965535 : Nat := 1015163235154106709582839

theorem tailTrace_2965535 : CollatzResearch.WordTrace tailWord_2965535 prefixEnd_2965535 1015163235154106709582839 := by
  unfold tailWord_2965535
  simp only [CollatzResearch.WordTrace]
  refine ⟨108161947311380642900730059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72107964874253761933820039 108161947311380642900730059)
  ·
    refine ⟨162242920967070964351095089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108161947311380642900730059 162242920967070964351095089)
    ·
      refine ⟨121682190725303223263321317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162242920967070964351095089 121682190725303223263321317)
      ·
        refine ⟨22815410760994354361872747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 121682190725303223263321317 22815410760994354361872747)
        ·
          refine ⟨34223116141491531542809121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22815410760994354361872747 34223116141491531542809121)
          ·
            refine ⟨25667337106118648657106841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34223116141491531542809121 25667337106118648657106841)
            ·
              refine ⟨19250502829588986492830131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25667337106118648657106841 19250502829588986492830131)
              ·
                refine ⟨28875754244383479739245197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19250502829588986492830131 28875754244383479739245197)
                ·
                  refine ⟨10828407841643804902216949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28875754244383479739245197 10828407841643804902216949)
                  ·
                    refine ⟨1015163235154106709582839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10828407841643804902216949 1015163235154106709582839)
                    ·
                      rfl

theorem cell22_2965535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 3, 5].length) (baseStart_2965535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2965535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2965535 prefixEnd_2965535 := by exact prefixLift 2965535
  have htrace : WordTrace (prefixWord ++ tailWord_2965535) baseStart_2965535 baseEnd_2965535 := by
    simpa [prefixWord, tailWord_2965535, baseEnd_2965535] using wordTrace_append hprefix tailTrace_2965535
  have hstable : (prefixWord ++ tailWord_2965535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2965535).length < 2 ^ (prefixWord ++ tailWord_2965535).sum := by decide
  have hdescent : baseEnd_2965535 < baseStart_2965535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2965535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2965552 : List Nat := [2, 1, 1, 1, 2, 5, 2, 1, 4, 3]
def baseStart_2965552 : Nat := 118140960795 + 2965552 * 2 ^ 59
def prefixEnd_2965552 : Nat := 4983230072969 + 3 ^ 40 * 2965552 * 2
def baseEnd_2965552 : Nat := 1015169054601524331907787

theorem tailTrace_2965552 : CollatzResearch.WordTrace tailWord_2965552 prefixEnd_2965552 1015169054601524331907787 := by
  unfold tailWord_2965552
  simp only [CollatzResearch.WordTrace]
  refine ⟨54081283676159527402049455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72108378234879369869399273 54081283676159527402049455)
  ·
    refine ⟨81121925514239291103074183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54081283676159527402049455 81121925514239291103074183)
    ·
      refine ⟨121682888271358936654611275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81121925514239291103074183 121682888271358936654611275)
      ·
        refine ⟨182524332407038404981916913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121682888271358936654611275 182524332407038404981916913)
        ·
          refine ⟨136893249305278803736437685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182524332407038404981916913 136893249305278803736437685)
          ·
            refine ⟨12833742122369887850291033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 136893249305278803736437685 12833742122369887850291033)
            ·
              refine ⟨9625306591777415887718275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12833742122369887850291033 9625306591777415887718275)
              ·
                refine ⟨14437959887666123831577413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9625306591777415887718275 14437959887666123831577413)
                ·
                  refine ⟨2707117478937398218420765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14437959887666123831577413 2707117478937398218420765)
                  ·
                    refine ⟨1015169054601524331907787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2707117478937398218420765 1015169054601524331907787)
                    ·
                      rfl

theorem cell22_2965552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 1, 4, 3].length) (baseStart_2965552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2965552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2965552 prefixEnd_2965552 := by exact prefixLift 2965552
  have htrace : WordTrace (prefixWord ++ tailWord_2965552) baseStart_2965552 baseEnd_2965552 := by
    simpa [prefixWord, tailWord_2965552, baseEnd_2965552] using wordTrace_append hprefix tailTrace_2965552
  have hstable : (prefixWord ++ tailWord_2965552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2965552).length < 2 ^ (prefixWord ++ tailWord_2965552).sum := by decide
  have hdescent : baseEnd_2965552 < baseStart_2965552 := by decide
  rcases family_descends (prefixWord ++ tailWord_2965552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2965580 : List Nat := [2, 2, 1, 3, 1, 1, 2, 1, 2, 7]
def baseStart_2965580 : Nat := 118140960795 + 2965580 * 2 ^ 59
def prefixEnd_2965580 : Nat := 4983230072969 + 3 ^ 40 * 2965580 * 2
def baseEnd_2965580 : Nat := 1015178639573741592207701

theorem tailTrace_2965580 : CollatzResearch.WordTrace tailWord_2965580 prefixEnd_2965580 1015178639573741592207701 := by
  unfold tailWord_2965580
  simp only [CollatzResearch.WordTrace]
  refine ⟨54081794298108807793059097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72109059064145077057412129 54081794298108807793059097)
  ·
    refine ⟨40561345723581605844794323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54081794298108807793059097 40561345723581605844794323)
    ·
      refine ⟨60842018585372408767191485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40561345723581605844794323 60842018585372408767191485)
      ·
        refine ⟨22815756969514653287696807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60842018585372408767191485 22815756969514653287696807)
        ·
          refine ⟨34223635454271979931545211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22815756969514653287696807 34223635454271979931545211)
          ·
            refine ⟨51335453181407969897317817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34223635454271979931545211 51335453181407969897317817)
            ·
              refine ⟨38501589886055977422988363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51335453181407969897317817 38501589886055977422988363)
              ·
                refine ⟨57752384829083966134482545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38501589886055977422988363 57752384829083966134482545)
                ·
                  refine ⟨43314288621812974600861909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57752384829083966134482545 43314288621812974600861909)
                  ·
                    refine ⟨1015178639573741592207701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43314288621812974600861909 1015178639573741592207701)
                    ·
                      rfl

theorem cell22_2965580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 2, 7].length) (baseStart_2965580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2965580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2965580 prefixEnd_2965580 := by exact prefixLift 2965580
  have htrace : WordTrace (prefixWord ++ tailWord_2965580) baseStart_2965580 baseEnd_2965580 := by
    simpa [prefixWord, tailWord_2965580, baseEnd_2965580] using wordTrace_append hprefix tailTrace_2965580
  have hstable : (prefixWord ++ tailWord_2965580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2965580).length < 2 ^ (prefixWord ++ tailWord_2965580).sum := by decide
  have hdescent : baseEnd_2965580 < baseStart_2965580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2965580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2965614 : List Nat := [4, 1, 2, 2, 1, 1, 2, 3, 3, 3]
def baseStart_2965614 : Nat := 118140960795 + 2965614 * 2 ^ 59
def prefixEnd_2965614 : Nat := 4983230072969 + 3 ^ 40 * 2965614 * 2
def baseEnd_2965614 : Nat := 1015190278468576836857597

theorem tailTrace_2965614 : CollatzResearch.WordTrace tailWord_2965614 prefixEnd_2965614 1015190278468576836857597 := by
  unfold tailWord_2965614
  simp only [CollatzResearch.WordTrace]
  refine ⟨13520603584761804924106987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72109885785396292928570597 13520603584761804924106987)
  ·
    refine ⟨20280905377142707386160481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13520603584761804924106987 20280905377142707386160481)
    ·
      refine ⟨15210679032857030539620361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20280905377142707386160481 15210679032857030539620361)
      ·
        refine ⟨11408009274642772904715271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15210679032857030539620361 11408009274642772904715271)
        ·
          refine ⟨17112013911964159357072907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11408009274642772904715271 17112013911964159357072907)
          ·
            refine ⟨25668020867946239035609361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17112013911964159357072907 25668020867946239035609361)
            ·
              refine ⟨19251015650959679276707021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25668020867946239035609361 19251015650959679276707021)
              ·
                refine ⟨7219130869109879728765133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19251015650959679276707021 7219130869109879728765133)
                ·
                  refine ⟨2707174075916204898286925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7219130869109879728765133 2707174075916204898286925)
                  ·
                    refine ⟨1015190278468576836857597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2707174075916204898286925 1015190278468576836857597)
                    ·
                      rfl

theorem cell22_2965614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 3, 3, 3].length) (baseStart_2965614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2965614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2965614 prefixEnd_2965614 := by exact prefixLift 2965614
  have htrace : WordTrace (prefixWord ++ tailWord_2965614) baseStart_2965614 baseEnd_2965614 := by
    simpa [prefixWord, tailWord_2965614, baseEnd_2965614] using wordTrace_append hprefix tailTrace_2965614
  have hstable : (prefixWord ++ tailWord_2965614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2965614).length < 2 ^ (prefixWord ++ tailWord_2965614).sum := by decide
  have hdescent : baseEnd_2965614 < baseStart_2965614 := by decide
  rcases family_descends (prefixWord ++ tailWord_2965614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2965654 : List Nat := [5, 3, 2, 1, 1, 2, 1, 2, 2, 3]
def baseStart_2965654 : Nat := 118140960795 + 2965654 * 2 ^ 59
def prefixEnd_2965654 : Nat := 4983230072969 + 3 ^ 40 * 2965654 * 2
def baseEnd_2965654 : Nat := 1015203971286030065857475

theorem tailTrace_2965654 : CollatzResearch.WordTrace tailWord_2965654 prefixEnd_2965654 1015203971286030065857475 := by
  unfold tailWord_2965654
  simp only [CollatzResearch.WordTrace]
  refine ⟨6760392974871845389019501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72110858398633017482874677 6760392974871845389019501)
  ·
    refine ⟨2535147365576942020882313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6760392974871845389019501 2535147365576942020882313)
    ·
      refine ⟨1901360524182706515661735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2535147365576942020882313 1901360524182706515661735)
      ·
        refine ⟨2852040786274059773492603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1901360524182706515661735 2852040786274059773492603)
        ·
          refine ⟨4278061179411089660238905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2852040786274059773492603 4278061179411089660238905)
          ·
            refine ⟨3208545884558317245179179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4278061179411089660238905 3208545884558317245179179)
            ·
              refine ⟨4812818826837475867768769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3208545884558317245179179 4812818826837475867768769)
              ·
                refine ⟨3609614120128106900826577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4812818826837475867768769 3609614120128106900826577)
                ·
                  refine ⟨2707210590096080175619933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3609614120128106900826577 2707210590096080175619933)
                  ·
                    refine ⟨1015203971286030065857475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2707210590096080175619933 1015203971286030065857475)
                    ·
                      rfl

theorem cell22_2965654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_2965654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2965654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2965654 prefixEnd_2965654 := by exact prefixLift 2965654
  have htrace : WordTrace (prefixWord ++ tailWord_2965654) baseStart_2965654 baseEnd_2965654 := by
    simpa [prefixWord, tailWord_2965654, baseEnd_2965654] using wordTrace_append hprefix tailTrace_2965654
  have hstable : (prefixWord ++ tailWord_2965654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2965654).length < 2 ^ (prefixWord ++ tailWord_2965654).sum := by decide
  have hdescent : baseEnd_2965654 < baseStart_2965654 := by decide
  rcases family_descends (prefixWord ++ tailWord_2965654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2965783 : List Nat := [1, 1, 3, 4, 1, 3, 1, 4, 1, 3]
def baseStart_2965783 : Nat := 118140960795 + 2965783 * 2 ^ 59
def prefixEnd_2965783 : Nat := 4983230072969 + 3 ^ 40 * 2965783 * 2
def baseEnd_2965783 : Nat := 1015248130622316729382079

theorem tailTrace_2965783 : CollatzResearch.WordTrace tailWord_2965783 prefixEnd_2965783 1015248130622316729382079 := by
  unfold tailWord_2965783
  simp only [CollatzResearch.WordTrace]
  refine ⟨108170992614482181255758003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72113995076321454170505335 108170992614482181255758003)
  ·
    refine ⟨162256488921723271883637005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108170992614482181255758003 162256488921723271883637005)
    ·
      refine ⟨60846183345646226956363877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162256488921723271883637005 60846183345646226956363877)
      ·
        refine ⟨11408659377308667554318227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60846183345646226956363877 11408659377308667554318227)
        ·
          refine ⟨17112989065963001331477341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11408659377308667554318227 17112989065963001331477341)
          ·
            refine ⟨6417370899736125499304003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17112989065963001331477341 6417370899736125499304003)
            ·
              refine ⟨9626056349604188248956005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6417370899736125499304003 9626056349604188248956005)
              ·
                refine ⟨1804885565550785296679251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9626056349604188248956005 1804885565550785296679251)
                ·
                  refine ⟨2707328348326177945018877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1804885565550785296679251 2707328348326177945018877)
                  ·
                    refine ⟨1015248130622316729382079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2707328348326177945018877 1015248130622316729382079)
                    ·
                      rfl

theorem cell22_2965783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 4, 1, 3].length) (baseStart_2965783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2965783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2965783 prefixEnd_2965783 := by exact prefixLift 2965783
  have htrace : WordTrace (prefixWord ++ tailWord_2965783) baseStart_2965783 baseEnd_2965783 := by
    simpa [prefixWord, tailWord_2965783, baseEnd_2965783] using wordTrace_append hprefix tailTrace_2965783
  have hstable : (prefixWord ++ tailWord_2965783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2965783).length < 2 ^ (prefixWord ++ tailWord_2965783).sum := by decide
  have hdescent : baseEnd_2965783 < baseStart_2965783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2965783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2965794 : List Nat := [3, 3, 1, 1, 3, 1, 1, 1, 1, 7]
def baseStart_2965794 : Nat := 118140960795 + 2965794 * 2 ^ 59
def prefixEnd_2965794 : Nat := 4983230072969 + 3 ^ 40 * 2965794 * 2
def baseEnd_2965794 : Nat := 1015251896147116367357045

theorem tailTrace_2965794 : CollatzResearch.WordTrace tailWord_2965794 prefixEnd_2965794 1015251896147116367357045 := by
  unfold tailWord_2965794
  simp only [CollatzResearch.WordTrace]
  refine ⟨27042848454360582533602109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72114262544961553422938957 27042848454360582533602109)
  ·
    refine ⟨10141068170385218450100791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27042848454360582533602109 10141068170385218450100791)
    ·
      refine ⟨15211602255577827675151187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10141068170385218450100791 15211602255577827675151187)
      ·
        refine ⟨22817403383366741512726781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15211602255577827675151187 22817403383366741512726781)
        ·
          refine ⟨8556526268762528067272543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22817403383366741512726781 8556526268762528067272543)
          ·
            refine ⟨12834789403143792100908815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8556526268762528067272543 12834789403143792100908815)
            ·
              refine ⟨19252184104715688151363223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12834789403143792100908815 19252184104715688151363223)
              ·
                refine ⟨28878276157073532227044835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19252184104715688151363223 28878276157073532227044835)
                ·
                  refine ⟨43317414235610298340567253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28878276157073532227044835 43317414235610298340567253)
                  ·
                    refine ⟨1015251896147116367357045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43317414235610298340567253 1015251896147116367357045)
                    ·
                      rfl

theorem cell22_2965794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_2965794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2965794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2965794 prefixEnd_2965794 := by exact prefixLift 2965794
  have htrace : WordTrace (prefixWord ++ tailWord_2965794) baseStart_2965794 baseEnd_2965794 := by
    simpa [prefixWord, tailWord_2965794, baseEnd_2965794] using wordTrace_append hprefix tailTrace_2965794
  have hstable : (prefixWord ++ tailWord_2965794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2965794).length < 2 ^ (prefixWord ++ tailWord_2965794).sum := by decide
  have hdescent : baseEnd_2965794 < baseStart_2965794 := by decide
  rcases family_descends (prefixWord ++ tailWord_2965794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2965807 : List Nat := [1, 1, 2, 1, 2, 1, 5, 1, 8]
def baseStart_2965807 : Nat := 118140960795 + 2965807 * 2 ^ 59
def prefixEnd_2965807 : Nat := 4983230072969 + 3 ^ 40 * 2965807 * 2
def baseEnd_2965807 : Nat := 338418782104262888927335

theorem tailTrace_2965807 : CollatzResearch.WordTrace tailWord_2965807 prefixEnd_2965807 338418782104262888927335 := by
  unfold tailWord_2965807
  simp only [CollatzResearch.WordTrace]
  refine ⟨108171867966395233354631675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72114578644263488903087783 108171867966395233354631675)
  ·
    refine ⟨162257801949592850031947513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108171867966395233354631675 162257801949592850031947513)
    ·
      refine ⟨121693351462194637523960635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162257801949592850031947513 121693351462194637523960635)
      ·
        refine ⟨182540027193291956285940953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121693351462194637523960635 182540027193291956285940953)
        ·
          refine ⟨136905020394968967214455715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182540027193291956285940953 136905020394968967214455715)
          ·
            refine ⟨205357530592453450821683573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136905020394968967214455715 205357530592453450821683573)
            ·
              refine ⟨19252268493042511014532835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 205357530592453450821683573 19252268493042511014532835)
              ·
                refine ⟨28878402739563766521799253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19252268493042511014532835 28878402739563766521799253)
                ·
                  refine ⟨338418782104262888927335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28878402739563766521799253 338418782104262888927335)
                  ·
                    rfl

theorem cell22_2965807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 8].length) (baseStart_2965807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2965807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2965807 prefixEnd_2965807 := by exact prefixLift 2965807
  have htrace : WordTrace (prefixWord ++ tailWord_2965807) baseStart_2965807 baseEnd_2965807 := by
    simpa [prefixWord, tailWord_2965807, baseEnd_2965807] using wordTrace_append hprefix tailTrace_2965807
  have hstable : (prefixWord ++ tailWord_2965807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2965807).length < 2 ^ (prefixWord ++ tailWord_2965807).sum := by decide
  have hdescent : baseEnd_2965807 < baseStart_2965807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2965807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2965841 : List Nat := [1, 2, 2, 1, 4, 2, 2, 4, 4]
def baseStart_2965841 : Nat := 118140960795 + 2965841 * 2 ^ 59
def prefixEnd_2965841 : Nat := 4983230072969 + 3 ^ 40 * 2965841 * 2
def baseEnd_2965841 : Nat := 338422661735874637143967

theorem tailTrace_2965841 : CollatzResearch.WordTrace tailWord_2965841 prefixEnd_2965841 338422661735874637143967 := by
  unfold tailWord_2965841
  simp only [CollatzResearch.WordTrace]
  refine ⟨108173108048272057161369377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72115405365514704774246251 108173108048272057161369377)
  ·
    refine ⟨81129831036204042871027033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108173108048272057161369377 81129831036204042871027033)
    ·
      refine ⟨60847373277153032153270275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81129831036204042871027033 60847373277153032153270275)
      ·
        refine ⟨91271059915729548229905413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60847373277153032153270275 91271059915729548229905413)
        ·
          refine ⟨17113323734199290293107265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91271059915729548229905413 17113323734199290293107265)
          ·
            refine ⟨12834992800649467719830449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17113323734199290293107265 12834992800649467719830449)
            ·
              refine ⟨9626244600487100789872837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12834992800649467719830449 9626244600487100789872837)
              ·
                refine ⟨1804920862591331398101157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9626244600487100789872837 1804920862591331398101157)
                ·
                  refine ⟨338422661735874637143967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1804920862591331398101157 338422661735874637143967)
                  ·
                    rfl

theorem cell22_2965841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 4, 4].length) (baseStart_2965841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2965841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2965841 prefixEnd_2965841 := by exact prefixLift 2965841
  have htrace : WordTrace (prefixWord ++ tailWord_2965841) baseStart_2965841 baseEnd_2965841 := by
    simpa [prefixWord, tailWord_2965841, baseEnd_2965841] using wordTrace_append hprefix tailTrace_2965841
  have hstable : (prefixWord ++ tailWord_2965841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2965841).length < 2 ^ (prefixWord ++ tailWord_2965841).sum := by decide
  have hdescent : baseEnd_2965841 < baseStart_2965841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2965841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2965869 : List Nat := [1, 5, 1, 1, 1, 2, 3, 8]
def baseStart_2965869 : Nat := 118140960795 + 2965869 * 2 ^ 59
def prefixEnd_2965869 : Nat := 4983230072969 + 3 ^ 40 * 2965869 * 2
def baseEnd_2965869 : Nat := 112808618908871241303535

theorem tailTrace_2965869 : CollatzResearch.WordTrace tailWord_2965869 prefixEnd_2965869 112808618908871241303535 := by
  unfold tailWord_2965869
  simp only [CollatzResearch.WordTrace]
  refine ⟨108174129292170617943388661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72116086194780411962259107 108174129292170617943388661)
  ·
    refine ⟨10141324621140995432192687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 108174129292170617943388661 10141324621140995432192687)
    ·
      refine ⟨15211986931711493148289031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10141324621140995432192687 15211986931711493148289031)
      ·
        refine ⟨22817980397567239722433547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15211986931711493148289031 22817980397567239722433547)
        ·
          refine ⟨34226970596350859583650321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22817980397567239722433547 34226970596350859583650321)
          ·
            refine ⟨25670227947263144687737741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34226970596350859583650321 25670227947263144687737741)
            ·
              refine ⟨9626335480223679257901653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25670227947263144687737741 9626335480223679257901653)
              ·
                refine ⟨112808618908871241303535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9626335480223679257901653 112808618908871241303535)
                ·
                  rfl

theorem cell22_2965869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 8].length) (baseStart_2965869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2965869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2965869 prefixEnd_2965869 := by exact prefixLift 2965869
  have htrace : WordTrace (prefixWord ++ tailWord_2965869) baseStart_2965869 baseEnd_2965869 := by
    simpa [prefixWord, tailWord_2965869, baseEnd_2965869] using wordTrace_append hprefix tailTrace_2965869
  have hstable : (prefixWord ++ tailWord_2965869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2965869).length < 2 ^ (prefixWord ++ tailWord_2965869).sum := by decide
  have hdescent : baseEnd_2965869 < baseStart_2965869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2965869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2965948 : List Nat := [2, 2, 2, 4, 1, 2, 2, 2, 5]
def baseStart_2965948 : Nat := 118140960795 + 2965948 * 2 ^ 59
def prefixEnd_2965948 : Nat := 4983230072969 + 3 ^ 40 * 2965948 * 2
def baseEnd_2965948 : Nat := 338434871164770433002191

theorem tailTrace_2965948 : CollatzResearch.WordTrace tailWord_2965948 prefixEnd_2965948 338434871164770433002191 := by
  unfold tailWord_2965948
  simp only [CollatzResearch.WordTrace]
  refine ⟨54088505329442207217757249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72118007105922942957009665 54088505329442207217757249)
  ·
    refine ⟨40566378997081655413317937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54088505329442207217757249 40566378997081655413317937)
    ·
      refine ⟨30424784247811241559988453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40566378997081655413317937 30424784247811241559988453)
      ·
        refine ⟨5704647046464607792497835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30424784247811241559988453 5704647046464607792497835)
        ·
          refine ⟨8556970569696911688746753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5704647046464607792497835 8556970569696911688746753)
          ·
            refine ⟨6417727927272683766560065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8556970569696911688746753 6417727927272683766560065)
            ·
              refine ⟨4813295945454512824920049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6417727927272683766560065 4813295945454512824920049)
              ·
                refine ⟨3609971959090884618690037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4813295945454512824920049 3609971959090884618690037)
                ·
                  refine ⟨338434871164770433002191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3609971959090884618690037 338434871164770433002191)
                  ·
                    rfl

theorem cell22_2965948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 2, 5].length) (baseStart_2965948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2965948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2965948 prefixEnd_2965948 := by exact prefixLift 2965948
  have htrace : WordTrace (prefixWord ++ tailWord_2965948) baseStart_2965948 baseEnd_2965948 := by
    simpa [prefixWord, tailWord_2965948, baseEnd_2965948] using wordTrace_append hprefix tailTrace_2965948
  have hstable : (prefixWord ++ tailWord_2965948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2965948).length < 2 ^ (prefixWord ++ tailWord_2965948).sum := by decide
  have hdescent : baseEnd_2965948 < baseStart_2965948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2965948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2965991 : List Nat := [1, 1, 5, 2, 1, 1, 1, 4, 1, 5]
def baseStart_2965991 : Nat := 118140960795 + 2965991 * 2 ^ 59
def prefixEnd_2965991 : Nat := 4983230072969 + 3 ^ 40 * 2965991 * 2
def baseEnd_2965991 : Nat := 1015319333273073520181441

theorem tailTrace_2965991 : CollatzResearch.WordTrace tailWord_2965991 prefixEnd_2965991 1015319333273073520181441 := by
  unfold tailWord_2965991
  simp only [CollatzResearch.WordTrace]
  refine ⟨108178578997728632779329827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72119052665152421852886551 108178578997728632779329827)
  ·
    refine ⟨162267868496592949168994741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108178578997728632779329827 162267868496592949168994741)
    ·
      refine ⟨15212612671555588984593257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 162267868496592949168994741 15212612671555588984593257)
      ·
        refine ⟨11409459503666691738444943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15212612671555588984593257 11409459503666691738444943)
        ·
          refine ⟨17114189255500037607667415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11409459503666691738444943 17114189255500037607667415)
          ·
            refine ⟨25671283883250056411501123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17114189255500037607667415 25671283883250056411501123)
            ·
              refine ⟨38506925824875084617251685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25671283883250056411501123 38506925824875084617251685)
              ·
                refine ⟨7220048592164078365734691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38506925824875084617251685 7220048592164078365734691)
                ·
                  refine ⟨10830072888246117548602037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7220048592164078365734691 10830072888246117548602037)
                  ·
                    refine ⟨1015319333273073520181441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10830072888246117548602037 1015319333273073520181441)
                    ·
                      rfl

theorem cell22_2965991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_2965991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2965991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2965991 prefixEnd_2965991 := by exact prefixLift 2965991
  have htrace : WordTrace (prefixWord ++ tailWord_2965991) baseStart_2965991 baseEnd_2965991 := by
    simpa [prefixWord, tailWord_2965991, baseEnd_2965991] using wordTrace_append hprefix tailTrace_2965991
  have hstable : (prefixWord ++ tailWord_2965991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2965991).length < 2 ^ (prefixWord ++ tailWord_2965991).sum := by decide
  have hdescent : baseEnd_2965991 < baseStart_2965991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2965991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966055 : List Nat := [1, 1, 7, 2, 1, 2, 8]
def baseStart_2966055 : Nat := 118140960795 + 2966055 * 2 ^ 59
def prefixEnd_2966055 : Nat := 4983230072969 + 3 ^ 40 * 2966055 * 2
def baseEnd_2966055 : Nat := 37605231177074025428935

theorem tailTrace_2966055 : CollatzResearch.WordTrace tailWord_2966055 prefixEnd_2966055 37605231177074025428935 := by
  unfold tailWord_2966055
  simp only [CollatzResearch.WordTrace]
  refine ⟨108180913269496771709659619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72120608846331181139773079 108180913269496771709659619)
  ·
    refine ⟨162271369904245157564489429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108180913269496771709659619 162271369904245157564489429)
    ·
      refine ⟨3803235232130745880417721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 162271369904245157564489429 3803235232130745880417721)
      ·
        refine ⟨2852426424098059410313291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3803235232130745880417721 2852426424098059410313291)
        ·
          refine ⟨4278639636147089115469937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2852426424098059410313291 4278639636147089115469937)
          ·
            refine ⟨3208979727110316836602453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4278639636147089115469937 3208979727110316836602453)
            ·
              refine ⟨37605231177074025428935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3208979727110316836602453 37605231177074025428935)
              ·
                rfl

theorem cell22_2966055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 8].length) (baseStart_2966055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2966055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2966055 prefixEnd_2966055 := by exact prefixLift 2966055
  have htrace : WordTrace (prefixWord ++ tailWord_2966055) baseStart_2966055 baseEnd_2966055 := by
    simpa [prefixWord, tailWord_2966055, baseEnd_2966055] using wordTrace_append hprefix tailTrace_2966055
  have hstable : (prefixWord ++ tailWord_2966055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966055).length < 2 ^ (prefixWord ++ tailWord_2966055).sum := by decide
  have hdescent : baseEnd_2966055 < baseStart_2966055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966061 : List Nat := [1, 5, 4, 1, 1, 1, 3, 2, 4]
def baseStart_2966061 : Nat := 118140960795 + 2966061 * 2 ^ 59
def prefixEnd_2966061 : Nat := 4983230072969 + 3 ^ 40 * 2966061 * 2
def baseEnd_2966061 : Nat := 338447765234538890310409

theorem tailTrace_2966061 : CollatzResearch.WordTrace tailWord_2966061 prefixEnd_2966061 338447765234538890310409 := by
  unfold tailWord_2966061
  simp only [CollatzResearch.WordTrace]
  refine ⟨108181132107475034734378037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72120754738316689822918691 108181132107475034734378037)
  ·
    refine ⟨10141981135075784506347941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 108181132107475034734378037 10141981135075784506347941)
    ·
      refine ⟨1901621462826709594940239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10141981135075784506347941 1901621462826709594940239)
      ·
        refine ⟨2852432194240064392410359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1901621462826709594940239 2852432194240064392410359)
        ·
          refine ⟨4278648291360096588615539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2852432194240064392410359 4278648291360096588615539)
          ·
            refine ⟨6417972437040144882923309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4278648291360096588615539 6417972437040144882923309)
            ·
              refine ⟨2406739663890054331096241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6417972437040144882923309 2406739663890054331096241)
              ·
                refine ⟨1805054747917540748322181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2406739663890054331096241 1805054747917540748322181)
                ·
                  refine ⟨338447765234538890310409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1805054747917540748322181 338447765234538890310409)
                  ·
                    rfl

theorem cell22_2966061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 3, 2, 4].length) (baseStart_2966061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2966061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2966061 prefixEnd_2966061 := by exact prefixLift 2966061
  have htrace : WordTrace (prefixWord ++ tailWord_2966061) baseStart_2966061 baseEnd_2966061 := by
    simpa [prefixWord, tailWord_2966061, baseEnd_2966061] using wordTrace_append hprefix tailTrace_2966061
  have hstable : (prefixWord ++ tailWord_2966061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966061).length < 2 ^ (prefixWord ++ tailWord_2966061).sum := by decide
  have hdescent : baseEnd_2966061 < baseStart_2966061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966066 : List Nat := [3, 2, 1, 1, 2, 1, 4, 1, 7]
def baseStart_2966066 : Nat := 118140960795 + 2966066 * 2 ^ 59
def prefixEnd_2966066 : Nat := 4983230072969 + 3 ^ 40 * 2966066 * 2
def baseEnd_2966066 : Nat := 338448335768599441518737

theorem tailTrace_2966066 : CollatzResearch.WordTrace tailWord_2966066 prefixEnd_2966066 338448335768599441518737 := by
  unfold tailWord_2966066
  simp only [CollatzResearch.WordTrace]
  refine ⟨27045328618114230147077513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72120876314971280392206701 27045328618114230147077513)
  ·
    refine ⟨20283996463585672610308135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27045328618114230147077513 20283996463585672610308135)
    ·
      refine ⟨30425994695378508915462203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20283996463585672610308135 30425994695378508915462203)
      ·
        refine ⟨45638992043067763373193305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30425994695378508915462203 45638992043067763373193305)
        ·
          refine ⟨34229244032300822529894979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45638992043067763373193305 34229244032300822529894979)
          ·
            refine ⟨51343866048451233794842469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34229244032300822529894979 51343866048451233794842469)
            ·
              refine ⟨9626974884084606336532963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51343866048451233794842469 9626974884084606336532963)
              ·
                refine ⟨14440462326126909504799445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9626974884084606336532963 14440462326126909504799445)
                ·
                  refine ⟨338448335768599441518737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14440462326126909504799445 338448335768599441518737)
                  ·
                    rfl

theorem cell22_2966066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 1, 7].length) (baseStart_2966066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2966066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2966066 prefixEnd_2966066 := by exact prefixLift 2966066
  have htrace : WordTrace (prefixWord ++ tailWord_2966066) baseStart_2966066 baseEnd_2966066 := by
    simpa [prefixWord, tailWord_2966066, baseEnd_2966066] using wordTrace_append hprefix tailTrace_2966066
  have hstable : (prefixWord ++ tailWord_2966066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966066).length < 2 ^ (prefixWord ++ tailWord_2966066).sum := by decide
  have hdescent : baseEnd_2966066 < baseStart_2966066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966158 : List Nat := [4, 1, 1, 3, 1, 1, 3, 1, 1, 6]
def baseStart_2966158 : Nat := 118140960795 + 2966158 * 2 ^ 59
def prefixEnd_2966158 : Nat := 4983230072969 + 3 ^ 40 * 2966158 * 2
def baseEnd_2966158 : Nat := 1015376500785940751255929

theorem tailTrace_2966158 : CollatzResearch.WordTrace tailWord_2966158 prefixEnd_2966158 1015376500785940751255929 := by
  unfold tailWord_2966158
  simp only [CollatzResearch.WordTrace]
  refine ⟨13523083748515452537582391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72123113325415746867106085 13523083748515452537582391)
  ·
    refine ⟨20284625622773178806373587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13523083748515452537582391 20284625622773178806373587)
    ·
      refine ⟨30426938434159768209560381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20284625622773178806373587 30426938434159768209560381)
      ·
        refine ⟨11410101912809913078585143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30426938434159768209560381 11410101912809913078585143)
        ·
          refine ⟨17115152869214869617877715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11410101912809913078585143 17115152869214869617877715)
          ·
            refine ⟨25672729303822304426816573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17115152869214869617877715 25672729303822304426816573)
            ·
              refine ⟨9627273488933364160056215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25672729303822304426816573 9627273488933364160056215)
              ·
                refine ⟨14440910233400046240084323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9627273488933364160056215 14440910233400046240084323)
                ·
                  refine ⟨21661365350100069360126485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14440910233400046240084323 21661365350100069360126485)
                  ·
                    refine ⟨1015376500785940751255929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21661365350100069360126485 1015376500785940751255929)
                    ·
                      rfl

theorem cell22_2966158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 1, 1, 6].length) (baseStart_2966158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2966158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2966158 prefixEnd_2966158 := by exact prefixLift 2966158
  have htrace : WordTrace (prefixWord ++ tailWord_2966158) baseStart_2966158 baseEnd_2966158 := by
    simpa [prefixWord, tailWord_2966158, baseEnd_2966158] using wordTrace_append hprefix tailTrace_2966158
  have hstable : (prefixWord ++ tailWord_2966158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966158).length < 2 ^ (prefixWord ++ tailWord_2966158).sum := by decide
  have hdescent : baseEnd_2966158 < baseStart_2966158 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966162 : List Nat := [3, 2, 3, 1, 2, 2, 2, 3, 4]
def baseStart_2966162 : Nat := 118140960795 + 2966162 * 2 ^ 59
def prefixEnd_2966162 : Nat := 4983230072969 + 3 ^ 40 * 2966162 * 2
def baseEnd_2966162 : Nat := 338459290022562024718639

theorem tailTrace_2966162 : CollatzResearch.WordTrace tailWord_2966162 prefixEnd_2966162 338459290022562024718639 := by
  unfold tailWord_2966162
  simp only [CollatzResearch.WordTrace]
  refine ⟨27046203970027282245951185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72123210586739419322536493 27046203970027282245951185)
  ·
    refine ⟨20284652977520461684463389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27046203970027282245951185 20284652977520461684463389)
    ·
      refine ⟨7606744866570173131673771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20284652977520461684463389 7606744866570173131673771)
      ·
        refine ⟨11410117299855259697510657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7606744866570173131673771 11410117299855259697510657)
        ·
          refine ⟨8557587974891444773132993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11410117299855259697510657 8557587974891444773132993)
          ·
            refine ⟨6418190981168583579849745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8557587974891444773132993 6418190981168583579849745)
            ·
              refine ⟨4813643235876437684887309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6418190981168583579849745 4813643235876437684887309)
              ·
                refine ⟨1805116213453664131832741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4813643235876437684887309 1805116213453664131832741)
                ·
                  refine ⟨338459290022562024718639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1805116213453664131832741 338459290022562024718639)
                  ·
                    rfl

theorem cell22_2966162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 3, 4].length) (baseStart_2966162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2966162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2966162 prefixEnd_2966162 := by exact prefixLift 2966162
  have htrace : WordTrace (prefixWord ++ tailWord_2966162) baseStart_2966162 baseEnd_2966162 := by
    simpa [prefixWord, tailWord_2966162, baseEnd_2966162] using wordTrace_append hprefix tailTrace_2966162
  have hstable : (prefixWord ++ tailWord_2966162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966162).length < 2 ^ (prefixWord ++ tailWord_2966162).sum := by decide
  have hdescent : baseEnd_2966162 < baseStart_2966162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966164 : List Nat := [2, 4, 2, 2, 1, 3, 2, 1, 1, 4]
def baseStart_2966164 : Nat := 118140960795 + 2966164 * 2 ^ 59
def prefixEnd_2966164 : Nat := 4983230072969 + 3 ^ 40 * 2966164 * 2
def baseEnd_2966164 : Nat := 1015378554708558735605911

theorem tailTrace_2966164 : CollatzResearch.WordTrace tailWord_2966164 prefixEnd_2966164 1015378554708558735605911 := by
  unfold tailWord_2966164
  simp only [CollatzResearch.WordTrace]
  refine ⟨54092444413050941662688773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72123259217401255550251697 54092444413050941662688773)
  ·
    refine ⟨10142333327447051561754145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54092444413050941662688773 10142333327447051561754145)
    ·
      refine ⟨7606749995585288671315609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10142333327447051561754145 7606749995585288671315609)
      ·
        refine ⟨5705062496688966503486707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7606749995585288671315609 5705062496688966503486707)
        ·
          refine ⟨8557593745033449755230061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5705062496688966503486707 8557593745033449755230061)
          ·
            refine ⟨3209097654387543658211273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8557593745033449755230061 3209097654387543658211273)
            ·
              refine ⟨2406823240790657743658455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3209097654387543658211273 2406823240790657743658455)
              ·
                refine ⟨3610234861185986615487683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2406823240790657743658455 3610234861185986615487683)
                ·
                  refine ⟨5415352291778979923231525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3610234861185986615487683 5415352291778979923231525)
                  ·
                    refine ⟨1015378554708558735605911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5415352291778979923231525 1015378554708558735605911)
                    ·
                      rfl

theorem cell22_2966164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_2966164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2966164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2966164 prefixEnd_2966164 := by exact prefixLift 2966164
  have htrace : WordTrace (prefixWord ++ tailWord_2966164) baseStart_2966164 baseEnd_2966164 := by
    simpa [prefixWord, tailWord_2966164, baseEnd_2966164] using wordTrace_append hprefix tailTrace_2966164
  have hstable : (prefixWord ++ tailWord_2966164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966164).length < 2 ^ (prefixWord ++ tailWord_2966164).sum := by decide
  have hdescent : baseEnd_2966164 < baseStart_2966164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966205 : List Nat := [1, 4, 1, 2, 1, 3, 2, 2, 3, 3]
def baseStart_2966205 : Nat := 118140960795 + 2966205 * 2 ^ 59
def prefixEnd_2966205 : Nat := 4983230072969 + 3 ^ 40 * 2966205 * 2
def baseEnd_2966205 : Nat := 1015392589846448295330785

theorem tailTrace_2966205 : CollatzResearch.WordTrace tailWord_2966205 prefixEnd_2966205 1015392589846448295330785 := by
  unfold tailWord_2966205
  simp only [CollatzResearch.WordTrace]
  refine ⟨108186384218953347327620069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72124256145968898218413379 108186384218953347327620069)
  ·
    refine ⟨20284947041053752623928763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108186384218953347327620069 20284947041053752623928763)
    ·
      refine ⟨30427420561580628935893145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20284947041053752623928763 30427420561580628935893145)
      ·
        refine ⟨22820565421185471701919859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30427420561580628935893145 22820565421185471701919859)
        ·
          refine ⟨34230848131778207552879789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22820565421185471701919859 34230848131778207552879789)
          ·
            refine ⟨12836568049416827832329921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34230848131778207552879789 12836568049416827832329921)
            ·
              refine ⟨9627426037062620874247441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12836568049416827832329921 9627426037062620874247441)
              ·
                refine ⟨7220569527796965655685581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9627426037062620874247441 7220569527796965655685581)
                ·
                  refine ⟨2707713572923862120882093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7220569527796965655685581 2707713572923862120882093)
                  ·
                    refine ⟨1015392589846448295330785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2707713572923862120882093 1015392589846448295330785)
                    ·
                      rfl

theorem cell22_2966205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 2, 3, 3].length) (baseStart_2966205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2966205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2966205 prefixEnd_2966205 := by exact prefixLift 2966205
  have htrace : WordTrace (prefixWord ++ tailWord_2966205) baseStart_2966205 baseEnd_2966205 := by
    simpa [prefixWord, tailWord_2966205, baseEnd_2966205] using wordTrace_append hprefix tailTrace_2966205
  have hstable : (prefixWord ++ tailWord_2966205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966205).length < 2 ^ (prefixWord ++ tailWord_2966205).sum := by decide
  have hdescent : baseEnd_2966205 < baseStart_2966205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966218 : List Nat := [3, 1, 2, 1, 4, 1, 1, 2, 7]
def baseStart_2966218 : Nat := 118140960795 + 2966218 * 2 ^ 59
def prefixEnd_2966218 : Nat := 4983230072969 + 3 ^ 40 * 2966218 * 2
def baseEnd_2966218 : Nat := 338465680004040198251915

theorem tailTrace_2966218 : CollatzResearch.WordTrace tailWord_2966218 prefixEnd_2966218 338465680004040198251915 := by
  unfold tailWord_2966218
  simp only [CollatzResearch.WordTrace]
  refine ⟨27046714591976562636960827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72124572245270833698562205 27046714591976562636960827)
  ·
    refine ⟨40570071887964843955441241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27046714591976562636960827 40570071887964843955441241)
    ·
      refine ⟨30427553915973632966580931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40570071887964843955441241 30427553915973632966580931)
      ·
        refine ⟨45641330873960449449871397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30427553915973632966580931 45641330873960449449871397)
        ·
          refine ⟨8557749538867584271850887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45641330873960449449871397 8557749538867584271850887)
          ·
            refine ⟨12836624308301376407776331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8557749538867584271850887 12836624308301376407776331)
            ·
              refine ⟨19254936462452064611664497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12836624308301376407776331 19254936462452064611664497)
              ·
                refine ⟨14441202346839048458748373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19254936462452064611664497 14441202346839048458748373)
                ·
                  refine ⟨338465680004040198251915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14441202346839048458748373 338465680004040198251915)
                  ·
                    rfl

theorem cell22_2966218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 2, 7].length) (baseStart_2966218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2966218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2966218 prefixEnd_2966218 := by exact prefixLift 2966218
  have htrace : WordTrace (prefixWord ++ tailWord_2966218) baseStart_2966218 baseEnd_2966218 := by
    simpa [prefixWord, tailWord_2966218, baseEnd_2966218] using wordTrace_append hprefix tailTrace_2966218
  have hstable : (prefixWord ++ tailWord_2966218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966218).length < 2 ^ (prefixWord ++ tailWord_2966218).sum := by decide
  have hdescent : baseEnd_2966218 < baseStart_2966218 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966239 : List Nat := [1, 1, 2, 3, 2, 4, 3, 2, 1, 3]
def baseStart_2966239 : Nat := 118140960795 + 2966239 * 2 ^ 59
def prefixEnd_2966239 : Nat := 4983230072969 + 3 ^ 40 * 2966239 * 2
def baseEnd_2966239 : Nat := 1015404228741283539980681

theorem tailTrace_2966239 : CollatzResearch.WordTrace tailWord_2966239 prefixEnd_2966239 1015404228741283539980681 := by
  unfold tailWord_2966239
  simp only [CollatzResearch.WordTrace]
  refine ⟨108187624300830171134357771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72125082867220114089571847 108187624300830171134357771)
  ·
    refine ⟨162281436451245256701536657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108187624300830171134357771 162281436451245256701536657)
    ·
      refine ⟨121711077338433942526152493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162281436451245256701536657 121711077338433942526152493)
      ·
        refine ⟨45641654001912728447307185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121711077338433942526152493 45641654001912728447307185)
        ·
          refine ⟨34231240501434546335480389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45641654001912728447307185 34231240501434546335480389)
          ·
            refine ⟨6418357594018977437902573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34231240501434546335480389 6418357594018977437902573)
            ·
              refine ⟨2406884097757116539213465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6418357594018977437902573 2406884097757116539213465)
              ·
                refine ⟨1805163073317837404410099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2406884097757116539213465 1805163073317837404410099)
                ·
                  refine ⟨2707744609976756106615149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1805163073317837404410099 2707744609976756106615149)
                  ·
                    refine ⟨1015404228741283539980681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2707744609976756106615149 1015404228741283539980681)
                    ·
                      rfl

theorem cell22_2966239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 3, 2, 1, 3].length) (baseStart_2966239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2966239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2966239 prefixEnd_2966239 := by exact prefixLift 2966239
  have htrace : WordTrace (prefixWord ++ tailWord_2966239) baseStart_2966239 baseEnd_2966239 := by
    simpa [prefixWord, tailWord_2966239, baseEnd_2966239] using wordTrace_append hprefix tailTrace_2966239
  have hstable : (prefixWord ++ tailWord_2966239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966239).length < 2 ^ (prefixWord ++ tailWord_2966239).sum := by decide
  have hdescent : baseEnd_2966239 < baseStart_2966239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966282 : List Nat := [3, 1, 2, 2, 1, 2, 5, 1, 1, 4]
def baseStart_2966282 : Nat := 118140960795 + 2966282 * 2 ^ 59
def prefixEnd_2966282 : Nat := 4983230072969 + 3 ^ 40 * 2966282 * 2
def baseEnd_2966282 : Nat := 1015418948520045761155549

theorem tailTrace_2966282 : CollatzResearch.WordTrace tailWord_2966282 prefixEnd_2966282 1015418948520045761155549 := by
  unfold tailWord_2966282
  simp only [CollatzResearch.WordTrace]
  refine ⟨27047298159918597369543275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72126128426449592985448733 27047298159918597369543275)
  ·
    refine ⟨40570947239877896054314913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27047298159918597369543275 40570947239877896054314913)
    ·
      refine ⟨30428210429908422040736185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40570947239877896054314913 30428210429908422040736185)
      ·
        refine ⟨22821157822431316530552139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30428210429908422040736185 22821157822431316530552139)
        ·
          refine ⟨34231736733646974795828209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22821157822431316530552139 34231736733646974795828209)
          ·
            refine ⟨25673802550235231096871157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34231736733646974795828209 25673802550235231096871157)
            ·
              refine ⟨2406918989084552915331671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25673802550235231096871157 2406918989084552915331671)
              ·
                refine ⟨3610378483626829372997507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2406918989084552915331671 3610378483626829372997507)
                ·
                  refine ⟨5415567725440244059496261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3610378483626829372997507 5415567725440244059496261)
                  ·
                    refine ⟨1015418948520045761155549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5415567725440244059496261 1015418948520045761155549)
                    ·
                      rfl

theorem cell22_2966282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 5, 1, 1, 4].length) (baseStart_2966282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2966282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2966282 prefixEnd_2966282 := by exact prefixLift 2966282
  have htrace : WordTrace (prefixWord ++ tailWord_2966282) baseStart_2966282 baseEnd_2966282 := by
    simpa [prefixWord, tailWord_2966282, baseEnd_2966282] using wordTrace_append hprefix tailTrace_2966282
  have hstable : (prefixWord ++ tailWord_2966282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966282).length < 2 ^ (prefixWord ++ tailWord_2966282).sum := by decide
  have hdescent : baseEnd_2966282 < baseStart_2966282 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966290 : List Nat := [3, 2, 4, 1, 3, 1, 2, 2, 1, 3]
def baseStart_2966290 : Nat := 118140960795 + 2966290 * 2 ^ 59
def prefixEnd_2966290 : Nat := 4983230072969 + 3 ^ 40 * 2966290 * 2
def baseEnd_2966290 : Nat := 1015421687083536406955525

theorem tailTrace_2966290 : CollatzResearch.WordTrace tailWord_2966290 prefixEnd_2966290 1015421687083536406955525 := by
  unfold tailWord_2966290
  simp only [CollatzResearch.WordTrace]
  refine ⟨27047371105911351711116081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72126322949096937896309549 27047371105911351711116081)
  ·
    refine ⟨20285528329433513783337061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27047371105911351711116081 20285528329433513783337061)
    ·
      refine ⟨3803536561768783834375699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20285528329433513783337061 3803536561768783834375699)
      ·
        refine ⟨5705304842653175751563549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3803536561768783834375699 5705304842653175751563549)
        ·
          refine ⟨2139489315994940906836331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5705304842653175751563549 2139489315994940906836331)
          ·
            refine ⟨3209233973992411360254497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2139489315994940906836331 3209233973992411360254497)
            ·
              refine ⟨2406925480494308520190873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3209233973992411360254497 2406925480494308520190873)
              ·
                refine ⟨1805194110370731390143155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2406925480494308520190873 1805194110370731390143155)
                ·
                  refine ⟨2707791165556097085214733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1805194110370731390143155 2707791165556097085214733)
                  ·
                    refine ⟨1015421687083536406955525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2707791165556097085214733 1015421687083536406955525)
                    ·
                      rfl

theorem cell22_2966290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_2966290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2966290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2966290 prefixEnd_2966290 := by exact prefixLift 2966290
  have htrace : WordTrace (prefixWord ++ tailWord_2966290) baseStart_2966290 baseEnd_2966290 := by
    simpa [prefixWord, tailWord_2966290, baseEnd_2966290] using wordTrace_append hprefix tailTrace_2966290
  have hstable : (prefixWord ++ tailWord_2966290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966290).length < 2 ^ (prefixWord ++ tailWord_2966290).sum := by decide
  have hdescent : baseEnd_2966290 < baseStart_2966290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966312 : List Nat := [2, 1, 5, 1, 1, 1, 1, 5, 2, 3]
def baseStart_2966312 : Nat := 118140960795 + 2966312 * 2 ^ 59
def prefixEnd_2966312 : Nat := 4983230072969 + 3 ^ 40 * 2966312 * 2
def baseEnd_2966312 : Nat := 1015429218133135682905457

theorem tailTrace_2966312 : CollatzResearch.WordTrace tailWord_2966312 prefixEnd_2966312 1015429218133135682905457 := by
  unfold tailWord_2966312
  simp only [CollatzResearch.WordTrace]
  refine ⟨54095143414782852300882595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72126857886377136401176793 54095143414782852300882595)
  ·
    refine ⟨81142715122174278451323893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54095143414782852300882595 81142715122174278451323893)
    ·
      refine ⟨7607129542703838604811615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 81142715122174278451323893 7607129542703838604811615)
      ·
        refine ⟨11410694314055757907217423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7607129542703838604811615 11410694314055757907217423)
        ·
          refine ⟨17116041471083636860826135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11410694314055757907217423 17116041471083636860826135)
          ·
            refine ⟨25674062206625455291239203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17116041471083636860826135 25674062206625455291239203)
            ·
              refine ⟨38511093309938182936858805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25674062206625455291239203 38511093309938182936858805)
              ·
                refine ⟨3610414997806704650330513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38511093309938182936858805 3610414997806704650330513)
                ·
                  refine ⟨2707811248355028487747885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3610414997806704650330513 2707811248355028487747885)
                  ·
                    refine ⟨1015429218133135682905457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2707811248355028487747885 1015429218133135682905457)
                    ·
                      rfl

theorem cell22_2966312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_2966312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2966312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2966312 prefixEnd_2966312 := by exact prefixLift 2966312
  have htrace : WordTrace (prefixWord ++ tailWord_2966312) baseStart_2966312 baseEnd_2966312 := by
    simpa [prefixWord, tailWord_2966312, baseEnd_2966312] using wordTrace_append hprefix tailTrace_2966312
  have hstable : (prefixWord ++ tailWord_2966312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966312).length < 2 ^ (prefixWord ++ tailWord_2966312).sum := by decide
  have hdescent : baseEnd_2966312 < baseStart_2966312 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966357 : List Nat := [1, 3, 2, 2, 2, 1, 4, 1, 3, 3]
def baseStart_2966357 : Nat := 118140960795 + 2966357 * 2 ^ 59
def prefixEnd_2966357 : Nat := 4983230072969 + 3 ^ 40 * 2966357 * 2
def baseEnd_2966357 : Nat := 1015444622552770565530319

theorem tailTrace_2966357 : CollatzResearch.WordTrace tailWord_2966357 prefixEnd_2966357 1015444622552770565530319 := by
  unfold tailWord_2966357
  simp only [CollatzResearch.WordTrace]
  refine ⟨108191928114402677287153325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72127952076268451524768883 108191928114402677287153325)
  ·
    refine ⟨40571973042901003982682497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108191928114402677287153325 40571973042901003982682497)
    ·
      refine ⟨30428979782175752987011873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40571973042901003982682497 30428979782175752987011873)
      ·
        refine ⟨22821734836631814740258905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30428979782175752987011873 22821734836631814740258905)
        ·
          refine ⟨17116301127473861055194179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22821734836631814740258905 17116301127473861055194179)
          ·
            refine ⟨25674451691210791582791269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17116301127473861055194179 25674451691210791582791269)
            ·
              refine ⟨4813959692102023421773363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25674451691210791582791269 4813959692102023421773363)
              ·
                refine ⟨7220939538153035132660045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4813959692102023421773363 7220939538153035132660045)
                ·
                  refine ⟨2707852326807388174747517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7220939538153035132660045 2707852326807388174747517)
                  ·
                    refine ⟨1015444622552770565530319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2707852326807388174747517 1015444622552770565530319)
                    ·
                      rfl

theorem cell22_2966357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 1, 3, 3].length) (baseStart_2966357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2966357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2966357 prefixEnd_2966357 := by exact prefixLift 2966357
  have htrace : WordTrace (prefixWord ++ tailWord_2966357) baseStart_2966357 baseEnd_2966357 := by
    simpa [prefixWord, tailWord_2966357, baseEnd_2966357] using wordTrace_append hprefix tailTrace_2966357
  have hstable : (prefixWord ++ tailWord_2966357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966357).length < 2 ^ (prefixWord ++ tailWord_2966357).sum := by decide
  have hdescent : baseEnd_2966357 < baseStart_2966357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966383 : List Nat := [1, 1, 2, 1, 3, 1, 1, 2, 2, 8]
def baseStart_2966383 : Nat := 118140960795 + 2966383 * 2 ^ 59
def prefixEnd_2966383 : Nat := 4983230072969 + 3 ^ 40 * 2966383 * 2
def baseEnd_2966383 : Nat := 1015453522884115164380239

theorem tailTrace_2966383 : CollatzResearch.WordTrace tailWord_2966383 prefixEnd_2966383 1015453522884115164380239 := by
  unfold tailWord_2966383
  simp only [CollatzResearch.WordTrace]
  refine ⟨108192876412308483727599803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72128584274872322485066535 108192876412308483727599803)
  ·
    refine ⟨162289314618462725591399705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108192876412308483727599803 162289314618462725591399705)
    ·
      refine ⟨121716985963847044193549779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162289314618462725591399705 121716985963847044193549779)
      ·
        refine ⟨182575478945770566290324669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121716985963847044193549779 182575478945770566290324669)
        ·
          refine ⟨68465804604663962358871751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 182575478945770566290324669 68465804604663962358871751)
          ·
            refine ⟨102698706906995943538307627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68465804604663962358871751 102698706906995943538307627)
            ·
              refine ⟨154048060360493915307461441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102698706906995943538307627 154048060360493915307461441)
              ·
                refine ⟨115536045270370436480596081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 154048060360493915307461441 115536045270370436480596081)
                ·
                  refine ⟨86652033952777827360447061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115536045270370436480596081 86652033952777827360447061)
                  ·
                    refine ⟨1015453522884115164380239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 86652033952777827360447061 1015453522884115164380239)
                    ·
                      rfl

theorem cell22_2966383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 8].length) (baseStart_2966383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2966383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2966383 prefixEnd_2966383 := by exact prefixLift 2966383
  have htrace : WordTrace (prefixWord ++ tailWord_2966383) baseStart_2966383 baseEnd_2966383 := by
    simpa [prefixWord, tailWord_2966383, baseEnd_2966383] using wordTrace_append hprefix tailTrace_2966383
  have hstable : (prefixWord ++ tailWord_2966383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966383).length < 2 ^ (prefixWord ++ tailWord_2966383).sum := by decide
  have hdescent : baseEnd_2966383 < baseStart_2966383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966434 : List Nat := [3, 3, 1, 2, 2, 1, 3, 2, 1, 4]
def baseStart_2966434 : Nat := 118140960795 + 2966434 * 2 ^ 59
def prefixEnd_2966434 : Nat := 4983230072969 + 3 ^ 40 * 2966434 * 2
def baseEnd_2966434 : Nat := 1015470981226368031355083

theorem tailTrace_2966434 : CollatzResearch.WordTrace tailWord_2966434 prefixEnd_2966434 1015470981226368031355083 := by
  unfold tailWord_2966434
  simp only [CollatzResearch.WordTrace]
  refine ⟨27048684133780929859426589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72129824356749146291804237 27048684133780929859426589)
  ·
    refine ⟨10143256550167848697284971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27048684133780929859426589 10143256550167848697284971)
    ·
      refine ⟨15214884825251773045927457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10143256550167848697284971 15214884825251773045927457)
      ·
        refine ⟨11411163618938829784445593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15214884825251773045927457 11411163618938829784445593)
        ·
          refine ⟨8558372714204122338334195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11411163618938829784445593 8558372714204122338334195)
          ·
            refine ⟨12837559071306183507501293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8558372714204122338334195 12837559071306183507501293)
            ·
              refine ⟨4814084651739818815312985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12837559071306183507501293 4814084651739818815312985)
              ·
                refine ⟨3610563488804864111484739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4814084651739818815312985 3610563488804864111484739)
                ·
                  refine ⟨5415845233207296167227109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3610563488804864111484739 5415845233207296167227109)
                  ·
                    refine ⟨1015470981226368031355083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5415845233207296167227109 1015470981226368031355083)
                    ·
                      rfl

theorem cell22_2966434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_2966434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2966434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2966434 prefixEnd_2966434 := by exact prefixLift 2966434
  have htrace : WordTrace (prefixWord ++ tailWord_2966434) baseStart_2966434 baseEnd_2966434 := by
    simpa [prefixWord, tailWord_2966434, baseEnd_2966434] using wordTrace_append hprefix tailTrace_2966434
  have hstable : (prefixWord ++ tailWord_2966434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966434).length < 2 ^ (prefixWord ++ tailWord_2966434).sum := by decide
  have hdescent : baseEnd_2966434 < baseStart_2966434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966462 : List Nat := [4, 2, 1, 1, 1, 2, 1, 4, 2, 4]
def baseStart_2966462 : Nat := 118140960795 + 2966462 * 2 ^ 59
def prefixEnd_2966462 : Nat := 4983230072969 + 3 ^ 40 * 2966462 * 2
def baseEnd_2966462 : Nat := 1015480566198585291654997

theorem tailTrace_2966462 : CollatzResearch.WordTrace tailWord_2966462 prefixEnd_2966462 1015480566198585291654997 := by
  unfold tailWord_2966462
  simp only [CollatzResearch.WordTrace]
  refine ⟨13524469722377785027465705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72130505186014853479817093 13524469722377785027465705)
  ·
    refine ⟨10143352291783338770599279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13524469722377785027465705 10143352291783338770599279)
    ·
      refine ⟨15215028437675008155898919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10143352291783338770599279 15215028437675008155898919)
      ·
        refine ⟨22822542656512512233848379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15215028437675008155898919 22822542656512512233848379)
        ·
          refine ⟨34233813984768768350772569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22822542656512512233848379 34233813984768768350772569)
          ·
            refine ⟨25675360488576576263079427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34233813984768768350772569 25675360488576576263079427)
            ·
              refine ⟨38513040732864864394619141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25675360488576576263079427 38513040732864864394619141)
              ·
                refine ⟨7221195137412162073991089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38513040732864864394619141 7221195137412162073991089)
                ·
                  refine ⟨5415896353059121555493317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7221195137412162073991089 5415896353059121555493317)
                  ·
                    refine ⟨1015480566198585291654997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5415896353059121555493317 1015480566198585291654997)
                    ·
                      rfl

theorem cell22_2966462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_2966462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2966462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2966462 prefixEnd_2966462 := by exact prefixLift 2966462
  have htrace : WordTrace (prefixWord ++ tailWord_2966462) baseStart_2966462 baseEnd_2966462 := by
    simpa [prefixWord, tailWord_2966462, baseEnd_2966462] using wordTrace_append hprefix tailTrace_2966462
  have hstable : (prefixWord ++ tailWord_2966462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966462).length < 2 ^ (prefixWord ++ tailWord_2966462).sum := by decide
  have hdescent : baseEnd_2966462 < baseStart_2966462 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966464 : List Nat := [2, 1, 1, 2, 3, 4, 2, 2, 2, 3]
def baseStart_2966464 : Nat := 118140960795 + 2966464 * 2 ^ 59
def prefixEnd_2966464 : Nat := 4983230072969 + 3 ^ 40 * 2966464 * 2
def baseEnd_2966464 : Nat := 1015481250839457953104991

theorem tailTrace_2966464 : CollatzResearch.WordTrace tailWord_2966464 prefixEnd_2966464 1015481250839457953104991 := by
  unfold tailWord_2966464
  simp only [CollatzResearch.WordTrace]
  refine ⟨54097915362507517280649223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72130553816676689707532297 54097915362507517280649223)
  ·
    refine ⟨81146873043761275920973835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54097915362507517280649223 81146873043761275920973835)
    ·
      refine ⟨121720309565641913881460753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81146873043761275920973835 121720309565641913881460753)
      ·
        refine ⟨91290232174231435411095565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121720309565641913881460753 91290232174231435411095565)
        ·
          refine ⟨34233837065336788279160837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91290232174231435411095565 34233837065336788279160837)
          ·
            refine ⟨6418844449750647802342657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34233837065336788279160837 6418844449750647802342657)
            ·
              refine ⟨4814133337312985851756993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6418844449750647802342657 4814133337312985851756993)
              ·
                refine ⟨3610600002984739388817745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4814133337312985851756993 3610600002984739388817745)
                ·
                  refine ⟨2707950002238554541613309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3610600002984739388817745 2707950002238554541613309)
                  ·
                    refine ⟨1015481250839457953104991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2707950002238554541613309 1015481250839457953104991)
                    ·
                      rfl

theorem cell22_2966464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 2, 2, 3].length) (baseStart_2966464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2966464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2966464 prefixEnd_2966464 := by exact prefixLift 2966464
  have htrace : WordTrace (prefixWord ++ tailWord_2966464) baseStart_2966464 baseEnd_2966464 := by
    simpa [prefixWord, tailWord_2966464, baseEnd_2966464] using wordTrace_append hprefix tailTrace_2966464
  have hstable : (prefixWord ++ tailWord_2966464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966464).length < 2 ^ (prefixWord ++ tailWord_2966464).sum := by decide
  have hdescent : baseEnd_2966464 < baseStart_2966464 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966539 : List Nat := [1, 1, 1, 1, 6, 3, 3, 1, 5]
def baseStart_2966539 : Nat := 118140960795 + 2966539 * 2 ^ 59
def prefixEnd_2966539 : Nat := 4983230072969 + 3 ^ 40 * 2966539 * 2
def baseEnd_2966539 : Nat := 338502308290727585826587

theorem tailTrace_2966539 : CollatzResearch.WordTrace tailWord_2966539 prefixEnd_2966539 338502308290727585826587 := by
  unfold tailWord_2966539
  simp only [CollatzResearch.WordTrace]
  refine ⟨108198566199743322370278671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72132377466495548246852447 108198566199743322370278671)
  ·
    refine ⟨162297849299614983555418007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108198566199743322370278671 162297849299614983555418007)
    ·
      refine ⟨243446773949422475333127011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162297849299614983555418007 243446773949422475333127011)
      ·
        refine ⟨365170160924133712999690517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243446773949422475333127011 365170160924133712999690517)
        ·
          refine ⟨17117351293318767796860493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 365170160924133712999690517 17117351293318767796860493)
          ·
            refine ⟨6419006734994537923822685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17117351293318767796860493 6419006734994537923822685)
            ·
              refine ⟨2407127525622951721433507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6419006734994537923822685 2407127525622951721433507)
              ·
                refine ⟨3610691288434427582150261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2407127525622951721433507 3610691288434427582150261)
                ·
                  refine ⟨338502308290727585826587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3610691288434427582150261 338502308290727585826587)
                  ·
                    rfl

theorem cell22_2966539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 3, 1, 5].length) (baseStart_2966539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2966539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2966539 prefixEnd_2966539 := by exact prefixLift 2966539
  have htrace : WordTrace (prefixWord ++ tailWord_2966539) baseStart_2966539 baseEnd_2966539 := by
    simpa [prefixWord, tailWord_2966539, baseEnd_2966539] using wordTrace_append hprefix tailTrace_2966539
  have hstable : (prefixWord ++ tailWord_2966539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966539).length < 2 ^ (prefixWord ++ tailWord_2966539).sum := by decide
  have hdescent : baseEnd_2966539 < baseStart_2966539 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966560 : List Nat := [2, 1, 1, 7, 1, 2, 1, 3, 1, 3]
def baseStart_2966560 : Nat := 118140960795 + 2966560 * 2 ^ 59
def prefixEnd_2966560 : Nat := 4983230072969 + 3 ^ 40 * 2966560 * 2
def baseEnd_2966560 : Nat := 1015514113601345702704697

theorem tailTrace_2966560 : CollatzResearch.WordTrace tailWord_2966560 prefixEnd_2966560 1015514113601345702704697 := by
  unfold tailWord_2966560
  simp only [CollatzResearch.WordTrace]
  refine ⟨54099666066333621478396567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72132888088444828637862089 54099666066333621478396567)
  ·
    refine ⟨81149499099500432217594851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54099666066333621478396567 81149499099500432217594851)
    ·
      refine ⟨121724248649250648326392277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81149499099500432217594851 121724248649250648326392277)
      ·
        refine ⟨2852912077716812070149819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 121724248649250648326392277 2852912077716812070149819)
        ·
          refine ⟨4279368116575218105224729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2852912077716812070149819 4279368116575218105224729)
          ·
            refine ⟨3209526087431413578918547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4279368116575218105224729 3209526087431413578918547)
            ·
              refine ⟨4814289131147120368377821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3209526087431413578918547 4814289131147120368377821)
              ·
                refine ⟨1805358424180170138141683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4814289131147120368377821 1805358424180170138141683)
                ·
                  refine ⟨2708037636270255207212525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1805358424180170138141683 2708037636270255207212525)
                  ·
                    refine ⟨1015514113601345702704697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2708037636270255207212525 1015514113601345702704697)
                    ·
                      rfl

theorem cell22_2966560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 3, 1, 3].length) (baseStart_2966560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2966560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2966560 prefixEnd_2966560 := by exact prefixLift 2966560
  have htrace : WordTrace (prefixWord ++ tailWord_2966560) baseStart_2966560 baseEnd_2966560 := by
    simpa [prefixWord, tailWord_2966560, baseEnd_2966560] using wordTrace_append hprefix tailTrace_2966560
  have hstable : (prefixWord ++ tailWord_2966560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966560).length < 2 ^ (prefixWord ++ tailWord_2966560).sum := by decide
  have hdescent : baseEnd_2966560 < baseStart_2966560 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966584 : List Nat := [2, 1, 2, 1, 5, 3, 1, 1, 6]
def baseStart_2966584 : Nat := 118140960795 + 2966584 * 2 ^ 59
def prefixEnd_2966584 : Nat := 4983230072969 + 3 ^ 40 * 2966584 * 2
def baseEnd_2966584 : Nat := 338507443097272546701541

theorem tailTrace_2966584 : CollatzResearch.WordTrace tailWord_2966584 prefixEnd_2966584 338507443097272546701541 := by
  unfold tailWord_2966584
  simp only [CollatzResearch.WordTrace]
  refine ⟨54100103742290147527833403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72133471656386863370444537 54100103742290147527833403)
  ·
    refine ⟨81150155613435221291750105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54100103742290147527833403 81150155613435221291750105)
    ·
      refine ⟨60862616710076415968812579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81150155613435221291750105 60862616710076415968812579)
      ·
        refine ⟨91293925065114623953218869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60862616710076415968812579 91293925065114623953218869)
        ·
          refine ⟨8558805474854495995614269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 91293925065114623953218869 8558805474854495995614269)
          ·
            refine ⟨3209552053070435998355351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8558805474854495995614269 3209552053070435998355351)
            ·
              refine ⟨4814328079605653997533027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3209552053070435998355351 4814328079605653997533027)
              ·
                refine ⟨7221492119408480996299541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4814328079605653997533027 7221492119408480996299541)
                ·
                  refine ⟨338507443097272546701541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7221492119408480996299541 338507443097272546701541)
                  ·
                    rfl

theorem cell22_2966584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 1, 6].length) (baseStart_2966584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2966584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2966584 prefixEnd_2966584 := by exact prefixLift 2966584
  have htrace : WordTrace (prefixWord ++ tailWord_2966584) baseStart_2966584 baseEnd_2966584 := by
    simpa [prefixWord, tailWord_2966584, baseEnd_2966584] using wordTrace_append hprefix tailTrace_2966584
  have hstable : (prefixWord ++ tailWord_2966584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966584).length < 2 ^ (prefixWord ++ tailWord_2966584).sum := by decide
  have hdescent : baseEnd_2966584 < baseStart_2966584 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966612 : List Nat := [2, 4, 1, 1, 1, 1, 4, 8]
def baseStart_2966612 : Nat := 118140960795 + 2966612 * 2 ^ 59
def prefixEnd_2966612 : Nat := 4983230072969 + 3 ^ 40 * 2966612 * 2
def baseEnd_2966612 : Nat := 112836879362670544489393

theorem tailTrace_2966612 : CollatzResearch.WordTrace tailWord_2966612 prefixEnd_2966612 112836879362670544489393 := by
  unfold tailWord_2966612
  simp only [CollatzResearch.WordTrace]
  refine ⟨54100614364239427918843045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72134152485652570558457393 54100614364239427918843045)
  ·
    refine ⟨10143865193294892734783071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54100614364239427918843045 10143865193294892734783071)
    ·
      refine ⟨15215797789942339102174607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10143865193294892734783071 15215797789942339102174607)
      ·
        refine ⟨22823696684913508653261911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15215797789942339102174607 22823696684913508653261911)
        ·
          refine ⟨34235545027370262979892867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22823696684913508653261911 34235545027370262979892867)
          ·
            refine ⟨51353317541055394469839301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34235545027370262979892867 51353317541055394469839301)
            ·
              refine ⟨9628747038947886463094869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51353317541055394469839301 9628747038947886463094869)
              ·
                refine ⟨112836879362670544489393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9628747038947886463094869 112836879362670544489393)
                ·
                  rfl

theorem cell22_2966612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 8].length) (baseStart_2966612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2966612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2966612 prefixEnd_2966612 := by exact prefixLift 2966612
  have htrace : WordTrace (prefixWord ++ tailWord_2966612) baseStart_2966612 baseEnd_2966612 := by
    simpa [prefixWord, tailWord_2966612, baseEnd_2966612] using wordTrace_append hprefix tailTrace_2966612
  have hstable : (prefixWord ++ tailWord_2966612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966612).length < 2 ^ (prefixWord ++ tailWord_2966612).sum := by decide
  have hdescent : baseEnd_2966612 < baseStart_2966612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966642 : List Nat := [3, 2, 1, 2, 2, 1, 1, 1, 1, 8]
def baseStart_2966642 : Nat := 118140960795 + 2966642 * 2 ^ 59
def prefixEnd_2966642 : Nat := 4983230072969 + 3 ^ 40 * 2966642 * 2
def baseEnd_2966642 : Nat := 1015542183877124822154445

theorem tailTrace_2966642 : CollatzResearch.WordTrace tailWord_2966642 prefixEnd_2966642 1015542183877124822154445 := by
  unfold tailWord_2966642
  simp only [CollatzResearch.WordTrace]
  refine ⟨27050580729592542740319545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72134881945580113974185453 27050580729592542740319545)
  ·
    refine ⟨20287935547194407055239659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27050580729592542740319545 20287935547194407055239659)
    ·
      refine ⟨30431903320791610582859489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20287935547194407055239659 30431903320791610582859489)
      ·
        refine ⟨22823927490593707937144617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30431903320791610582859489 22823927490593707937144617)
        ·
          refine ⟨17117945617945280952858463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22823927490593707937144617 17117945617945280952858463)
          ·
            refine ⟨25676918426917921429287695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17117945617945280952858463 25676918426917921429287695)
            ·
              refine ⟨38515377640376882143931543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25676918426917921429287695 38515377640376882143931543)
              ·
                refine ⟨57773066460565323215897315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38515377640376882143931543 57773066460565323215897315)
                ·
                  refine ⟨86659599690847984823845973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57773066460565323215897315 86659599690847984823845973)
                  ·
                    refine ⟨1015542183877124822154445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 86659599690847984823845973 1015542183877124822154445)
                    ·
                      rfl

theorem cell22_2966642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 1, 8].length) (baseStart_2966642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2966642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2966642 prefixEnd_2966642 := by exact prefixLift 2966642
  have htrace : WordTrace (prefixWord ++ tailWord_2966642) baseStart_2966642 baseEnd_2966642 := by
    simpa [prefixWord, tailWord_2966642, baseEnd_2966642] using wordTrace_append hprefix tailTrace_2966642
  have hstable : (prefixWord ++ tailWord_2966642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966642).length < 2 ^ (prefixWord ++ tailWord_2966642).sum := by decide
  have hdescent : baseEnd_2966642 < baseStart_2966642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966661 : List Nat := [1, 3, 1, 1, 6, 1, 1, 2, 3, 3]
def baseStart_2966661 : Nat := 118140960795 + 2966661 * 2 ^ 59
def prefixEnd_2966661 : Nat := 4983230072969 + 3 ^ 40 * 2966661 * 2
def baseEnd_2966661 : Nat := 1015548687965415105929387

theorem tailTrace_2966661 : CollatzResearch.WordTrace tailWord_2966661 prefixEnd_2966661 1015548687965415105929387 := by
  unfold tailWord_2966661
  simp only [CollatzResearch.WordTrace]
  refine ⟨108203015905301337206219837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72135343936867558137479891 108203015905301337206219837)
  ·
    refine ⟨40576130964488001452332439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108203015905301337206219837 40576130964488001452332439)
    ·
      refine ⟨60864196446732002178498659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40576130964488001452332439 60864196446732002178498659)
      ·
        refine ⟨91296294670098003267747989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60864196446732002178498659 91296294670098003267747989)
        ·
          refine ⟨4279513812660843903175687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 91296294670098003267747989 4279513812660843903175687)
          ·
            refine ⟨6419270718991265854763531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4279513812660843903175687 6419270718991265854763531)
            ·
              refine ⟨9628906078486898782145297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6419270718991265854763531 9628906078486898782145297)
              ·
                refine ⟨7221679558865174086608973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9628906078486898782145297 7221679558865174086608973)
                ·
                  refine ⟨2708129834574440282478365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7221679558865174086608973 2708129834574440282478365)
                  ·
                    refine ⟨1015548687965415105929387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2708129834574440282478365 1015548687965415105929387)
                    ·
                      rfl

theorem cell22_2966661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 2, 3, 3].length) (baseStart_2966661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2966661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2966661 prefixEnd_2966661 := by exact prefixLift 2966661
  have htrace : WordTrace (prefixWord ++ tailWord_2966661) baseStart_2966661 baseEnd_2966661 := by
    simpa [prefixWord, tailWord_2966661, baseEnd_2966661] using wordTrace_append hprefix tailTrace_2966661
  have hstable : (prefixWord ++ tailWord_2966661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966661).length < 2 ^ (prefixWord ++ tailWord_2966661).sum := by decide
  have hdescent : baseEnd_2966661 < baseStart_2966661 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966753 : List Nat := [1, 2, 3, 1, 3, 3, 3, 2, 4]
def baseStart_2966753 : Nat := 118140960795 + 2966753 * 2 ^ 59
def prefixEnd_2966753 : Nat := 4983230072969 + 3 ^ 40 * 2966753 * 2
def baseEnd_2966753 : Nat := 338526727148519177543035

theorem tailTrace_2966753 : CollatzResearch.WordTrace tailWord_2966753 prefixEnd_2966753 338526727148519177543035 := by
  unfold tailWord_2966753
  simp only [CollatzResearch.WordTrace]
  refine ⟨108206371420968036918568913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72137580947312024612379275 108206371420968036918568913)
  ·
    refine ⟨81154778565726027688926685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108206371420968036918568913 81154778565726027688926685)
    ·
      refine ⟨30433041962147260383347507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81154778565726027688926685 30433041962147260383347507)
      ·
        refine ⟨45649562943220890575021261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30433041962147260383347507 45649562943220890575021261)
        ·
          refine ⟨17118586103707833965632973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45649562943220890575021261 17118586103707833965632973)
          ·
            refine ⟨6419469788890437737112365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17118586103707833965632973 6419469788890437737112365)
            ·
              refine ⟨2407301170833914151417137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6419469788890437737112365 2407301170833914151417137)
              ·
                refine ⟨1805475878125435613562853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2407301170833914151417137 1805475878125435613562853)
                ·
                  refine ⟨338526727148519177543035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1805475878125435613562853 338526727148519177543035)
                  ·
                    rfl

theorem cell22_2966753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 3, 2, 4].length) (baseStart_2966753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2966753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2966753 prefixEnd_2966753 := by exact prefixLift 2966753
  have htrace : WordTrace (prefixWord ++ tailWord_2966753) baseStart_2966753 baseEnd_2966753 := by
    simpa [prefixWord, tailWord_2966753, baseEnd_2966753] using wordTrace_append hprefix tailTrace_2966753
  have hstable : (prefixWord ++ tailWord_2966753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966753).length < 2 ^ (prefixWord ++ tailWord_2966753).sum := by decide
  have hdescent : baseEnd_2966753 < baseStart_2966753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966764 : List Nat := [2, 2, 1, 1, 2, 5, 2, 7]
def baseStart_2966764 : Nat := 118140960795 + 2966764 * 2 ^ 59
def prefixEnd_2966764 : Nat := 4983230072969 + 3 ^ 40 * 2966764 * 2
def baseEnd_2966764 : Nat := 112842660774484130067119

theorem tailTrace_2966764 : CollatzResearch.WordTrace tailWord_2966764 prefixEnd_2966764 112842660774484130067119 := by
  unfold tailWord_2966764
  simp only [CollatzResearch.WordTrace]
  refine ⟨54103386311964092898609673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72137848415952123864812897 54103386311964092898609673)
  ·
    refine ⟨40577539733973069673957255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54103386311964092898609673 40577539733973069673957255)
    ·
      refine ⟨60866309600959604510935883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40577539733973069673957255 60866309600959604510935883)
      ·
        refine ⟨91299464401439406766403825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60866309600959604510935883 91299464401439406766403825)
        ·
          refine ⟨68474598301079555074802869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91299464401439406766403825 68474598301079555074802869)
          ·
            refine ⟨6419493590726208288262769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 68474598301079555074802869 6419493590726208288262769)
            ·
              refine ⟨4814620193044656216197077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6419493590726208288262769 4814620193044656216197077)
              ·
                refine ⟨112842660774484130067119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4814620193044656216197077 112842660774484130067119)
                ·
                  rfl

theorem cell22_2966764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 7].length) (baseStart_2966764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2966764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2966764 prefixEnd_2966764 := by exact prefixLift 2966764
  have htrace : WordTrace (prefixWord ++ tailWord_2966764) baseStart_2966764 baseEnd_2966764 := by
    simpa [prefixWord, tailWord_2966764, baseEnd_2966764] using wordTrace_append hprefix tailTrace_2966764
  have hstable : (prefixWord ++ tailWord_2966764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966764).length < 2 ^ (prefixWord ++ tailWord_2966764).sum := by decide
  have hdescent : baseEnd_2966764 < baseStart_2966764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966802 : List Nat := [3, 2, 4, 2, 1, 1, 2, 2, 2, 3]
def baseStart_2966802 : Nat := 118140960795 + 2966802 * 2 ^ 59
def prefixEnd_2966802 : Nat := 4983230072969 + 3 ^ 40 * 2966802 * 2
def baseEnd_2966802 : Nat := 1015596955146937738153955

theorem tailTrace_2966802 : CollatzResearch.WordTrace tailWord_2966802 prefixEnd_2966802 1015596955146937738153955 := by
  unfold tailWord_2966802
  simp only [CollatzResearch.WordTrace]
  refine ⟨27052039649447629571775665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72138772398527012191401773 27052039649447629571775665)
  ·
    refine ⟨20289029737085722178831749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27052039649447629571775665 20289029737085722178831749)
    ·
      refine ⟨3804193075703572908530953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20289029737085722178831749 3804193075703572908530953)
      ·
        refine ⟨2853144806777679681398215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3804193075703572908530953 2853144806777679681398215)
        ·
          refine ⟨4279717210166519522097323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2853144806777679681398215 4279717210166519522097323)
          ·
            refine ⟨6419575815249779283145985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4279717210166519522097323 6419575815249779283145985)
            ·
              refine ⟨4814681861437334462359489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6419575815249779283145985 4814681861437334462359489)
              ·
                refine ⟨3611011396078000846769617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4814681861437334462359489 3611011396078000846769617)
                ·
                  refine ⟨2708258547058500635077213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3611011396078000846769617 2708258547058500635077213)
                  ·
                    refine ⟨1015596955146937738153955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2708258547058500635077213 1015596955146937738153955)
                    ·
                      rfl

theorem cell22_2966802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_2966802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2966802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2966802 prefixEnd_2966802 := by exact prefixLift 2966802
  have htrace : WordTrace (prefixWord ++ tailWord_2966802) baseStart_2966802 baseEnd_2966802 := by
    simpa [prefixWord, tailWord_2966802, baseEnd_2966802] using wordTrace_append hprefix tailTrace_2966802
  have hstable : (prefixWord ++ tailWord_2966802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966802).length < 2 ^ (prefixWord ++ tailWord_2966802).sum := by decide
  have hdescent : baseEnd_2966802 < baseStart_2966802 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966871 : List Nat := [1, 1, 3, 2, 3, 3, 2, 1, 6]
def baseStart_2966871 : Nat := 118140960795 + 2966871 * 2 ^ 59
def prefixEnd_2966871 : Nat := 4983230072969 + 3 ^ 40 * 2966871 * 2
def baseEnd_2966871 : Nat := 338540191752348186059581

theorem tailTrace_2966871 : CollatzResearch.WordTrace tailWord_2966871 prefixEnd_2966871 338540191752348186059581 := by
  unfold tailWord_2966871
  simp only [CollatzResearch.WordTrace]
  refine ⟨108210675234540543071364467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72140450156360362047576311 108210675234540543071364467)
  ·
    refine ⟨162316012851810814607046701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108210675234540543071364467 162316012851810814607046701)
    ·
      refine ⟨60868504819429055477642513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162316012851810814607046701 60868504819429055477642513)
      ·
        refine ⟨45651378614571791608231885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60868504819429055477642513 45651378614571791608231885)
        ·
          refine ⟨17119266980464421853086957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45651378614571791608231885 17119266980464421853086957)
          ·
            refine ⟨6419725117674158194907609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17119266980464421853086957 6419725117674158194907609)
            ·
              refine ⟨4814793838255618646180707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6419725117674158194907609 4814793838255618646180707)
              ·
                refine ⟨7222190757383427969271061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4814793838255618646180707 7222190757383427969271061)
                ·
                  refine ⟨338540191752348186059581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7222190757383427969271061 338540191752348186059581)
                  ·
                    rfl

theorem cell22_2966871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 1, 6].length) (baseStart_2966871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2966871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2966871 prefixEnd_2966871 := by exact prefixLift 2966871
  have htrace : WordTrace (prefixWord ++ tailWord_2966871) baseStart_2966871 baseEnd_2966871 := by
    simpa [prefixWord, tailWord_2966871, baseEnd_2966871] using wordTrace_append hprefix tailTrace_2966871
  have hstable : (prefixWord ++ tailWord_2966871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966871).length < 2 ^ (prefixWord ++ tailWord_2966871).sum := by decide
  have hdescent : baseEnd_2966871 < baseStart_2966871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966890 : List Nat := [3, 1, 3, 3, 2, 1, 2, 2, 1, 4]
def baseStart_2966890 : Nat := 118140960795 + 2966890 * 2 ^ 59
def prefixEnd_2966890 : Nat := 4983230072969 + 3 ^ 40 * 2966890 * 2
def baseEnd_2966890 : Nat := 1015627079345334841953685

theorem tailTrace_2966890 : CollatzResearch.WordTrace tailWord_2966890 prefixEnd_2966890 1015627079345334841953685 := by
  unfold tailWord_2966890
  simp only [CollatzResearch.WordTrace]
  refine ⟨27052842055367927329076531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72140912147647806210870749 27052842055367927329076531)
  ·
    refine ⟨40579263083051890993614797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27052842055367927329076531 40579263083051890993614797)
    ·
      refine ⟨15217223656144459122605549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40579263083051890993614797 15217223656144459122605549)
      ·
        refine ⟨5706458871054172170977081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15217223656144459122605549 5706458871054172170977081)
        ·
          refine ⟨4279844153290629128232811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5706458871054172170977081 4279844153290629128232811)
          ·
            refine ⟨6419766229935943692349217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4279844153290629128232811 6419766229935943692349217)
            ·
              refine ⟨4814824672451957769261913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6419766229935943692349217 4814824672451957769261913)
              ·
                refine ⟨3611118504338968326946435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4814824672451957769261913 3611118504338968326946435)
                ·
                  refine ⟨5416677756508452490419653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3611118504338968326946435 5416677756508452490419653)
                  ·
                    refine ⟨1015627079345334841953685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5416677756508452490419653 1015627079345334841953685)
                    ·
                      rfl

theorem cell22_2966890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_2966890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2966890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2966890 prefixEnd_2966890 := by exact prefixLift 2966890
  have htrace : WordTrace (prefixWord ++ tailWord_2966890) baseStart_2966890 baseEnd_2966890 := by
    simpa [prefixWord, tailWord_2966890, baseEnd_2966890] using wordTrace_append hprefix tailTrace_2966890
  have hstable : (prefixWord ++ tailWord_2966890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966890).length < 2 ^ (prefixWord ++ tailWord_2966890).sum := by decide
  have hdescent : baseEnd_2966890 < baseStart_2966890 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966916 : List Nat := [2, 3, 2, 1, 1, 5, 8]
def baseStart_2966916 : Nat := 118140960795 + 2966916 * 2 ^ 59
def prefixEnd_2966916 : Nat := 4983230072969 + 3 ^ 40 * 2966916 * 2
def baseEnd_2966916 : Nat := 37616147395432571881615

theorem tailTrace_2966916 : CollatzResearch.WordTrace tailWord_2966916 prefixEnd_2966916 37616147395432571881615 := by
  unfold tailWord_2966916
  simp only [CollatzResearch.WordTrace]
  refine ⟨54106158259688757878376301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72141544346251677171168401 54106158259688757878376301)
  ·
    refine ⟨20289809347383284204391113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54106158259688757878376301 20289809347383284204391113)
    ·
      refine ⟨15217357010537463153293335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20289809347383284204391113 15217357010537463153293335)
      ·
        refine ⟨22826035515806194729940003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15217357010537463153293335 22826035515806194729940003)
        ·
          refine ⟨34239053273709292094910005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22826035515806194729940003 34239053273709292094910005)
          ·
            refine ⟨3209911244410246133897813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34239053273709292094910005 3209911244410246133897813)
            ·
              refine ⟨37616147395432571881615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3209911244410246133897813 37616147395432571881615)
              ·
                rfl

theorem cell22_2966916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 8].length) (baseStart_2966916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2966916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2966916 prefixEnd_2966916 := by exact prefixLift 2966916
  have htrace : WordTrace (prefixWord ++ tailWord_2966916) baseStart_2966916 baseEnd_2966916 := by
    simpa [prefixWord, tailWord_2966916, baseEnd_2966916] using wordTrace_append hprefix tailTrace_2966916
  have hstable : (prefixWord ++ tailWord_2966916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966916).length < 2 ^ (prefixWord ++ tailWord_2966916).sum := by decide
  have hdescent : baseEnd_2966916 < baseStart_2966916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966929 : List Nat := [1, 2, 2, 1, 1, 1, 2, 3, 1, 8]
def baseStart_2966929 : Nat := 118140960795 + 2966929 * 2 ^ 59
def prefixEnd_2966929 : Nat := 4983230072969 + 3 ^ 40 * 2966929 * 2
def baseEnd_2966929 : Nat := 1015640429842351740228565

theorem tailTrace_2966929 : CollatzResearch.WordTrace tailWord_2966929 prefixEnd_2966929 1015640429842351740228565 := by
  unfold tailWord_2966929
  simp only [CollatzResearch.WordTrace]
  refine ⟨108212790668330418976975841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72141860445553612651317227 108212790668330418976975841)
  ·
    refine ⟨81159593001247814232731881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108212790668330418976975841 81159593001247814232731881)
    ·
      refine ⟨60869694750935860674548911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81159593001247814232731881 60869694750935860674548911)
      ·
        refine ⟨91304542126403791011823367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60869694750935860674548911 91304542126403791011823367)
        ·
          refine ⟨136956813189605686517735051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91304542126403791011823367 136956813189605686517735051)
          ·
            refine ⟨205435219784408529776602577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136956813189605686517735051 205435219784408529776602577)
            ·
              refine ⟨154076414838306397332451933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 205435219784408529776602577 154076414838306397332451933)
              ·
                refine ⟨57778655564364898999669475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 154076414838306397332451933 57778655564364898999669475)
                ·
                  refine ⟨86667983346547348499504213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57778655564364898999669475 86667983346547348499504213)
                  ·
                    refine ⟨1015640429842351740228565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 86667983346547348499504213 1015640429842351740228565)
                    ·
                      rfl

theorem cell22_2966929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 8].length) (baseStart_2966929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2966929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2966929 prefixEnd_2966929 := by exact prefixLift 2966929
  have htrace : WordTrace (prefixWord ++ tailWord_2966929) baseStart_2966929 baseEnd_2966929 := by
    simpa [prefixWord, tailWord_2966929, baseEnd_2966929] using wordTrace_append hprefix tailTrace_2966929
  have hstable : (prefixWord ++ tailWord_2966929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966929).length < 2 ^ (prefixWord ++ tailWord_2966929).sum := by decide
  have hdescent : baseEnd_2966929 < baseStart_2966929 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2966991 : List Nat := [1, 1, 2, 1, 1, 4, 3, 2, 3, 4]
def baseStart_2966991 : Nat := 118140960795 + 2966991 * 2 ^ 59
def prefixEnd_2966991 : Nat := 4983230072969 + 3 ^ 40 * 2966991 * 2
def baseEnd_2966991 : Nat := 1015661653709404245178375

theorem tailTrace_2966991 : CollatzResearch.WordTrace tailWord_2966991 prefixEnd_2966991 1015661653709404245178375 := by
  unfold tailWord_2966991
  simp only [CollatzResearch.WordTrace]
  refine ⟨108215051994105803565732827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72143367996070535710488551 108215051994105803565732827)
  ·
    refine ⟨162322577991158705348599241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108215051994105803565732827 162322577991158705348599241)
    ·
      refine ⟨121741933493369029011449431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162322577991158705348599241 121741933493369029011449431)
      ·
        refine ⟨182612900240053543517174147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121741933493369029011449431 182612900240053543517174147)
        ·
          refine ⟨273919350360080315275761221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182612900240053543517174147 273919350360080315275761221)
          ·
            refine ⟨51359878192515059114205229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 273919350360080315275761221 51359878192515059114205229)
            ·
              refine ⟨19259954322193147167826961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51359878192515059114205229 19259954322193147167826961)
              ·
                refine ⟨14444965741644860375870221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19259954322193147167826961 14444965741644860375870221)
                ·
                  refine ⟨5416862153116822640951333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14444965741644860375870221 5416862153116822640951333)
                  ·
                    refine ⟨1015661653709404245178375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5416862153116822640951333 1015661653709404245178375)
                    ·
                      rfl

theorem cell22_2966991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 2, 3, 4].length) (baseStart_2966991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2966991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2966991 prefixEnd_2966991 := by exact prefixLift 2966991
  have htrace : WordTrace (prefixWord ++ tailWord_2966991) baseStart_2966991 baseEnd_2966991 := by
    simpa [prefixWord, tailWord_2966991, baseEnd_2966991] using wordTrace_append hprefix tailTrace_2966991
  have hstable : (prefixWord ++ tailWord_2966991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2966991).length < 2 ^ (prefixWord ++ tailWord_2966991).sum := by decide
  have hdescent : baseEnd_2966991 < baseStart_2966991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2966991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2967023 : List Nat := [1, 1, 2, 1, 4, 1, 3, 5, 4]
def baseStart_2967023 : Nat := 118140960795 + 2967023 * 2 ^ 59
def prefixEnd_2967023 : Nat := 4983230072969 + 3 ^ 40 * 2967023 * 2
def baseEnd_2967023 : Nat := 338557535987788942792759

theorem tailTrace_2967023 : CollatzResearch.WordTrace tailWord_2967023 prefixEnd_2967023 338557535987788942792759 := by
  unfold tailWord_2967023
  simp only [CollatzResearch.WordTrace]
  refine ⟨108216219129989873030897723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72144146086659915353931815 108216219129989873030897723)
  ·
    refine ⟨162324328694984809546346585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108216219129989873030897723 162324328694984809546346585)
    ·
      refine ⟨121743246521238607159759939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162324328694984809546346585 121743246521238607159759939)
      ·
        refine ⟨182614869781857910739639909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121743246521238607159759939 182614869781857910739639909)
        ·
          refine ⟨34240288084098358263682483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 182614869781857910739639909 34240288084098358263682483)
          ·
            refine ⟨51360432126147537395523725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34240288084098358263682483 51360432126147537395523725)
            ·
              refine ⟨19260162047305326523321397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51360432126147537395523725 19260162047305326523321397)
              ·
                refine ⟨1805640191934874361561381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19260162047305326523321397 1805640191934874361561381)
                ·
                  refine ⟨338557535987788942792759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1805640191934874361561381 338557535987788942792759)
                  ·
                    rfl

theorem cell22_2967023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 5, 4].length) (baseStart_2967023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2967023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2967023 prefixEnd_2967023 := by exact prefixLift 2967023
  have htrace : WordTrace (prefixWord ++ tailWord_2967023) baseStart_2967023 baseEnd_2967023 := by
    simpa [prefixWord, tailWord_2967023, baseEnd_2967023] using wordTrace_append hprefix tailTrace_2967023
  have hstable : (prefixWord ++ tailWord_2967023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2967023).length < 2 ^ (prefixWord ++ tailWord_2967023).sum := by decide
  have hdescent : baseEnd_2967023 < baseStart_2967023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2967023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2967025 : List Nat := [1, 2, 2, 2, 3, 2, 4, 1, 1, 4]
def baseStart_2967025 : Nat := 118140960795 + 2967025 * 2 ^ 59
def prefixEnd_2967025 : Nat := 4983230072969 + 3 ^ 40 * 2967025 * 2
def baseEnd_2967025 : Nat := 1015673292604239489828271

theorem tailTrace_2967025 : CollatzResearch.WordTrace tailWord_2967025 prefixEnd_2967025 1015673292604239489828271 := by
  unfold tailWord_2967025
  simp only [CollatzResearch.WordTrace]
  refine ⟨108216292075982627372470529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72144194717321751581647019 108216292075982627372470529)
  ·
    refine ⟨81162219056986970529352897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108216292075982627372470529 81162219056986970529352897)
    ·
      refine ⟨60871664292740227897014673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81162219056986970529352897 60871664292740227897014673)
      ·
        refine ⟨45653748219555170922761005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60871664292740227897014673 45653748219555170922761005)
        ·
          refine ⟨17120155582333189096035377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45653748219555170922761005 17120155582333189096035377)
          ·
            refine ⟨12840116686749891822026533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17120155582333189096035377 12840116686749891822026533)
            ·
              refine ⟨2407521878765604716629975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12840116686749891822026533 2407521878765604716629975)
              ·
                refine ⟨3611282818148407074944963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2407521878765604716629975 3611282818148407074944963)
                ·
                  refine ⟨5416924227222610612417445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3611282818148407074944963 5416924227222610612417445)
                  ·
                    refine ⟨1015673292604239489828271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5416924227222610612417445 1015673292604239489828271)
                    ·
                      rfl

theorem cell22_2967025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 4, 1, 1, 4].length) (baseStart_2967025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2967025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2967025 prefixEnd_2967025 := by exact prefixLift 2967025
  have htrace : WordTrace (prefixWord ++ tailWord_2967025) baseStart_2967025 baseEnd_2967025 := by
    simpa [prefixWord, tailWord_2967025, baseEnd_2967025] using wordTrace_append hprefix tailTrace_2967025
  have hstable : (prefixWord ++ tailWord_2967025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2967025).length < 2 ^ (prefixWord ++ tailWord_2967025).sum := by decide
  have hdescent : baseEnd_2967025 < baseStart_2967025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2967025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2967046 : List Nat := [6, 2, 1, 1, 2, 1, 3, 1, 5]
def baseStart_2967046 : Nat := 118140960795 + 2967046 * 2 ^ 59
def prefixEnd_2967046 : Nat := 4983230072969 + 3 ^ 40 * 2967046 * 2
def baseEnd_2967046 : Nat := 338560160444467478351069

theorem tailTrace_2967046 : CollatzResearch.WordTrace tailWord_2967046 prefixEnd_2967046 338560160444467478351069 := by
  unfold tailWord_2967046
  simp only [CollatzResearch.WordTrace]
  refine ⟨3381783062778329623718281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 72144705339271031972656661 3381783062778329623718281)
  ·
    refine ⟨2536337297083747217788711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3381783062778329623718281 2536337297083747217788711)
    ·
      refine ⟨3804505945625620826683067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2536337297083747217788711 3804505945625620826683067)
      ·
        refine ⟨5706758918438431240024601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3804505945625620826683067 5706758918438431240024601)
        ·
          refine ⟨4280069188828823430018451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5706758918438431240024601 4280069188828823430018451)
          ·
            refine ⟨6420103783243235145027677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4280069188828823430018451 6420103783243235145027677)
            ·
              refine ⟨2407538918716213179385379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6420103783243235145027677 2407538918716213179385379)
              ·
                refine ⟨3611308378074319769078069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2407538918716213179385379 3611308378074319769078069)
                ·
                  refine ⟨338560160444467478351069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3611308378074319769078069 338560160444467478351069)
                  ·
                    rfl

theorem cell22_2967046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_2967046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2967046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2967046 prefixEnd_2967046 := by exact prefixLift 2967046
  have htrace : WordTrace (prefixWord ++ tailWord_2967046) baseStart_2967046 baseEnd_2967046 := by
    simpa [prefixWord, tailWord_2967046, baseEnd_2967046] using wordTrace_append hprefix tailTrace_2967046
  have hstable : (prefixWord ++ tailWord_2967046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2967046).length < 2 ^ (prefixWord ++ tailWord_2967046).sum := by decide
  have hdescent : baseEnd_2967046 < baseStart_2967046 := by decide
  rcases family_descends (prefixWord ++ tailWord_2967046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2967066 : List Nat := [3, 1, 1, 3, 1, 1, 1, 1, 1, 9]
def baseStart_2967066 : Nat := 118140960795 + 2967066 * 2 ^ 59
def prefixEnd_2967066 : Nat := 4983230072969 + 3 ^ 40 * 2967066 * 2
def baseEnd_2967066 : Nat := 1015687327742129049553145

theorem tailTrace_2967066 : CollatzResearch.WordTrace tailWord_2967066 prefixEnd_2967066 1015687327742129049553145 := by
  unfold tailWord_2967066
  simp only [CollatzResearch.WordTrace]
  refine ⟨27054446867208522843678263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72145191645889394249808701 27054446867208522843678263)
  ·
    refine ⟨40581670300812784265517395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27054446867208522843678263 40581670300812784265517395)
    ·
      refine ⟨60872505451219176398276093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40581670300812784265517395 60872505451219176398276093)
      ·
        refine ⟨22827189544207191149353535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60872505451219176398276093 22827189544207191149353535)
        ·
          refine ⟨34240784316310786724030303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22827189544207191149353535 34240784316310786724030303)
          ·
            refine ⟨51361176474466180086045455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34240784316310786724030303 51361176474466180086045455)
            ·
              refine ⟨77041764711699270129068183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51361176474466180086045455 77041764711699270129068183)
              ·
                refine ⟨115562647067548905193602275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77041764711699270129068183 115562647067548905193602275)
                ·
                  refine ⟨173343970601323357790403413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 115562647067548905193602275 173343970601323357790403413)
                  ·
                    refine ⟨1015687327742129049553145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 173343970601323357790403413 1015687327742129049553145)
                    ·
                      rfl

theorem cell22_2967066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 1, 9].length) (baseStart_2967066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2967066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2967066 prefixEnd_2967066 := by exact prefixLift 2967066
  have htrace : WordTrace (prefixWord ++ tailWord_2967066) baseStart_2967066 baseEnd_2967066 := by
    simpa [prefixWord, tailWord_2967066, baseEnd_2967066] using wordTrace_append hprefix tailTrace_2967066
  have hstable : (prefixWord ++ tailWord_2967066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2967066).length < 2 ^ (prefixWord ++ tailWord_2967066).sum := by decide
  have hdescent : baseEnd_2967066 < baseStart_2967066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2967066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2967192 : List Nat := [2, 1, 2, 4, 1, 3, 2, 3, 4]
def baseStart_2967192 : Nat := 118140960795 + 2967192 * 2 ^ 59
def prefixEnd_2967192 : Nat := 4983230072969 + 3 ^ 40 * 2967192 * 2
def baseEnd_2967192 : Nat := 338576820039035573634253

theorem tailTrace_2967192 : CollatzResearch.WordTrace tailWord_2967192 prefixEnd_2967192 338576820039035573634253 := by
  unfold tailWord_2967192
  simp only [CollatzResearch.WordTrace]
  refine ⟨54111191533188807446899915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72148255377585076595866553 54111191533188807446899915)
  ·
    refine ⟨81166787299783211170349873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54111191533188807446899915 81166787299783211170349873)
    ·
      refine ⟨60875090474837408377762405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81166787299783211170349873 60875090474837408377762405)
      ·
        refine ⟨11414079464032014070830451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60875090474837408377762405 11414079464032014070830451)
        ·
          refine ⟨17121119196048021106245677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11414079464032014070830451 17121119196048021106245677)
          ·
            refine ⟨6420419698518007914842129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17121119196048021106245677 6420419698518007914842129)
            ·
              refine ⟨4815314773888505936131597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6420419698518007914842129 4815314773888505936131597)
              ·
                refine ⟨1805743040208189726049349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4815314773888505936131597 1805743040208189726049349)
                ·
                  refine ⟨338576820039035573634253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1805743040208189726049349 338576820039035573634253)
                  ·
                    rfl

theorem cell22_2967192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 3, 4].length) (baseStart_2967192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2967192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2967192 prefixEnd_2967192 := by exact prefixLift 2967192
  have htrace : WordTrace (prefixWord ++ tailWord_2967192) baseStart_2967192 baseEnd_2967192 := by
    simpa [prefixWord, tailWord_2967192, baseEnd_2967192] using wordTrace_append hprefix tailTrace_2967192
  have hstable : (prefixWord ++ tailWord_2967192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2967192).length < 2 ^ (prefixWord ++ tailWord_2967192).sum := by decide
  have hdescent : baseEnd_2967192 < baseStart_2967192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2967192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2967222 : List Nat := [5, 1, 3, 1, 1, 1, 1, 2, 1, 6]
def baseStart_2967222 : Nat := 118140960795 + 2967222 * 2 ^ 59
def prefixEnd_2967222 : Nat := 4983230072969 + 3 ^ 40 * 2967222 * 2
def baseEnd_2967222 : Nat := 1015740729730196642652667

theorem tailTrace_2967222 : CollatzResearch.WordTrace tailWord_2967222 prefixEnd_2967222 1015740729730196642652667 := by
  unfold tailWord_2967222
  simp only [CollatzResearch.WordTrace]
  refine ⟨6763967328516808126086995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72148984837512620011594613 6763967328516808126086995)
  ·
    refine ⟨10145950992775212189130493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6763967328516808126086995 10145950992775212189130493)
    ·
      refine ⟨3804731622290704570923935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10145950992775212189130493 3804731622290704570923935)
      ·
        refine ⟨5707097433436056856385903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3804731622290704570923935 5707097433436056856385903)
        ·
          refine ⟨8560646150154085284578855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5707097433436056856385903 8560646150154085284578855)
          ·
            refine ⟨12840969225231127926868283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8560646150154085284578855 12840969225231127926868283)
            ·
              refine ⟨19261453837846691890302425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12840969225231127926868283 19261453837846691890302425)
              ·
                refine ⟨14446090378385018917726819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19261453837846691890302425 14446090378385018917726819)
                ·
                  refine ⟨21669135567577528376590229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14446090378385018917726819 21669135567577528376590229)
                  ·
                    refine ⟨1015740729730196642652667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21669135567577528376590229 1015740729730196642652667)
                    ·
                      rfl

theorem cell22_2967222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_2967222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2967222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2967222 prefixEnd_2967222 := by exact prefixLift 2967222
  have htrace : WordTrace (prefixWord ++ tailWord_2967222) baseStart_2967222 baseEnd_2967222 := by
    simpa [prefixWord, tailWord_2967222, baseEnd_2967222] using wordTrace_append hprefix tailTrace_2967222
  have hstable : (prefixWord ++ tailWord_2967222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2967222).length < 2 ^ (prefixWord ++ tailWord_2967222).sum := by decide
  have hdescent : baseEnd_2967222 < baseStart_2967222 := by decide
  rcases family_descends (prefixWord ++ tailWord_2967222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2967254 : List Nat := [5, 2, 1, 3, 1, 2, 8]
def baseStart_2967254 : Nat := 118140960795 + 2967254 * 2 ^ 59
def prefixEnd_2967254 : Nat := 4983230072969 + 3 ^ 40 * 2967254 * 2
def baseEnd_2967254 : Nat := 37620432740154045401947

theorem tailTrace_2967254 : CollatzResearch.WordTrace tailWord_2967254 prefixEnd_2967254 37620432740154045401947 := by
  unfold tailWord_2967254
  simp only [CollatzResearch.WordTrace]
  refine ⟨6764040274509562467659801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72149762928101999655037877 6764040274509562467659801)
  ·
    refine ⟨5073030205882171850744851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6764040274509562467659801 5073030205882171850744851)
    ·
      refine ⟨7609545308823257776117277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5073030205882171850744851 7609545308823257776117277)
      ·
        refine ⟨2853579490808721666043979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7609545308823257776117277 2853579490808721666043979)
        ·
          refine ⟨4280369236213082499065969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2853579490808721666043979 4280369236213082499065969)
          ·
            refine ⟨3210276927159811874299477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4280369236213082499065969 3210276927159811874299477)
            ·
              refine ⟨37620432740154045401947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3210276927159811874299477 37620432740154045401947)
              ·
                rfl

theorem cell22_2967254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 8].length) (baseStart_2967254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2967254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2967254 prefixEnd_2967254 := by exact prefixLift 2967254
  have htrace : WordTrace (prefixWord ++ tailWord_2967254) baseStart_2967254 baseEnd_2967254 := by
    simpa [prefixWord, tailWord_2967254, baseEnd_2967254] using wordTrace_append hprefix tailTrace_2967254
  have hstable : (prefixWord ++ tailWord_2967254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2967254).length < 2 ^ (prefixWord ++ tailWord_2967254).sum := by decide
  have hdescent : baseEnd_2967254 < baseStart_2967254 := by decide
  rcases family_descends (prefixWord ++ tailWord_2967254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2967327 : List Nat := [1, 1, 2, 4, 2, 1, 3, 4, 4]
def baseStart_2967327 : Nat := 118140960795 + 2967327 * 2 ^ 59
def prefixEnd_2967327 : Nat := 4983230072969 + 3 ^ 40 * 2967327 * 2
def baseEnd_2967327 : Nat := 338592224458670456259115

theorem tailTrace_2967327 : CollatzResearch.WordTrace tailWord_2967327 prefixEnd_2967327 338592224458670456259115 := by
  unfold tailWord_2967327
  simp only [CollatzResearch.WordTrace]
  refine ⟨108227306920888532949964235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72151537947259021966642823 108227306920888532949964235)
  ·
    refine ⟨162340960381332799424946353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108227306920888532949964235 162340960381332799424946353)
    ·
      refine ⟨121755720285999599568709765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162340960381332799424946353 121755720285999599568709765)
      ·
        refine ⟨22829197553624924919133081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 121755720285999599568709765 22829197553624924919133081)
        ·
          refine ⟨17121898165218693689349811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22829197553624924919133081 17121898165218693689349811)
          ·
            refine ⟨25682847247828040534024717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17121898165218693689349811 25682847247828040534024717)
            ·
              refine ⟨9631067717935515200259269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25682847247828040534024717 9631067717935515200259269)
              ·
                refine ⟨1805825197112909100048613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9631067717935515200259269 1805825197112909100048613)
                ·
                  refine ⟨338592224458670456259115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1805825197112909100048613 338592224458670456259115)
                  ·
                    rfl

theorem cell22_2967327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 4, 4].length) (baseStart_2967327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2967327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2967327 prefixEnd_2967327 := by exact prefixLift 2967327
  have htrace : WordTrace (prefixWord ++ tailWord_2967327) baseStart_2967327 baseEnd_2967327 := by
    simpa [prefixWord, tailWord_2967327, baseEnd_2967327] using wordTrace_append hprefix tailTrace_2967327
  have hstable : (prefixWord ++ tailWord_2967327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2967327).length < 2 ^ (prefixWord ++ tailWord_2967327).sum := by decide
  have hdescent : baseEnd_2967327 < baseStart_2967327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2967327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2967357 : List Nat := [1, 4, 1, 4, 1, 2, 1, 1, 1, 6]
def baseStart_2967357 : Nat := 118140960795 + 2967357 * 2 ^ 59
def prefixEnd_2967357 : Nat := 4983230072969 + 3 ^ 40 * 2967357 * 2
def baseEnd_2967357 : Nat := 1015786942989101290527253

theorem tailTrace_2967357 : CollatzResearch.WordTrace tailWord_2967357 prefixEnd_2967357 1015786942989101290527253 := by
  unfold tailWord_2967357
  simp only [CollatzResearch.WordTrace]
  refine ⟨108228401110779848073556325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72152267407186565382370883 108228401110779848073556325)
  ·
    refine ⟨20292825208271221513791811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108228401110779848073556325 20292825208271221513791811)
    ·
      refine ⟨30439237812406832270687717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20292825208271221513791811 30439237812406832270687717)
      ·
        refine ⟨5707357089826281050753947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30439237812406832270687717 5707357089826281050753947)
        ·
          refine ⟨8561035634739421576130921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5707357089826281050753947 8561035634739421576130921)
          ·
            refine ⟨6420776726054566182098191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8561035634739421576130921 6420776726054566182098191)
            ·
              refine ⟨9631165089081849273147287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6420776726054566182098191 9631165089081849273147287)
              ·
                refine ⟨14446747633622773909720931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9631165089081849273147287 14446747633622773909720931)
                ·
                  refine ⟨21670121450434160864581397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14446747633622773909720931 21670121450434160864581397)
                  ·
                    refine ⟨1015786942989101290527253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21670121450434160864581397 1015786942989101290527253)
                    ·
                      rfl

theorem cell22_2967357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 1, 1, 6].length) (baseStart_2967357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2967357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2967357 prefixEnd_2967357 := by exact prefixLift 2967357
  have htrace : WordTrace (prefixWord ++ tailWord_2967357) baseStart_2967357 baseEnd_2967357 := by
    simpa [prefixWord, tailWord_2967357, baseEnd_2967357] using wordTrace_append hprefix tailTrace_2967357
  have hstable : (prefixWord ++ tailWord_2967357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2967357).length < 2 ^ (prefixWord ++ tailWord_2967357).sum := by decide
  have hdescent : baseEnd_2967357 < baseStart_2967357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2967357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2967438 : List Nat := [4, 1, 1, 5, 1, 2, 1, 1, 3, 3]
def baseStart_2967438 : Nat := 118140960795 + 2967438 * 2 ^ 59
def prefixEnd_2967438 : Nat := 4983230072969 + 3 ^ 40 * 2967438 * 2
def baseEnd_2967438 : Nat := 1015814670944444079252005

theorem tailTrace_2967438 : CollatzResearch.WordTrace tailWord_2967438 prefixEnd_2967438 1015814670944444079252005 := by
  unfold tailWord_2967438
  simp only [CollatzResearch.WordTrace]
  refine ⟨13528919427935799863406871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72154236948990932604836645 13528919427935799863406871)
  ·
    refine ⟨20293379141903699795110307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13528919427935799863406871 20293379141903699795110307)
    ·
      refine ⟨30440068712855549692665461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20293379141903699795110307 30440068712855549692665461)
      ·
        refine ⟨2853756441830207783687387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30440068712855549692665461 2853756441830207783687387)
        ·
          refine ⟨4280634662745311675531081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2853756441830207783687387 4280634662745311675531081)
          ·
            refine ⟨3210475997058983756648311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4280634662745311675531081 3210475997058983756648311)
            ·
              refine ⟨4815713995588475634972467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3210475997058983756648311 4815713995588475634972467)
              ·
                refine ⟨7223570993382713452458701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4815713995588475634972467 7223570993382713452458701)
                ·
                  refine ⟨2708839122518517544672013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7223570993382713452458701 2708839122518517544672013)
                  ·
                    refine ⟨1015814670944444079252005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2708839122518517544672013 1015814670944444079252005)
                    ·
                      rfl

theorem cell22_2967438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 1, 3, 3].length) (baseStart_2967438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2967438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2967438 prefixEnd_2967438 := by exact prefixLift 2967438
  have htrace : WordTrace (prefixWord ++ tailWord_2967438) baseStart_2967438 baseEnd_2967438 := by
    simpa [prefixWord, tailWord_2967438, baseEnd_2967438] using wordTrace_append hprefix tailTrace_2967438
  have hstable : (prefixWord ++ tailWord_2967438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2967438).length < 2 ^ (prefixWord ++ tailWord_2967438).sum := by decide
  have hdescent : baseEnd_2967438 < baseStart_2967438 := by decide
  rcases family_descends (prefixWord ++ tailWord_2967438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2967477 : List Nat := [1, 3, 3, 2, 1, 2, 1, 1, 3, 5]
def baseStart_2967477 : Nat := 118140960795 + 2967477 * 2 ^ 59
def prefixEnd_2967477 : Nat := 4983230072969 + 3 ^ 40 * 2967477 * 2
def baseEnd_2967477 : Nat := 1015828021441460977526885

theorem tailTrace_2967477 : CollatzResearch.WordTrace tailWord_2967477 prefixEnd_2967477 1015828021441460977526885 := by
  unfold tailWord_2967477
  simp only [CollatzResearch.WordTrace]
  refine ⟨108232777870345108567924685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72155185246896739045283123 108232777870345108567924685)
  ·
    refine ⟨40587291701379415712971757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108232777870345108567924685 40587291701379415712971757)
    ·
      refine ⟨15220234388017280892364409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40587291701379415712971757 15220234388017280892364409)
      ·
        refine ⟨11415175791012960669273307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15220234388017280892364409 11415175791012960669273307)
        ·
          refine ⟨17122763686519441003909961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11415175791012960669273307 17122763686519441003909961)
          ·
            refine ⟨12842072764889580752932471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17122763686519441003909961 12842072764889580752932471)
            ·
              refine ⟨19263109147334371129398707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12842072764889580752932471 19263109147334371129398707)
              ·
                refine ⟨28894663721001556694098061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19263109147334371129398707 28894663721001556694098061)
                ·
                  refine ⟨10835498895375583760286773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28894663721001556694098061 10835498895375583760286773)
                  ·
                    refine ⟨1015828021441460977526885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10835498895375583760286773 1015828021441460977526885)
                    ·
                      rfl

theorem cell22_2967477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_2967477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2967477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2967477 prefixEnd_2967477 := by exact prefixLift 2967477
  have htrace : WordTrace (prefixWord ++ tailWord_2967477) baseStart_2967477 baseEnd_2967477 := by
    simpa [prefixWord, tailWord_2967477, baseEnd_2967477] using wordTrace_append hprefix tailTrace_2967477
  have hstable : (prefixWord ++ tailWord_2967477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2967477).length < 2 ^ (prefixWord ++ tailWord_2967477).sum := by decide
  have hdescent : baseEnd_2967477 < baseStart_2967477 := by decide
  rcases family_descends (prefixWord ++ tailWord_2967477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2967496 : List Nat := [2, 1, 3, 1, 4, 1, 4, 2, 4]
def baseStart_2967496 : Nat := 118140960795 + 2967496 * 2 ^ 59
def prefixEnd_2967496 : Nat := 4983230072969 + 3 ^ 40 * 2967496 * 2
def baseEnd_2967496 : Nat := 338611508509917087100609

theorem tailTrace_2967496 : CollatzResearch.WordTrace tailWord_2967496 prefixEnd_2967496 338611508509917087100609 := by
  unfold tailWord_2967496
  simp only [CollatzResearch.WordTrace]
  refine ⟨54116735428638137406433171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72155647238184183208577561 54116735428638137406433171)
  ·
    refine ⟨81175103142957206109649757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54116735428638137406433171 81175103142957206109649757)
    ·
      refine ⟨30440663678608952291118659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81175103142957206109649757 30440663678608952291118659)
      ·
        refine ⟨45660995517913428436677989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30440663678608952291118659 45660995517913428436677989)
        ·
          refine ⟨8561436659608767831877123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45660995517913428436677989 8561436659608767831877123)
          ·
            refine ⟨12842154989413151747815685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8561436659608767831877123 12842154989413151747815685)
            ·
              refine ⟨2407904060514965952715441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12842154989413151747815685 2407904060514965952715441)
              ·
                refine ⟨1805928045386224464536581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2407904060514965952715441 1805928045386224464536581)
                ·
                  refine ⟨338611508509917087100609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1805928045386224464536581 338611508509917087100609)
                  ·
                    rfl

theorem cell22_2967496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 4, 2, 4].length) (baseStart_2967496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2967496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2967496 prefixEnd_2967496 := by exact prefixLift 2967496
  have htrace : WordTrace (prefixWord ++ tailWord_2967496) baseStart_2967496 baseEnd_2967496 := by
    simpa [prefixWord, tailWord_2967496, baseEnd_2967496] using wordTrace_append hprefix tailTrace_2967496
  have hstable : (prefixWord ++ tailWord_2967496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2967496).length < 2 ^ (prefixWord ++ tailWord_2967496).sum := by decide
  have hdescent : baseEnd_2967496 < baseStart_2967496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2967496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2967552 : List Nat := [2, 1, 1, 2, 1, 1, 1, 8, 5]
def baseStart_2967552 : Nat := 118140960795 + 2967552 * 2 ^ 59
def prefixEnd_2967552 : Nat := 4983230072969 + 3 ^ 40 * 2967552 * 2
def baseEnd_2967552 : Nat := 338617898491395260633885

theorem tailTrace_2967552 : CollatzResearch.WordTrace tailWord_2967552 prefixEnd_2967552 338617898491395260633885 := by
  unfold tailWord_2967552
  simp only [CollatzResearch.WordTrace]
  refine ⟨54117756672536698188452455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72157008896715597584603273 54117756672536698188452455)
  ·
    refine ⟨81176635008805047282678683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54117756672536698188452455 81176635008805047282678683)
    ·
      refine ⟨121764952513207570924018025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81176635008805047282678683 121764952513207570924018025)
      ·
        refine ⟨91323714384905678193013519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121764952513207570924018025 91323714384905678193013519)
        ·
          refine ⟨136985571577358517289520279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91323714384905678193013519 136985571577358517289520279)
          ·
            refine ⟨205478357366037775934280419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136985571577358517289520279 205478357366037775934280419)
            ·
              refine ⟨308217536049056663901420629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205478357366037775934280419 308217536049056663901420629)
              ·
                refine ⟨3611924250574882780094773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 308217536049056663901420629 3611924250574882780094773)
                ·
                  refine ⟨338617898491395260633885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3611924250574882780094773 338617898491395260633885)
                  ·
                    rfl

theorem cell22_2967552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 8, 5].length) (baseStart_2967552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2967552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2967552 prefixEnd_2967552 := by exact prefixLift 2967552
  have htrace : WordTrace (prefixWord ++ tailWord_2967552) baseStart_2967552 baseEnd_2967552 := by
    simpa [prefixWord, tailWord_2967552, baseEnd_2967552] using wordTrace_append hprefix tailTrace_2967552
  have hstable : (prefixWord ++ tailWord_2967552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2967552).length < 2 ^ (prefixWord ++ tailWord_2967552).sum := by decide
  have hdescent : baseEnd_2967552 < baseStart_2967552 := by decide
  rcases family_descends (prefixWord ++ tailWord_2967552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2967642 : List Nat := [3, 1, 1, 2, 1, 1, 3, 10]
def baseStart_2967642 : Nat := 118140960795 + 2967642 * 2 ^ 59
def prefixEnd_2967642 : Nat := 4983230072969 + 3 ^ 40 * 2967642 * 2
def baseEnd_2967642 : Nat := 112876056034828394127931

theorem tailTrace_2967642 : CollatzResearch.WordTrace tailWord_2967642 prefixEnd_2967642 112876056034828394127931 := by
  unfold tailWord_2967642
  simp only [CollatzResearch.WordTrace]
  refine ⟨27059698978686835436920295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72159197276498227831787453 27059698978686835436920295)
  ·
    refine ⟨40589548468030253155380443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27059698978686835436920295 40589548468030253155380443)
    ·
      refine ⟨60884322702045379733070665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40589548468030253155380443 60884322702045379733070665)
      ·
        refine ⟨45663242026534034799802999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60884322702045379733070665 45663242026534034799802999)
        ·
          refine ⟨68494863039801052199704499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45663242026534034799802999 68494863039801052199704499)
          ·
            refine ⟨102742294559701578299556749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68494863039801052199704499 102742294559701578299556749)
            ·
              refine ⟨38528360459888091862333781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102742294559701578299556749 38528360459888091862333781)
              ·
                refine ⟨112876056034828394127931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 38528360459888091862333781 112876056034828394127931)
                ·
                  rfl

theorem cell22_2967642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 10].length) (baseStart_2967642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2967642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2967642 prefixEnd_2967642 := by exact prefixLift 2967642
  have htrace : WordTrace (prefixWord ++ tailWord_2967642) baseStart_2967642 baseEnd_2967642 := by
    simpa [prefixWord, tailWord_2967642, baseEnd_2967642] using wordTrace_append hprefix tailTrace_2967642
  have hstable : (prefixWord ++ tailWord_2967642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2967642).length < 2 ^ (prefixWord ++ tailWord_2967642).sum := by decide
  have hdescent : baseEnd_2967642 < baseStart_2967642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2967642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2967650 : List Nat := [3, 3, 2, 2, 2, 1, 3, 1, 1, 4]
def baseStart_2967650 : Nat := 118140960795 + 2967650 * 2 ^ 59
def prefixEnd_2967650 : Nat := 4983230072969 + 3 ^ 40 * 2967650 * 2
def baseEnd_2967650 : Nat := 1015887242876946192951355

theorem tailTrace_2967650 : CollatzResearch.WordTrace tailWord_2967650 prefixEnd_2967650 1015887242876946192951355 := by
  unfold tailWord_2967650
  simp only [CollatzResearch.WordTrace]
  refine ⟨27059771924679589778493101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72159391799145572742648269 27059771924679589778493101)
  ·
    refine ⟨10147414471754846166934913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27059771924679589778493101 10147414471754846166934913)
    ·
      refine ⟨7610560853816134625201185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10147414471754846166934913 7610560853816134625201185)
      ·
        refine ⟨5707920640362100968900889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7610560853816134625201185 5707920640362100968900889)
        ·
          refine ⟨4280940480271575726675667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5707920640362100968900889 4280940480271575726675667)
          ·
            refine ⟨6421410720407363590013501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4280940480271575726675667 6421410720407363590013501)
            ·
              refine ⟨2408029020152761346255063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6421410720407363590013501 2408029020152761346255063)
              ·
                refine ⟨3612043530229142019382595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2408029020152761346255063 3612043530229142019382595)
                ·
                  refine ⟨5418065295343713029073893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3612043530229142019382595 5418065295343713029073893)
                  ·
                    refine ⟨1015887242876946192951355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5418065295343713029073893 1015887242876946192951355)
                    ·
                      rfl

theorem cell22_2967650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_2967650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2967650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2967650 prefixEnd_2967650 := by exact prefixLift 2967650
  have htrace : WordTrace (prefixWord ++ tailWord_2967650) baseStart_2967650 baseEnd_2967650 := by
    simpa [prefixWord, tailWord_2967650, baseEnd_2967650] using wordTrace_append hprefix tailTrace_2967650
  have hstable : (prefixWord ++ tailWord_2967650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2967650).length < 2 ^ (prefixWord ++ tailWord_2967650).sum := by decide
  have hdescent : baseEnd_2967650 < baseStart_2967650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2967650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2967674 : List Nat := [3, 1, 1, 1, 1, 1, 1, 1, 9, 3]
def baseStart_2967674 : Nat := 118140960795 + 2967674 * 2 ^ 59
def prefixEnd_2967674 : Nat := 4983230072969 + 3 ^ 40 * 2967674 * 2
def baseEnd_2967674 : Nat := 1015895458567418130351281

theorem tailTrace_2967674 : CollatzResearch.WordTrace tailWord_2967674 prefixEnd_2967674 1015895458567418130351281 := by
  unfold tailWord_2967674
  simp only [CollatzResearch.WordTrace]
  refine ⟨27059990762657852803211519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72159975367087607475230717 27059990762657852803211519)
  ·
    refine ⟨40589986143986779204817279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27059990762657852803211519 40589986143986779204817279)
    ·
      refine ⟨60884979215980168807225919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40589986143986779204817279 60884979215980168807225919)
      ·
        refine ⟨91327468823970253210838879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60884979215980168807225919 91327468823970253210838879)
        ·
          refine ⟨136991203235955379816258319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91327468823970253210838879 136991203235955379816258319)
          ·
            refine ⟨205486804853933069724387479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136991203235955379816258319 205486804853933069724387479)
            ·
              refine ⟨308230207280899604586581219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205486804853933069724387479 308230207280899604586581219)
              ·
                refine ⟨462345310921349406879871829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 308230207280899604586581219 462345310921349406879871829)
                ·
                  refine ⟨2709054556179781680936749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 462345310921349406879871829 2709054556179781680936749)
                  ·
                    refine ⟨1015895458567418130351281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2709054556179781680936749 1015895458567418130351281)
                    ·
                      rfl

theorem cell22_2967674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 9, 3].length) (baseStart_2967674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2967674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2967674 prefixEnd_2967674 := by exact prefixLift 2967674
  have htrace : WordTrace (prefixWord ++ tailWord_2967674) baseStart_2967674 baseEnd_2967674 := by
    simpa [prefixWord, tailWord_2967674, baseEnd_2967674] using wordTrace_append hprefix tailTrace_2967674
  have hstable : (prefixWord ++ tailWord_2967674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2967674).length < 2 ^ (prefixWord ++ tailWord_2967674).sum := by decide
  have hdescent : baseEnd_2967674 < baseStart_2967674 := by decide
  rcases family_descends (prefixWord ++ tailWord_2967674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2967725 : List Nat := [1, 5, 2, 1, 2, 1, 2, 4, 1, 3]
def baseStart_2967725 : Nat := 118140960795 + 2967725 * 2 ^ 59
def prefixEnd_2967725 : Nat := 4983230072969 + 3 ^ 40 * 2967725 * 2
def baseEnd_2967725 : Nat := 1015912916909670997326125

theorem tailTrace_2967725 : CollatzResearch.WordTrace tailWord_2967725 prefixEnd_2967725 1015912916909670997326125 := by
  unfold tailWord_2967725
  simp only [CollatzResearch.WordTrace]
  refine ⟨108241823173446646922952629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72161215448964431281968419 108241823173446646922952629)
  ·
    refine ⟨10147670922510623149026809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 108241823173446646922952629 10147670922510623149026809)
    ·
      refine ⟨7610753191882967361770107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10147670922510623149026809 7610753191882967361770107)
      ·
        refine ⟨11416129787824451042655161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7610753191882967361770107 11416129787824451042655161)
        ·
          refine ⟨8562097340868338281991371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11416129787824451042655161 8562097340868338281991371)
          ·
            refine ⟨12843146011302507422987057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8562097340868338281991371 12843146011302507422987057)
            ·
              refine ⟨9632359508476880567240293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12843146011302507422987057 9632359508476880567240293)
              ·
                refine ⟨1806067407839415106357555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9632359508476880567240293 1806067407839415106357555)
                ·
                  refine ⟨2709101111759122659536333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1806067407839415106357555 2709101111759122659536333)
                  ·
                    refine ⟨1015912916909670997326125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2709101111759122659536333 1015912916909670997326125)
                    ·
                      rfl

theorem cell22_2967725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_2967725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2967725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2967725 prefixEnd_2967725 := by exact prefixLift 2967725
  have htrace : WordTrace (prefixWord ++ tailWord_2967725) baseStart_2967725 baseEnd_2967725 := by
    simpa [prefixWord, tailWord_2967725, baseEnd_2967725] using wordTrace_append hprefix tailTrace_2967725
  have hstable : (prefixWord ++ tailWord_2967725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2967725).length < 2 ^ (prefixWord ++ tailWord_2967725).sum := by decide
  have hdescent : baseEnd_2967725 < baseStart_2967725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2967725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2967749 : List Nat := [1, 3, 1, 1, 1, 1, 6, 2, 6]
def baseStart_2967749 : Nat := 118140960795 + 2967749 * 2 ^ 59
def prefixEnd_2967749 : Nat := 4983230072969 + 3 ^ 40 * 2967749 * 2
def baseEnd_2967749 : Nat := 338640377533380978242017

theorem tailTrace_2967749 : CollatzResearch.WordTrace tailWord_2967749 prefixEnd_2967749 338640377533380978242017 := by
  unfold tailWord_2967749
  simp only [CollatzResearch.WordTrace]
  refine ⟨108242698525359699021826301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72161799016906466014550867 108242698525359699021826301)
  ·
    refine ⟨40591011947009887133184863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108242698525359699021826301 40591011947009887133184863)
    ·
      refine ⟨60886517920514830699777295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40591011947009887133184863 60886517920514830699777295)
      ·
        refine ⟨91329776880772246049665943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60886517920514830699777295 91329776880772246049665943)
        ·
          refine ⟨136994665321158369074498915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91329776880772246049665943 136994665321158369074498915)
          ·
            refine ⟨205491997981737553611748373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136994665321158369074498915 205491997981737553611748373)
            ·
              refine ⟨9632437405393947825550705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 205491997981737553611748373 9632437405393947825550705)
              ·
                refine ⟨7224328054045460869163029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9632437405393947825550705 7224328054045460869163029)
                ·
                  refine ⟨338640377533380978242017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7224328054045460869163029 338640377533380978242017)
                  ·
                    rfl

theorem cell22_2967749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 2, 6].length) (baseStart_2967749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2967749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2967749 prefixEnd_2967749 := by exact prefixLift 2967749
  have htrace : WordTrace (prefixWord ++ tailWord_2967749) baseStart_2967749 baseEnd_2967749 := by
    simpa [prefixWord, tailWord_2967749, baseEnd_2967749] using wordTrace_append hprefix tailTrace_2967749
  have hstable : (prefixWord ++ tailWord_2967749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2967749).length < 2 ^ (prefixWord ++ tailWord_2967749).sum := by decide
  have hdescent : baseEnd_2967749 < baseStart_2967749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2967749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2967783 : List Nat := [1, 1, 5, 3, 1, 3, 1, 1, 6]
def baseStart_2967783 : Nat := 118140960795 + 2967783 * 2 ^ 59
def prefixEnd_2967783 : Nat := 4983230072969 + 3 ^ 40 * 2967783 * 2
def baseEnd_2967783 : Nat := 338644257164992726458649

theorem tailTrace_2967783 : CollatzResearch.WordTrace tailWord_2967783 prefixEnd_2967783 338644257164992726458649 := by
  unfold tailWord_2967783
  simp only [CollatzResearch.WordTrace]
  refine ⟨108243938607236522828564003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72162625738157681885709335 108243938607236522828564003)
  ·
    refine ⟨162365907910854784242846005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108243938607236522828564003 162365907910854784242846005)
    ·
      refine ⟨15221803866642636022766813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 162365907910854784242846005 15221803866642636022766813)
      ·
        refine ⟨5708176449990988508537555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15221803866642636022766813 5708176449990988508537555)
        ·
          refine ⟨8562264674986482762806333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5708176449990988508537555 8562264674986482762806333)
          ·
            refine ⟨3210849253119931036052375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8562264674986482762806333 3210849253119931036052375)
            ·
              refine ⟨4816273879679896554078563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3210849253119931036052375 4816273879679896554078563)
              ·
                refine ⟨7224410819519844831117845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4816273879679896554078563 7224410819519844831117845)
                ·
                  refine ⟨338644257164992726458649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7224410819519844831117845 338644257164992726458649)
                  ·
                    rfl

theorem cell22_2967783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 1, 6].length) (baseStart_2967783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2967783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2967783 prefixEnd_2967783 := by exact prefixLift 2967783
  have htrace : WordTrace (prefixWord ++ tailWord_2967783) baseStart_2967783 baseEnd_2967783 := by
    simpa [prefixWord, tailWord_2967783, baseEnd_2967783] using wordTrace_append hprefix tailTrace_2967783
  have hstable : (prefixWord ++ tailWord_2967783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2967783).length < 2 ^ (prefixWord ++ tailWord_2967783).sum := by decide
  have hdescent : baseEnd_2967783 < baseStart_2967783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2967783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2967860 : List Nat := [2, 5, 1, 1, 1, 3, 1, 2, 3, 3]
def baseStart_2967860 : Nat := 118140960795 + 2967860 * 2 ^ 59
def prefixEnd_2967860 : Nat := 4983230072969 + 3 ^ 40 * 2967860 * 2
def baseEnd_2967860 : Nat := 1015959130168575645200711

theorem tailTrace_2967860 : CollatzResearch.WordTrace tailWord_2967860 prefixEnd_2967860 1015959130168575645200711 := by
  unfold tailWord_2967860
  simp only [CollatzResearch.WordTrace]
  refine ⟨54123373513978782489558517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72164498018638376652744689 54123373513978782489558517)
  ·
    refine ⟨5074066266935510858396111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54123373513978782489558517 5074066266935510858396111)
    ·
      refine ⟨7611099400403266287594167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5074066266935510858396111 7611099400403266287594167)
      ·
        refine ⟨11416649100604899431391251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7611099400403266287594167 11416649100604899431391251)
        ·
          refine ⟨17124973650907349147086877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11416649100604899431391251 17124973650907349147086877)
          ·
            refine ⟨6421865119090255930157579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17124973650907349147086877 6421865119090255930157579)
            ·
              refine ⟨9632797678635383895236369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6421865119090255930157579 9632797678635383895236369)
              ·
                refine ⟨7224598258976537921427277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9632797678635383895236369 7224598258976537921427277)
                ·
                  refine ⟨2709224347116201720535229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7224598258976537921427277 2709224347116201720535229)
                  ·
                    refine ⟨1015959130168575645200711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2709224347116201720535229 1015959130168575645200711)
                    ·
                      rfl

theorem cell22_2967860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_2967860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2967860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2967860 prefixEnd_2967860 := by exact prefixLift 2967860
  have htrace : WordTrace (prefixWord ++ tailWord_2967860) baseStart_2967860 baseEnd_2967860 := by
    simpa [prefixWord, tailWord_2967860, baseEnd_2967860] using wordTrace_append hprefix tailTrace_2967860
  have hstable : (prefixWord ++ tailWord_2967860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2967860).length < 2 ^ (prefixWord ++ tailWord_2967860).sum := by decide
  have hdescent : baseEnd_2967860 < baseStart_2967860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2967860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2967886 : List Nat := [4, 1, 1, 1, 1, 1, 2, 2, 5, 4]
def baseStart_2967886 : Nat := 118140960795 + 2967886 * 2 ^ 59
def prefixEnd_2967886 : Nat := 4983230072969 + 3 ^ 40 * 2967886 * 2
def baseEnd_2967886 : Nat := 1015968030499920244050631

theorem tailTrace_2967886 : CollatzResearch.WordTrace tailWord_2967886 prefixEnd_2967886 1015968030499920244050631 := by
  unfold tailWord_2967886
  simp only [CollatzResearch.WordTrace]
  refine ⟨13530961915732921427445439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72165130217242247613042341 13530961915732921427445439)
  ·
    refine ⟨20296442873599382141168159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13530961915732921427445439 20296442873599382141168159)
    ·
      refine ⟨30444664310399073211752239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20296442873599382141168159 30444664310399073211752239)
      ·
        refine ⟨45666996465598609817628359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30444664310399073211752239 45666996465598609817628359)
        ·
          refine ⟨68500494698397914726442539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45666996465598609817628359 68500494698397914726442539)
          ·
            refine ⟨102750742047596872089663809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68500494698397914726442539 102750742047596872089663809)
            ·
              refine ⟨77063056535697654067247857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102750742047596872089663809 77063056535697654067247857)
              ·
                refine ⟨57797292401773240550435893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77063056535697654067247857 57797292401773240550435893)
                ·
                  refine ⟨5418496162666241301603365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57797292401773240550435893 5418496162666241301603365)
                  ·
                    refine ⟨1015968030499920244050631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5418496162666241301603365 1015968030499920244050631)
                    ·
                      rfl

theorem cell22_2967886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 5, 4].length) (baseStart_2967886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2967886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2967886 prefixEnd_2967886 := by exact prefixLift 2967886
  have htrace : WordTrace (prefixWord ++ tailWord_2967886) baseStart_2967886 baseEnd_2967886 := by
    simpa [prefixWord, tailWord_2967886, baseEnd_2967886] using wordTrace_append hprefix tailTrace_2967886
  have hstable : (prefixWord ++ tailWord_2967886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2967886).length < 2 ^ (prefixWord ++ tailWord_2967886).sum := by decide
  have hdescent : baseEnd_2967886 < baseStart_2967886 := by decide
  rcases family_descends (prefixWord ++ tailWord_2967886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2967931 : List Nat := [1, 1, 1, 1, 1, 7, 2, 1, 1, 6]
def baseStart_2967931 : Nat := 118140960795 + 2967931 * 2 ^ 59
def prefixEnd_2967931 : Nat := 4983230072969 + 3 ^ 40 * 2967931 * 2
def baseEnd_2967931 : Nat := 1015983434919555126675493

theorem tailTrace_2967931 : CollatzResearch.WordTrace tailWord_2967931 prefixEnd_2967931 1015983434919555126675493 := by
  unfold tailWord_2967931
  simp only [CollatzResearch.WordTrace]
  refine ⟨108249336610700344104951647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72166224407133562736634431 108249336610700344104951647)
  ·
    refine ⟨162374004916050516157427471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108249336610700344104951647 162374004916050516157427471)
    ·
      refine ⟨243561007374075774236141207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162374004916050516157427471 243561007374075774236141207)
      ·
        refine ⟨365341511061113661354211811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243561007374075774236141207 365341511061113661354211811)
        ·
          refine ⟨548012266591670492031317717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 365341511061113661354211811 548012266591670492031317717)
          ·
            refine ⟨12844037498242277156984009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 548012266591670492031317717 12844037498242277156984009)
            ·
              refine ⟨9633028123681707867738007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12844037498242277156984009 9633028123681707867738007)
              ·
                refine ⟨14449542185522561801607011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9633028123681707867738007 14449542185522561801607011)
                ·
                  refine ⟨21674313278283842702410517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14449542185522561801607011 21674313278283842702410517)
                  ·
                    refine ⟨1015983434919555126675493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21674313278283842702410517 1015983434919555126675493)
                    ·
                      rfl

theorem cell22_2967931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 1, 1, 6].length) (baseStart_2967931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2967931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2967931 prefixEnd_2967931 := by exact prefixLift 2967931
  have htrace : WordTrace (prefixWord ++ tailWord_2967931) baseStart_2967931 baseEnd_2967931 := by
    simpa [prefixWord, tailWord_2967931, baseEnd_2967931] using wordTrace_append hprefix tailTrace_2967931
  have hstable : (prefixWord ++ tailWord_2967931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2967931).length < 2 ^ (prefixWord ++ tailWord_2967931).sum := by decide
  have hdescent : baseEnd_2967931 < baseStart_2967931 := by decide
  rcases family_descends (prefixWord ++ tailWord_2967931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2967933 : List Nat := [1, 4, 1, 1, 2, 3, 1, 2, 4, 3]
def baseStart_2967933 : Nat := 118140960795 + 2967933 * 2 ^ 59
def prefixEnd_2967933 : Nat := 4983230072969 + 3 ^ 40 * 2967933 * 2
def baseEnd_2967933 : Nat := 1015984119560427788125487

theorem tailTrace_2967933 : CollatzResearch.WordTrace tailWord_2967933 prefixEnd_2967933 1015984119560427788125487 := by
  unfold tailWord_2967933
  simp only [CollatzResearch.WordTrace]
  refine ⟨108249409556693098446524453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72166273037795398964349635 108249409556693098446524453)
  ·
    refine ⟨20296764291879955958723335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108249409556693098446524453 20296764291879955958723335)
    ·
      refine ⟨30445146437819933938085003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20296764291879955958723335 30445146437819933938085003)
      ·
        refine ⟨45667719656729900907127505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30445146437819933938085003 45667719656729900907127505)
        ·
          refine ⟨34250789742547425680345629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45667719656729900907127505 34250789742547425680345629)
          ·
            refine ⟨12844046153455284630129611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34250789742547425680345629 12844046153455284630129611)
            ·
              refine ⟨19266069230182926945194417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12844046153455284630129611 19266069230182926945194417)
              ·
                refine ⟨14449551922637195208895813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19266069230182926945194417 14449551922637195208895813)
                ·
                  refine ⟨2709290985494474101667965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14449551922637195208895813 2709290985494474101667965)
                  ·
                    refine ⟨1015984119560427788125487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2709290985494474101667965 1015984119560427788125487)
                    ·
                      rfl

theorem cell22_2967933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 2, 4, 3].length) (baseStart_2967933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2967933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2967933 prefixEnd_2967933 := by exact prefixLift 2967933
  have htrace : WordTrace (prefixWord ++ tailWord_2967933) baseStart_2967933 baseEnd_2967933 := by
    simpa [prefixWord, tailWord_2967933, baseEnd_2967933] using wordTrace_append hprefix tailTrace_2967933
  have hstable : (prefixWord ++ tailWord_2967933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2967933).length < 2 ^ (prefixWord ++ tailWord_2967933).sum := by decide
  have hdescent : baseEnd_2967933 < baseStart_2967933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2967933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2967948 : List Nat := [2, 2, 1, 2, 1, 5, 1, 2, 2, 4]
def baseStart_2967948 : Nat := 118140960795 + 2967948 * 2 ^ 59
def prefixEnd_2967948 : Nat := 4983230072969 + 3 ^ 40 * 2967948 * 2
def baseEnd_2967948 : Nat := 1015989254366972749000441

theorem tailTrace_2967948 : CollatzResearch.WordTrace tailWord_2967948 prefixEnd_2967948 1015989254366972749000441 := by
  unfold tailWord_2967948
  simp only [CollatzResearch.WordTrace]
  refine ⟨54124978325819378004160249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72166637767759170672213665 54124978325819378004160249)
  ·
    refine ⟨40593733744364533503120187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54124978325819378004160249 40593733744364533503120187)
    ·
      refine ⟨60890600616546800254680281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40593733744364533503120187 60890600616546800254680281)
      ·
        refine ⟨45667950462410100191010211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60890600616546800254680281 45667950462410100191010211)
        ·
          refine ⟨68501925693615150286515317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45667950462410100191010211 68501925693615150286515317)
          ·
            refine ⟨6422055533776420339360811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 68501925693615150286515317 6422055533776420339360811)
            ·
              refine ⟨9633083300664630509041217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6422055533776420339360811 9633083300664630509041217)
              ·
                refine ⟨7224812475498472881780913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9633083300664630509041217 7224812475498472881780913)
                ·
                  refine ⟨5418609356623854661335685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7224812475498472881780913 5418609356623854661335685)
                  ·
                    refine ⟨1015989254366972749000441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5418609356623854661335685 1015989254366972749000441)
                    ·
                      rfl

theorem cell22_2967948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 2, 2, 4].length) (baseStart_2967948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2967948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2967948 prefixEnd_2967948 := by exact prefixLift 2967948
  have htrace : WordTrace (prefixWord ++ tailWord_2967948) baseStart_2967948 baseEnd_2967948 := by
    simpa [prefixWord, tailWord_2967948, baseEnd_2967948] using wordTrace_append hprefix tailTrace_2967948
  have hstable : (prefixWord ++ tailWord_2967948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2967948).length < 2 ^ (prefixWord ++ tailWord_2967948).sum := by decide
  have hdescent : baseEnd_2967948 < baseStart_2967948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2967948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2967950 : List Nat := [4, 1, 1, 4, 1, 1, 2, 1, 4, 3]
def baseStart_2967950 : Nat := 118140960795 + 2967950 * 2 ^ 59
def prefixEnd_2967950 : Nat := 4983230072969 + 3 ^ 40 * 2967950 * 2
def baseEnd_2967950 : Nat := 1015989939007845410450435

theorem tailTrace_2967950 : CollatzResearch.WordTrace tailWord_2967950 prefixEnd_2967950 1015989939007845410450435 := by
  unfold tailWord_2967950
  simp only [CollatzResearch.WordTrace]
  refine ⟨13531253699703938793736663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72166686398421006899928869 13531253699703938793736663)
  ·
    refine ⟨20296880549555908190604995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13531253699703938793736663 20296880549555908190604995)
    ·
      refine ⟨30445320824333862285907493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20296880549555908190604995 30445320824333862285907493)
      ·
        refine ⟨5708497654562599178607655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30445320824333862285907493 5708497654562599178607655)
        ·
          refine ⟨8562746481843898767911483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5708497654562599178607655 8562746481843898767911483)
          ·
            refine ⟨12844119722765848151867225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8562746481843898767911483 12844119722765848151867225)
            ·
              refine ⟨9633089792074386113900419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12844119722765848151867225 9633089792074386113900419)
              ·
                refine ⟨14449634688111579170850629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9633089792074386113900419 14449634688111579170850629)
                ·
                  refine ⟨2709306504020921094534493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14449634688111579170850629 2709306504020921094534493)
                  ·
                    refine ⟨1015989939007845410450435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2709306504020921094534493 1015989939007845410450435)
                    ·
                      rfl

theorem cell22_2967950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 1, 4, 3].length) (baseStart_2967950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2967950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2967950 prefixEnd_2967950 := by exact prefixLift 2967950
  have htrace : WordTrace (prefixWord ++ tailWord_2967950) baseStart_2967950 baseEnd_2967950 := by
    simpa [prefixWord, tailWord_2967950, baseEnd_2967950] using wordTrace_append hprefix tailTrace_2967950
  have hstable : (prefixWord ++ tailWord_2967950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2967950).length < 2 ^ (prefixWord ++ tailWord_2967950).sum := by decide
  have hdescent : baseEnd_2967950 < baseStart_2967950 := by decide
  rcases family_descends (prefixWord ++ tailWord_2967950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2967958 : List Nat := [5, 3, 1, 2, 2, 1, 2, 1, 5]
def baseStart_2967958 : Nat := 118140960795 + 2967958 * 2 ^ 59
def prefixEnd_2967958 : Nat := 4983230072969 + 3 ^ 40 * 2967958 * 2
def baseEnd_2967958 : Nat := 338664225857112018750137

theorem tailTrace_2967958 : CollatzResearch.WordTrace tailWord_2967958 prefixEnd_2967958 338664225857112018750137 := by
  unfold tailWord_2967958
  simp only [CollatzResearch.WordTrace]
  refine ⟨6765645086350157982261533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72166880921068351810789685 6765645086350157982261533)
  ·
    refine ⟨2537116907381309243348075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6765645086350157982261533 2537116907381309243348075)
    ·
      refine ⟨3805675361071963865022113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2537116907381309243348075 3805675361071963865022113)
      ·
        refine ⟨2854256520803972898766585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3805675361071963865022113 2854256520803972898766585)
        ·
          refine ⟨2140692390602979674074939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2854256520803972898766585 2140692390602979674074939)
          ·
            refine ⟨3211038585904469511112409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2140692390602979674074939 3211038585904469511112409)
            ·
              refine ⟨2408278939428352133334307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3211038585904469511112409 2408278939428352133334307)
              ·
                refine ⟨3612418409142528200001461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2408278939428352133334307 3612418409142528200001461)
                ·
                  refine ⟨338664225857112018750137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3612418409142528200001461 338664225857112018750137)
                  ·
                    rfl

theorem cell22_2967958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_2967958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2967958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2967958 prefixEnd_2967958 := by exact prefixLift 2967958
  have htrace : WordTrace (prefixWord ++ tailWord_2967958) baseStart_2967958 baseEnd_2967958 := by
    simpa [prefixWord, tailWord_2967958, baseEnd_2967958] using wordTrace_append hprefix tailTrace_2967958
  have hstable : (prefixWord ++ tailWord_2967958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2967958).length < 2 ^ (prefixWord ++ tailWord_2967958).sum := by decide
  have hdescent : baseEnd_2967958 < baseStart_2967958 := by decide
  rcases family_descends (prefixWord ++ tailWord_2967958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968001 : List Nat := [1, 2, 7, 1, 1, 1, 2, 2, 2, 3]
def baseStart_2968001 : Nat := 118140960795 + 2968001 * 2 ^ 59
def prefixEnd_2968001 : Nat := 4983230072969 + 3 ^ 40 * 2968001 * 2
def baseEnd_2968001 : Nat := 1016007397350098277425279

theorem tailTrace_2968001 : CollatzResearch.WordTrace tailWord_2968001 prefixEnd_2968001 1016007397350098277425279 := by
  unfold tailWord_2968001
  simp only [CollatzResearch.WordTrace]
  refine ⟨108251889720446746059999857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72167926480297830706666571 108251889720446746059999857)
  ·
    refine ⟨81188917290335059544999893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108251889720446746059999857 81188917290335059544999893)
    ·
      refine ⟨1902865248992227958085935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 81188917290335059544999893 1902865248992227958085935)
      ·
        refine ⟨2854297873488341937128903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1902865248992227958085935 2854297873488341937128903)
        ·
          refine ⟨4281446810232512905693355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2854297873488341937128903 4281446810232512905693355)
          ·
            refine ⟨6422170215348769358540033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4281446810232512905693355 6422170215348769358540033)
            ·
              refine ⟨4816627661511577018905025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6422170215348769358540033 4816627661511577018905025)
              ·
                refine ⟨3612470746133682764178769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4816627661511577018905025 3612470746133682764178769)
                ·
                  refine ⟨2709353059600262073134077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3612470746133682764178769 2709353059600262073134077)
                  ·
                    refine ⟨1016007397350098277425279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2709353059600262073134077 1016007397350098277425279)
                    ·
                      rfl

theorem cell22_2968001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_2968001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2968001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2968001 prefixEnd_2968001 := by exact prefixLift 2968001
  have htrace : WordTrace (prefixWord ++ tailWord_2968001) baseStart_2968001 baseEnd_2968001 := by
    simpa [prefixWord, tailWord_2968001, baseEnd_2968001] using wordTrace_append hprefix tailTrace_2968001
  have hstable : (prefixWord ++ tailWord_2968001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968001).length < 2 ^ (prefixWord ++ tailWord_2968001).sum := by decide
  have hdescent : baseEnd_2968001 < baseStart_2968001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968008 : List Nat := [2, 1, 3, 1, 3, 2, 1, 4, 5]
def baseStart_2968008 : Nat := 118140960795 + 2968008 * 2 ^ 59
def prefixEnd_2968008 : Nat := 4983230072969 + 3 ^ 40 * 2968008 * 2
def baseEnd_2968008 : Nat := 338669931197717530833419

theorem tailTrace_2968008 : CollatzResearch.WordTrace tailWord_2968008 prefixEnd_2968008 338669931197717530833419 := by
  unfold tailWord_2968008
  simp only [CollatzResearch.WordTrace]
  refine ⟨54126072515710693127752339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72168096687614257503669785 54126072515710693127752339)
  ·
    refine ⟨81189108773566039691628509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54126072515710693127752339 81189108773566039691628509)
    ·
      refine ⟨30445915790087264884360691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81189108773566039691628509 30445915790087264884360691)
      ·
        refine ⟨45668873685130897326541037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30445915790087264884360691 45668873685130897326541037)
        ·
          refine ⟨17125827631924086497452889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45668873685130897326541037 17125827631924086497452889)
          ·
            refine ⟨12844370723943064873089667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17125827631924086497452889 12844370723943064873089667)
            ·
              refine ⟨19266556085914597309634501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12844370723943064873089667 19266556085914597309634501)
              ·
                refine ⟨3612479266108986995556469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19266556085914597309634501 3612479266108986995556469)
                ·
                  refine ⟨338669931197717530833419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3612479266108986995556469 338669931197717530833419)
                  ·
                    rfl

theorem cell22_2968008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 4, 5].length) (baseStart_2968008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2968008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2968008 prefixEnd_2968008 := by exact prefixLift 2968008
  have htrace : WordTrace (prefixWord ++ tailWord_2968008) baseStart_2968008 baseEnd_2968008 := by
    simpa [prefixWord, tailWord_2968008, baseEnd_2968008] using wordTrace_append hprefix tailTrace_2968008
  have hstable : (prefixWord ++ tailWord_2968008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968008).length < 2 ^ (prefixWord ++ tailWord_2968008).sum := by decide
  have hdescent : baseEnd_2968008 < baseStart_2968008 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968104 : List Nat := [2, 1, 5, 2, 1, 3, 1, 3, 4]
def baseStart_2968104 : Nat := 118140960795 + 2968104 * 2 ^ 59
def prefixEnd_2968104 : Nat := 4983230072969 + 3 ^ 40 * 2968104 * 2
def baseEnd_2968104 : Nat := 338680885451680114033321

theorem tailTrace_2968104 : CollatzResearch.WordTrace tailWord_2968104 prefixEnd_2968104 338680885451680114033321 := by
  unfold tailWord_2968104
  simp only [CollatzResearch.WordTrace]
  refine ⟨54127823219536797325499683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72170430959382396433999577 54127823219536797325499683)
  ·
    refine ⟨81191734829305195988249525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54127823219536797325499683 81191734829305195988249525)
    ·
      refine ⟨7611725140247362123898393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 81191734829305195988249525 7611725140247362123898393)
      ·
        refine ⟨5708793855185521592923795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7611725140247362123898393 5708793855185521592923795)
        ·
          refine ⟨8563190782778282389385693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5708793855185521592923795 8563190782778282389385693)
          ·
            refine ⟨3211196543541855896019635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8563190782778282389385693 3211196543541855896019635)
            ·
              refine ⟨4816794815312783844029453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3211196543541855896019635 4816794815312783844029453)
              ·
                refine ⟨1806298055742293941511045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4816794815312783844029453 1806298055742293941511045)
                ·
                  refine ⟨338680885451680114033321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1806298055742293941511045 338680885451680114033321)
                  ·
                    rfl

theorem cell22_2968104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 3, 4].length) (baseStart_2968104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2968104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2968104 prefixEnd_2968104 := by exact prefixLift 2968104
  have htrace : WordTrace (prefixWord ++ tailWord_2968104) baseStart_2968104 baseEnd_2968104 := by
    simpa [prefixWord, tailWord_2968104, baseEnd_2968104] using wordTrace_append hprefix tailTrace_2968104
  have hstable : (prefixWord ++ tailWord_2968104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968104).length < 2 ^ (prefixWord ++ tailWord_2968104).sum := by decide
  have hdescent : baseEnd_2968104 < baseStart_2968104 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968181 : List Nat := [1, 3, 4, 2, 2, 1, 1, 4, 1, 3]
def baseStart_2968181 : Nat := 118140960795 + 2968181 * 2 ^ 59
def prefixEnd_2968181 : Nat := 4983230072969 + 3 ^ 40 * 2968181 * 2
def baseEnd_2968181 : Nat := 1016069015028637807924727

theorem tailTrace_2968181 : CollatzResearch.WordTrace tailWord_2968181 prefixEnd_2968181 1016069015028637807924727 := by
  unfold tailWord_2968181
  simp only [CollatzResearch.WordTrace]
  refine ⟨108258454859794636801552397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72172303239863091201034931 108258454859794636801552397)
  ·
    refine ⟨40596920572422988800582149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108258454859794636801552397 40596920572422988800582149)
    ·
      refine ⟨7611922607329310400109153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40596920572422988800582149 7611922607329310400109153)
      ·
        refine ⟨5708941955496982800081865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7611922607329310400109153 5708941955496982800081865)
        ·
          refine ⟨4281706466622737100061399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5708941955496982800081865 4281706466622737100061399)
          ·
            refine ⟨6422559699934105650092099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4281706466622737100061399 6422559699934105650092099)
            ·
              refine ⟨9633839549901158475138149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6422559699934105650092099 9633839549901158475138149)
              ·
                refine ⟨1806344915606467214088403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9633839549901158475138149 1806344915606467214088403)
                ·
                  refine ⟨2709517373409700821132605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1806344915606467214088403 2709517373409700821132605)
                  ·
                    refine ⟨1016069015028637807924727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2709517373409700821132605 1016069015028637807924727)
                    ·
                      rfl

theorem cell22_2968181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_2968181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2968181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2968181 prefixEnd_2968181 := by exact prefixLift 2968181
  have htrace : WordTrace (prefixWord ++ tailWord_2968181) baseStart_2968181 baseEnd_2968181 := by
    simpa [prefixWord, tailWord_2968181, baseEnd_2968181] using wordTrace_append hprefix tailTrace_2968181
  have hstable : (prefixWord ++ tailWord_2968181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968181).length < 2 ^ (prefixWord ++ tailWord_2968181).sum := by decide
  have hdescent : baseEnd_2968181 < baseStart_2968181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968355 : List Nat := [1, 1, 1, 4, 2, 1, 1, 1, 5, 5]
def baseStart_2968355 : Nat := 118140960795 + 2968355 * 2 ^ 59
def prefixEnd_2968355 : Nat := 4983230072969 + 3 ^ 40 * 2968355 * 2
def baseEnd_2968355 : Nat := 1016128578784559354074193

theorem tailTrace_2968355 : CollatzResearch.WordTrace tailWord_2968355 prefixEnd_2968355 1016128578784559354074193 := by
  unfold tailWord_2968355
  simp only [CollatzResearch.WordTrace]
  refine ⟨108264801161164264518386519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72176534107442843012257679 108264801161164264518386519)
  ·
    refine ⟨162397201741746396777579779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108264801161164264518386519 162397201741746396777579779)
    ·
      refine ⟨243595802612619595166369669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162397201741746396777579779 243595802612619595166369669)
      ·
        refine ⟨45674212989866174093694313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 243595802612619595166369669 45674212989866174093694313)
        ·
          refine ⟨34255659742399630570270735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45674212989866174093694313 34255659742399630570270735)
          ·
            refine ⟨51383489613599445855406103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34255659742399630570270735 51383489613599445855406103)
            ·
              refine ⟨77075234420399168783109155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51383489613599445855406103 77075234420399168783109155)
              ·
                refine ⟨115612851630598753174663733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77075234420399168783109155 115612851630598753174663733)
                ·
                  refine ⟨10838704840368633110124725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 115612851630598753174663733 10838704840368633110124725)
                  ·
                    refine ⟨1016128578784559354074193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10838704840368633110124725 1016128578784559354074193)
                    ·
                      rfl

theorem cell22_2968355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 5, 5].length) (baseStart_2968355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2968355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2968355 prefixEnd_2968355 := by exact prefixLift 2968355
  have htrace : WordTrace (prefixWord ++ tailWord_2968355) baseStart_2968355 baseEnd_2968355 := by
    simpa [prefixWord, tailWord_2968355, baseEnd_2968355] using wordTrace_append hprefix tailTrace_2968355
  have hstable : (prefixWord ++ tailWord_2968355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968355).length < 2 ^ (prefixWord ++ tailWord_2968355).sum := by decide
  have hdescent : baseEnd_2968355 < baseStart_2968355 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968434 : List Nat := [3, 2, 1, 2, 1, 1, 4, 2, 3, 3]
def baseStart_2968434 : Nat := 118140960795 + 2968434 * 2 ^ 59
def prefixEnd_2968434 : Nat := 4983230072969 + 3 ^ 40 * 2968434 * 2
def baseEnd_2968434 : Nat := 1016155622099029481348951

theorem tailTrace_2968434 : CollatzResearch.WordTrace tailWord_2968434 prefixEnd_2968434 1016155622099029481348951 := by
  unfold tailWord_2968434
  simp only [CollatzResearch.WordTrace]
  refine ⟨27066920631969515252628089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72178455018585374007008237 27066920631969515252628089)
  ·
    refine ⟨20300190473977136439471067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27066920631969515252628089 20300190473977136439471067)
    ·
      refine ⟨30450285710965704659206601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20300190473977136439471067 30450285710965704659206601)
      ·
        refine ⟨22837714283224278494404951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30450285710965704659206601 22837714283224278494404951)
        ·
          refine ⟨34256571424836417741607427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22837714283224278494404951 34256571424836417741607427)
          ·
            refine ⟨51384857137254626612411141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34256571424836417741607427 51384857137254626612411141)
            ·
              refine ⟨9634660713235242489827089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51384857137254626612411141 9634660713235242489827089)
              ·
                refine ⟨7225995534926431867370317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9634660713235242489827089 7225995534926431867370317)
                ·
                  refine ⟨2709748325597411950263869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7225995534926431867370317 2709748325597411950263869)
                  ·
                    refine ⟨1016155622099029481348951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2709748325597411950263869 1016155622099029481348951)
                    ·
                      rfl

theorem cell22_2968434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 2, 3, 3].length) (baseStart_2968434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2968434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2968434 prefixEnd_2968434 := by exact prefixLift 2968434
  have htrace : WordTrace (prefixWord ++ tailWord_2968434) baseStart_2968434 baseEnd_2968434 := by
    simpa [prefixWord, tailWord_2968434, baseEnd_2968434] using wordTrace_append hprefix tailTrace_2968434
  have hstable : (prefixWord ++ tailWord_2968434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968434).length < 2 ^ (prefixWord ++ tailWord_2968434).sum := by decide
  have hdescent : baseEnd_2968434 < baseStart_2968434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968481 : List Nat := [1, 2, 3, 4, 1, 1, 4, 1, 5]
def baseStart_2968481 : Nat := 118140960795 + 2968481 * 2 ^ 59
def prefixEnd_2968481 : Nat := 4983230072969 + 3 ^ 40 * 2968481 * 2
def baseEnd_2968481 : Nat := 338723903719845675141269

theorem tailTrace_2968481 : CollatzResearch.WordTrace tailWord_2968481 prefixEnd_2968481 338723903719845675141269 := by
  unfold tailWord_2968481
  simp only [CollatzResearch.WordTrace]
  refine ⟨108269396758707788037473297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72179597839138525358315531 108269396758707788037473297)
  ·
    refine ⟨81202047569030841028104973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108269396758707788037473297 81202047569030841028104973)
    ·
      refine ⟨30450767838386565385539365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81202047569030841028104973 30450767838386565385539365)
      ·
        refine ⟨5709518969697481009788631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30450767838386565385539365 5709518969697481009788631)
        ·
          refine ⟨8564278454546221514682947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5709518969697481009788631 8564278454546221514682947)
          ·
            refine ⟨12846417681819332272024421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8564278454546221514682947 12846417681819332272024421)
            ·
              refine ⟨2408703315341124801004579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12846417681819332272024421 2408703315341124801004579)
              ·
                refine ⟨3613054973011687201506869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2408703315341124801004579 3613054973011687201506869)
                ·
                  refine ⟨338723903719845675141269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3613054973011687201506869 338723903719845675141269)
                  ·
                    rfl

theorem cell22_2968481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 4, 1, 5].length) (baseStart_2968481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2968481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2968481 prefixEnd_2968481 := by exact prefixLift 2968481
  have htrace : WordTrace (prefixWord ++ tailWord_2968481) baseStart_2968481 baseEnd_2968481 := by
    simpa [prefixWord, tailWord_2968481, baseEnd_2968481] using wordTrace_append hprefix tailTrace_2968481
  have hstable : (prefixWord ++ tailWord_2968481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968481).length < 2 ^ (prefixWord ++ tailWord_2968481).sum := by decide
  have hdescent : baseEnd_2968481 < baseStart_2968481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968522 : List Nat := [3, 1, 2, 1, 2, 1, 1, 2, 3, 6]
def baseStart_2968522 : Nat := 118140960795 + 2968522 * 2 ^ 59
def prefixEnd_2968522 : Nat := 4983230072969 + 3 ^ 40 * 2968522 * 2
def baseEnd_2968522 : Nat := 1016185746297426585148681

theorem tailTrace_2968522 : CollatzResearch.WordTrace tailWord_2968522 prefixEnd_2968522 1016185746297426585148681 := by
  unfold tailWord_2968522
  simp only [CollatzResearch.WordTrace]
  refine ⟨27067723037889813009928955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72180594767706168026477213 27067723037889813009928955)
  ·
    refine ⟨40601584556834719514893433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27067723037889813009928955 40601584556834719514893433)
    ·
      refine ⟨30451188417626039636170075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40601584556834719514893433 30451188417626039636170075)
      ·
        refine ⟨45676782626439059454255113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30451188417626039636170075 45676782626439059454255113)
        ·
          refine ⟨34257586969829294590691335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45676782626439059454255113 34257586969829294590691335)
          ·
            refine ⟨51386380454743941886037003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34257586969829294590691335 51386380454743941886037003)
            ·
              refine ⟨77079570682115912829055505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51386380454743941886037003 77079570682115912829055505)
              ·
                refine ⟨57809678011586934621791629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77079570682115912829055505 57809678011586934621791629)
                ·
                  refine ⟨21678629254345100483171861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57809678011586934621791629 21678629254345100483171861)
                  ·
                    refine ⟨1016185746297426585148681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21678629254345100483171861 1016185746297426585148681)
                    ·
                      rfl

theorem cell22_2968522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 3, 6].length) (baseStart_2968522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2968522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2968522 prefixEnd_2968522 := by exact prefixLift 2968522
  have htrace : WordTrace (prefixWord ++ tailWord_2968522) baseStart_2968522 baseEnd_2968522 := by
    simpa [prefixWord, tailWord_2968522, baseEnd_2968522] using wordTrace_append hprefix tailTrace_2968522
  have hstable : (prefixWord ++ tailWord_2968522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968522).length < 2 ^ (prefixWord ++ tailWord_2968522).sum := by decide
  have hdescent : baseEnd_2968522 < baseStart_2968522 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968526 : List Nat := [4, 1, 1, 1, 2, 4, 1, 4, 4]
def baseStart_2968526 : Nat := 118140960795 + 2968526 * 2 ^ 59
def prefixEnd_2968526 : Nat := 4983230072969 + 3 ^ 40 * 2968526 * 2
def baseEnd_2968526 : Nat := 338729038526390636016223

theorem tailTrace_2968526 : CollatzResearch.WordTrace tailWord_2968526 prefixEnd_2968526 338729038526390636016223 := by
  unfold tailWord_2968526
  simp only [CollatzResearch.WordTrace]
  refine ⟨13533879755443095090357679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72180692029029840481907621 13533879755443095090357679)
  ·
    refine ⟨20300819633164642635536519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13533879755443095090357679 20300819633164642635536519)
    ·
      refine ⟨30451229449746963953304779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20300819633164642635536519 30451229449746963953304779)
      ·
        refine ⟨45676844174620445929957169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30451229449746963953304779 45676844174620445929957169)
        ·
          refine ⟨34257633130965334447467877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45676844174620445929957169 34257633130965334447467877)
          ·
            refine ⟨6423306212056000208900227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34257633130965334447467877 6423306212056000208900227)
            ·
              refine ⟨9634959318084000313350341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6423306212056000208900227 9634959318084000313350341)
              ·
                refine ⟨1806554872140750058753189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9634959318084000313350341 1806554872140750058753189)
                ·
                  refine ⟨338729038526390636016223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1806554872140750058753189 338729038526390636016223)
                  ·
                    rfl

theorem cell22_2968526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 4, 4].length) (baseStart_2968526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2968526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2968526 prefixEnd_2968526 := by exact prefixLift 2968526
  have htrace : WordTrace (prefixWord ++ tailWord_2968526) baseStart_2968526 baseEnd_2968526 := by
    simpa [prefixWord, tailWord_2968526, baseEnd_2968526] using wordTrace_append hprefix tailTrace_2968526
  have hstable : (prefixWord ++ tailWord_2968526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968526).length < 2 ^ (prefixWord ++ tailWord_2968526).sum := by decide
  have hdescent : baseEnd_2968526 < baseStart_2968526 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968541 : List Nat := [1, 4, 3, 1, 2, 2, 2, 1, 1, 5]
def baseStart_2968541 : Nat := 118140960795 + 2968541 * 2 ^ 59
def prefixEnd_2968541 : Nat := 4983230072969 + 3 ^ 40 * 2968541 * 2
def baseEnd_2968541 : Nat := 1016192250385716868923623

theorem tailTrace_2968541 : CollatzResearch.WordTrace tailWord_2968541 prefixEnd_2968541 1016192250385716868923623 := by
  unfold tailWord_2968541
  simp only [CollatzResearch.WordTrace]
  refine ⟨108271585138490418284657477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72181056758993612189771651 108271585138490418284657477)
  ·
    refine ⟨20300922213466953428373277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108271585138490418284657477 20300922213466953428373277)
    ·
      refine ⟨7612845830050107535639979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20300922213466953428373277 7612845830050107535639979)
      ·
        refine ⟨11419268745075161303459969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7612845830050107535639979 11419268745075161303459969)
        ·
          refine ⟨8564451558806370977594977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11419268745075161303459969 8564451558806370977594977)
          ·
            refine ⟨6423338669104778233196233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8564451558806370977594977 6423338669104778233196233)
            ·
              refine ⟨4817504001828583674897175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6423338669104778233196233 4817504001828583674897175)
              ·
                refine ⟨7226256002742875512345763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4817504001828583674897175 7226256002742875512345763)
                ·
                  refine ⟨10839384004114313268518645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7226256002742875512345763 10839384004114313268518645)
                  ·
                    refine ⟨1016192250385716868923623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10839384004114313268518645 1016192250385716868923623)
                    ·
                      rfl

theorem cell22_2968541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_2968541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2968541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2968541 prefixEnd_2968541 := by exact prefixLift 2968541
  have htrace : WordTrace (prefixWord ++ tailWord_2968541) baseStart_2968541 baseEnd_2968541 := by
    simpa [prefixWord, tailWord_2968541, baseEnd_2968541] using wordTrace_append hprefix tailTrace_2968541
  have hstable : (prefixWord ++ tailWord_2968541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968541).length < 2 ^ (prefixWord ++ tailWord_2968541).sum := by decide
  have hdescent : baseEnd_2968541 < baseStart_2968541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968562 : List Nat := [3, 2, 1, 5, 2, 1, 2, 1, 1, 4]
def baseStart_2968562 : Nat := 118140960795 + 2968562 * 2 ^ 59
def prefixEnd_2968562 : Nat := 4983230072969 + 3 ^ 40 * 2968562 * 2
def baseEnd_2968562 : Nat := 1016199439114879814148559

theorem tailTrace_2968562 : CollatzResearch.WordTrace tailWord_2968562 prefixEnd_2968562 1016199439114879814148559 := by
  unfold tailWord_2968562
  simp only [CollatzResearch.WordTrace]
  refine ⟨27068087767853584717792985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72181567380942892580781293 27068087767853584717792985)
  ·
    refine ⟨20301065825890188538344739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27068087767853584717792985 20301065825890188538344739)
    ·
      refine ⟨30451598738835282807517109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20301065825890188538344739 30451598738835282807517109)
      ·
        refine ⟨2854837381765807763204729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30451598738835282807517109 2854837381765807763204729)
        ·
          refine ⟨2141128036324355822403547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2854837381765807763204729 2141128036324355822403547)
          ·
            refine ⟨3211692054486533733605321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2141128036324355822403547 3211692054486533733605321)
            ·
              refine ⟨2408769040864900300203991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3211692054486533733605321 2408769040864900300203991)
              ·
                refine ⟨3613153561297350450305987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2408769040864900300203991 3613153561297350450305987)
                ·
                  refine ⟨5419730341946025675458981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3613153561297350450305987 5419730341946025675458981)
                  ·
                    refine ⟨1016199439114879814148559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5419730341946025675458981 1016199439114879814148559)
                    ·
                      rfl

theorem cell22_2968562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 2, 1, 1, 4].length) (baseStart_2968562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2968562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2968562 prefixEnd_2968562 := by exact prefixLift 2968562
  have htrace : WordTrace (prefixWord ++ tailWord_2968562) baseStart_2968562 baseEnd_2968562 := by
    simpa [prefixWord, tailWord_2968562, baseEnd_2968562] using wordTrace_append hprefix tailTrace_2968562
  have hstable : (prefixWord ++ tailWord_2968562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968562).length < 2 ^ (prefixWord ++ tailWord_2968562).sum := by decide
  have hdescent : baseEnd_2968562 < baseStart_2968562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968569 : List Nat := [1, 2, 1, 3, 1, 3, 1, 2, 5, 3]
def baseStart_2968569 : Nat := 118140960795 + 2968569 * 2 ^ 59
def prefixEnd_2968569 : Nat := 4983230072969 + 3 ^ 40 * 2968569 * 2
def baseEnd_2968569 : Nat := 1016201835357934129223537

theorem tailTrace_2968569 : CollatzResearch.WordTrace tailWord_2968569 prefixEnd_2968569 1016201835357934129223537 := by
  unfold tailWord_2968569
  simp only [CollatzResearch.WordTrace]
  refine ⟨108272606382388979066676761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72181737588259319377784507 108272606382388979066676761)
  ·
    refine ⟨81204454786791734300007571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108272606382388979066676761 81204454786791734300007571)
    ·
      refine ⟨121806682180187601450011357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81204454786791734300007571 121806682180187601450011357)
      ·
        refine ⟨45677505817570350543754259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121806682180187601450011357 45677505817570350543754259)
        ·
          refine ⟨68516258726355525815631389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45677505817570350543754259 68516258726355525815631389)
          ·
            refine ⟨25693597022383322180861771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68516258726355525815631389 25693597022383322180861771)
            ·
              refine ⟨38540395533574983271292657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25693597022383322180861771 38540395533574983271292657)
              ·
                refine ⟨28905296650181237453469493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38540395533574983271292657 28905296650181237453469493)
                ·
                  refine ⟨2709871560954491011262765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28905296650181237453469493 2709871560954491011262765)
                  ·
                    refine ⟨1016201835357934129223537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2709871560954491011262765 1016201835357934129223537)
                    ·
                      rfl

theorem cell22_2968569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 5, 3].length) (baseStart_2968569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2968569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2968569 prefixEnd_2968569 := by exact prefixLift 2968569
  have htrace : WordTrace (prefixWord ++ tailWord_2968569) baseStart_2968569 baseEnd_2968569 := by
    simpa [prefixWord, tailWord_2968569, baseEnd_2968569] using wordTrace_append hprefix tailTrace_2968569
  have hstable : (prefixWord ++ tailWord_2968569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968569).length < 2 ^ (prefixWord ++ tailWord_2968569).sum := by decide
  have hdescent : baseEnd_2968569 < baseStart_2968569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968586 : List Nat := [3, 1, 2, 2, 3, 1, 1, 3, 3, 3]
def baseStart_2968586 : Nat := 118140960795 + 2968586 * 2 ^ 59
def prefixEnd_2968586 : Nat := 4983230072969 + 3 ^ 40 * 2968586 * 2
def baseEnd_2968586 : Nat := 1016207654805351751548485

theorem tailTrace_2968586 : CollatzResearch.WordTrace tailWord_2968586 prefixEnd_2968586 1016207654805351751548485 := by
  unfold tailWord_2968586
  simp only [CollatzResearch.WordTrace]
  refine ⟨27068306605831847742511403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72182150948884927313363741 27068306605831847742511403)
  ·
    refine ⟨40602459908747771613767105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27068306605831847742511403 40602459908747771613767105)
    ·
      refine ⟨30451844931560828710325329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40602459908747771613767105 30451844931560828710325329)
      ·
        refine ⟨22838883698670621532743997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30451844931560828710325329 22838883698670621532743997)
        ·
          refine ⟨8564581387001483074778999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22838883698670621532743997 8564581387001483074778999)
          ·
            refine ⟨12846872080502224612168499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8564581387001483074778999 12846872080502224612168499)
            ·
              refine ⟨19270308120753336918252749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12846872080502224612168499 19270308120753336918252749)
              ·
                refine ⟨7226365545282501344344781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19270308120753336918252749 7226365545282501344344781)
                ·
                  refine ⟨2709887079480938004129293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7226365545282501344344781 2709887079480938004129293)
                  ·
                    refine ⟨1016207654805351751548485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2709887079480938004129293 1016207654805351751548485)
                    ·
                      rfl

theorem cell22_2968586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 3, 3, 3].length) (baseStart_2968586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2968586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2968586 prefixEnd_2968586 := by exact prefixLift 2968586
  have htrace : WordTrace (prefixWord ++ tailWord_2968586) baseStart_2968586 baseEnd_2968586 := by
    simpa [prefixWord, tailWord_2968586, baseEnd_2968586] using wordTrace_append hprefix tailTrace_2968586
  have hstable : (prefixWord ++ tailWord_2968586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968586).length < 2 ^ (prefixWord ++ tailWord_2968586).sum := by decide
  have hdescent : baseEnd_2968586 < baseStart_2968586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968629 : List Nat := [1, 3, 3, 1, 1, 1, 1, 2, 5, 4]
def baseStart_2968629 : Nat := 118140960795 + 2968629 * 2 ^ 59
def prefixEnd_2968629 : Nat := 4983230072969 + 3 ^ 40 * 2968629 * 2
def baseEnd_2968629 : Nat := 1016222374584113972723353

theorem tailTrace_2968629 : CollatzResearch.WordTrace tailWord_2968629 prefixEnd_2968629 1016222374584113972723353 := by
  unfold tailWord_2968629
  simp only [CollatzResearch.WordTrace]
  refine ⟨108274794762171609313860941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72183196508114406209240627 108274794762171609313860941)
  ·
    refine ⟨40603048035814353492697853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108274794762171609313860941 40603048035814353492697853)
    ·
      refine ⟨15226143013430382559761695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40603048035814353492697853 15226143013430382559761695)
      ·
        refine ⟨22839214520145573839642543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15226143013430382559761695 22839214520145573839642543)
        ·
          refine ⟨34258821780218360759463815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22839214520145573839642543 34258821780218360759463815)
          ·
            refine ⟨51388232670327541139195723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34258821780218360759463815 51388232670327541139195723)
            ·
              refine ⟨77082349005491311708793585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51388232670327541139195723 77082349005491311708793585)
              ·
                refine ⟨57811761754118483781595189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77082349005491311708793585 57811761754118483781595189)
                ·
                  refine ⟨5419852664448607854524549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57811761754118483781595189 5419852664448607854524549)
                  ·
                    refine ⟨1016222374584113972723353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5419852664448607854524549 1016222374584113972723353)
                    ·
                      rfl

theorem cell22_2968629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_2968629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2968629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2968629 prefixEnd_2968629 := by exact prefixLift 2968629
  have htrace : WordTrace (prefixWord ++ tailWord_2968629) baseStart_2968629 baseEnd_2968629 := by
    simpa [prefixWord, tailWord_2968629, baseEnd_2968629] using wordTrace_append hprefix tailTrace_2968629
  have hstable : (prefixWord ++ tailWord_2968629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968629).length < 2 ^ (prefixWord ++ tailWord_2968629).sum := by decide
  have hdescent : baseEnd_2968629 < baseStart_2968629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968751 : List Nat := [1, 1, 2, 1, 2, 3, 5, 2, 5]
def baseStart_2968751 : Nat := 118140960795 + 2968751 * 2 ^ 59
def prefixEnd_2968751 : Nat := 4983230072969 + 3 ^ 40 * 2968751 * 2
def baseEnd_2968751 : Nat := 338754712559115440390993

theorem tailTrace_2968751 : CollatzResearch.WordTrace tailWord_2968751 prefixEnd_2968751 338754712559115440390993 := by
  unfold tailWord_2968751
  simp only [CollatzResearch.WordTrace]
  refine ⟨108279244467729624149802107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72186162978486416099868071 108279244467729624149802107)
  ·
    refine ⟨162418866701594436224703161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108279244467729624149802107 162418866701594436224703161)
    ·
      refine ⟨121814150026195827168527371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162418866701594436224703161 121814150026195827168527371)
      ·
        refine ⟨182721225039293740752791057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121814150026195827168527371 182721225039293740752791057)
        ·
          refine ⟨137040918779470305564593293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182721225039293740752791057 137040918779470305564593293)
          ·
            refine ⟨51390344542301364586722485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137040918779470305564593293 51390344542301364586722485)
            ·
              refine ⟨4817844800840752930005233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51390344542301364586722485 4817844800840752930005233)
              ·
                refine ⟨3613383600630564697503925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4817844800840752930005233 3613383600630564697503925)
                ·
                  refine ⟨338754712559115440390993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3613383600630564697503925 338754712559115440390993)
                  ·
                    rfl

theorem cell22_2968751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 2, 5].length) (baseStart_2968751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2968751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2968751 prefixEnd_2968751 := by exact prefixLift 2968751
  have htrace : WordTrace (prefixWord ++ tailWord_2968751) baseStart_2968751 baseEnd_2968751 := by
    simpa [prefixWord, tailWord_2968751, baseEnd_2968751] using wordTrace_append hprefix tailTrace_2968751
  have hstable : (prefixWord ++ tailWord_2968751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968751).length < 2 ^ (prefixWord ++ tailWord_2968751).sum := by decide
  have hdescent : baseEnd_2968751 < baseStart_2968751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968774 : List Nat := [6, 1, 2, 2, 1, 2, 2, 6]
def baseStart_2968774 : Nat := 118140960795 + 2968774 * 2 ^ 59
def prefixEnd_2968774 : Nat := 4983230072969 + 3 ^ 40 * 2968774 * 2
def baseEnd_2968774 : Nat := 112919112338597991983101

theorem tailTrace_2968774 : CollatzResearch.WordTrace tailWord_2968774 prefixEnd_2968774 112919112338597991983101 := by
  unfold tailWord_2968774
  simp only [CollatzResearch.WordTrace]
  refine ⟨3383752604582696846184043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 72186722231097532718592917 3383752604582696846184043)
  ·
    refine ⟨5075628906874045269276065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3383752604582696846184043 5075628906874045269276065)
    ·
      refine ⟨3806721680155533951957049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5075628906874045269276065 3806721680155533951957049)
      ·
        refine ⟨2855041260116650463967787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3806721680155533951957049 2855041260116650463967787)
        ·
          refine ⟨4282561890174975695951681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2855041260116650463967787 4282561890174975695951681)
          ·
            refine ⟨3211921417631231771963761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4282561890174975695951681 3211921417631231771963761)
            ·
              refine ⟨2408941063223423828972821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3211921417631231771963761 2408941063223423828972821)
              ·
                refine ⟨112919112338597991983101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2408941063223423828972821 112919112338597991983101)
                ·
                  rfl

theorem cell22_2968774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 2, 6].length) (baseStart_2968774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2968774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2968774 prefixEnd_2968774 := by exact prefixLift 2968774
  have htrace : WordTrace (prefixWord ++ tailWord_2968774) baseStart_2968774 baseEnd_2968774 := by
    simpa [prefixWord, tailWord_2968774, baseEnd_2968774] using wordTrace_append hprefix tailTrace_2968774
  have hstable : (prefixWord ++ tailWord_2968774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968774).length < 2 ^ (prefixWord ++ tailWord_2968774).sum := by decide
  have hdescent : baseEnd_2968774 < baseStart_2968774 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968779 : List Nat := [1, 1, 1, 1, 3, 2, 2, 3, 8]
def baseStart_2968779 : Nat := 118140960795 + 2968779 * 2 ^ 59
def prefixEnd_2968779 : Nat := 4983230072969 + 3 ^ 40 * 2968779 * 2
def baseEnd_2968779 : Nat := 338757907549854527157631

theorem tailTrace_2968779 : CollatzResearch.WordTrace tailWord_2968779 prefixEnd_2968779 338757907549854527157631 := by
  unfold tailWord_2968779
  simp only [CollatzResearch.WordTrace]
  refine ⟨108280265711628184931821391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72186843807752123287880927 108280265711628184931821391)
  ·
    refine ⟨162420398567442277397732087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108280265711628184931821391 162420398567442277397732087)
    ·
      refine ⟨243630597851163416096598131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162420398567442277397732087 243630597851163416096598131)
      ·
        refine ⟨365445896776745124144897197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243630597851163416096598131 365445896776745124144897197)
        ·
          refine ⟨137042211291279421554336449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 365445896776745124144897197 137042211291279421554336449)
          ·
            refine ⟨102781658468459566165752337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137042211291279421554336449 102781658468459566165752337)
            ·
              refine ⟨77086243851344674624314253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102781658468459566165752337 77086243851344674624314253)
              ·
                refine ⟨28907341444254252984117845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77086243851344674624314253 28907341444254252984117845)
                ·
                  refine ⟨338757907549854527157631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28907341444254252984117845 338757907549854527157631)
                  ·
                    rfl

theorem cell22_2968779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 8].length) (baseStart_2968779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2968779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2968779 prefixEnd_2968779 := by exact prefixLift 2968779
  have htrace : WordTrace (prefixWord ++ tailWord_2968779) baseStart_2968779 baseEnd_2968779 := by
    simpa [prefixWord, tailWord_2968779, baseEnd_2968779] using wordTrace_append hprefix tailTrace_2968779
  have hstable : (prefixWord ++ tailWord_2968779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968779).length < 2 ^ (prefixWord ++ tailWord_2968779).sum := by decide
  have hdescent : baseEnd_2968779 < baseStart_2968779 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968813 : List Nat := [1, 5, 1, 2, 2, 1, 3, 1, 6]
def baseStart_2968813 : Nat := 118140960795 + 2968813 * 2 ^ 59
def prefixEnd_2968813 : Nat := 4983230072969 + 3 ^ 40 * 2968813 * 2
def baseEnd_2968813 : Nat := 338761787181466275374263

theorem tailTrace_2968813 : CollatzResearch.WordTrace tailWord_2968813 prefixEnd_2968813 338761787181466275374263 := by
  unfold tailWord_2968813
  simp only [CollatzResearch.WordTrace]
  refine ⟨108281505793505008738559093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72187670529003339159039395 108281505793505008738559093)
  ·
    refine ⟨10151391168141094569239915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 108281505793505008738559093 10151391168141094569239915)
    ·
      refine ⟨15227086752211641853859873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10151391168141094569239915 15227086752211641853859873)
      ·
        refine ⟨11420315064158731390394905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15227086752211641853859873 11420315064158731390394905)
        ·
          refine ⟨8565236298119048542796179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11420315064158731390394905 8565236298119048542796179)
          ·
            refine ⟨12847854447178572814194269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8565236298119048542796179 12847854447178572814194269)
            ·
              refine ⟨4817945417691964805322851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12847854447178572814194269 4817945417691964805322851)
              ·
                refine ⟨7226918126537947207984277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4817945417691964805322851 7226918126537947207984277)
                ·
                  refine ⟨338761787181466275374263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7226918126537947207984277 338761787181466275374263)
                  ·
                    rfl

theorem cell22_2968813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 1, 6].length) (baseStart_2968813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2968813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2968813 prefixEnd_2968813 := by exact prefixLift 2968813
  have htrace : WordTrace (prefixWord ++ tailWord_2968813) baseStart_2968813 baseEnd_2968813 := by
    simpa [prefixWord, tailWord_2968813, baseEnd_2968813] using wordTrace_append hprefix tailTrace_2968813
  have hstable : (prefixWord ++ tailWord_2968813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968813).length < 2 ^ (prefixWord ++ tailWord_2968813).sum := by decide
  have hdescent : baseEnd_2968813 < baseStart_2968813 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968826 : List Nat := [3, 1, 1, 1, 1, 4, 1, 2, 4, 4]
def baseStart_2968826 : Nat := 118140960795 + 2968826 * 2 ^ 59
def prefixEnd_2968826 : Nat := 4983230072969 + 3 ^ 40 * 2968826 * 2
def baseEnd_2968826 : Nat := 1016289811710071125547749

theorem tailTrace_2968826 : CollatzResearch.WordTrace tailWord_2968826 prefixEnd_2968826 1016289811710071125547749 := by
  unfold tailWord_2968826
  simp only [CollatzResearch.WordTrace]
  refine ⟨27070494985614477989695583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72187986628305274639188221 27070494985614477989695583)
  ·
    refine ⟨40605742478421716984543375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27070494985614477989695583 40605742478421716984543375)
    ·
      refine ⟨60908613717632575476815063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40605742478421716984543375 60908613717632575476815063)
      ·
        refine ⟨91362920576448863215222595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60908613717632575476815063 91362920576448863215222595)
        ·
          refine ⟨137044380864673294822833893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91362920576448863215222595 137044380864673294822833893)
          ·
            refine ⟨25695821412126242779281355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 137044380864673294822833893 25695821412126242779281355)
            ·
              refine ⟨38543732118189364168922033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25695821412126242779281355 38543732118189364168922033)
              ·
                refine ⟨28907799088642023126691525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38543732118189364168922033 28907799088642023126691525)
                ·
                  refine ⟨5420212329120379336254661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28907799088642023126691525 5420212329120379336254661)
                  ·
                    refine ⟨1016289811710071125547749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5420212329120379336254661 1016289811710071125547749)
                    ·
                      rfl

theorem cell22_2968826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 4, 4].length) (baseStart_2968826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2968826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2968826 prefixEnd_2968826 := by exact prefixLift 2968826
  have htrace : WordTrace (prefixWord ++ tailWord_2968826) baseStart_2968826 baseEnd_2968826 := by
    simpa [prefixWord, tailWord_2968826, baseEnd_2968826] using wordTrace_append hprefix tailTrace_2968826
  have hstable : (prefixWord ++ tailWord_2968826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968826).length < 2 ^ (prefixWord ++ tailWord_2968826).sum := by decide
  have hdescent : baseEnd_2968826 < baseStart_2968826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968843 : List Nat := [1, 1, 1, 1, 5, 4, 2, 1, 2, 4]
def baseStart_2968843 : Nat := 118140960795 + 2968843 * 2 ^ 59
def prefixEnd_2968843 : Nat := 4983230072969 + 3 ^ 40 * 2968843 * 2
def baseEnd_2968843 : Nat := 1016295631157488747872697

theorem tailTrace_2968843 : CollatzResearch.WordTrace tailWord_2968843 prefixEnd_2968843 1016295631157488747872697 := by
  unfold tailWord_2968843
  simp only [CollatzResearch.WordTrace]
  refine ⟨108282599983396323862151183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72188399988930882574767455 108282599983396323862151183)
  ·
    refine ⟨162423899975094485793226775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108282599983396323862151183 162423899975094485793226775)
    ·
      refine ⟨243635849962641728689840163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162423899975094485793226775 243635849962641728689840163)
      ·
        refine ⟨365453774943962593034760245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243635849962641728689840163 365453774943962593034760245)
        ·
          refine ⟨34261291400996493097008773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 365453774943962593034760245 34261291400996493097008773)
          ·
            refine ⟨6423992137686842455689145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34261291400996493097008773 6423992137686842455689145)
            ·
              refine ⟨4817994103265131841766859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6423992137686842455689145 4817994103265131841766859)
              ·
                refine ⟨7226991154897697762650289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4817994103265131841766859 7226991154897697762650289)
                ·
                  refine ⟨5420243366173273321987717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7226991154897697762650289 5420243366173273321987717)
                  ·
                    refine ⟨1016295631157488747872697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5420243366173273321987717 1016295631157488747872697)
                    ·
                      rfl

theorem cell22_2968843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 1, 2, 4].length) (baseStart_2968843 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2968843 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2968843 prefixEnd_2968843 := by exact prefixLift 2968843
  have htrace : WordTrace (prefixWord ++ tailWord_2968843) baseStart_2968843 baseEnd_2968843 := by
    simpa [prefixWord, tailWord_2968843, baseEnd_2968843] using wordTrace_append hprefix tailTrace_2968843
  have hstable : (prefixWord ++ tailWord_2968843).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968843).length < 2 ^ (prefixWord ++ tailWord_2968843).sum := by decide
  have hdescent : baseEnd_2968843 < baseStart_2968843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968864 : List Nat := [2, 1, 1, 5, 4, 1, 2, 2, 4]
def baseStart_2968864 : Nat := 118140960795 + 2968864 * 2 ^ 59
def prefixEnd_2968864 : Nat := 4983230072969 + 3 ^ 40 * 2968864 * 2
def baseEnd_2968864 : Nat := 338767606628883897699211

theorem tailTrace_2968864 : CollatzResearch.WordTrace tailWord_2968864 prefixEnd_2968864 338767606628883897699211 := by
  unfold tailWord_2968864
  simp only [CollatzResearch.WordTrace]
  refine ⟨54141682958160122224332823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72188910610880162965777097 54141682958160122224332823)
  ·
    refine ⟨81212524437240183336499235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54141682958160122224332823 81212524437240183336499235)
    ·
      refine ⟨121818786655860275004748853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81212524437240183336499235 121818786655860275004748853)
      ·
        refine ⟨11420511248986900781695205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 121818786655860275004748853 11420511248986900781695205)
        ·
          refine ⟨2141345859185043896567851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11420511248986900781695205 2141345859185043896567851)
          ·
            refine ⟨3212018788777565844851777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2141345859185043896567851 3212018788777565844851777)
            ·
              refine ⟨2409014091583174383638833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3212018788777565844851777 2409014091583174383638833)
              ·
                refine ⟨1806760568687380787729125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2409014091583174383638833 1806760568687380787729125)
                ·
                  refine ⟨338767606628883897699211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1806760568687380787729125 338767606628883897699211)
                  ·
                    rfl

theorem cell22_2968864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 2, 2, 4].length) (baseStart_2968864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2968864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2968864 prefixEnd_2968864 := by exact prefixLift 2968864
  have htrace : WordTrace (prefixWord ++ tailWord_2968864) baseStart_2968864 baseEnd_2968864 := by
    simpa [prefixWord, tailWord_2968864, baseEnd_2968864] using wordTrace_append hprefix tailTrace_2968864
  have hstable : (prefixWord ++ tailWord_2968864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968864).length < 2 ^ (prefixWord ++ tailWord_2968864).sum := by decide
  have hdescent : baseEnd_2968864 < baseStart_2968864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968958 : List Nat := [4, 2, 3, 2, 1, 2, 1, 3, 1, 3]
def baseStart_2968958 : Nat := 118140960795 + 2968958 * 2 ^ 59
def prefixEnd_2968958 : Nat := 4983230072969 + 3 ^ 40 * 2968958 * 2
def baseEnd_2968958 : Nat := 1016334998007666781247345

theorem tailTrace_2968958 : CollatzResearch.WordTrace tailWord_2968958 prefixEnd_2968958 1016334998007666781247345 := by
  unfold tailWord_2968958
  simp only [CollatzResearch.WordTrace]
  refine ⟨13535849297247462312823441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72191196251986465668391685 13535849297247462312823441)
  ·
    refine ⟨10151886972935596734617581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13535849297247462312823441 10151886972935596734617581)
    ·
      refine ⟨3806957614850848775481593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10151886972935596734617581 3806957614850848775481593)
      ·
        refine ⟨2855218211138136581611195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3806957614850848775481593 2855218211138136581611195)
        ·
          refine ⟨4282827316707204872416793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2855218211138136581611195 4282827316707204872416793)
          ·
            refine ⟨3212120487530403654312595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4282827316707204872416793 3212120487530403654312595)
            ·
              refine ⟨4818180731295605481468893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3212120487530403654312595 4818180731295605481468893)
              ·
                refine ⟨1806817774235852055550835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4818180731295605481468893 1806817774235852055550835)
                ·
                  refine ⟨2710226661353778083326253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1806817774235852055550835 2710226661353778083326253)
                  ·
                    refine ⟨1016334998007666781247345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2710226661353778083326253 1016334998007666781247345)
                    ·
                      rfl

theorem cell22_2968958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_2968958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2968958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2968958 prefixEnd_2968958 := by exact prefixLift 2968958
  have htrace : WordTrace (prefixWord ++ tailWord_2968958) baseStart_2968958 baseEnd_2968958 := by
    simpa [prefixWord, tailWord_2968958, baseEnd_2968958] using wordTrace_append hprefix tailTrace_2968958
  have hstable : (prefixWord ++ tailWord_2968958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968958).length < 2 ^ (prefixWord ++ tailWord_2968958).sum := by decide
  have hdescent : baseEnd_2968958 < baseStart_2968958 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968965 : List Nat := [1, 3, 1, 1, 3, 1, 5, 3, 4]
def baseStart_2968965 : Nat := 118140960795 + 2968965 * 2 ^ 59
def prefixEnd_2968965 : Nat := 4983230072969 + 3 ^ 40 * 2968965 * 2
def baseEnd_2968965 : Nat := 338779131416907032107441

theorem tailTrace_2968965 : CollatzResearch.WordTrace tailWord_2968965 prefixEnd_2968965 338779131416907032107441 := by
  unfold tailWord_2968965
  simp only [CollatzResearch.WordTrace]
  refine ⟨108287049688954338698092349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72191366459302892465394899 108287049688954338698092349)
  ·
    refine ⟨40607643633357877011784631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108287049688954338698092349 40607643633357877011784631)
    ·
      refine ⟨60911465450036815517676947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40607643633357877011784631 60911465450036815517676947)
      ·
        refine ⟨91367198175055223276515421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60911465450036815517676947 91367198175055223276515421)
        ·
          refine ⟨34262699315645708728693283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91367198175055223276515421 34262699315645708728693283)
          ·
            refine ⟨51394048973468563093039925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34262699315645708728693283 51394048973468563093039925)
            ·
              refine ⟨4818192091262677789972493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51394048973468563093039925 4818192091262677789972493)
              ·
                refine ⟨1806822034223504171239685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4818192091262677789972493 1806822034223504171239685)
                ·
                  refine ⟨338779131416907032107441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1806822034223504171239685 338779131416907032107441)
                  ·
                    rfl

theorem cell22_2968965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 3, 4].length) (baseStart_2968965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2968965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2968965 prefixEnd_2968965 := by exact prefixLift 2968965
  have htrace : WordTrace (prefixWord ++ tailWord_2968965) baseStart_2968965 baseEnd_2968965 := by
    simpa [prefixWord, tailWord_2968965, baseEnd_2968965] using wordTrace_append hprefix tailTrace_2968965
  have hstable : (prefixWord ++ tailWord_2968965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968965).length < 2 ^ (prefixWord ++ tailWord_2968965).sum := by decide
  have hdescent : baseEnd_2968965 < baseStart_2968965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2969038 : List Nat := [4, 1, 1, 1, 2, 1, 2, 3, 7]
def baseStart_2969038 : Nat := 118140960795 + 2969038 * 2 ^ 59
def prefixEnd_2969038 : Nat := 4983230072969 + 3 ^ 40 * 2969038 * 2
def baseEnd_2969038 : Nat := 338787461214191079749033

theorem tailTrace_2969038 : CollatzResearch.WordTrace tailWord_2969038 prefixEnd_2969038 338787461214191079749033 := by
  unfold tailWord_2969038
  simp only [CollatzResearch.WordTrace]
  refine ⟨13536214027211234020687471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72193141478459914776999845 13536214027211234020687471)
  ·
    refine ⟨20304321040816851031031207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13536214027211234020687471 20304321040816851031031207)
    ·
      refine ⟨30456481561225276546546811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20304321040816851031031207 30456481561225276546546811)
      ·
        refine ⟨45684722341837914819820217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30456481561225276546546811 45684722341837914819820217)
        ·
          refine ⟨34263541756378436114865163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45684722341837914819820217 34263541756378436114865163)
          ·
            refine ⟨51395312634567654172297745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34263541756378436114865163 51395312634567654172297745)
            ·
              refine ⟨38546484475925740629223309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51395312634567654172297745 38546484475925740629223309)
              ·
                refine ⟨14454931678472152735958741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38546484475925740629223309 14454931678472152735958741)
                ·
                  refine ⟨338787461214191079749033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14454931678472152735958741 338787461214191079749033)
                  ·
                    rfl

theorem cell22_2969038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 3, 7].length) (baseStart_2969038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2969038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2969038 prefixEnd_2969038 := by exact prefixLift 2969038
  have htrace : WordTrace (prefixWord ++ tailWord_2969038) baseStart_2969038 baseEnd_2969038 := by
    simpa [prefixWord, tailWord_2969038, baseEnd_2969038] using wordTrace_append hprefix tailTrace_2969038
  have hstable : (prefixWord ++ tailWord_2969038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2969038).length < 2 ^ (prefixWord ++ tailWord_2969038).sum := by decide
  have hdescent : baseEnd_2969038 < baseStart_2969038 := by decide
  rcases family_descends (prefixWord ++ tailWord_2969038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2969089 : List Nat := [1, 2, 4, 1, 5, 1, 1, 2, 5]
def baseStart_2969089 : Nat := 118140960795 + 2969089 * 2 ^ 59
def prefixEnd_2969089 : Nat := 4983230072969 + 3 ^ 40 * 2969089 * 2
def baseEnd_2969089 : Nat := 338793280661608702073981

theorem tailTrace_2969089 : CollatzResearch.WordTrace tailWord_2969089 prefixEnd_2969089 338793280661608702073981 := by
  unfold tailWord_2969089
  simp only [CollatzResearch.WordTrace]
  refine ⟨108291572340505107875606321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72194381560336738583737547 108291572340505107875606321)
  ·
    refine ⟨81218679255378830906704741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108291572340505107875606321 81218679255378830906704741)
    ·
      refine ⟨15228502360383530795007139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81218679255378830906704741 15228502360383530795007139)
      ·
        refine ⟨22842753540575296192510709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15228502360383530795007139 22842753540575296192510709)
        ·
          refine ⟨2141508144428934018047879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22842753540575296192510709 2141508144428934018047879)
          ·
            refine ⟨3212262216643401027071819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2141508144428934018047879 3212262216643401027071819)
            ·
              refine ⟨4818393324965101540607729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3212262216643401027071819 4818393324965101540607729)
              ·
                refine ⟨3613794993723826155455797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4818393324965101540607729 3613794993723826155455797)
                ·
                  refine ⟨338793280661608702073981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3613794993723826155455797 338793280661608702073981)
                  ·
                    rfl

theorem cell22_2969089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 2, 5].length) (baseStart_2969089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2969089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2969089 prefixEnd_2969089 := by exact prefixLift 2969089
  have htrace : WordTrace (prefixWord ++ tailWord_2969089) baseStart_2969089 baseEnd_2969089 := by
    simpa [prefixWord, tailWord_2969089, baseEnd_2969089] using wordTrace_append hprefix tailTrace_2969089
  have hstable : (prefixWord ++ tailWord_2969089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2969089).length < 2 ^ (prefixWord ++ tailWord_2969089).sum := by decide
  have hdescent : baseEnd_2969089 < baseStart_2969089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2969089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2969130 : List Nat := [3, 1, 4, 1, 1, 1, 1, 3, 1, 6]
def baseStart_2969130 : Nat := 118140960795 + 2969130 * 2 ^ 59
def prefixEnd_2969130 : Nat := 4983230072969 + 3 ^ 40 * 2969130 * 2
def baseEnd_2969130 : Nat := 1016393877122715665946817

theorem tailTrace_2969130 : CollatzResearch.WordTrace tailWord_2969130 prefixEnd_2969130 1016393877122715665946817 := by
  unfold tailWord_2969130
  simp only [CollatzResearch.WordTrace]
  refine ⟨27073266933339142969462211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72195378488904381251899229 27073266933339142969462211)
  ·
    refine ⟨40609900400008714454193317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27073266933339142969462211 40609900400008714454193317)
    ·
      refine ⟨7614356325001633960161247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40609900400008714454193317 7614356325001633960161247)
      ·
        refine ⟨11421534487502450940241871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7614356325001633960161247 11421534487502450940241871)
        ·
          refine ⟨17132301731253676410362807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11421534487502450940241871 17132301731253676410362807)
          ·
            refine ⟨25698452596880514615544211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17132301731253676410362807 25698452596880514615544211)
            ·
              refine ⟨38547678895320771923316317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25698452596880514615544211 38547678895320771923316317)
              ·
                refine ⟨14455379585745289471243619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38547678895320771923316317 14455379585745289471243619)
                ·
                  refine ⟨21683069378617934206865429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14455379585745289471243619 21683069378617934206865429)
                  ·
                    refine ⟨1016393877122715665946817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21683069378617934206865429 1016393877122715665946817)
                    ·
                      rfl

theorem cell22_2969130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_2969130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2969130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2969130 prefixEnd_2969130 := by exact prefixLift 2969130
  have htrace : WordTrace (prefixWord ++ tailWord_2969130) baseStart_2969130 baseEnd_2969130 := by
    simpa [prefixWord, tailWord_2969130, baseEnd_2969130] using wordTrace_append hprefix tailTrace_2969130
  have hstable : (prefixWord ++ tailWord_2969130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2969130).length < 2 ^ (prefixWord ++ tailWord_2969130).sum := by decide
  have hdescent : baseEnd_2969130 < baseStart_2969130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2969130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2969134 : List Nat := [4, 1, 3, 1, 2, 1, 3, 3, 4]
def baseStart_2969134 : Nat := 118140960795 + 2969134 * 2 ^ 59
def prefixEnd_2969134 : Nat := 4983230072969 + 3 ^ 40 * 2969134 * 2
def baseEnd_2969134 : Nat := 338798415468153662948935

theorem tailTrace_2969134 : CollatzResearch.WordTrace tailWord_2969134 prefixEnd_2969134 338798415468153662948935 := by
  unfold tailWord_2969134
  simp only [CollatzResearch.WordTrace]
  refine ⟨13536651703167760070124307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72195475750228053707329637 13536651703167760070124307)
  ·
    refine ⟨20304977554751640105186461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13536651703167760070124307 20304977554751640105186461)
    ·
      refine ⟨7614366583031865039444923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20304977554751640105186461 7614366583031865039444923)
      ·
        refine ⟨11421549874547797559167385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7614366583031865039444923 11421549874547797559167385)
        ·
          refine ⟨8566162405910848169375539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11421549874547797559167385 8566162405910848169375539)
          ·
            refine ⟨12849243608866272254063309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8566162405910848169375539 12849243608866272254063309)
            ·
              refine ⟨4818466353324852095273741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12849243608866272254063309 4818466353324852095273741)
              ·
                refine ⟨1806924882496819535727653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4818466353324852095273741 1806924882496819535727653)
                ·
                  refine ⟨338798415468153662948935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1806924882496819535727653 338798415468153662948935)
                  ·
                    rfl

theorem cell22_2969134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 3, 4].length) (baseStart_2969134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2969134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2969134 prefixEnd_2969134 := by exact prefixLift 2969134
  have htrace : WordTrace (prefixWord ++ tailWord_2969134) baseStart_2969134 baseEnd_2969134 := by
    simpa [prefixWord, tailWord_2969134, baseEnd_2969134] using wordTrace_append hprefix tailTrace_2969134
  have hstable : (prefixWord ++ tailWord_2969134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2969134).length < 2 ^ (prefixWord ++ tailWord_2969134).sum := by decide
  have hdescent : baseEnd_2969134 < baseStart_2969134 := by decide
  rcases family_descends (prefixWord ++ tailWord_2969134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2969145 : List Nat := [1, 2, 1, 5, 1, 4, 8]
def baseStart_2969145 : Nat := 118140960795 + 2969145 * 2 ^ 59
def prefixEnd_2969145 : Nat := 4983230072969 + 3 ^ 40 * 2969145 * 2
def baseEnd_2969145 : Nat := 37644407849231875067473

theorem tailTrace_2969145 : CollatzResearch.WordTrace tailWord_2969145 prefixEnd_2969145 37644407849231875067473 := by
  unfold tailWord_2969145
  simp only [CollatzResearch.WordTrace]
  refine ⟨108293614828302229439644889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72195743218868152959763259 108293614828302229439644889)
  ·
    refine ⟨81220211121226672079733667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108293614828302229439644889 81220211121226672079733667)
    ·
      refine ⟨121830316681840008119600501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81220211121226672079733667 121830316681840008119600501)
      ·
        refine ⟨11421592188922500761212547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 121830316681840008119600501 11421592188922500761212547)
        ·
          refine ⟨17132388283383751141818821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11421592188922500761212547 17132388283383751141818821)
          ·
            refine ⟨3212322803134453339091029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17132388283383751141818821 3212322803134453339091029)
            ·
              refine ⟨37644407849231875067473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3212322803134453339091029 37644407849231875067473)
              ·
                rfl

theorem cell22_2969145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 8].length) (baseStart_2969145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2969145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2969145 prefixEnd_2969145 := by exact prefixLift 2969145
  have htrace : WordTrace (prefixWord ++ tailWord_2969145) baseStart_2969145 baseEnd_2969145 := by
    simpa [prefixWord, tailWord_2969145, baseEnd_2969145] using wordTrace_append hprefix tailTrace_2969145
  have hstable : (prefixWord ++ tailWord_2969145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2969145).length < 2 ^ (prefixWord ++ tailWord_2969145).sum := by decide
  have hdescent : baseEnd_2969145 < baseStart_2969145 := by decide
  rcases family_descends (prefixWord ++ tailWord_2969145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2969181 : List Nat := [1, 4, 4, 2, 1, 1, 2, 1, 2, 4]
def baseStart_2969181 : Nat := 118140960795 + 2969181 * 2 ^ 59
def prefixEnd_2969181 : Nat := 4983230072969 + 3 ^ 40 * 2969181 * 2
def baseEnd_2969181 : Nat := 1016411335464968532921661

theorem tailTrace_2969181 : CollatzResearch.WordTrace tailWord_2969181 prefixEnd_2969181 1016411335464968532921661 := by
  unfold tailWord_2969181
  simp only [CollatzResearch.WordTrace]
  refine ⟨108294927856171807587955397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72196618570781205058636931 108294927856171807587955397)
  ·
    refine ⟨20305298973032213922741637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108294927856171807587955397 20305298973032213922741637)
    ·
      refine ⟨3807243557443540110514057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20305298973032213922741637 3807243557443540110514057)
      ·
        refine ⟨2855432668082655082885543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3807243557443540110514057 2855432668082655082885543)
        ·
          refine ⟨4283149002123982624328315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2855432668082655082885543 4283149002123982624328315)
          ·
            refine ⟨6424723503185973936492473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4283149002123982624328315 6424723503185973936492473)
            ·
              refine ⟨4818542627389480452369355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6424723503185973936492473 4818542627389480452369355)
              ·
                refine ⟨7227813941084220678554033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4818542627389480452369355 7227813941084220678554033)
                ·
                  refine ⟨5420860455813165508915525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7227813941084220678554033 5420860455813165508915525)
                  ·
                    refine ⟨1016411335464968532921661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5420860455813165508915525 1016411335464968532921661)
                    ·
                      rfl

theorem cell22_2969181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_2969181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2969181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2969181 prefixEnd_2969181 := by exact prefixLift 2969181
  have htrace : WordTrace (prefixWord ++ tailWord_2969181) baseStart_2969181 baseEnd_2969181 := by
    simpa [prefixWord, tailWord_2969181, baseEnd_2969181] using wordTrace_append hprefix tailTrace_2969181
  have hstable : (prefixWord ++ tailWord_2969181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2969181).length < 2 ^ (prefixWord ++ tailWord_2969181).sum := by decide
  have hdescent : baseEnd_2969181 < baseStart_2969181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2969181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2969267 : List Nat := [1, 1, 1, 2, 3, 3, 3, 1, 4, 3]
def baseStart_2969267 : Nat := 118140960795 + 2969267 * 2 ^ 59
def prefixEnd_2969267 : Nat := 4983230072969 + 3 ^ 40 * 2969267 * 2
def baseEnd_2969267 : Nat := 1016440775022492975271397

theorem tailTrace_2969267 : CollatzResearch.WordTrace tailWord_2969267 prefixEnd_2969267 1016440775022492975271397 := by
  unfold tailWord_2969267
  simp only [CollatzResearch.WordTrace]
  refine ⟨108298064533860244275586055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72198709689240162850390703 108298064533860244275586055)
  ·
    refine ⟨162447096800790366413379083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108298064533860244275586055 162447096800790366413379083)
    ·
      refine ⟨243670645201185549620068625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162447096800790366413379083 243670645201185549620068625)
      ·
        refine ⟨182752983900889162215051469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243670645201185549620068625 182752983900889162215051469)
        ·
          refine ⟨68532368962833435830644301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 182752983900889162215051469 68532368962833435830644301)
          ·
            refine ⟨25699638361062538436491613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68532368962833435830644301 25699638361062538436491613)
            ·
              refine ⟨9637364385398451913684355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25699638361062538436491613 9637364385398451913684355)
              ·
                refine ⟨14456046578097677870526533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9637364385398451913684355 14456046578097677870526533)
                ·
                  refine ⟨2710508733393314600723725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14456046578097677870526533 2710508733393314600723725)
                  ·
                    refine ⟨1016440775022492975271397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2710508733393314600723725 1016440775022492975271397)
                    ·
                      rfl

theorem cell22_2969267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 1, 4, 3].length) (baseStart_2969267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2969267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2969267 prefixEnd_2969267 := by exact prefixLift 2969267
  have htrace : WordTrace (prefixWord ++ tailWord_2969267) baseStart_2969267 baseEnd_2969267 := by
    simpa [prefixWord, tailWord_2969267, baseEnd_2969267] using wordTrace_append hprefix tailTrace_2969267
  have hstable : (prefixWord ++ tailWord_2969267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2969267).length < 2 ^ (prefixWord ++ tailWord_2969267).sum := by decide
  have hdescent : baseEnd_2969267 < baseStart_2969267 := by decide
  rcases family_descends (prefixWord ++ tailWord_2969267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2969269 : List Nat := [1, 3, 3, 3, 2, 1, 2, 1, 6]
def baseStart_2969269 : Nat := 118140960795 + 2969269 * 2 ^ 59
def prefixEnd_2969269 : Nat := 4983230072969 + 3 ^ 40 * 2969269 * 2
def baseEnd_2969269 : Nat := 338813819887788545573797

theorem tailTrace_2969269 : CollatzResearch.WordTrace tailWord_2969269 prefixEnd_2969269 338813819887788545573797 := by
  unfold tailWord_2969269
  simp only [CollatzResearch.WordTrace]
  refine ⟨108298137479852998617158861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72198758319901999078105907 108298137479852998617158861)
  ·
    refine ⟨40611801554944874481434573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108298137479852998617158861 40611801554944874481434573)
    ·
      refine ⟨15229425583104327930537965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40611801554944874481434573 15229425583104327930537965)
      ·
        refine ⟨5711034593664122973951737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15229425583104327930537965 5711034593664122973951737)
        ·
          refine ⟨4283275945248092230463803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5711034593664122973951737 4283275945248092230463803)
          ·
            refine ⟨6424913917872138345695705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4283275945248092230463803 6424913917872138345695705)
            ·
              refine ⟨4818685438404103759271779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6424913917872138345695705 4818685438404103759271779)
              ·
                refine ⟨7228028157606155638907669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4818685438404103759271779 7228028157606155638907669)
                ·
                  refine ⟨338813819887788545573797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7228028157606155638907669 338813819887788545573797)
                  ·
                    rfl

theorem cell22_2969269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 1, 6].length) (baseStart_2969269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2969269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2969269 prefixEnd_2969269 := by exact prefixLift 2969269
  have htrace : WordTrace (prefixWord ++ tailWord_2969269) baseStart_2969269 baseEnd_2969269 := by
    simpa [prefixWord, tailWord_2969269, baseEnd_2969269] using wordTrace_append hprefix tailTrace_2969269
  have hstable : (prefixWord ++ tailWord_2969269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2969269).length < 2 ^ (prefixWord ++ tailWord_2969269).sum := by decide
  have hdescent : baseEnd_2969269 < baseStart_2969269 := by decide
  rcases family_descends (prefixWord ++ tailWord_2969269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2969280 : List Nat := [2, 1, 1, 2, 4, 1, 2, 9]
def baseStart_2969280 : Nat := 118140960795 + 2969280 * 2 ^ 59
def prefixEnd_2969280 : Nat := 4983230072969 + 3 ^ 40 * 2969280 * 2
def baseEnd_2969280 : Nat := 112938358354240586077373

theorem tailTrace_2969280 : CollatzResearch.WordTrace tailWord_2969280 prefixEnd_2969280 112938358354240586077373 := by
  unfold tailWord_2969280
  simp only [CollatzResearch.WordTrace]
  refine ⟨54149269341406573747904647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72199025788542098330539529 54149269341406573747904647)
  ·
    refine ⟨81223904012109860621856971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54149269341406573747904647 81223904012109860621856971)
    ·
      refine ⟨121835856018164790932785457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81223904012109860621856971 121835856018164790932785457)
      ·
        refine ⟨91376892013623593199589093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121835856018164790932785457 91376892013623593199589093)
        ·
          refine ⟨17133167252554423724922955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91376892013623593199589093 17133167252554423724922955)
          ·
            refine ⟨25699750878831635587384433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17133167252554423724922955 25699750878831635587384433)
            ·
              refine ⟨19274813159123726690538325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25699750878831635587384433 19274813159123726690538325)
              ·
                refine ⟨112938358354240586077373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19274813159123726690538325 112938358354240586077373)
                ·
                  rfl

theorem cell22_2969280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 9].length) (baseStart_2969280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2969280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2969280 prefixEnd_2969280 := by exact prefixLift 2969280
  have htrace : WordTrace (prefixWord ++ tailWord_2969280) baseStart_2969280 baseEnd_2969280 := by
    simpa [prefixWord, tailWord_2969280, baseEnd_2969280] using wordTrace_append hprefix tailTrace_2969280
  have hstable : (prefixWord ++ tailWord_2969280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2969280).length < 2 ^ (prefixWord ++ tailWord_2969280).sum := by decide
  have hdescent : baseEnd_2969280 < baseStart_2969280 := by decide
  rcases family_descends (prefixWord ++ tailWord_2969280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2969286 : List Nat := [6, 1, 2, 1, 1, 1, 2, 2, 6]
def baseStart_2969286 : Nat := 118140960795 + 2969286 * 2 ^ 59
def prefixEnd_2969286 : Nat := 4983230072969 + 3 ^ 40 * 2969286 * 2
def baseEnd_2969286 : Nat := 338815759703594419682113

theorem tailTrace_2969286 : CollatzResearch.WordTrace tailWord_2969286 prefixEnd_2969286 338815759703594419682113 := by
  unfold tailWord_2969286
  simp only [CollatzResearch.WordTrace]
  refine ⟨3384336172524731578766491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 72199171680527607013685141 3384336172524731578766491)
  ·
    refine ⟨5076504258787097368149737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3384336172524731578766491 5076504258787097368149737)
    ·
      refine ⟨3807378194090323026112303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5076504258787097368149737 3807378194090323026112303)
      ·
        refine ⟨5711067291135484539168455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3807378194090323026112303 5711067291135484539168455)
        ·
          refine ⟨8566600936703226808752683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5711067291135484539168455 8566600936703226808752683)
          ·
            refine ⟨12849901405054840213129025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8566600936703226808752683 12849901405054840213129025)
            ·
              refine ⟨9637426053791130159846769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12849901405054840213129025 9637426053791130159846769)
              ·
                refine ⟨7228069540343347619885077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9637426053791130159846769 7228069540343347619885077)
                ·
                  refine ⟨338815759703594419682113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7228069540343347619885077 338815759703594419682113)
                  ·
                    rfl

theorem cell22_2969286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_2969286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2969286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2969286 prefixEnd_2969286 := by exact prefixLift 2969286
  have htrace : WordTrace (prefixWord ++ tailWord_2969286) baseStart_2969286 baseEnd_2969286 := by
    simpa [prefixWord, tailWord_2969286, baseEnd_2969286] using wordTrace_append hprefix tailTrace_2969286
  have hstable : (prefixWord ++ tailWord_2969286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2969286).length < 2 ^ (prefixWord ++ tailWord_2969286).sum := by decide
  have hdescent : baseEnd_2969286 < baseStart_2969286 := by decide
  rcases family_descends (prefixWord ++ tailWord_2969286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2969297 : List Nat := [1, 2, 2, 1, 2, 4, 4, 6]
def baseStart_2969297 : Nat := 118140960795 + 2969297 * 2 ^ 59
def prefixEnd_2969297 : Nat := 4983230072969 + 3 ^ 40 * 2969297 * 2
def baseEnd_2969297 : Nat := 112939004959509210780145

theorem tailTrace_2969297 : CollatzResearch.WordTrace tailWord_2969297 prefixEnd_2969297 112939004959509210780145 := by
  unfold tailWord_2969297
  simp only [CollatzResearch.WordTrace]
  refine ⟨108299158723751559399178145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72199439149167706266118763 108299158723751559399178145)
  ·
    refine ⟨81224369042813669549383609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108299158723751559399178145 81224369042813669549383609)
    ·
      refine ⟨60918276782110252162037707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81224369042813669549383609 60918276782110252162037707)
      ·
        refine ⟨91377415173165378243056561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60918276782110252162037707 91377415173165378243056561)
        ·
          refine ⟨68533061379874033682292421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91377415173165378243056561 68533061379874033682292421)
          ·
            refine ⟨12849949008726381315429829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68533061379874033682292421 12849949008726381315429829)
            ·
              refine ⟨2409365439136196496643093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12849949008726381315429829 2409365439136196496643093)
              ·
                refine ⟨112939004959509210780145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2409365439136196496643093 112939004959509210780145)
                ·
                  rfl

theorem cell22_2969297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 4, 6].length) (baseStart_2969297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2969297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2969297 prefixEnd_2969297 := by exact prefixLift 2969297
  have htrace : WordTrace (prefixWord ++ tailWord_2969297) baseStart_2969297 baseEnd_2969297 := by
    simpa [prefixWord, tailWord_2969297, baseEnd_2969297] using wordTrace_append hprefix tailTrace_2969297
  have hstable : (prefixWord ++ tailWord_2969297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2969297).length < 2 ^ (prefixWord ++ tailWord_2969297).sum := by decide
  have hdescent : baseEnd_2969297 < baseStart_2969297 := by decide
  rcases family_descends (prefixWord ++ tailWord_2969297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2969312 : List Nat := [2, 1, 1, 3, 1, 2, 2, 2, 5, 3]
def baseStart_2969312 : Nat := 118140960795 + 2969312 * 2 ^ 59
def prefixEnd_2969312 : Nat := 4983230072969 + 3 ^ 40 * 2969312 * 2
def baseEnd_2969312 : Nat := 1016456179442127857896259

theorem tailTrace_2969312 : CollatzResearch.WordTrace tailWord_2969312 prefixEnd_2969312 1016456179442127857896259 := by
  unfold tailWord_2969312
  simp only [CollatzResearch.WordTrace]
  refine ⟨54149852909348608480487095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72199803879131477973982793 54149852909348608480487095)
  ·
    refine ⟨81224779364022912720730643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54149852909348608480487095 81224779364022912720730643)
    ·
      refine ⟨121837169046034369081095965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81224779364022912720730643 121837169046034369081095965)
      ·
        refine ⟨45688938392262888405410987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121837169046034369081095965 45688938392262888405410987)
        ·
          refine ⟨68533407588394332608116481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45688938392262888405410987 68533407588394332608116481)
          ·
            refine ⟨51400055691295749456087361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68533407588394332608116481 51400055691295749456087361)
            ·
              refine ⟨38550041768471812092065521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51400055691295749456087361 38550041768471812092065521)
              ·
                refine ⟨28912531326353859069049141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38550041768471812092065521 28912531326353859069049141)
                ·
                  refine ⟨2710549811845674287723357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28912531326353859069049141 2710549811845674287723357)
                  ·
                    refine ⟨1016456179442127857896259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2710549811845674287723357 1016456179442127857896259)
                    ·
                      rfl

theorem cell22_2969312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 5, 3].length) (baseStart_2969312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2969312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2969312 prefixEnd_2969312 := by exact prefixLift 2969312
  have htrace : WordTrace (prefixWord ++ tailWord_2969312) baseStart_2969312 baseEnd_2969312 := by
    simpa [prefixWord, tailWord_2969312, baseEnd_2969312] using wordTrace_append hprefix tailTrace_2969312
  have hstable : (prefixWord ++ tailWord_2969312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2969312).length < 2 ^ (prefixWord ++ tailWord_2969312).sum := by decide
  have hdescent : baseEnd_2969312 < baseStart_2969312 := by decide
  rcases family_descends (prefixWord ++ tailWord_2969312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2969329 : List Nat := [1, 2, 2, 2, 2, 3, 3, 1, 3, 3]
def baseStart_2969329 : Nat := 118140960795 + 2969329 * 2 ^ 59
def prefixEnd_2969329 : Nat := 4983230072969 + 3 ^ 40 * 2969329 * 2
def baseEnd_2969329 : Nat := 1016461998889545480221207

theorem tailTrace_2969329 : CollatzResearch.WordTrace tailWord_2969329 prefixEnd_2969329 1016461998889545480221207 := by
  unfold tailWord_2969329
  simp only [CollatzResearch.WordTrace]
  refine ⟨108300325859635628864343041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72200217239757085909562027 108300325859635628864343041)
  ·
    refine ⟨81225244394726721648257281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108300325859635628864343041 81225244394726721648257281)
    ·
      refine ⟨60918933296045041236192961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81225244394726721648257281 60918933296045041236192961)
      ·
        refine ⟨45689199972033780927144721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60918933296045041236192961 45689199972033780927144721)
        ·
          refine ⟨34266899979025335695358541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45689199972033780927144721 34266899979025335695358541)
          ·
            refine ⟨12850087492134500885759453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34266899979025335695358541 12850087492134500885759453)
            ·
              refine ⟨4818782809550437832159795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12850087492134500885759453 4818782809550437832159795)
              ·
                refine ⟨7228174214325656748239693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4818782809550437832159795 7228174214325656748239693)
                ·
                  refine ⟨2710565330372121280589885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7228174214325656748239693 2710565330372121280589885)
                  ·
                    refine ⟨1016461998889545480221207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2710565330372121280589885 1016461998889545480221207)
                    ·
                      rfl

theorem cell22_2969329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 1, 3, 3].length) (baseStart_2969329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2969329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2969329 prefixEnd_2969329 := by exact prefixLift 2969329
  have htrace : WordTrace (prefixWord ++ tailWord_2969329) baseStart_2969329 baseEnd_2969329 := by
    simpa [prefixWord, tailWord_2969329, baseEnd_2969329] using wordTrace_append hprefix tailTrace_2969329
  have hstable : (prefixWord ++ tailWord_2969329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2969329).length < 2 ^ (prefixWord ++ tailWord_2969329).sum := by decide
  have hdescent : baseEnd_2969329 < baseStart_2969329 := by decide
  rcases family_descends (prefixWord ++ tailWord_2969329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2969380 : List Nat := [2, 3, 1, 3, 2, 3, 2, 2, 1, 3]
def baseStart_2969380 : Nat := 118140960795 + 2969380 * 2 ^ 59
def prefixEnd_2969380 : Nat := 4983230072969 + 3 ^ 40 * 2969380 * 2
def baseEnd_2969380 : Nat := 1016479457231798347196051

theorem tailTrace_2969380 : CollatzResearch.WordTrace tailWord_2969380 prefixEnd_2969380 1016479457231798347196051 := by
  unfold tailWord_2969380
  simp only [CollatzResearch.WordTrace]
  refine ⟨54151092991225432287224797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72201457321633909716299729 54151092991225432287224797)
  ·
    refine ⟨20306659871709537107709299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54151092991225432287224797 20306659871709537107709299)
    ·
      refine ⟨30459989807564305661563949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20306659871709537107709299 30459989807564305661563949)
      ·
        refine ⟨11422496177836614623086481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30459989807564305661563949 11422496177836614623086481)
        ·
          refine ⟨8566872133377460967314861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11422496177836614623086481 8566872133377460967314861)
          ·
            refine ⟨3212577050016547862743073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8566872133377460967314861 3212577050016547862743073)
            ·
              refine ⟨2409432787512410897057305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3212577050016547862743073 2409432787512410897057305)
              ·
                refine ⟨1807074590634308172792979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2409432787512410897057305 1807074590634308172792979)
                ·
                  refine ⟨2710611885951462259189469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1807074590634308172792979 2710611885951462259189469)
                  ·
                    refine ⟨1016479457231798347196051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2710611885951462259189469 1016479457231798347196051)
                    ·
                      rfl

theorem cell22_2969380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 2, 2, 1, 3].length) (baseStart_2969380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2969380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2969380 prefixEnd_2969380 := by exact prefixLift 2969380
  have htrace : WordTrace (prefixWord ++ tailWord_2969380) baseStart_2969380 baseEnd_2969380 := by
    simpa [prefixWord, tailWord_2969380, baseEnd_2969380] using wordTrace_append hprefix tailTrace_2969380
  have hstable : (prefixWord ++ tailWord_2969380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2969380).length < 2 ^ (prefixWord ++ tailWord_2969380).sum := by decide
  have hdescent : baseEnd_2969380 < baseStart_2969380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2969380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2969417 : List Nat := [1, 2, 1, 1, 2, 4, 3, 1, 1, 6]
def baseStart_2969417 : Nat := 118140960795 + 2969417 * 2 ^ 59
def prefixEnd_2969417 : Nat := 4983230072969 + 3 ^ 40 * 2969417 * 2
def baseEnd_2969417 : Nat := 1016492123087942584020937

theorem tailTrace_2969417 : CollatzResearch.WordTrace tailWord_2969417 prefixEnd_2969417 1016492123087942584020937 := by
  unfold tailWord_2969417
  simp only [CollatzResearch.WordTrace]
  refine ⟨108303535483316819893546505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72202356988877879929031003 108303535483316819893546505)
  ·
    refine ⟨81227651612487614920159879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108303535483316819893546505 81227651612487614920159879)
    ·
      refine ⟨121841477418731422380239819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81227651612487614920159879 121841477418731422380239819)
      ·
        refine ⟨182762216128097133570359729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121841477418731422380239819 182762216128097133570359729)
        ·
          refine ⟨137071662096072850177769797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182762216128097133570359729 137071662096072850177769797)
          ·
            refine ⟨25700936643013659408331837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 137071662096072850177769797 25700936643013659408331837)
            ·
              refine ⟨9637851241130122278124439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25700936643013659408331837 9637851241130122278124439)
              ·
                refine ⟨14456776861695183417186659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9637851241130122278124439 14456776861695183417186659)
                ·
                  refine ⟨21685165292542775125779989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14456776861695183417186659 21685165292542775125779989)
                  ·
                    refine ⟨1016492123087942584020937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21685165292542775125779989 1016492123087942584020937)
                    ·
                      rfl

theorem cell22_2969417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 1, 1, 6].length) (baseStart_2969417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2969417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2969417 prefixEnd_2969417 := by exact prefixLift 2969417
  have htrace : WordTrace (prefixWord ++ tailWord_2969417) baseStart_2969417 baseEnd_2969417 := by
    simpa [prefixWord, tailWord_2969417, baseEnd_2969417] using wordTrace_append hprefix tailTrace_2969417
  have hstable : (prefixWord ++ tailWord_2969417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2969417).length < 2 ^ (prefixWord ++ tailWord_2969417).sum := by decide
  have hdescent : baseEnd_2969417 < baseStart_2969417 := by decide
  rcases family_descends (prefixWord ++ tailWord_2969417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2969477 : List Nat := [1, 3, 1, 1, 3, 2, 1, 1, 9]
def baseStart_2969477 : Nat := 118140960795 + 2969477 * 2 ^ 59
def prefixEnd_2969477 : Nat := 4983230072969 + 3 ^ 40 * 2969477 * 2
def baseEnd_2969477 : Nat := 338837554104707475840251

theorem tailTrace_2969477 : CollatzResearch.WordTrace tailWord_2969477 prefixEnd_2969477 338837554104707475840251 := by
  unfold tailWord_2969477
  simp only [CollatzResearch.WordTrace]
  refine ⟨108305723863099450140730685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72203815908732966760487123 108305723863099450140730685)
  ·
    refine ⟨40614646448662293802774007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108305723863099450140730685 40614646448662293802774007)
    ·
      refine ⟨60921969672993440704161011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40614646448662293802774007 60921969672993440704161011)
      ·
        refine ⟨91382954509490161056241517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60921969672993440704161011 91382954509490161056241517)
        ·
          refine ⟨34268607941058810396090569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91382954509490161056241517 34268607941058810396090569)
          ·
            refine ⟨25701455955794107797067927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34268607941058810396090569 25701455955794107797067927)
            ·
              refine ⟨38552183933691161695601891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25701455955794107797067927 38552183933691161695601891)
              ·
                refine ⟨57828275900536742543402837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38552183933691161695601891 57828275900536742543402837)
                ·
                  refine ⟨338837554104707475840251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 57828275900536742543402837 338837554104707475840251)
                  ·
                    rfl

theorem cell22_2969477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 9].length) (baseStart_2969477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2969477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2969477 prefixEnd_2969477 := by exact prefixLift 2969477
  have htrace : WordTrace (prefixWord ++ tailWord_2969477) baseStart_2969477 baseEnd_2969477 := by
    simpa [prefixWord, tailWord_2969477, baseEnd_2969477] using wordTrace_append hprefix tailTrace_2969477
  have hstable : (prefixWord ++ tailWord_2969477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2969477).length < 2 ^ (prefixWord ++ tailWord_2969477).sum := by decide
  have hdescent : baseEnd_2969477 < baseStart_2969477 := by decide
  rcases family_descends (prefixWord ++ tailWord_2969477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2969498 : List Nat := [3, 1, 1, 4, 2, 3, 1, 1, 3, 3]
def baseStart_2969498 : Nat := 118140960795 + 2969498 * 2 ^ 59
def prefixEnd_2969498 : Nat := 4983230072969 + 3 ^ 40 * 2969498 * 2
def baseEnd_2969498 : Nat := 1016519851043285372745689

theorem tailTrace_2969498 : CollatzResearch.WordTrace tailWord_2969498 prefixEnd_2969498 1016519851043285372745689 := by
  unfold tailWord_2969498
  simp only [CollatzResearch.WordTrace]
  refine ⟨27076622449005842681811287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72204326530682247151496765 27076622449005842681811287)
  ·
    refine ⟨40614933673508764022716931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27076622449005842681811287 40614933673508764022716931)
    ·
      refine ⟨60922400510263146034075397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40614933673508764022716931 60922400510263146034075397)
      ·
        refine ⟨11422950095674339881389137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60922400510263146034075397 11422950095674339881389137)
        ·
          refine ⟨8567212571755754911041853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11422950095674339881389137 8567212571755754911041853)
          ·
            refine ⟨3212704714408408091640695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8567212571755754911041853 3212704714408408091640695)
            ·
              refine ⟨4819057071612612137461043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3212704714408408091640695 4819057071612612137461043)
              ·
                refine ⟨7228585607418918206191565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4819057071612612137461043 7228585607418918206191565)
                ·
                  refine ⟨2710719602782094327321837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7228585607418918206191565 2710719602782094327321837)
                  ·
                    refine ⟨1016519851043285372745689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2710719602782094327321837 1016519851043285372745689)
                    ·
                      rfl

theorem cell22_2969498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 1, 3, 3].length) (baseStart_2969498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2969498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2969498 prefixEnd_2969498 := by exact prefixLift 2969498
  have htrace : WordTrace (prefixWord ++ tailWord_2969498) baseStart_2969498 baseEnd_2969498 := by
    simpa [prefixWord, tailWord_2969498, baseEnd_2969498] using wordTrace_append hprefix tailTrace_2969498
  have hstable : (prefixWord ++ tailWord_2969498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2969498).length < 2 ^ (prefixWord ++ tailWord_2969498).sum := by decide
  have hdescent : baseEnd_2969498 < baseStart_2969498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2969498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2969507 : List Nat := [1, 1, 1, 4, 1, 2, 1, 1, 2, 8]
def baseStart_2969507 : Nat := 118140960795 + 2969507 * 2 ^ 59
def prefixEnd_2969507 : Nat := 4983230072969 + 3 ^ 40 * 2969507 * 2
def baseEnd_2969507 : Nat := 1016522931927212349270661

theorem tailTrace_2969507 : CollatzResearch.WordTrace tailWord_2969507 prefixEnd_2969507 1016522931927212349270661 := by
  unfold tailWord_2969507
  simp only [CollatzResearch.WordTrace]
  refine ⟨108306818052990765264322775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72204545368660510176215183 108306818052990765264322775)
  ·
    refine ⟨162460227079486147896484163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108306818052990765264322775 162460227079486147896484163)
    ·
      refine ⟨243690340619229221844726245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162460227079486147896484163 243690340619229221844726245)
      ·
        refine ⟨45691938866105479095886171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 243690340619229221844726245 45691938866105479095886171)
        ·
          refine ⟨68537908299158218643829257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45691938866105479095886171 68537908299158218643829257)
          ·
            refine ⟨51403431224368663982871943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68537908299158218643829257 51403431224368663982871943)
            ·
              refine ⟨77105146836552995974307915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51403431224368663982871943 77105146836552995974307915)
              ·
                refine ⟨115657720254829493961461873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77105146836552995974307915 115657720254829493961461873)
                ·
                  refine ⟨86743290191122120471096405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115657720254829493961461873 86743290191122120471096405)
                  ·
                    refine ⟨1016522931927212349270661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 86743290191122120471096405 1016522931927212349270661)
                    ·
                      rfl

theorem cell22_2969507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 8].length) (baseStart_2969507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2969507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2969507 prefixEnd_2969507 := by exact prefixLift 2969507
  have htrace : WordTrace (prefixWord ++ tailWord_2969507) baseStart_2969507 baseEnd_2969507 := by
    simpa [prefixWord, tailWord_2969507, baseEnd_2969507] using wordTrace_append hprefix tailTrace_2969507
  have hstable : (prefixWord ++ tailWord_2969507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2969507).length < 2 ^ (prefixWord ++ tailWord_2969507).sum := by decide
  have hdescent : baseEnd_2969507 < baseStart_2969507 := by decide
  rcases family_descends (prefixWord ++ tailWord_2969507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2969511 : List Nat := [1, 1, 6, 1, 2, 2, 1, 3, 5]
def baseStart_2969511 : Nat := 118140960795 + 2969511 * 2 ^ 59
def prefixEnd_2969511 : Nat := 4983230072969 + 3 ^ 40 * 2969511 * 2
def baseEnd_2969511 : Nat := 338841433736319224056883

theorem tailTrace_2969511 : CollatzResearch.WordTrace tailWord_2969511 prefixEnd_2969511 338841433736319224056883 := by
  unfold tailWord_2969511
  simp only [CollatzResearch.WordTrace]
  refine ⟨108306963944976273947468387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72204642629984182631645591 108306963944976273947468387)
  ·
    refine ⟨162460445917464410921202581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108306963944976273947468387 162460445917464410921202581)
    ·
      refine ⟨7615333402381144261931371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 162460445917464410921202581 7615333402381144261931371)
      ·
        refine ⟨11423000103571716392897057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7615333402381144261931371 11423000103571716392897057)
        ·
          refine ⟨8567250077678787294672793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11423000103571716392897057 8567250077678787294672793)
          ·
            refine ⟨6425437558259090471004595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8567250077678787294672793 6425437558259090471004595)
            ·
              refine ⟨9638156337388635706506893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6425437558259090471004595 9638156337388635706506893)
              ·
                refine ⟨3614308626520738389940085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9638156337388635706506893 3614308626520738389940085)
                ·
                  refine ⟨338841433736319224056883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3614308626520738389940085 338841433736319224056883)
                  ·
                    rfl

theorem cell22_2969511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 3, 5].length) (baseStart_2969511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2969511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2969511 prefixEnd_2969511 := by exact prefixLift 2969511
  have htrace : WordTrace (prefixWord ++ tailWord_2969511) baseStart_2969511 baseEnd_2969511 := by
    simpa [prefixWord, tailWord_2969511, baseEnd_2969511] using wordTrace_append hprefix tailTrace_2969511
  have hstable : (prefixWord ++ tailWord_2969511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2969511).length < 2 ^ (prefixWord ++ tailWord_2969511).sum := by decide
  have hdescent : baseEnd_2969511 < baseStart_2969511 := by decide
  rcases family_descends (prefixWord ++ tailWord_2969511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2969569 : List Nat := [1, 2, 3, 1, 2, 1, 2, 2, 4, 4]
def baseStart_2969569 : Nat := 118140960795 + 2969569 * 2 ^ 59
def prefixEnd_2969569 : Nat := 4983230072969 + 3 ^ 40 * 2969569 * 2
def baseEnd_2969569 : Nat := 1016544155794264854220471

theorem tailTrace_2969569 : CollatzResearch.WordTrace tailWord_2969569 prefixEnd_2969569 1016544155794264854220471 := by
  unfold tailWord_2969569
  simp only [CollatzResearch.WordTrace]
  refine ⟨108309079378766149853079761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72206052919177433235386507 108309079378766149853079761)
  ·
    refine ⟨81231809534074612389809821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108309079378766149853079761 81231809534074612389809821)
    ·
      refine ⟨30461928575277979646178683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81231809534074612389809821 30461928575277979646178683)
      ·
        refine ⟨45692892862916969469268025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30461928575277979646178683 45692892862916969469268025)
        ·
          refine ⟨34269669647187727101951019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45692892862916969469268025 34269669647187727101951019)
          ·
            refine ⟨51404504470781590652926529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34269669647187727101951019 51404504470781590652926529)
            ·
              refine ⟨38553378353086192989694897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51404504470781590652926529 38553378353086192989694897)
              ·
                refine ⟨28915033764814644742271173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38553378353086192989694897 28915033764814644742271173)
                ·
                  refine ⟨5421568830902745889175845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28915033764814644742271173 5421568830902745889175845)
                  ·
                    refine ⟨1016544155794264854220471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5421568830902745889175845 1016544155794264854220471)
                    ·
                      rfl

theorem cell22_2969569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 4, 4].length) (baseStart_2969569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2969569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2969569 prefixEnd_2969569 := by exact prefixLift 2969569
  have htrace : WordTrace (prefixWord ++ tailWord_2969569) baseStart_2969569 baseEnd_2969569 := by
    simpa [prefixWord, tailWord_2969569, baseEnd_2969569] using wordTrace_append hprefix tailTrace_2969569
  have hstable : (prefixWord ++ tailWord_2969569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2969569).length < 2 ^ (prefixWord ++ tailWord_2969569).sum := by decide
  have hdescent : baseEnd_2969569 < baseStart_2969569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2969569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2969571 : List Nat := [1, 1, 1, 6, 1, 3, 2, 1, 1, 5]
def baseStart_2969571 : Nat := 118140960795 + 2969571 * 2 ^ 59
def prefixEnd_2969571 : Nat := 4983230072969 + 3 ^ 40 * 2969571 * 2
def baseEnd_2969571 : Nat := 1016544840435137515670465

theorem tailTrace_2969571 : CollatzResearch.WordTrace tailWord_2969571 prefixEnd_2969571 1016544840435137515670465 := by
  unfold tailWord_2969571
  simp only [CollatzResearch.WordTrace]
  refine ⟨108309152324758904194652567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72206101549839269463101711 108309152324758904194652567)
  ·
    refine ⟨162463728487138356291978851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108309152324758904194652567 162463728487138356291978851)
    ·
      refine ⟨243695592730707534437968277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162463728487138356291978851 243695592730707534437968277)
      ·
        refine ⟨11423230909251915676779763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 243695592730707534437968277 11423230909251915676779763)
        ·
          refine ⟨17134846363877873515169645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11423230909251915676779763 17134846363877873515169645)
          ·
            refine ⟨6425567386454202568188617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17134846363877873515169645 6425567386454202568188617)
            ·
              refine ⟨4819175539840651926141463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6425567386454202568188617 4819175539840651926141463)
              ·
                refine ⟨7228763309760977889212195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4819175539840651926141463 7228763309760977889212195)
                ·
                  refine ⟨10843144964641466833818293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7228763309760977889212195 10843144964641466833818293)
                  ·
                    refine ⟨1016544840435137515670465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10843144964641466833818293 1016544840435137515670465)
                    ·
                      rfl

theorem cell22_2969571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 1, 1, 5].length) (baseStart_2969571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2969571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2969571 prefixEnd_2969571 := by exact prefixLift 2969571
  have htrace : WordTrace (prefixWord ++ tailWord_2969571) baseStart_2969571 baseEnd_2969571 := by
    simpa [prefixWord, tailWord_2969571, baseEnd_2969571] using wordTrace_append hprefix tailTrace_2969571
  have hstable : (prefixWord ++ tailWord_2969571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2969571).length < 2 ^ (prefixWord ++ tailWord_2969571).sum := by decide
  have hdescent : baseEnd_2969571 < baseStart_2969571 := by decide
  rcases family_descends (prefixWord ++ tailWord_2969571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2969590 : List Nat := [5, 1, 1, 1, 4, 1, 2, 3, 4]
def baseStart_2969590 : Nat := 118140960795 + 2969590 * 2 ^ 59
def prefixEnd_2969590 : Nat := 4983230072969 + 3 ^ 40 * 2969590 * 2
def baseEnd_2969590 : Nat := 338850448174475933148469

theorem tailTrace_2969590 : CollatzResearch.WordTrace tailWord_2969590 prefixEnd_2969590 338850448174475933148469 := by
  unfold tailWord_2969590
  simp only [CollatzResearch.WordTrace]
  refine ⟨6769365331980629402474639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72206563541126713626396149 6769365331980629402474639)
  ·
    refine ⟨10154047997970944103711959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6769365331980629402474639 10154047997970944103711959)
    ·
      refine ⟨15231071996956416155567939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10154047997970944103711959 15231071996956416155567939)
      ·
        refine ⟨22846607995434624233351909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15231071996956416155567939 22846607995434624233351909)
        ·
          refine ⟨4283738999143992043753483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22846607995434624233351909 4283738999143992043753483)
          ·
            refine ⟨6425608498715988065630225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4283738999143992043753483 6425608498715988065630225)
            ·
              refine ⟨4819206374036991049222669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6425608498715988065630225 4819206374036991049222669)
              ·
                refine ⟨1807202390263871643458501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4819206374036991049222669 1807202390263871643458501)
                ·
                  refine ⟨338850448174475933148469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1807202390263871643458501 338850448174475933148469)
                  ·
                    rfl

theorem cell22_2969590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 3, 4].length) (baseStart_2969590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2969590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2969590 prefixEnd_2969590 := by exact prefixLift 2969590
  have htrace : WordTrace (prefixWord ++ tailWord_2969590) baseStart_2969590 baseEnd_2969590 := by
    simpa [prefixWord, tailWord_2969590, baseEnd_2969590] using wordTrace_append hprefix tailTrace_2969590
  have hstable : (prefixWord ++ tailWord_2969590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2969590).length < 2 ^ (prefixWord ++ tailWord_2969590).sum := by decide
  have hdescent : baseEnd_2969590 < baseStart_2969590 := by decide
  rcases family_descends (prefixWord ++ tailWord_2969590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2969644 : List Nat := [2, 2, 1, 1, 1, 2, 2, 2, 4, 5]
def baseStart_2969644 : Nat := 118140960795 + 2969644 * 2 ^ 59
def prefixEnd_2969644 : Nat := 4983230072969 + 3 ^ 40 * 2969644 * 2
def baseEnd_2969644 : Nat := 1016569829826989658595241

theorem tailTrace_2969644 : CollatzResearch.WordTrace tailWord_2969644 prefixEnd_2969644 1016569829826989658595241 := by
  unfold tailWord_2969644
  simp only [CollatzResearch.WordTrace]
  refine ⟨54155907426747218831029993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72207876568996291774706657 54155907426747218831029993)
  ·
    refine ⟨40616930570060414123272495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54155907426747218831029993 40616930570060414123272495)
    ·
      refine ⟨60925395855090621184908743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40616930570060414123272495 60925395855090621184908743)
      ·
        refine ⟨91388093782635931777363115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60925395855090621184908743 91388093782635931777363115)
        ·
          refine ⟨137082140673953897666044673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91388093782635931777363115 137082140673953897666044673)
          ·
            refine ⟨102811605505465423249533505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137082140673953897666044673 102811605505465423249533505)
            ·
              refine ⟨77108704129099067437150129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102811605505465423249533505 77108704129099067437150129)
              ·
                refine ⟨57831528096824300577862597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77108704129099067437150129 57831528096824300577862597)
                ·
                  refine ⟨10843411518154556358349237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57831528096824300577862597 10843411518154556358349237)
                  ·
                    refine ⟨1016569829826989658595241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10843411518154556358349237 1016569829826989658595241)
                    ·
                      rfl

theorem cell22_2969644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 5].length) (baseStart_2969644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2969644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2969644 prefixEnd_2969644 := by exact prefixLift 2969644
  have htrace : WordTrace (prefixWord ++ tailWord_2969644) baseStart_2969644 baseEnd_2969644 := by
    simpa [prefixWord, tailWord_2969644, baseEnd_2969644] using wordTrace_append hprefix tailTrace_2969644
  have hstable : (prefixWord ++ tailWord_2969644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2969644).length < 2 ^ (prefixWord ++ tailWord_2969644).sum := by decide
  have hdescent : baseEnd_2969644 < baseStart_2969644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2969644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2969646 : List Nat := [4, 1, 3, 1, 1, 2, 1, 2, 7]
def baseStart_2969646 : Nat := 118140960795 + 2969646 * 2 ^ 59
def prefixEnd_2969646 : Nat := 4983230072969 + 3 ^ 40 * 2969646 * 2
def baseEnd_2969646 : Nat := 338856838155954106681745

theorem tailTrace_2969646 : CollatzResearch.WordTrace tailWord_2969646 prefixEnd_2969646 338856838155954106681745 := by
  unfold tailWord_2969646
  simp only [CollatzResearch.WordTrace]
  refine ⟨13538985974935899000454099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72207925199658128002421861 13538985974935899000454099)
  ·
    refine ⟨20308478962403848500681149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13538985974935899000454099 20308478962403848500681149)
    ·
      refine ⟨7615679610901443187755431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20308478962403848500681149 7615679610901443187755431)
      ·
        refine ⟨11423519416352164781633147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7615679610901443187755431 11423519416352164781633147)
        ·
          refine ⟨17135279124528247172449721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11423519416352164781633147 17135279124528247172449721)
          ·
            refine ⟨12851459343396185379337291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17135279124528247172449721 12851459343396185379337291)
            ·
              refine ⟨19277189015094278069005937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12851459343396185379337291 19277189015094278069005937)
              ·
                refine ⟨14457891761320708551754453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19277189015094278069005937 14457891761320708551754453)
                ·
                  refine ⟨338856838155954106681745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14457891761320708551754453 338856838155954106681745)
                  ·
                    rfl

theorem cell22_2969646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 2, 7].length) (baseStart_2969646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2969646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2969646 prefixEnd_2969646 := by exact prefixLift 2969646
  have htrace : WordTrace (prefixWord ++ tailWord_2969646) baseStart_2969646 baseEnd_2969646 := by
    simpa [prefixWord, tailWord_2969646, baseEnd_2969646] using wordTrace_append hprefix tailTrace_2969646
  have hstable : (prefixWord ++ tailWord_2969646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2969646).length < 2 ^ (prefixWord ++ tailWord_2969646).sum := by decide
  have hdescent : baseEnd_2969646 < baseStart_2969646 := by decide
  rcases family_descends (prefixWord ++ tailWord_2969646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2969650 : List Nat := [3, 2, 1, 1, 2, 3, 3, 3, 1, 3]
def baseStart_2969650 : Nat := 118140960795 + 2969650 * 2 ^ 59
def prefixEnd_2969650 : Nat := 4983230072969 + 3 ^ 40 * 2969650 * 2
def baseEnd_2969650 : Nat := 1016571883749607642945223

theorem tailTrace_2969650 : CollatzResearch.WordTrace tailWord_2969650 prefixEnd_2969650 1016571883749607642945223 := by
  unfold tailWord_2969650
  simp only [CollatzResearch.WordTrace]
  refine ⟨27078008422868175171694601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72208022460981800457852269 27078008422868175171694601)
  ·
    refine ⟨20308506317151131378770951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27078008422868175171694601 20308506317151131378770951)
    ·
      refine ⟨30462759475726697068156427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20308506317151131378770951 30462759475726697068156427)
      ·
        refine ⟨45694139213590045602234641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30462759475726697068156427 45694139213590045602234641)
        ·
          refine ⟨34270604410192534201675981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45694139213590045602234641 34270604410192534201675981)
          ·
            refine ⟨12851476653822200325628493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34270604410192534201675981 12851476653822200325628493)
            ·
              refine ⟨4819303745183325122110685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12851476653822200325628493 4819303745183325122110685)
              ·
                refine ⟨1807238904443746920791507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4819303745183325122110685 1807238904443746920791507)
                ·
                  refine ⟨2710858356665620381187261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1807238904443746920791507 2710858356665620381187261)
                  ·
                    refine ⟨1016571883749607642945223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2710858356665620381187261 1016571883749607642945223)
                    ·
                      rfl

theorem cell22_2969650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 3, 1, 3].length) (baseStart_2969650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2969650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2969650 prefixEnd_2969650 := by exact prefixLift 2969650
  have htrace : WordTrace (prefixWord ++ tailWord_2969650) baseStart_2969650 baseEnd_2969650 := by
    simpa [prefixWord, tailWord_2969650, baseEnd_2969650] using wordTrace_append hprefix tailTrace_2969650
  have hstable : (prefixWord ++ tailWord_2969650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2969650).length < 2 ^ (prefixWord ++ tailWord_2969650).sum := by decide
  have hdescent : baseEnd_2969650 < baseStart_2969650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2969650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2969710 : List Nat := [4, 1, 2, 2, 1, 1, 5, 1, 1, 4]
def baseStart_2969710 : Nat := 118140960795 + 2969710 * 2 ^ 59
def prefixEnd_2969710 : Nat := 4983230072969 + 3 ^ 40 * 2969710 * 2
def baseEnd_2969710 : Nat := 1016592422975787486445039

theorem tailTrace_2969710 : CollatzResearch.WordTrace tailWord_2969710 prefixEnd_2969710 1016592422975787486445039 := by
  unfold tailWord_2969710
  simp only [CollatzResearch.WordTrace]
  refine ⟨13539277758906916366745323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72209481380836887289308389 13539277758906916366745323)
  ·
    refine ⟨20308916638360374550117985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13539277758906916366745323 20308916638360374550117985)
    ·
      refine ⟨15231687478770280912588489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20308916638360374550117985 15231687478770280912588489)
      ·
        refine ⟨11423765609077710684441367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15231687478770280912588489 11423765609077710684441367)
        ·
          refine ⟨17135648413616566026662051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11423765609077710684441367 17135648413616566026662051)
          ·
            refine ⟨25703472620424849039993077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17135648413616566026662051 25703472620424849039993077)
            ·
              refine ⟨2409700558164829597499351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25703472620424849039993077 2409700558164829597499351)
              ·
                refine ⟨3614550837247244396249027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2409700558164829597499351 3614550837247244396249027)
                ·
                  refine ⟨5421826255870866594373541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3614550837247244396249027 5421826255870866594373541)
                  ·
                    refine ⟨1016592422975787486445039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5421826255870866594373541 1016592422975787486445039)
                    ·
                      rfl

theorem cell22_2969710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 5, 1, 1, 4].length) (baseStart_2969710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2969710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2969710 prefixEnd_2969710 := by exact prefixLift 2969710
  have htrace : WordTrace (prefixWord ++ tailWord_2969710) baseStart_2969710 baseEnd_2969710 := by
    simpa [prefixWord, tailWord_2969710, baseEnd_2969710] using wordTrace_append hprefix tailTrace_2969710
  have hstable : (prefixWord ++ tailWord_2969710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2969710).length < 2 ^ (prefixWord ++ tailWord_2969710).sum := by decide
  have hdescent : baseEnd_2969710 < baseStart_2969710 := by decide
  rcases family_descends (prefixWord ++ tailWord_2969710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2969719 : List Nat := [1, 1, 3, 1, 1, 15]
def baseStart_2969719 : Nat := 118140960795 + 2969719 * 2 ^ 59
def prefixEnd_2969719 : Nat := 4983230072969 + 3 ^ 40 * 2969719 * 2
def baseEnd_2969719 : Nat := 12550561776045857567531

theorem tailTrace_2969719 : CollatzResearch.WordTrace tailWord_2969719 prefixEnd_2969719 12550561776045857567531 := by
  unfold tailWord_2969719
  simp only [CollatzResearch.WordTrace]
  refine ⟨108314550328222725471040211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72209700218815150314026807 108314550328222725471040211)
  ·
    refine ⟨162471825492334088206560317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108314550328222725471040211 162471825492334088206560317)
    ·
      refine ⟨60926934559625283077460119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162471825492334088206560317 60926934559625283077460119)
      ·
        refine ⟨91390401839437924616190179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60926934559625283077460119 91390401839437924616190179)
        ·
          refine ⟨137085602759156886924285269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91390401839437924616190179 137085602759156886924285269)
          ·
            refine ⟨12550561776045857567531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 15 137085602759156886924285269 12550561776045857567531)
            ·
              rfl

theorem cell22_2969719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 15].length) (baseStart_2969719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2969719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2969719 prefixEnd_2969719 := by exact prefixLift 2969719
  have htrace : WordTrace (prefixWord ++ tailWord_2969719) baseStart_2969719 baseEnd_2969719 := by
    simpa [prefixWord, tailWord_2969719, baseEnd_2969719] using wordTrace_append hprefix tailTrace_2969719
  have hstable : (prefixWord ++ tailWord_2969719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2969719).length < 2 ^ (prefixWord ++ tailWord_2969719).sum := by decide
  have hdescent : baseEnd_2969719 < baseStart_2969719 := by decide
  rcases family_descends (prefixWord ++ tailWord_2969719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2969725 : List Nat := [1, 4, 1, 1, 3, 2, 4, 2, 4]
def baseStart_2969725 : Nat := 118140960795 + 2969725 * 2 ^ 59
def prefixEnd_2969725 : Nat := 4983230072969 + 3 ^ 40 * 2969725 * 2
def baseEnd_2969725 : Nat := 338865852594110815773331

theorem tailTrace_2969725 : CollatzResearch.WordTrace tailWord_2969725 prefixEnd_2969725 338865852594110815773331 := by
  unfold tailWord_2969725
  simp only [CollatzResearch.WordTrace]
  refine ⟨108314769166200988495758629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72209846110800658997172419 108314769166200988495758629)
  ·
    refine ⟨20309019218662685342954743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108314769166200988495758629 20309019218662685342954743)
    ·
      refine ⟨30463528827994028014432115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20309019218662685342954743 30463528827994028014432115)
      ·
        refine ⟨45695293241991042021648173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30463528827994028014432115 45695293241991042021648173)
        ·
          refine ⟨17135734965746640758118065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45695293241991042021648173 17135734965746640758118065)
          ·
            refine ⟨12851801224309980568588549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17135734965746640758118065 12851801224309980568588549)
            ·
              refine ⟨2409712729558121356610353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12851801224309980568588549 2409712729558121356610353)
              ·
                refine ⟨1807284547168591017457765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2409712729558121356610353 1807284547168591017457765)
                ·
                  refine ⟨338865852594110815773331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1807284547168591017457765 338865852594110815773331)
                  ·
                    rfl

theorem cell22_2969725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 4, 2, 4].length) (baseStart_2969725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2969725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2969725 prefixEnd_2969725 := by exact prefixLift 2969725
  have htrace : WordTrace (prefixWord ++ tailWord_2969725) baseStart_2969725 baseEnd_2969725 := by
    simpa [prefixWord, tailWord_2969725, baseEnd_2969725] using wordTrace_append hprefix tailTrace_2969725
  have hstable : (prefixWord ++ tailWord_2969725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2969725).length < 2 ^ (prefixWord ++ tailWord_2969725).sum := by decide
  have hdescent : baseEnd_2969725 < baseStart_2969725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2969725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2969785 : List Nat := [1, 2, 1, 4, 1, 2, 1, 6, 1, 3]
def baseStart_2969785 : Nat := 118140960795 + 2969785 * 2 ^ 59
def prefixEnd_2969785 : Nat := 4983230072969 + 3 ^ 40 * 2969785 * 2
def baseEnd_2969785 : Nat := 1016618097008512290819809

theorem tailTrace_2969785 : CollatzResearch.WordTrace tailWord_2969785 prefixEnd_2969785 1016618097008512290819809 := by
  unfold tailWord_2969785
  simp only [CollatzResearch.WordTrace]
  refine ⟨108316957545983618742942809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72211305030655745828628539 108316957545983618742942809)
  ·
    refine ⟨81237718159487714057207107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108316957545983618742942809 81237718159487714057207107)
    ·
      refine ⟨121856577239231571085810661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81237718159487714057207107 121856577239231571085810661)
      ·
        refine ⟨22848108232355919578589499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 121856577239231571085810661 22848108232355919578589499)
        ·
          refine ⟨34272162348533879367884249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22848108232355919578589499 34272162348533879367884249)
          ·
            refine ⟨25704121761400409525913187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34272162348533879367884249 25704121761400409525913187)
            ·
              refine ⟨38556182642100614288869781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25704121761400409525913187 38556182642100614288869781)
              ·
                refine ⟨1807321061348466294790771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 38556182642100614288869781 1807321061348466294790771)
                ·
                  refine ⟨2710981592022699442186157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1807321061348466294790771 2710981592022699442186157)
                  ·
                    refine ⟨1016618097008512290819809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2710981592022699442186157 1016618097008512290819809)
                    ·
                      rfl

theorem cell22_2969785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 6, 1, 3].length) (baseStart_2969785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2969785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2969785 prefixEnd_2969785 := by exact prefixLift 2969785
  have htrace : WordTrace (prefixWord ++ tailWord_2969785) baseStart_2969785 baseEnd_2969785 := by
    simpa [prefixWord, tailWord_2969785, baseEnd_2969785] using wordTrace_append hprefix tailTrace_2969785
  have hstable : (prefixWord ++ tailWord_2969785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2969785).length < 2 ^ (prefixWord ++ tailWord_2969785).sum := by decide
  have hdescent : baseEnd_2969785 < baseStart_2969785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2969785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2969856 : List Nat := [2, 1, 1, 2, 1, 1, 4, 1, 3, 6]
def baseStart_2969856 : Nat := 118140960795 + 2969856 * 2 ^ 59
def prefixEnd_2969856 : Nat := 4983230072969 + 3 ^ 40 * 2969856 * 2
def baseEnd_2969856 : Nat := 1016642401759491772294591

theorem tailTrace_2969856 : CollatzResearch.WordTrace tailWord_2969856 prefixEnd_2969856 1016642401759491772294591 := by
  unfold tailWord_2969856
  simp only [CollatzResearch.WordTrace]
  refine ⟨54159773564363198934388711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72213031419150931912518281 54159773564363198934388711)
  ·
    refine ⟨81239660346544798401583067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54159773564363198934388711 81239660346544798401583067)
    ·
      refine ⟨121859490519817197602374601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81239660346544798401583067 121859490519817197602374601)
      ·
        refine ⟨91394617889862898201780951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121859490519817197602374601 91394617889862898201780951)
        ·
          refine ⟨137091926834794347302671427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91394617889862898201780951 137091926834794347302671427)
          ·
            refine ⟨205637890252191520954007141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137091926834794347302671427 205637890252191520954007141)
            ·
              refine ⟨38557104422285910178876339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 205637890252191520954007141 38557104422285910178876339)
              ·
                refine ⟨57835656633428865268314509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38557104422285910178876339 57835656633428865268314509)
                ·
                  refine ⟨21688371237535824475617941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57835656633428865268314509 21688371237535824475617941)
                  ·
                    refine ⟨1016642401759491772294591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21688371237535824475617941 1016642401759491772294591)
                    ·
                      rfl

theorem cell22_2969856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 3, 6].length) (baseStart_2969856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2969856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2969856 prefixEnd_2969856 := by exact prefixLift 2969856
  have htrace : WordTrace (prefixWord ++ tailWord_2969856) baseStart_2969856 baseEnd_2969856 := by
    simpa [prefixWord, tailWord_2969856, baseEnd_2969856] using wordTrace_append hprefix tailTrace_2969856
  have hstable : (prefixWord ++ tailWord_2969856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2969856).length < 2 ^ (prefixWord ++ tailWord_2969856).sum := by decide
  have hdescent : baseEnd_2969856 < baseStart_2969856 := by decide
  rcases family_descends (prefixWord ++ tailWord_2969856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2969873 : List Nat := [1, 2, 2, 1, 1, 5, 1, 3, 2, 4]
def baseStart_2969873 : Nat := 118140960795 + 2969873 * 2 ^ 59
def prefixEnd_2969873 : Nat := 4983230072969 + 3 ^ 40 * 2969873 * 2
def baseEnd_2969873 : Nat := 1016648221206909394619539

theorem tailTrace_2969873 : CollatzResearch.WordTrace tailWord_2969873 prefixEnd_2969873 1016648221206909394619539 := by
  unfold tailWord_2969873
  simp only [CollatzResearch.WordTrace]
  refine ⟨108320167169664809772146273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72213444779776539848097515 108320167169664809772146273)
  ·
    refine ⟨81240125377248607329109705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108320167169664809772146273 81240125377248607329109705)
    ·
      refine ⟨60930094032936455496832279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81240125377248607329109705 60930094032936455496832279)
      ·
        refine ⟨91395141049404683245248419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60930094032936455496832279 91395141049404683245248419)
        ·
          refine ⟨137092711574107024867872629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91395141049404683245248419 137092711574107024867872629)
          ·
            refine ⟨12852441710072533581363059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 137092711574107024867872629 12852441710072533581363059)
            ·
              refine ⟨19278662565108800372044589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12852441710072533581363059 19278662565108800372044589)
              ·
                refine ⟨7229498461915800139516721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19278662565108800372044589 7229498461915800139516721)
                ·
                  refine ⟨5422123846436850104637541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7229498461915800139516721 5422123846436850104637541)
                  ·
                    refine ⟨1016648221206909394619539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5422123846436850104637541 1016648221206909394619539)
                    ·
                      rfl

theorem cell22_2969873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 4].length) (baseStart_2969873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2969873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2969873 prefixEnd_2969873 := by exact prefixLift 2969873
  have htrace : WordTrace (prefixWord ++ tailWord_2969873) baseStart_2969873 baseEnd_2969873 := by
    simpa [prefixWord, tailWord_2969873, baseEnd_2969873] using wordTrace_append hprefix tailTrace_2969873
  have hstable : (prefixWord ++ tailWord_2969873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2969873).length < 2 ^ (prefixWord ++ tailWord_2969873).sum := by decide
  have hdescent : baseEnd_2969873 < baseStart_2969873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2969873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2969890 : List Nat := [3, 3, 1, 1, 3, 1, 2, 2, 2, 4]
def baseStart_2969890 : Nat := 118140960795 + 2969890 * 2 ^ 59
def prefixEnd_2969890 : Nat := 4983230072969 + 3 ^ 40 * 2969890 * 2
def baseEnd_2969890 : Nat := 1016654040654327016944487

theorem tailTrace_2969890 : CollatzResearch.WordTrace tailWord_2969890 prefixEnd_2969890 1016654040654327016944487 := by
  unfold tailWord_2969890
  simp only [CollatzResearch.WordTrace]
  refine ⟨27080196802650805418878781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72213858140402147783676749 27080196802650805418878781)
  ·
    refine ⟨10155073800994052032079543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27080196802650805418878781 10155073800994052032079543)
    ·
      refine ⟨15232610701491078048119315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10155073800994052032079543 15232610701491078048119315)
      ·
        refine ⟨22848916052236617072178973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15232610701491078048119315 22848916052236617072178973)
        ·
          refine ⟨8568343519588731402067115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22848916052236617072178973 8568343519588731402067115)
          ·
            refine ⟨12852515279383097103100673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8568343519588731402067115 12852515279383097103100673)
            ·
              refine ⟨9639386459537322827325505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12852515279383097103100673 9639386459537322827325505)
              ·
                refine ⟨7229539844652992120494129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9639386459537322827325505 7229539844652992120494129)
                ·
                  refine ⟨5422154883489744090370597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7229539844652992120494129 5422154883489744090370597)
                  ·
                    refine ⟨1016654040654327016944487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5422154883489744090370597 1016654040654327016944487)
                    ·
                      rfl

theorem cell22_2969890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_2969890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2969890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2969890 prefixEnd_2969890 := by exact prefixLift 2969890
  have htrace : WordTrace (prefixWord ++ tailWord_2969890) baseStart_2969890 baseEnd_2969890 := by
    simpa [prefixWord, tailWord_2969890, baseEnd_2969890] using wordTrace_append hprefix tailTrace_2969890
  have hstable : (prefixWord ++ tailWord_2969890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2969890).length < 2 ^ (prefixWord ++ tailWord_2969890).sum := by decide
  have hdescent : baseEnd_2969890 < baseStart_2969890 := by decide
  rcases family_descends (prefixWord ++ tailWord_2969890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2969892 : List Nat := [2, 3, 1, 3, 1, 3, 2, 2, 2, 3]
def baseStart_2969892 : Nat := 118140960795 + 2969892 * 2 ^ 59
def prefixEnd_2969892 : Nat := 4983230072969 + 3 ^ 40 * 2969892 * 2
def baseEnd_2969892 : Nat := 1016654725295199678394481

theorem tailTrace_2969892 : CollatzResearch.WordTrace tailWord_2969892 prefixEnd_2969892 1016654725295199678394481 := by
  unfold tailWord_2969892
  simp only [CollatzResearch.WordTrace]
  refine ⟨54160430078297988008543965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72213906771063984011391953 54160430078297988008543965)
  ·
    refine ⟨20310161279361745503203987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54160430078297988008543965 20310161279361745503203987)
    ·
      refine ⟨30465241919042618254805981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20310161279361745503203987 30465241919042618254805981)
      ·
        refine ⟨11424465719640981845552243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30465241919042618254805981 11424465719640981845552243)
        ·
          refine ⟨17136698579461472768328365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11424465719640981845552243 17136698579461472768328365)
          ·
            refine ⟨6426261967298052288123137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17136698579461472768328365 6426261967298052288123137)
            ·
              refine ⟨4819696475473539216092353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6426261967298052288123137 4819696475473539216092353)
              ·
                refine ⟨3614772356605154412069265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4819696475473539216092353 3614772356605154412069265)
                ·
                  refine ⟨2711079267453865809051949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3614772356605154412069265 2711079267453865809051949)
                  ·
                    refine ⟨1016654725295199678394481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2711079267453865809051949 1016654725295199678394481)
                    ·
                      rfl

theorem cell22_2969892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 2, 2, 3].length) (baseStart_2969892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2969892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2969892 prefixEnd_2969892 := by exact prefixLift 2969892
  have htrace : WordTrace (prefixWord ++ tailWord_2969892) baseStart_2969892 baseEnd_2969892 := by
    simpa [prefixWord, tailWord_2969892, baseEnd_2969892] using wordTrace_append hprefix tailTrace_2969892
  have hstable : (prefixWord ++ tailWord_2969892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2969892).length < 2 ^ (prefixWord ++ tailWord_2969892).sum := by decide
  have hdescent : baseEnd_2969892 < baseStart_2969892 := by decide
  rcases family_descends (prefixWord ++ tailWord_2969892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2969905 : List Nat := [1, 2, 2, 3, 4, 2, 1, 7]
def baseStart_2969905 : Nat := 118140960795 + 2969905 * 2 ^ 59
def prefixEnd_2969905 : Nat := 4983230072969 + 3 ^ 40 * 2969905 * 2
def baseEnd_2969905 : Nat := 112962130606763553091049

theorem tailTrace_2969905 : CollatzResearch.WordTrace tailWord_2969905 prefixEnd_2969905 112962130606763553091049 := by
  unfold tailWord_2969905
  simp only [CollatzResearch.WordTrace]
  refine ⟨108321334305548879237311169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72214222870365919491540779 108321334305548879237311169)
  ·
    refine ⟨81241000729161659427983377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108321334305548879237311169 81241000729161659427983377)
    ·
      refine ⟨60930750546871244570987533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81241000729161659427983377 60930750546871244570987533)
      ·
        refine ⟨22849031455076716714120325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60930750546871244570987533 22849031455076716714120325)
        ·
          refine ⟨4284193397826884383897561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22849031455076716714120325 4284193397826884383897561)
          ·
            refine ⟨3213145048370163287923171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4284193397826884383897561 3213145048370163287923171)
            ·
              refine ⟨4819717572555244931884757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3213145048370163287923171 4819717572555244931884757)
              ·
                refine ⟨112962130606763553091049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4819717572555244931884757 112962130606763553091049)
                ·
                  rfl

theorem cell22_2969905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 7].length) (baseStart_2969905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2969905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2969905 prefixEnd_2969905 := by exact prefixLift 2969905
  have htrace : WordTrace (prefixWord ++ tailWord_2969905) baseStart_2969905 baseEnd_2969905 := by
    simpa [prefixWord, tailWord_2969905, baseEnd_2969905] using wordTrace_append hprefix tailTrace_2969905
  have hstable : (prefixWord ++ tailWord_2969905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2969905).length < 2 ^ (prefixWord ++ tailWord_2969905).sum := by decide
  have hdescent : baseEnd_2969905 < baseStart_2969905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2969905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2969924 : List Nat := [2, 3, 4, 1, 2, 2, 1, 1, 2, 4]
def baseStart_2969924 : Nat := 118140960795 + 2969924 * 2 ^ 59
def prefixEnd_2969924 : Nat := 4983230072969 + 3 ^ 40 * 2969924 * 2
def baseEnd_2969924 : Nat := 1016665679549162261594383

theorem tailTrace_2969924 : CollatzResearch.WordTrace tailWord_2969924 prefixEnd_2969924 1016665679549162261594383 := by
  unfold tailWord_2969924
  simp only [CollatzResearch.WordTrace]
  refine ⟨54161013646240022741126413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72214684861653363654835217 54161013646240022741126413)
  ·
    refine ⟨20310380117340008527922405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54161013646240022741126413 20310380117340008527922405)
    ·
      refine ⟨3808196272001251598985451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20310380117340008527922405 3808196272001251598985451)
      ·
        refine ⟨5712294408001877398478177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3808196272001251598985451 5712294408001877398478177)
        ·
          refine ⟨4284220806001408048858633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5712294408001877398478177 4284220806001408048858633)
          ·
            refine ⟨3213165604501056036643975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4284220806001408048858633 3213165604501056036643975)
            ·
              refine ⟨4819748406751584054965963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3213165604501056036643975 4819748406751584054965963)
              ·
                refine ⟨7229622610127376082448945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4819748406751584054965963 7229622610127376082448945)
                ·
                  refine ⟨5422216957595532061836709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7229622610127376082448945 5422216957595532061836709)
                  ·
                    refine ⟨1016665679549162261594383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5422216957595532061836709 1016665679549162261594383)
                    ·
                      rfl

theorem cell22_2969924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_2969924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2969924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2969924 prefixEnd_2969924 := by exact prefixLift 2969924
  have htrace : WordTrace (prefixWord ++ tailWord_2969924) baseStart_2969924 baseEnd_2969924 := by
    simpa [prefixWord, tailWord_2969924, baseEnd_2969924] using wordTrace_append hprefix tailTrace_2969924
  have hstable : (prefixWord ++ tailWord_2969924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2969924).length < 2 ^ (prefixWord ++ tailWord_2969924).sum := by decide
  have hdescent : baseEnd_2969924 < baseStart_2969924 := by decide
  rcases family_descends (prefixWord ++ tailWord_2969924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2969937 : List Nat := [1, 2, 2, 1, 4, 2, 1, 5, 1, 3]
def baseStart_2969937 : Nat := 118140960795 + 2969937 * 2 ^ 59
def prefixEnd_2969937 : Nat := 4983230072969 + 3 ^ 40 * 2969937 * 2
def baseEnd_2969937 : Nat := 1016670129714834561019343

theorem tailTrace_2969937 : CollatzResearch.WordTrace tailWord_2969937 prefixEnd_2969937 1016670129714834561019343 := by
  unfold tailWord_2969937
  simp only [CollatzResearch.WordTrace]
  refine ⟨108322501441432948702476065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72215000960955299134984043 108322501441432948702476065)
  ·
    refine ⟨81241876081074711526857049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108322501441432948702476065 81241876081074711526857049)
    ·
      refine ⟨60931407060806033645142787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81241876081074711526857049 60931407060806033645142787)
      ·
        refine ⟨91397110591209050467714181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60931407060806033645142787 91397110591209050467714181)
        ·
          refine ⟨17136958235851696962696409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91397110591209050467714181 17136958235851696962696409)
          ·
            refine ⟨12852718676888772722022307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17136958235851696962696409 12852718676888772722022307)
            ·
              refine ⟨19279078015333159083033461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12852718676888772722022307 19279078015333159083033461)
              ·
                refine ⟨1807413563937483664034387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19279078015333159083033461 1807413563937483664034387)
                ·
                  refine ⟨2711120345906225496051581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1807413563937483664034387 2711120345906225496051581)
                  ·
                    refine ⟨1016670129714834561019343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2711120345906225496051581 1016670129714834561019343)
                    ·
                      rfl

theorem cell22_2969937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 5, 1, 3].length) (baseStart_2969937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2969937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2969937 prefixEnd_2969937 := by exact prefixLift 2969937
  have htrace : WordTrace (prefixWord ++ tailWord_2969937) baseStart_2969937 baseEnd_2969937 := by
    simpa [prefixWord, tailWord_2969937, baseEnd_2969937] using wordTrace_append hprefix tailTrace_2969937
  have hstable : (prefixWord ++ tailWord_2969937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2969937).length < 2 ^ (prefixWord ++ tailWord_2969937).sum := by decide
  have hdescent : baseEnd_2969937 < baseStart_2969937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2969937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2969954 : List Nat := [3, 3, 2, 1, 1, 2, 2, 4, 1, 3]
def baseStart_2969954 : Nat := 118140960795 + 2969954 * 2 ^ 59
def prefixEnd_2969954 : Nat := 4983230072969 + 3 ^ 40 * 2969954 * 2
def baseEnd_2969954 : Nat := 1016675949162252183344291

theorem tailTrace_2969954 : CollatzResearch.WordTrace tailWord_2969954 prefixEnd_2969954 1016675949162252183344291 := by
  unfold tailWord_2969954
  simp only [CollatzResearch.WordTrace]
  refine ⟨27080780370592840151461229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72215414321580907070563277 27080780370592840151461229)
  ·
    refine ⟨10155292638972315056797961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27080780370592840151461229 10155292638972315056797961)
    ·
      refine ⟨7616469479229236292598471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10155292638972315056797961 7616469479229236292598471)
      ·
        refine ⟨11424704218843854438897707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7616469479229236292598471 11424704218843854438897707)
        ·
          refine ⟨17137056328265781658346561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11424704218843854438897707 17137056328265781658346561)
          ·
            refine ⟨12852792246199336243759921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17137056328265781658346561 12852792246199336243759921)
            ·
              refine ⟨9639594184649502182819941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12852792246199336243759921 9639594184649502182819941)
              ·
                refine ⟨1807423909621781659278739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9639594184649502182819941 1807423909621781659278739)
                ·
                  refine ⟨2711135864432672488918109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1807423909621781659278739 2711135864432672488918109)
                  ·
                    refine ⟨1016675949162252183344291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2711135864432672488918109 1016675949162252183344291)
                    ·
                      rfl

theorem cell22_2969954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_2969954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2969954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2969954 prefixEnd_2969954 := by exact prefixLift 2969954
  have htrace : WordTrace (prefixWord ++ tailWord_2969954) baseStart_2969954 baseEnd_2969954 := by
    simpa [prefixWord, tailWord_2969954, baseEnd_2969954] using wordTrace_append hprefix tailTrace_2969954
  have hstable : (prefixWord ++ tailWord_2969954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2969954).length < 2 ^ (prefixWord ++ tailWord_2969954).sum := by decide
  have hdescent : baseEnd_2969954 < baseStart_2969954 := by decide
  rcases family_descends (prefixWord ++ tailWord_2969954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2970053 : List Nat := [1, 3, 1, 1, 1, 1, 1, 1, 6, 6]
def baseStart_2970053 : Nat := 118140960795 + 2970053 * 2 ^ 59
def prefixEnd_2970053 : Nat := 4983230072969 + 3 ^ 40 * 2970053 * 2
def baseEnd_2970053 : Nat := 1016709838885448925118987

theorem tailTrace_2970053 : CollatzResearch.WordTrace tailWord_2970053 prefixEnd_2970053 1016709838885448925118987 := by
  unfold tailWord_2970053
  simp only [CollatzResearch.WordTrace]
  refine ⟨108326732309012700513698813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72217821539341800342465875 108326732309012700513698813)
  ·
    refine ⟨40622524615879762692637055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108326732309012700513698813 40622524615879762692637055)
    ·
      refine ⟨60933786923819644038955583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40622524615879762692637055 60933786923819644038955583)
      ·
        refine ⟨91400680385729466058433375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60933786923819644038955583 91400680385729466058433375)
        ·
          refine ⟨137101020578594199087650063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91400680385729466058433375 137101020578594199087650063)
          ·
            refine ⟨205651530867891298631475095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137101020578594199087650063 205651530867891298631475095)
            ·
              refine ⟨308477296301836947947212643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205651530867891298631475095 308477296301836947947212643)
              ·
                refine ⟨462715944452755421920818965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 308477296301836947947212643 462715944452755421920818965)
                ·
                  refine ⟨21689809896222910402538389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 462715944452755421920818965 21689809896222910402538389)
                  ·
                    refine ⟨1016709838885448925118987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21689809896222910402538389 1016709838885448925118987)
                    ·
                      rfl

theorem cell22_2970053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 6, 6].length) (baseStart_2970053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2970053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2970053 prefixEnd_2970053 := by exact prefixLift 2970053
  have htrace : WordTrace (prefixWord ++ tailWord_2970053) baseStart_2970053 baseEnd_2970053 := by
    simpa [prefixWord, tailWord_2970053, baseEnd_2970053] using wordTrace_append hprefix tailTrace_2970053
  have hstable : (prefixWord ++ tailWord_2970053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2970053).length < 2 ^ (prefixWord ++ tailWord_2970053).sum := by decide
  have hdescent : baseEnd_2970053 < baseStart_2970053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2970053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2970119 : List Nat := [1, 1, 4, 3, 3, 2, 1, 2, 5]
def baseStart_2970119 : Nat := 118140960795 + 2970119 * 2 ^ 59
def prefixEnd_2970119 : Nat := 4983230072969 + 3 ^ 40 * 2970119 * 2
def baseEnd_2970119 : Nat := 338910810678082250989595

theorem tailTrace_2970119 : CollatzResearch.WordTrace tailWord_2970119 prefixEnd_2970119 338910810678082250989595 := by
  unfold tailWord_2970119
  simp only [CollatzResearch.WordTrace]
  refine ⟨108329139526773593785601411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72219426351182395857067607 108329139526773593785601411)
  ·
    refine ⟨162493709290160390678402117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108329139526773593785601411 162493709290160390678402117)
    ·
      refine ⟨30467570491905073252200397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 162493709290160390678402117 30467570491905073252200397)
      ·
        refine ⟨11425338934464402469575149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30467570491905073252200397 11425338934464402469575149)
        ·
          refine ⟨4284502100424150926090681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11425338934464402469575149 4284502100424150926090681)
          ·
            refine ⟨3213376575318113194568011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4284502100424150926090681 3213376575318113194568011)
            ·
              refine ⟨4820064862977169791852017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3213376575318113194568011 4820064862977169791852017)
              ·
                refine ⟨3615048647232877343889013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4820064862977169791852017 3615048647232877343889013)
                ·
                  refine ⟨338910810678082250989595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3615048647232877343889013 338910810678082250989595)
                  ·
                    rfl

theorem cell22_2970119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 2, 5].length) (baseStart_2970119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2970119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2970119 prefixEnd_2970119 := by exact prefixLift 2970119
  have htrace : WordTrace (prefixWord ++ tailWord_2970119) baseStart_2970119 baseEnd_2970119 := by
    simpa [prefixWord, tailWord_2970119, baseEnd_2970119] using wordTrace_append hprefix tailTrace_2970119
  have hstable : (prefixWord ++ tailWord_2970119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2970119).length < 2 ^ (prefixWord ++ tailWord_2970119).sum := by decide
  have hdescent : baseEnd_2970119 < baseStart_2970119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2970119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2970157 : List Nat := [1, 5, 4, 1, 1, 2, 1, 3, 1, 3]
def baseStart_2970157 : Nat := 118140960795 + 2970157 * 2 ^ 59
def prefixEnd_2970157 : Nat := 4983230072969 + 3 ^ 40 * 2970157 * 2
def baseEnd_2970157 : Nat := 1016745440210827320518669

theorem tailTrace_2970157 : CollatzResearch.WordTrace tailWord_2970157 prefixEnd_2970157 1016745440210827320518669 := by
  unfold tailWord_2970157
  simp only [CollatzResearch.WordTrace]
  refine ⟨108330525500635926275484725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72220350333757284183656483 108330525500635926275484725)
  ·
    refine ⟨10155986765684618088326693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 108330525500635926275484725 10155986765684618088326693)
    ·
      refine ⟨1904247518565865891561255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10155986765684618088326693 1904247518565865891561255)
      ·
        refine ⟨2856371277848798837341883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1904247518565865891561255 2856371277848798837341883)
        ·
          refine ⟨4284556916773198256012825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2856371277848798837341883 4284556916773198256012825)
          ·
            refine ⟨3213417687579898692009619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4284556916773198256012825 3213417687579898692009619)
            ·
              refine ⟨4820126531369848038014429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3213417687579898692009619 4820126531369848038014429)
              ·
                refine ⟨1807547449263693014255411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4820126531369848038014429 1807547449263693014255411)
                ·
                  refine ⟨2711321173895539521383117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1807547449263693014255411 2711321173895539521383117)
                  ·
                    refine ⟨1016745440210827320518669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2711321173895539521383117 1016745440210827320518669)
                    ·
                      rfl

theorem cell22_2970157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_2970157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2970157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2970157 prefixEnd_2970157 := by exact prefixLift 2970157
  have htrace : WordTrace (prefixWord ++ tailWord_2970157) baseStart_2970157 baseEnd_2970157 := by
    simpa [prefixWord, tailWord_2970157, baseEnd_2970157] using wordTrace_append hprefix tailTrace_2970157
  have hstable : (prefixWord ++ tailWord_2970157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2970157).length < 2 ^ (prefixWord ++ tailWord_2970157).sum := by decide
  have hdescent : baseEnd_2970157 < baseStart_2970157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2970157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2970160 : List Nat := [2, 1, 1, 1, 2, 3, 4, 1, 1, 6]
def baseStart_2970160 : Nat := 118140960795 + 2970160 * 2 ^ 59
def prefixEnd_2970160 : Nat := 4983230072969 + 3 ^ 40 * 2970160 * 2
def baseEnd_2970160 : Nat := 1016746467172136312693659

theorem tailTrace_2970160 : CollatzResearch.WordTrace tailWord_2970160 prefixEnd_2970160 1016746467172136312693659 := by
  unfold tailWord_2970160
  simp only [CollatzResearch.WordTrace]
  refine ⟨54165317459812528893921967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72220423279750038525229289 54165317459812528893921967)
  ·
    refine ⟨81247976189718793340882951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54165317459812528893921967 81247976189718793340882951)
    ·
      refine ⟨121871964284578190011324427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81247976189718793340882951 121871964284578190011324427)
      ·
        refine ⟨182807946426867285016986641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121871964284578190011324427 182807946426867285016986641)
        ·
          refine ⟨137105959820150463762739981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182807946426867285016986641 137105959820150463762739981)
          ·
            refine ⟨51414734932556423911027493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137105959820150463762739981 51414734932556423911027493)
            ·
              refine ⟨9640262799854329483317655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51414734932556423911027493 9640262799854329483317655)
              ·
                refine ⟨14460394199781494224976483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9640262799854329483317655 14460394199781494224976483)
                ·
                  refine ⟨21690591299672241337464725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14460394199781494224976483 21690591299672241337464725)
                  ·
                    refine ⟨1016746467172136312693659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21690591299672241337464725 1016746467172136312693659)
                    ·
                      rfl

theorem cell22_2970160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 1, 1, 6].length) (baseStart_2970160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2970160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2970160 prefixEnd_2970160 := by exact prefixLift 2970160
  have htrace : WordTrace (prefixWord ++ tailWord_2970160) baseStart_2970160 baseEnd_2970160 := by
    simpa [prefixWord, tailWord_2970160, baseEnd_2970160] using wordTrace_append hprefix tailTrace_2970160
  have hstable : (prefixWord ++ tailWord_2970160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2970160).length < 2 ^ (prefixWord ++ tailWord_2970160).sum := by decide
  have hdescent : baseEnd_2970160 < baseStart_2970160 := by decide
  rcases family_descends (prefixWord ++ tailWord_2970160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2970162 : List Nat := [3, 2, 1, 1, 2, 1, 3, 2, 4, 3]
def baseStart_2970162 : Nat := 118140960795 + 2970162 * 2 ^ 59
def prefixEnd_2970162 : Nat := 4983230072969 + 3 ^ 40 * 2970162 * 2
def baseEnd_2970162 : Nat := 1016747151813008974143653

theorem tailTrace_2970162 : CollatzResearch.WordTrace tailWord_2970162 prefixEnd_2970162 1016747151813008974143653 := by
  unfold tailWord_2970162
  simp only [CollatzResearch.WordTrace]
  refine ⟨27082676966404453032354185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72220471910411874752944493 27082676966404453032354185)
  ·
    refine ⟨20312007724803339774265639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27082676966404453032354185 20312007724803339774265639)
    ·
      refine ⟨30468011587205009661398459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20312007724803339774265639 30468011587205009661398459)
      ·
        refine ⟨45702017380807514492097689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30468011587205009661398459 45702017380807514492097689)
        ·
          refine ⟨34276513035605635869073267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45702017380807514492097689 34276513035605635869073267)
          ·
            refine ⟨51414769553408453803609901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34276513035605635869073267 51414769553408453803609901)
            ·
              refine ⟨19280538582528170176353713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51414769553408453803609901 19280538582528170176353713)
              ·
                refine ⟨14460403936896127632265285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19280538582528170176353713 14460403936896127632265285)
                ·
                  refine ⟨2711325738168023931049741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14460403936896127632265285 2711325738168023931049741)
                  ·
                    refine ⟨1016747151813008974143653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2711325738168023931049741 1016747151813008974143653)
                    ·
                      rfl

theorem cell22_2970162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 2, 4, 3].length) (baseStart_2970162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2970162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2970162 prefixEnd_2970162 := by exact prefixLift 2970162
  have htrace : WordTrace (prefixWord ++ tailWord_2970162) baseStart_2970162 baseEnd_2970162 := by
    simpa [prefixWord, tailWord_2970162, baseEnd_2970162] using wordTrace_append hprefix tailTrace_2970162
  have hstable : (prefixWord ++ tailWord_2970162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2970162).length < 2 ^ (prefixWord ++ tailWord_2970162).sum := by decide
  have hdescent : baseEnd_2970162 < baseStart_2970162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2970162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2970177 : List Nat := [1, 2, 5, 1, 1, 2, 1, 1, 4, 4]
def baseStart_2970177 : Nat := 118140960795 + 2970177 * 2 ^ 59
def prefixEnd_2970177 : Nat := 4983230072969 + 3 ^ 40 * 2970177 * 2
def baseEnd_2970177 : Nat := 1016752286619553935018607

theorem tailTrace_2970177 : CollatzResearch.WordTrace tailWord_2970177 prefixEnd_2970177 1016752286619553935018607 := by
  unfold tailWord_2970177
  simp only [CollatzResearch.WordTrace]
  refine ⟨108331254960563469691212785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72220836640375646460808523 108331254960563469691212785)
  ·
    refine ⟨81248441220422602268409589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108331254960563469691212785 81248441220422602268409589)
    ·
      refine ⟨7617041364414618962663399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 81248441220422602268409589 7617041364414618962663399)
      ·
        refine ⟨11425562046621928443995099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7617041364414618962663399 11425562046621928443995099)
        ·
          refine ⟨17138343069932892665992649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11425562046621928443995099 17138343069932892665992649)
          ·
            refine ⟨12853757302449669499494487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17138343069932892665992649 12853757302449669499494487)
            ·
              refine ⟨19280635953674504249241731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12853757302449669499494487 19280635953674504249241731)
              ·
                refine ⟨28920953930511756373862597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19280635953674504249241731 28920953930511756373862597)
                ·
                  refine ⟨5422678861970954320099237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28920953930511756373862597 5422678861970954320099237)
                  ·
                    refine ⟨1016752286619553935018607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5422678861970954320099237 1016752286619553935018607)
                    ·
                      rfl

theorem cell22_2970177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_2970177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2970177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2970177 prefixEnd_2970177 := by exact prefixLift 2970177
  have htrace : WordTrace (prefixWord ++ tailWord_2970177) baseStart_2970177 baseEnd_2970177 := by
    simpa [prefixWord, tailWord_2970177, baseEnd_2970177] using wordTrace_append hprefix tailTrace_2970177
  have hstable : (prefixWord ++ tailWord_2970177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2970177).length < 2 ^ (prefixWord ++ tailWord_2970177).sum := by decide
  have hdescent : baseEnd_2970177 < baseStart_2970177 := by decide
  rcases family_descends (prefixWord ++ tailWord_2970177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2970196 : List Nat := [2, 4, 1, 1, 1, 3, 4, 1, 2, 3]
def baseStart_2970196 : Nat := 118140960795 + 2970196 * 2 ^ 59
def prefixEnd_2970196 : Nat := 4983230072969 + 3 ^ 40 * 2970196 * 2
def baseEnd_2970196 : Nat := 1016758790707844218793549

theorem tailTrace_2970196 : CollatzResearch.WordTrace tailWord_2970196 prefixEnd_2970196 1016758790707844218793549 := by
  unfold tailWord_2970196
  simp only [CollatzResearch.WordTrace]
  refine ⟨54165973973747317968077221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72221298631663090624102961 54165973973747317968077221)
  ·
    refine ⟨10156120120077622119014479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54165973973747317968077221 10156120120077622119014479)
    ·
      refine ⟨15234180180116433178521719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10156120120077622119014479 15234180180116433178521719)
      ·
        refine ⟨22851270270174649767782579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15234180180116433178521719 22851270270174649767782579)
        ·
          refine ⟨34276905405261974651673869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22851270270174649767782579 34276905405261974651673869)
          ·
            refine ⟨12853839526973240494377701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34276905405261974651673869 12853839526973240494377701)
            ·
              refine ⟨2410094911307482592695819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12853839526973240494377701 2410094911307482592695819)
              ·
                refine ⟨3615142366961223889043729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2410094911307482592695819 3615142366961223889043729)
                ·
                  refine ⟨2711356775220917916782797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3615142366961223889043729 2711356775220917916782797)
                  ·
                    refine ⟨1016758790707844218793549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2711356775220917916782797 1016758790707844218793549)
                    ·
                      rfl

theorem cell22_2970196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 4, 1, 2, 3].length) (baseStart_2970196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2970196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2970196 prefixEnd_2970196 := by exact prefixLift 2970196
  have htrace : WordTrace (prefixWord ++ tailWord_2970196) baseStart_2970196 baseEnd_2970196 := by
    simpa [prefixWord, tailWord_2970196, baseEnd_2970196] using wordTrace_append hprefix tailTrace_2970196
  have hstable : (prefixWord ++ tailWord_2970196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2970196).length < 2 ^ (prefixWord ++ tailWord_2970196).sum := by decide
  have hdescent : baseEnd_2970196 < baseStart_2970196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2970196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2970207 : List Nat := [1, 1, 2, 3, 1, 1, 1, 6, 3, 3]
def baseStart_2970207 : Nat := 118140960795 + 2970207 * 2 ^ 59
def prefixEnd_2970207 : Nat := 4983230072969 + 3 ^ 40 * 2970207 * 2
def baseEnd_2970207 : Nat := 1016762556232643856768515

theorem tailTrace_2970207 : CollatzResearch.WordTrace tailWord_2970207 prefixEnd_2970207 1016762556232643856768515 := by
  unfold tailWord_2970207
  simp only [CollatzResearch.WordTrace]
  refine ⟨108332349150454784814804875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72221566100303189876536583 108332349150454784814804875)
  ·
    refine ⟨162498523725682177222207313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108332349150454784814804875 162498523725682177222207313)
    ·
      refine ⟨121873892794261632916655485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162498523725682177222207313 121873892794261632916655485)
      ·
        refine ⟨45702709797848112343745807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121873892794261632916655485 45702709797848112343745807)
        ·
          refine ⟨68554064696772168515618711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45702709797848112343745807 68554064696772168515618711)
          ·
            refine ⟨102831097045158252773428067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68554064696772168515618711 102831097045158252773428067)
            ·
              refine ⟨154246645567737379160142101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102831097045158252773428067 154246645567737379160142101)
              ·
                refine ⟨7230311510987689648131661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 154246645567737379160142101 7230311510987689648131661)
                ·
                  refine ⟨2711366816620383618049373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7230311510987689648131661 2711366816620383618049373)
                  ·
                    refine ⟨1016762556232643856768515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2711366816620383618049373 1016762556232643856768515)
                    ·
                      rfl

theorem cell22_2970207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 6, 3, 3].length) (baseStart_2970207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2970207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2970207 prefixEnd_2970207 := by exact prefixLift 2970207
  have htrace : WordTrace (prefixWord ++ tailWord_2970207) baseStart_2970207 baseEnd_2970207 := by
    simpa [prefixWord, tailWord_2970207, baseEnd_2970207] using wordTrace_append hprefix tailTrace_2970207
  have hstable : (prefixWord ++ tailWord_2970207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2970207).length < 2 ^ (prefixWord ++ tailWord_2970207).sum := by decide
  have hdescent : baseEnd_2970207 < baseStart_2970207 := by decide
  rcases family_descends (prefixWord ++ tailWord_2970207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2970220 : List Nat := [2, 2, 1, 1, 3, 1, 2, 1, 9]
def baseStart_2970220 : Nat := 118140960795 + 2970220 * 2 ^ 59
def prefixEnd_2970220 : Nat := 4983230072969 + 3 ^ 40 * 2970220 * 2
def baseEnd_2970220 : Nat := 338922335466105385397825

theorem tailTrace_2970220 : CollatzResearch.WordTrace tailWord_2970220 prefixEnd_2970220 338922335466105385397825 := by
  unfold tailWord_2970220
  simp only [CollatzResearch.WordTrace]
  refine ⟨54166411649703844017514057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72221882199605125356685409 54166411649703844017514057)
  ·
    refine ⟨40624808737277883013135543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54166411649703844017514057 40624808737277883013135543)
    ·
      refine ⟨60937213105916824519703315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40624808737277883013135543 60937213105916824519703315)
      ·
        refine ⟨91405819658875236779554973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60937213105916824519703315 91405819658875236779554973)
        ·
          refine ⟨34277182372078213792333115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91405819658875236779554973 34277182372078213792333115)
          ·
            refine ⟨51415773558117320688499673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34277182372078213792333115 51415773558117320688499673)
            ·
              refine ⟨38561830168587990516374755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51415773558117320688499673 38561830168587990516374755)
              ·
                refine ⟨57842745252881985774562133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38561830168587990516374755 57842745252881985774562133)
                ·
                  refine ⟨338922335466105385397825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 57842745252881985774562133 338922335466105385397825)
                  ·
                    rfl

theorem cell22_2970220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 9].length) (baseStart_2970220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2970220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2970220 prefixEnd_2970220 := by exact prefixLift 2970220
  have htrace : WordTrace (prefixWord ++ tailWord_2970220) baseStart_2970220 baseEnd_2970220 := by
    simpa [prefixWord, tailWord_2970220, baseEnd_2970220] using wordTrace_append hprefix tailTrace_2970220
  have hstable : (prefixWord ++ tailWord_2970220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2970220).length < 2 ^ (prefixWord ++ tailWord_2970220).sum := by decide
  have hdescent : baseEnd_2970220 < baseStart_2970220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2970220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2970241 : List Nat := [1, 2, 4, 2, 1, 1, 3, 4, 1, 3]
def baseStart_2970241 : Nat := 118140960795 + 2970241 * 2 ^ 59
def prefixEnd_2970241 : Nat := 4983230072969 + 3 ^ 40 * 2970241 * 2
def baseEnd_2970241 : Nat := 1016774195127479101418411

theorem tailTrace_2970241 : CollatzResearch.WordTrace tailWord_2970241 prefixEnd_2970241 1016774195127479101418411 := by
  unfold tailWord_2970241
  simp only [CollatzResearch.WordTrace]
  refine ⟨108333589232331608621542577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72222392821554405747695051 108333589232331608621542577)
  ·
    refine ⟨81250191924248706466156933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108333589232331608621542577 81250191924248706466156933)
    ·
      refine ⟨15234410985796632462404425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81250191924248706466156933 15234410985796632462404425)
      ·
        refine ⟨11425808239347474346803319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15234410985796632462404425 11425808239347474346803319)
        ·
          refine ⟨17138712359021211520204979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11425808239347474346803319 17138712359021211520204979)
          ·
            refine ⟨25708068538531817280307469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17138712359021211520204979 25708068538531817280307469)
            ·
              refine ⟨9640525701949431480115301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25708068538531817280307469 9640525701949431480115301)
              ·
                refine ⟨1807598569115518402521619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9640525701949431480115301 1807598569115518402521619)
                ·
                  refine ⟨2711397853673277603782429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1807598569115518402521619 2711397853673277603782429)
                  ·
                    refine ⟨1016774195127479101418411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2711397853673277603782429 1016774195127479101418411)
                    ·
                      rfl

theorem cell22_2970241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 4, 1, 3].length) (baseStart_2970241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2970241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2970241 prefixEnd_2970241 := by exact prefixLift 2970241
  have htrace : WordTrace (prefixWord ++ tailWord_2970241) baseStart_2970241 baseEnd_2970241 := by
    simpa [prefixWord, tailWord_2970241, baseEnd_2970241] using wordTrace_append hprefix tailTrace_2970241
  have hstable : (prefixWord ++ tailWord_2970241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2970241).length < 2 ^ (prefixWord ++ tailWord_2970241).sum := by decide
  have hdescent : baseEnd_2970241 < baseStart_2970241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2970241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2970312 : List Nat := [2, 1, 3, 1, 2, 3, 1, 2, 1, 6]
def baseStart_2970312 : Nat := 118140960795 + 2970312 * 2 ^ 59
def prefixEnd_2970312 : Nat := 4983230072969 + 3 ^ 40 * 2970312 * 2
def baseEnd_2970312 : Nat := 1016798499878458582893193

theorem tailTrace_2970312 : CollatzResearch.WordTrace tailWord_2970312 prefixEnd_2970312 1016798499878458582893193 := by
  unfold tailWord_2970312
  simp only [CollatzResearch.WordTrace]
  refine ⟨54168089407537193873688595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72224119210049591831584793 54168089407537193873688595)
  ·
    refine ⟨81252134111305790810532893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54168089407537193873688595 81252134111305790810532893)
    ·
      refine ⟨30469550291739671553949835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81252134111305790810532893 30469550291739671553949835)
      ·
        refine ⟨45704325437609507330924753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30469550291739671553949835 45704325437609507330924753)
        ·
          refine ⟨34278244078207130498193565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45704325437609507330924753 34278244078207130498193565)
          ·
            refine ⟨12854341529327673936822587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34278244078207130498193565 12854341529327673936822587)
            ·
              refine ⟨19281512293991510905233881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12854341529327673936822587 19281512293991510905233881)
              ·
                refine ⟨14461134220493633178925411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19281512293991510905233881 14461134220493633178925411)
                ·
                  refine ⟨21691701330740449768388117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14461134220493633178925411 21691701330740449768388117)
                  ·
                    refine ⟨1016798499878458582893193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21691701330740449768388117 1016798499878458582893193)
                    ·
                      rfl

theorem cell22_2970312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 2, 1, 6].length) (baseStart_2970312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2970312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2970312 prefixEnd_2970312 := by exact prefixLift 2970312
  have htrace : WordTrace (prefixWord ++ tailWord_2970312) baseStart_2970312 baseEnd_2970312 := by
    simpa [prefixWord, tailWord_2970312, baseEnd_2970312] using wordTrace_append hprefix tailTrace_2970312
  have hstable : (prefixWord ++ tailWord_2970312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2970312).length < 2 ^ (prefixWord ++ tailWord_2970312).sum := by decide
  have hdescent : baseEnd_2970312 < baseStart_2970312 := by decide
  rcases family_descends (prefixWord ++ tailWord_2970312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2970314 : List Nat := [3, 1, 2, 1, 4, 1, 3, 1, 1, 5]
def baseStart_2970314 : Nat := 118140960795 + 2970314 * 2 ^ 59
def prefixEnd_2970314 : Nat := 4983230072969 + 3 ^ 40 * 2970314 * 2
def baseEnd_2970314 : Nat := 1016799184519331244343187

theorem tailTrace_2970314 : CollatzResearch.WordTrace tailWord_2970314 prefixEnd_2970314 1016799184519331244343187 := by
  unfold tailWord_2970314
  simp only [CollatzResearch.WordTrace]
  refine ⟨27084062940266785522237499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72224167840711428059299997 27084062940266785522237499)
  ·
    refine ⟨40626094410400178283356249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27084062940266785522237499 40626094410400178283356249)
    ·
      refine ⟨30469570807800133712517187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40626094410400178283356249 30469570807800133712517187)
      ·
        refine ⟨45704356211700200568775781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30469570807800133712517187 45704356211700200568775781)
        ·
          refine ⟨8569566789693787606645459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45704356211700200568775781 8569566789693787606645459)
          ·
            refine ⟨12854350184540681409968189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8569566789693787606645459 12854350184540681409968189)
            ·
              refine ⟨4820381319202755528738071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12854350184540681409968189 4820381319202755528738071)
              ·
                refine ⟨7230571978804133293107107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4820381319202755528738071 7230571978804133293107107)
                ·
                  refine ⟨10845857968206199939660661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7230571978804133293107107 10845857968206199939660661)
                  ·
                    refine ⟨1016799184519331244343187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10845857968206199939660661 1016799184519331244343187)
                    ·
                      rfl

theorem cell22_2970314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 1, 1, 5].length) (baseStart_2970314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2970314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2970314 prefixEnd_2970314 := by exact prefixLift 2970314
  have htrace : WordTrace (prefixWord ++ tailWord_2970314) baseStart_2970314 baseEnd_2970314 := by
    simpa [prefixWord, tailWord_2970314, baseEnd_2970314] using wordTrace_append hprefix tailTrace_2970314
  have hstable : (prefixWord ++ tailWord_2970314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2970314).length < 2 ^ (prefixWord ++ tailWord_2970314).sum := by decide
  have hdescent : baseEnd_2970314 < baseStart_2970314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2970314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2970327 : List Nat := [1, 1, 3, 2, 1, 5, 1, 8]
def baseStart_2970327 : Nat := 118140960795 + 2970327 * 2 ^ 59
def prefixEnd_2970327 : Nat := 4983230072969 + 3 ^ 40 * 2970327 * 2
def baseEnd_2970327 : Nat := 112978181631667060418683

theorem tailTrace_2970327 : CollatzResearch.WordTrace tailWord_2970327 prefixEnd_2970327 112978181631667060418683 := by
  unfold tailWord_2970327
  simp only [CollatzResearch.WordTrace]
  refine ⟨108336725910020045309173235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72224483940013363539448823 108336725910020045309173235)
  ·
    refine ⟨162505088865030067963759853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108336725910020045309173235 162505088865030067963759853)
    ·
      refine ⟨60939408324386275486409945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162505088865030067963759853 60939408324386275486409945)
      ·
        refine ⟨45704556243289706614807459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60939408324386275486409945 45704556243289706614807459)
        ·
          refine ⟨68556834364934559922211189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45704556243289706614807459 68556834364934559922211189)
          ·
            refine ⟨6427203221712614992707299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 68556834364934559922211189 6427203221712614992707299)
            ·
              refine ⟨9640804832568922489060949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6427203221712614992707299 9640804832568922489060949)
              ·
                refine ⟨112978181631667060418683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9640804832568922489060949 112978181631667060418683)
                ·
                  rfl

theorem cell22_2970327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 8].length) (baseStart_2970327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2970327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2970327 prefixEnd_2970327 := by exact prefixLift 2970327
  have htrace : WordTrace (prefixWord ++ tailWord_2970327) baseStart_2970327 baseEnd_2970327 := by
    simpa [prefixWord, tailWord_2970327, baseEnd_2970327] using wordTrace_append hprefix tailTrace_2970327
  have hstable : (prefixWord ++ tailWord_2970327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2970327).length < 2 ^ (prefixWord ++ tailWord_2970327).sum := by decide
  have hdescent : baseEnd_2970327 < baseStart_2970327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2970327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2970344 : List Nat := [2, 1, 4, 1, 4, 2, 8]
def baseStart_2970344 : Nat := 118140960795 + 2970344 * 2 ^ 59
def prefixEnd_2970344 : Nat := 4983230072969 + 3 ^ 40 * 2970344 * 2
def baseEnd_2970344 : Nat := 37659609412311895040485

theorem tailTrace_2970344 : CollatzResearch.WordTrace tailWord_2970344 prefixEnd_2970344 37659609412311895040485 := by
  unfold tailWord_2970344
  simp only [CollatzResearch.WordTrace]
  refine ⟨54168672975479228606271043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72224897300638971475028057 54168672975479228606271043)
  ·
    refine ⟨81253009463218842909406565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54168672975479228606271043 81253009463218842909406565)
    ·
      refine ⟨15234939274353533045513731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81253009463218842909406565 15234939274353533045513731)
      ·
        refine ⟨22852408911530299568270597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15234939274353533045513731 22852408911530299568270597)
        ·
          refine ⟨4284826670911931169050737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22852408911530299568270597 4284826670911931169050737)
          ·
            refine ⟨3213620003183948376788053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4284826670911931169050737 3213620003183948376788053)
            ·
              refine ⟨37659609412311895040485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3213620003183948376788053 37659609412311895040485)
              ·
                rfl

theorem cell22_2970344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 8].length) (baseStart_2970344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2970344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2970344 prefixEnd_2970344 := by exact prefixLift 2970344
  have htrace : WordTrace (prefixWord ++ tailWord_2970344) baseStart_2970344 baseEnd_2970344 := by
    simpa [prefixWord, tailWord_2970344, baseEnd_2970344] using wordTrace_append hprefix tailTrace_2970344
  have hstable : (prefixWord ++ tailWord_2970344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2970344).length < 2 ^ (prefixWord ++ tailWord_2970344).sum := by decide
  have hdescent : baseEnd_2970344 < baseStart_2970344 := by decide
  rcases family_descends (prefixWord ++ tailWord_2970344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2970419 : List Nat := [1, 1, 1, 2, 6, 1, 1, 2, 3, 4]
def baseStart_2970419 : Nat := 118140960795 + 2970419 * 2 ^ 59
def prefixEnd_2970419 : Nat := 4983230072969 + 3 ^ 40 * 2970419 * 2
def baseEnd_2970419 : Nat := 1016835128165145970467865

theorem tailTrace_2970419 : CollatzResearch.WordTrace tailWord_2970419 prefixEnd_2970419 1016835128165145970467865 := by
  unfold tailWord_2970419
  simp only [CollatzResearch.WordTrace]
  refine ⟨108340081425686745021522311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72226720950457830014348207 108340081425686745021522311)
  ·
    refine ⟨162510122138530117532283467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108340081425686745021522311 162510122138530117532283467)
    ·
      refine ⟨243765183207795176298425201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162510122138530117532283467 243765183207795176298425201)
      ·
        refine ⟨182823887405846382223818901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243765183207795176298425201 182823887405846382223818901)
        ·
          refine ⟨8569869722149049166741511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 182823887405846382223818901 8569869722149049166741511)
          ·
            refine ⟨12854804583223573750112267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8569869722149049166741511 12854804583223573750112267)
            ·
              refine ⟨19282206874835360625168401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12854804583223573750112267 19282206874835360625168401)
              ·
                refine ⟨14461655156126520468876301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19282206874835360625168401 14461655156126520468876301)
                ·
                  refine ⟨5423120683547445175828613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14461655156126520468876301 5423120683547445175828613)
                  ·
                    refine ⟨1016835128165145970467865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5423120683547445175828613 1016835128165145970467865)
                    ·
                      rfl

theorem cell22_2970419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 2, 3, 4].length) (baseStart_2970419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2970419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2970419 prefixEnd_2970419 := by exact prefixLift 2970419
  have htrace : WordTrace (prefixWord ++ tailWord_2970419) baseStart_2970419 baseEnd_2970419 := by
    simpa [prefixWord, tailWord_2970419, baseEnd_2970419] using wordTrace_append hprefix tailTrace_2970419
  have hstable : (prefixWord ++ tailWord_2970419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2970419).length < 2 ^ (prefixWord ++ tailWord_2970419).sum := by decide
  have hdescent : baseEnd_2970419 < baseStart_2970419 := by decide
  rcases family_descends (prefixWord ++ tailWord_2970419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2970464 : List Nat := [2, 1, 1, 3, 3, 1, 2, 1, 4, 4]
def baseStart_2970464 : Nat := 118140960795 + 2970464 * 2 ^ 59
def prefixEnd_2970464 : Nat := 4983230072969 + 3 ^ 40 * 2970464 * 2
def baseEnd_2970464 : Nat := 1016850532584780853092727

theorem tailTrace_2970464 : CollatzResearch.WordTrace tailWord_2970464 prefixEnd_2970464 1016850532584780853092727 := by
  unfold tailWord_2970464
  simp only [CollatzResearch.WordTrace]
  refine ⟨54170861355261858853455223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72227815140349145137940297 54170861355261858853455223)
  ·
    refine ⟨81256292032892788280182835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54170861355261858853455223 81256292032892788280182835)
    ·
      refine ⟨121884438049339182420274253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81256292032892788280182835 121884438049339182420274253)
      ·
        refine ⟨45706664268502193407602845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121884438049339182420274253 45706664268502193407602845)
        ·
          refine ⟨17139999100688322527851067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45706664268502193407602845 17139999100688322527851067)
          ·
            refine ⟨25709998651032483791776601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17139999100688322527851067 25709998651032483791776601)
            ·
              refine ⟨19282498988274362843832451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25709998651032483791776601 19282498988274362843832451)
              ·
                refine ⟨28923748482411544265748677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19282498988274362843832451 28923748482411544265748677)
                ·
                  refine ⟨5423202840452164549827877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28923748482411544265748677 5423202840452164549827877)
                  ·
                    refine ⟨1016850532584780853092727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5423202840452164549827877 1016850532584780853092727)
                    ·
                      rfl

theorem cell22_2970464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 4, 4].length) (baseStart_2970464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2970464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2970464 prefixEnd_2970464 := by exact prefixLift 2970464
  have htrace : WordTrace (prefixWord ++ tailWord_2970464) baseStart_2970464 baseEnd_2970464 := by
    simpa [prefixWord, tailWord_2970464, baseEnd_2970464] using wordTrace_append hprefix tailTrace_2970464
  have hstable : (prefixWord ++ tailWord_2970464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2970464).length < 2 ^ (prefixWord ++ tailWord_2970464).sum := by decide
  have hdescent : baseEnd_2970464 < baseStart_2970464 := by decide
  rcases family_descends (prefixWord ++ tailWord_2970464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2970528 : List Nat := [2, 1, 1, 4, 1, 1, 2, 6, 1, 3]
def baseStart_2970528 : Nat := 118140960795 + 2970528 * 2 ^ 59
def prefixEnd_2970528 : Nat := 4983230072969 + 3 ^ 40 * 2970528 * 2
def baseEnd_2970528 : Nat := 1016872441092706019492531

theorem tailTrace_2970528 : CollatzResearch.WordTrace tailWord_2970528 prefixEnd_2970528 1016872441092706019492531 := by
  unfold tailWord_2970528
  simp only [CollatzResearch.WordTrace]
  refine ⟨54172028491145928318620119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72229371321527904424826825 54172028491145928318620119)
  ·
    refine ⟨81258042736718892477930179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54172028491145928318620119 81258042736718892477930179)
    ·
      refine ⟨121887064105078338716895269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81258042736718892477930179 121887064105078338716895269)
      ·
        refine ⟨22853824519702188509417863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 121887064105078338716895269 22853824519702188509417863)
        ·
          refine ⟨34280736779553282764126795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22853824519702188509417863 34280736779553282764126795)
          ·
            refine ⟨51421105169329924146190193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34280736779553282764126795 51421105169329924146190193)
            ·
              refine ⟨38565828876997443109642645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51421105169329924146190193 38565828876997443109642645)
              ·
                refine ⟨1807773228609255145764499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 38565828876997443109642645 1807773228609255145764499)
                ·
                  refine ⟨2711659842913882718646749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1807773228609255145764499 2711659842913882718646749)
                  ·
                    refine ⟨1016872441092706019492531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2711659842913882718646749 1016872441092706019492531)
                    ·
                      rfl

theorem cell22_2970528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 6, 1, 3].length) (baseStart_2970528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2970528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2970528 prefixEnd_2970528 := by exact prefixLift 2970528
  have htrace : WordTrace (prefixWord ++ tailWord_2970528) baseStart_2970528 baseEnd_2970528 := by
    simpa [prefixWord, tailWord_2970528, baseEnd_2970528] using wordTrace_append hprefix tailTrace_2970528
  have hstable : (prefixWord ++ tailWord_2970528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2970528).length < 2 ^ (prefixWord ++ tailWord_2970528).sum := by decide
  have hdescent : baseEnd_2970528 < baseStart_2970528 := by decide
  rcases family_descends (prefixWord ++ tailWord_2970528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2970635 : List Nat := [1, 1, 1, 1, 6, 4, 1, 2, 2, 3]
def baseStart_2970635 : Nat := 118140960795 + 2970635 * 2 ^ 59
def prefixEnd_2970635 : Nat := 4983230072969 + 3 ^ 40 * 2970635 * 2
def baseEnd_2970635 : Nat := 1016909069379393407067203

theorem tailTrace_2970635 : CollatzResearch.WordTrace tailWord_2970635 prefixEnd_2970635 1016909069379393407067203 := by
  unfold tailWord_2970635
  simp only [CollatzResearch.WordTrace]
  refine ⟨108347959592904213911385359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72231973061936142607590239 108347959592904213911385359)
  ·
    refine ⟨162521939389356320867078039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108347959592904213911385359 162521939389356320867078039)
    ·
      refine ⟨243782909084034481300617059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162521939389356320867078039 243782909084034481300617059)
      ·
        refine ⟨365674363626051721950925589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243782909084034481300617059 365674363626051721950925589)
        ·
          refine ⟨17140985794971174466449637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 365674363626051721950925589 17140985794971174466449637)
          ·
            refine ⟨3213934836557095212459307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17140985794971174466449637 3213934836557095212459307)
            ·
              refine ⟨4820902254835642818688961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3213934836557095212459307 4820902254835642818688961)
              ·
                refine ⟨3615676691126732114016721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4820902254835642818688961 3615676691126732114016721)
                ·
                  refine ⟨2711757518345049085512541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3615676691126732114016721 2711757518345049085512541)
                  ·
                    refine ⟨1016909069379393407067203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2711757518345049085512541 1016909069379393407067203)
                    ·
                      rfl

theorem cell22_2970635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 2, 2, 3].length) (baseStart_2970635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2970635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2970635 prefixEnd_2970635 := by exact prefixLift 2970635
  have htrace : WordTrace (prefixWord ++ tailWord_2970635) baseStart_2970635 baseEnd_2970635 := by
    simpa [prefixWord, tailWord_2970635, baseEnd_2970635] using wordTrace_append hprefix tailTrace_2970635
  have hstable : (prefixWord ++ tailWord_2970635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2970635).length < 2 ^ (prefixWord ++ tailWord_2970635).sum := by decide
  have hdescent : baseEnd_2970635 < baseStart_2970635 := by decide
  rcases family_descends (prefixWord ++ tailWord_2970635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2970652 : List Nat := [2, 2, 3, 1, 4, 1, 3, 1, 2, 3]
def baseStart_2970652 : Nat := 118140960795 + 2970652 * 2 ^ 59
def prefixEnd_2970652 : Nat := 4983230072969 + 3 ^ 40 * 2970652 * 2
def baseEnd_2970652 : Nat := 1016914888826811029392151

theorem tailTrace_2970652 : CollatzResearch.WordTrace tailWord_2970652 prefixEnd_2970652 1016914888826811029392151 := by
  unfold tailWord_2970652
  simp only [CollatzResearch.WordTrace]
  refine ⟨54174289816921312907377105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72232386422561750543169473 54174289816921312907377105)
  ·
    refine ⟨40630717362690984680532829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54174289816921312907377105 40630717362690984680532829)
    ·
      refine ⟨15236519011009119255199811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40630717362690984680532829 15236519011009119255199811)
      ·
        refine ⟨22854778516513678882799717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15236519011009119255199811 22854778516513678882799717)
        ·
          refine ⟨4285270971846314790524947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22854778516513678882799717 4285270971846314790524947)
          ·
            refine ⟨6427906457769472185787421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4285270971846314790524947 6427906457769472185787421)
            ·
              refine ⟨2410464921663552069670283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6427906457769472185787421 2410464921663552069670283)
              ·
                refine ⟨3615697382495328104505425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2410464921663552069670283 3615697382495328104505425)
                ·
                  refine ⟨2711773036871496078379069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3615697382495328104505425 2711773036871496078379069)
                  ·
                    refine ⟨1016914888826811029392151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2711773036871496078379069 1016914888826811029392151)
                    ·
                      rfl

theorem cell22_2970652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 3, 1, 2, 3].length) (baseStart_2970652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2970652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2970652 prefixEnd_2970652 := by exact prefixLift 2970652
  have htrace : WordTrace (prefixWord ++ tailWord_2970652) baseStart_2970652 baseEnd_2970652 := by
    simpa [prefixWord, tailWord_2970652, baseEnd_2970652] using wordTrace_append hprefix tailTrace_2970652
  have hstable : (prefixWord ++ tailWord_2970652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2970652).length < 2 ^ (prefixWord ++ tailWord_2970652).sum := by decide
  have hdescent : baseEnd_2970652 < baseStart_2970652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2970652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2970721 : List Nat := [1, 2, 3, 1, 1, 2, 2, 4, 6]
def baseStart_2970721 : Nat := 118140960795 + 2970721 * 2 ^ 59
def prefixEnd_2970721 : Nat := 4983230072969 + 3 ^ 40 * 2970721 * 2
def baseEnd_2970721 : Nat := 338979502978972616472313

theorem tailTrace_2970721 : CollatzResearch.WordTrace tailWord_2970721 prefixEnd_2970721 338979502978972616472313 := by
  unfold tailWord_2970721
  simp only [CollatzResearch.WordTrace]
  refine ⟨108351096270592650599016017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72234064180395100399344011 108351096270592650599016017)
  ·
    refine ⟨81263322202944487949262013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108351096270592650599016017 81263322202944487949262013)
    ·
      refine ⟨30473745826104182980973255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81263322202944487949262013 30473745826104182980973255)
      ·
        refine ⟨45710618739156274471459883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30473745826104182980973255 45710618739156274471459883)
        ·
          refine ⟨68565928108734411707189825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45710618739156274471459883 68565928108734411707189825)
          ·
            refine ⟨51424446081550808780392369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68565928108734411707189825 51424446081550808780392369)
            ·
              refine ⟨38568334561163106585294277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51424446081550808780392369 38568334561163106585294277)
              ·
                refine ⟨7231562730218082484742677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38568334561163106585294277 7231562730218082484742677)
                ·
                  refine ⟨338979502978972616472313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7231562730218082484742677 338979502978972616472313)
                  ·
                    rfl

theorem cell22_2970721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 4, 6].length) (baseStart_2970721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2970721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2970721 prefixEnd_2970721 := by exact prefixLift 2970721
  have htrace : WordTrace (prefixWord ++ tailWord_2970721) baseStart_2970721 baseEnd_2970721 := by
    simpa [prefixWord, tailWord_2970721, baseEnd_2970721] using wordTrace_append hprefix tailTrace_2970721
  have hstable : (prefixWord ++ tailWord_2970721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2970721).length < 2 ^ (prefixWord ++ tailWord_2970721).sum := by decide
  have hdescent : baseEnd_2970721 < baseStart_2970721 := by decide
  rcases family_descends (prefixWord ++ tailWord_2970721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2970770 : List Nat := [3, 2, 3, 1, 1, 3, 2, 1, 1, 5]
def baseStart_2970770 : Nat := 118140960795 + 2970770 * 2 ^ 59
def prefixEnd_2970770 : Nat := 4983230072969 + 3 ^ 40 * 2970770 * 2
def baseEnd_2970770 : Nat := 1016955282638298054941789

theorem tailTrace_2970770 : CollatzResearch.WordTrace tailWord_2970770 prefixEnd_2970770 1016955282638298054941789 := by
  unfold tailWord_2970770
  simp only [CollatzResearch.WordTrace]
  refine ⟨27088220861853782991887441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72235255631610087978366509 27088220861853782991887441)
  ·
    refine ⟨20316165646390337243915581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27088220861853782991887441 20316165646390337243915581)
    ·
      refine ⟨7618562117396376466468343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20316165646390337243915581 7618562117396376466468343)
      ·
        refine ⟨11427843176094564699702515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7618562117396376466468343 11427843176094564699702515)
        ·
          refine ⟨17141764764141847049553773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11427843176094564699702515 17141764764141847049553773)
          ·
            refine ⟨6428161786553192643582665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17141764764141847049553773 6428161786553192643582665)
            ·
              refine ⟨4821121339914894482686999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6428161786553192643582665 4821121339914894482686999)
              ·
                refine ⟨7231682009872341724030499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4821121339914894482686999 7231682009872341724030499)
                ·
                  refine ⟨10847523014808512586045749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7231682009872341724030499 10847523014808512586045749)
                  ·
                    refine ⟨1016955282638298054941789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10847523014808512586045749 1016955282638298054941789)
                    ·
                      rfl

theorem cell22_2970770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_2970770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2970770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2970770 prefixEnd_2970770 := by exact prefixLift 2970770
  have htrace : WordTrace (prefixWord ++ tailWord_2970770) baseStart_2970770 baseEnd_2970770 := by
    simpa [prefixWord, tailWord_2970770, baseEnd_2970770] using wordTrace_append hprefix tailTrace_2970770
  have hstable : (prefixWord ++ tailWord_2970770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2970770).length < 2 ^ (prefixWord ++ tailWord_2970770).sum := by decide
  have hdescent : baseEnd_2970770 < baseStart_2970770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2970770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2970796 : List Nat := [2, 2, 1, 1, 1, 1, 1, 4, 1, 8]
def baseStart_2970796 : Nat := 118140960795 + 2970796 * 2 ^ 59
def prefixEnd_2970796 : Nat := 4983230072969 + 3 ^ 40 * 2970796 * 2
def baseEnd_2970796 : Nat := 1016964182969642653791709

theorem tailTrace_2970796 : CollatzResearch.WordTrace tailWord_2970796 prefixEnd_2970796 1016964182969642653791709 := by
  unfold tailWord_2970796
  simp only [CollatzResearch.WordTrace]
  refine ⟨54176915872660469203998121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72235887830213958938664161 54176915872660469203998121)
  ·
    refine ⟨40632686904495351902998591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54176915872660469203998121 40632686904495351902998591)
    ·
      refine ⟨60949030356743027854497887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40632686904495351902998591 60949030356743027854497887)
      ·
        refine ⟨91423545535114541781746831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60949030356743027854497887 91423545535114541781746831)
        ·
          refine ⟨137135318302671812672620247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91423545535114541781746831 137135318302671812672620247)
          ·
            refine ⟨205702977454007719008930371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137135318302671812672620247 205702977454007719008930371)
            ·
              refine ⟨308554466181011578513395557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205702977454007719008930371 308554466181011578513395557)
              ·
                refine ⟨57853962408939670971261667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 308554466181011578513395557 57853962408939670971261667)
                ·
                  refine ⟨86780943613409506456892501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57853962408939670971261667 86780943613409506456892501)
                  ·
                    refine ⟨1016964182969642653791709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 86780943613409506456892501 1016964182969642653791709)
                    ·
                      rfl

theorem cell22_2970796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 8].length) (baseStart_2970796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2970796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2970796 prefixEnd_2970796 := by exact prefixLift 2970796
  have htrace : WordTrace (prefixWord ++ tailWord_2970796) baseStart_2970796 baseEnd_2970796 := by
    simpa [prefixWord, tailWord_2970796, baseEnd_2970796] using wordTrace_append hprefix tailTrace_2970796
  have hstable : (prefixWord ++ tailWord_2970796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2970796).length < 2 ^ (prefixWord ++ tailWord_2970796).sum := by decide
  have hdescent : baseEnd_2970796 < baseStart_2970796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2970796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2970849 : List Nat := [1, 2, 3, 1, 3, 4, 1, 3, 1, 3]
def baseStart_2970849 : Nat := 118140960795 + 2970849 * 2 ^ 59
def prefixEnd_2970849 : Nat := 4983230072969 + 3 ^ 40 * 2970849 * 2
def baseEnd_2970849 : Nat := 1016982325952768182216547

theorem tailTrace_2970849 : CollatzResearch.WordTrace tailWord_2970849 prefixEnd_2970849 1016982325952768182216547 := by
  unfold tailWord_2970849
  simp only [CollatzResearch.WordTrace]
  refine ⟨108355764814128928459675601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72237176542752618973117067 108355764814128928459675601)
  ·
    refine ⟨81266823610596696344756701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108355764814128928459675601 81266823610596696344756701)
    ·
      refine ⟨30475058853973761129283763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81266823610596696344756701 30475058853973761129283763)
      ·
        refine ⟨45712588280960641693925645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30475058853973761129283763 45712588280960641693925645)
        ·
          refine ⟨17142220605360240635222117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45712588280960641693925645 17142220605360240635222117)
          ·
            refine ⟨3214166363505045119104147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17142220605360240635222117 3214166363505045119104147)
            ·
              refine ⟨4821249545257567678656221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3214166363505045119104147 4821249545257567678656221)
              ·
                refine ⟨1807968579471587879496083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4821249545257567678656221 1807968579471587879496083)
                ·
                  refine ⟨2711952869207381819244125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1807968579471587879496083 2711952869207381819244125)
                  ·
                    refine ⟨1016982325952768182216547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2711952869207381819244125 1016982325952768182216547)
                    ·
                      rfl

theorem cell22_2970849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 3, 1, 3].length) (baseStart_2970849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2970849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2970849 prefixEnd_2970849 := by exact prefixLift 2970849
  have htrace : WordTrace (prefixWord ++ tailWord_2970849) baseStart_2970849 baseEnd_2970849 := by
    simpa [prefixWord, tailWord_2970849, baseEnd_2970849] using wordTrace_append hprefix tailTrace_2970849
  have hstable : (prefixWord ++ tailWord_2970849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2970849).length < 2 ^ (prefixWord ++ tailWord_2970849).sum := by decide
  have hdescent : baseEnd_2970849 < baseStart_2970849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2970849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2970866 : List Nat := [3, 2, 1, 3, 3, 1, 3, 2, 1, 3]
def baseStart_2970866 : Nat := 118140960795 + 2970866 * 2 ^ 59
def prefixEnd_2970866 : Nat := 4983230072969 + 3 ^ 40 * 2970866 * 2
def baseEnd_2970866 : Nat := 1016988145400185804541495

theorem tailTrace_2970866 : CollatzResearch.WordTrace tailWord_2970866 prefixEnd_2970866 1016988145400185804541495 := by
  unfold tailWord_2970866
  simp only [CollatzResearch.WordTrace]
  refine ⟨27089096213766835090761113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72237589903378226908696301 27089096213766835090761113)
  ·
    refine ⟨20316822160325126318070835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27089096213766835090761113 20316822160325126318070835)
    ·
      refine ⟨30475233240487689477106253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20316822160325126318070835 30475233240487689477106253)
      ·
        refine ⟨11428212465182883553914845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30475233240487689477106253 11428212465182883553914845)
        ·
          refine ⟨4285579674443581332718067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11428212465182883553914845 4285579674443581332718067)
          ·
            refine ⟨6428369511665371999077101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4285579674443581332718067 6428369511665371999077101)
            ·
              refine ⟨2410638566874514499653913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6428369511665371999077101 2410638566874514499653913)
              ·
                refine ⟨1807978925155885874740435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2410638566874514499653913 1807978925155885874740435)
                ·
                  refine ⟨2711968387733828812110653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1807978925155885874740435 2711968387733828812110653)
                  ·
                    refine ⟨1016988145400185804541495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2711968387733828812110653 1016988145400185804541495)
                    ·
                      rfl

theorem cell22_2970866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 3, 2, 1, 3].length) (baseStart_2970866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2970866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2970866 prefixEnd_2970866 := by exact prefixLift 2970866
  have htrace : WordTrace (prefixWord ++ tailWord_2970866) baseStart_2970866 baseEnd_2970866 := by
    simpa [prefixWord, tailWord_2970866, baseEnd_2970866] using wordTrace_append hprefix tailTrace_2970866
  have hstable : (prefixWord ++ tailWord_2970866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2970866).length < 2 ^ (prefixWord ++ tailWord_2970866).sum := by decide
  have hdescent : baseEnd_2970866 < baseStart_2970866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2970866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2970892 : List Nat := [2, 2, 1, 2, 2, 5, 1, 2, 1, 4]
def baseStart_2970892 : Nat := 118140960795 + 2970892 * 2 ^ 59
def prefixEnd_2970892 : Nat := 4983230072969 + 3 ^ 40 * 2970892 * 2
def baseEnd_2970892 : Nat := 1016997045731530403391415

theorem tailTrace_2970892 : CollatzResearch.WordTrace tailWord_2970892 prefixEnd_2970892 1016997045731530403391415 := by
  unfold tailWord_2970892
  simp only [CollatzResearch.WordTrace]
  refine ⟨54178666576486573401745465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72238222101982097868993953 54178666576486573401745465)
  ·
    refine ⟨40633999932364930051309099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54178666576486573401745465 40633999932364930051309099)
    ·
      refine ⟨60950999898547395076963649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40633999932364930051309099 60950999898547395076963649)
      ·
        refine ⟨45713249923910546307722737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60950999898547395076963649 45713249923910546307722737)
        ·
          refine ⟨34284937442932909730792053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45713249923910546307722737 34284937442932909730792053)
          ·
            refine ⟨3214212885274960287261755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34284937442932909730792053 3214212885274960287261755)
            ·
              refine ⟨4821319327912440430892633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3214212885274960287261755 4821319327912440430892633)
              ·
                refine ⟨3615989495934330323169475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4821319327912440430892633 3615989495934330323169475)
                ·
                  refine ⟨5423984243901495484754213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3615989495934330323169475 5423984243901495484754213)
                  ·
                    refine ⟨1016997045731530403391415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5423984243901495484754213 1016997045731530403391415)
                    ·
                      rfl

theorem cell22_2970892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 2, 1, 4].length) (baseStart_2970892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2970892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2970892 prefixEnd_2970892 := by exact prefixLift 2970892
  have htrace : WordTrace (prefixWord ++ tailWord_2970892) baseStart_2970892 baseEnd_2970892 := by
    simpa [prefixWord, tailWord_2970892, baseEnd_2970892] using wordTrace_append hprefix tailTrace_2970892
  have hstable : (prefixWord ++ tailWord_2970892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2970892).length < 2 ^ (prefixWord ++ tailWord_2970892).sum := by decide
  have hdescent : baseEnd_2970892 < baseStart_2970892 := by decide
  rcases family_descends (prefixWord ++ tailWord_2970892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2970909 : List Nat := [1, 4, 2, 3, 1, 2, 3, 1, 1, 4]
def baseStart_2970909 : Nat := 118140960795 + 2970909 * 2 ^ 59
def prefixEnd_2970909 : Nat := 4983230072969 + 3 ^ 40 * 2970909 * 2
def baseEnd_2970909 : Nat := 1017002865178948025716363

theorem tailTrace_2970909 : CollatzResearch.WordTrace tailWord_2970909 prefixEnd_2970909 1017002865178948025716363 := by
  unfold tailWord_2970909
  simp only [CollatzResearch.WordTrace]
  refine ⟨108357953193911558706859781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72238635462607705804573187 108357953193911558706859781)
  ·
    refine ⟨20317116223858417257536209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108357953193911558706859781 20317116223858417257536209)
    ·
      refine ⟨15237837167893812943152157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20317116223858417257536209 15237837167893812943152157)
      ·
        refine ⟨5714188937960179853682059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15237837167893812943152157 5714188937960179853682059)
        ·
          refine ⟨8571283406940269780523089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5714188937960179853682059 8571283406940269780523089)
          ·
            refine ⟨6428462555205202335392317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8571283406940269780523089 6428462555205202335392317)
            ·
              refine ⟨2410673458201950875772119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6428462555205202335392317 2410673458201950875772119)
              ·
                refine ⟨3616010187302926313658179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2410673458201950875772119 3616010187302926313658179)
                ·
                  refine ⟨5424015280954389470487269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3616010187302926313658179 5424015280954389470487269)
                  ·
                    refine ⟨1017002865178948025716363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5424015280954389470487269 1017002865178948025716363)
                    ·
                      rfl

theorem cell22_2970909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 3, 1, 1, 4].length) (baseStart_2970909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2970909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2970909 prefixEnd_2970909 := by exact prefixLift 2970909
  have htrace : WordTrace (prefixWord ++ tailWord_2970909) baseStart_2970909 baseEnd_2970909 := by
    simpa [prefixWord, tailWord_2970909, baseEnd_2970909] using wordTrace_append hprefix tailTrace_2970909
  have hstable : (prefixWord ++ tailWord_2970909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2970909).length < 2 ^ (prefixWord ++ tailWord_2970909).sum := by decide
  have hdescent : baseEnd_2970909 < baseStart_2970909 := by decide
  rcases family_descends (prefixWord ++ tailWord_2970909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2970963 : List Nat := [1, 1, 1, 2, 1, 1, 6, 2, 7]
def baseStart_2970963 : Nat := 118140960795 + 2970963 * 2 ^ 59
def prefixEnd_2970963 : Nat := 4983230072969 + 3 ^ 40 * 2970963 * 2
def baseEnd_2970963 : Nat := 339007116827503294955399

theorem tailTrace_2970963 : CollatzResearch.WordTrace tailWord_2970963 prefixEnd_2970963 339007116827503294955399 := by
  unfold tailWord_2970963
  simp only [CollatzResearch.WordTrace]
  refine ⟨108359922735715925929325543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72239948490477283952883695 108359922735715925929325543)
  ·
    refine ⟨162539884103573888893988315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108359922735715925929325543 162539884103573888893988315)
    ·
      refine ⟨243809826155360833340982473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162539884103573888893988315 243809826155360833340982473)
      ·
        refine ⟨182857369616520625005736855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243809826155360833340982473 182857369616520625005736855)
        ·
          refine ⟨274286054424780937508605283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182857369616520625005736855 274286054424780937508605283)
          ·
            refine ⟨411429081637171406262907925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274286054424780937508605283 411429081637171406262907925)
            ·
              refine ⟨19285738201742409668573809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 411429081637171406262907925 19285738201742409668573809)
              ·
                refine ⟨14464303651306807251430357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19285738201742409668573809 14464303651306807251430357)
                ·
                  refine ⟨339007116827503294955399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14464303651306807251430357 339007116827503294955399)
                  ·
                    rfl

theorem cell22_2970963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 2, 7].length) (baseStart_2970963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2970963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2970963 prefixEnd_2970963 := by exact prefixLift 2970963
  have htrace : WordTrace (prefixWord ++ tailWord_2970963) baseStart_2970963 baseEnd_2970963 := by
    simpa [prefixWord, tailWord_2970963, baseEnd_2970963] using wordTrace_append hprefix tailTrace_2970963
  have hstable : (prefixWord ++ tailWord_2970963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2970963).length < 2 ^ (prefixWord ++ tailWord_2970963).sum := by decide
  have hdescent : baseEnd_2970963 < baseStart_2970963 := by decide
  rcases family_descends (prefixWord ++ tailWord_2970963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2970980 : List Nat := [2, 3, 1, 1, 3, 3, 1, 1, 7]
def baseStart_2970980 : Nat := 118140960795 + 2970980 * 2 ^ 59
def prefixEnd_2970980 : Nat := 4983230072969 + 3 ^ 40 * 2970980 * 2
def baseEnd_2970980 : Nat := 339009056643309169063715

theorem tailTrace_2970980 : CollatzResearch.WordTrace tailWord_2970980 prefixEnd_2970980 339009056643309169063715 := by
  unfold tailWord_2970980
  simp only [CollatzResearch.WordTrace]
  refine ⟨54180271388327168916347197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72240361851102891888462929 54180271388327168916347197)
  ·
    refine ⟨20317601770622688343630199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54180271388327168916347197 20317601770622688343630199)
    ·
      refine ⟨30476402655934032515445299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20317601770622688343630199 30476402655934032515445299)
      ·
        refine ⟨45714603983901048773167949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30476402655934032515445299 45714603983901048773167949)
        ·
          refine ⟨17142976493962893289937981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45714603983901048773167949 17142976493962893289937981)
          ·
            refine ⟨6428616185236084983726743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17142976493962893289937981 6428616185236084983726743)
            ·
              refine ⟨9642924277854127475590115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6428616185236084983726743 9642924277854127475590115)
              ·
                refine ⟨14464386416781191213385173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9642924277854127475590115 14464386416781191213385173)
                ·
                  refine ⟨339009056643309169063715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14464386416781191213385173 339009056643309169063715)
                  ·
                    rfl

theorem cell22_2970980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 1, 7].length) (baseStart_2970980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2970980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2970980 prefixEnd_2970980 := by exact prefixLift 2970980
  have htrace : WordTrace (prefixWord ++ tailWord_2970980) baseStart_2970980 baseEnd_2970980 := by
    simpa [prefixWord, tailWord_2970980, baseEnd_2970980] using wordTrace_append hprefix tailTrace_2970980
  have hstable : (prefixWord ++ tailWord_2970980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2970980).length < 2 ^ (prefixWord ++ tailWord_2970980).sum := by decide
  have hdescent : baseEnd_2970980 < baseStart_2970980 := by decide
  rcases family_descends (prefixWord ++ tailWord_2970980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2970984 : List Nat := [2, 1, 4, 2, 3, 1, 2, 1, 3, 3]
def baseStart_2970984 : Nat := 118140960795 + 2970984 * 2 ^ 59
def prefixEnd_2970984 : Nat := 4983230072969 + 3 ^ 40 * 2970984 * 2
def baseEnd_2970984 : Nat := 1017028539211672830091133

theorem tailTrace_2970984 : CollatzResearch.WordTrace tailWord_2970984 prefixEnd_2970984 1017028539211672830091133 := by
  unfold tailWord_2970984
  simp only [CollatzResearch.WordTrace]
  refine ⟨54180344334319923257920003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72240459112426564343893337 54180344334319923257920003)
  ·
    refine ⟨81270516501479884886880005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54180344334319923257920003 81270516501479884886880005)
    ·
      refine ⟨15238221844027478416290001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81270516501479884886880005 15238221844027478416290001)
      ·
        refine ⟨11428666383020608812217501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15238221844027478416290001 11428666383020608812217501)
        ·
          refine ⟨4285749893632728304581563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11428666383020608812217501 4285749893632728304581563)
          ·
            refine ⟨6428624840449092456872345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4285749893632728304581563 6428624840449092456872345)
            ·
              refine ⟨4821468630336819342654259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6428624840449092456872345 4821468630336819342654259)
              ·
                refine ⟨7232202945505229013981389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4821468630336819342654259 7232202945505229013981389)
                ·
                  refine ⟨2712076104564460880243021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7232202945505229013981389 2712076104564460880243021)
                  ·
                    refine ⟨1017028539211672830091133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2712076104564460880243021 1017028539211672830091133)
                    ·
                      rfl

theorem cell22_2970984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 1, 3, 3].length) (baseStart_2970984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2970984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2970984 prefixEnd_2970984 := by exact prefixLift 2970984
  have htrace : WordTrace (prefixWord ++ tailWord_2970984) baseStart_2970984 baseEnd_2970984 := by
    simpa [prefixWord, tailWord_2970984, baseEnd_2970984] using wordTrace_append hprefix tailTrace_2970984
  have hstable : (prefixWord ++ tailWord_2970984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2970984).length < 2 ^ (prefixWord ++ tailWord_2970984).sum := by decide
  have hdescent : baseEnd_2970984 < baseStart_2970984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2970984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2971042 : List Nat := [3, 3, 1, 2, 1, 2, 3, 1, 6]
def baseStart_2971042 : Nat := 118140960795 + 2971042 * 2 ^ 59
def prefixEnd_2971042 : Nat := 4983230072969 + 3 ^ 40 * 2971042 * 2
def baseEnd_2971042 : Nat := 339016131265660004046985

theorem tailTrace_2971042 : CollatzResearch.WordTrace tailWord_2971042 prefixEnd_2971042 339016131265660004046985 := by
  unfold tailWord_2971042
  simp only [CollatzResearch.WordTrace]
  refine ⟨27090701025607430605362845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72241869401619814947634253 27090701025607430605362845)
  ·
    refine ⟨10159012884602786477011067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27090701025607430605362845 10159012884602786477011067)
    ·
      refine ⟨15238519326904179715516601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10159012884602786477011067 15238519326904179715516601)
      ·
        refine ⟨11428889495178134786637451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15238519326904179715516601 11428889495178134786637451)
        ·
          refine ⟨17143334242767202179956177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11428889495178134786637451 17143334242767202179956177)
          ·
            refine ⟨12857500682075401634967133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17143334242767202179956177 12857500682075401634967133)
            ·
              refine ⟨4821562755778275613112675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12857500682075401634967133 4821562755778275613112675)
              ·
                refine ⟨7232344133667413419669013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4821562755778275613112675 7232344133667413419669013)
                ·
                  refine ⟨339016131265660004046985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7232344133667413419669013 339016131265660004046985)
                  ·
                    rfl

theorem cell22_2971042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 1, 6].length) (baseStart_2971042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2971042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2971042 prefixEnd_2971042 := by exact prefixLift 2971042
  have htrace : WordTrace (prefixWord ++ tailWord_2971042) baseStart_2971042 baseEnd_2971042 := by
    simpa [prefixWord, tailWord_2971042, baseEnd_2971042] using wordTrace_append hprefix tailTrace_2971042
  have hstable : (prefixWord ++ tailWord_2971042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2971042).length < 2 ^ (prefixWord ++ tailWord_2971042).sum := by decide
  have hdescent : baseEnd_2971042 < baseStart_2971042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2971042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2971048 : List Nat := [2, 1, 6, 1, 3, 1, 2, 1, 5]
def baseStart_2971048 : Nat := 118140960795 + 2971048 * 2 ^ 59
def prefixEnd_2971048 : Nat := 4983230072969 + 3 ^ 40 * 2971048 * 2
def baseEnd_2971048 : Nat := 339016815906532665496979

theorem tailTrace_2971048 : CollatzResearch.WordTrace tailWord_2971048 prefixEnd_2971048 339016815906532665496979 := by
  unfold tailWord_2971048
  simp only [CollatzResearch.WordTrace]
  refine ⟨54181511470203992723084899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72242015293605323630779865 54181511470203992723084899)
  ·
    refine ⟨81272267205305989084627349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54181511470203992723084899 81272267205305989084627349)
    ·
      refine ⟨3809637525248718238341907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 81272267205305989084627349 3809637525248718238341907)
      ·
        refine ⟨5714456287873077357512861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3809637525248718238341907 5714456287873077357512861)
        ·
          refine ⟨2142921107952404009067323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5714456287873077357512861 2142921107952404009067323)
          ·
            refine ⟨3214381661928606013600985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2142921107952404009067323 3214381661928606013600985)
            ·
              refine ⟨2410786246446454510200739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3214381661928606013600985 2410786246446454510200739)
              ·
                refine ⟨3616179369669681765301109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2410786246446454510200739 3616179369669681765301109)
                ·
                  refine ⟨339016815906532665496979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3616179369669681765301109 339016815906532665496979)
                  ·
                    rfl

theorem cell22_2971048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 2, 1, 5].length) (baseStart_2971048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2971048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2971048 prefixEnd_2971048 := by exact prefixLift 2971048
  have htrace : WordTrace (prefixWord ++ tailWord_2971048) baseStart_2971048 baseEnd_2971048 := by
    simpa [prefixWord, tailWord_2971048, baseEnd_2971048] using wordTrace_append hprefix tailTrace_2971048
  have hstable : (prefixWord ++ tailWord_2971048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2971048).length < 2 ^ (prefixWord ++ tailWord_2971048).sum := by decide
  have hdescent : baseEnd_2971048 < baseStart_2971048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2971048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2971130 : List Nat := [3, 1, 1, 1, 1, 2, 3, 2, 1, 7]
def baseStart_2971130 : Nat := 118140960795 + 2971130 * 2 ^ 59
def prefixEnd_2971130 : Nat := 4983230072969 + 3 ^ 40 * 2971130 * 2
def baseEnd_2971130 : Nat := 1017078517995377115940685

theorem tailTrace_2971130 : CollatzResearch.WordTrace tailWord_2971130 prefixEnd_2971130 1017078517995377115940685 := by
  unfold tailWord_2971130
  simp only [CollatzResearch.WordTrace]
  refine ⟨27091503431527728362663711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72244009150740608967103229 27091503431527728362663711)
  ·
    refine ⟨40637255147291592543995567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27091503431527728362663711 40637255147291592543995567)
    ·
      refine ⟨60955882720937388815993351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40637255147291592543995567 60955882720937388815993351)
      ·
        refine ⟨91433824081406083223990027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60955882720937388815993351 91433824081406083223990027)
        ·
          refine ⟨137150736122109124835985041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91433824081406083223990027 137150736122109124835985041)
          ·
            refine ⟨102863052091581843626988781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137150736122109124835985041 102863052091581843626988781)
            ·
              refine ⟨38573644534343191360120793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102863052091581843626988781 38573644534343191360120793)
              ·
                refine ⟨28930233400757393520090595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38573644534343191360120793 28930233400757393520090595)
                ·
                  refine ⟨43395350101136090280135893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28930233400757393520090595 43395350101136090280135893)
                  ·
                    refine ⟨1017078517995377115940685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43395350101136090280135893 1017078517995377115940685)
                    ·
                      rfl

theorem cell22_2971130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 1, 7].length) (baseStart_2971130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2971130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2971130 prefixEnd_2971130 := by exact prefixLift 2971130
  have htrace : WordTrace (prefixWord ++ tailWord_2971130) baseStart_2971130 baseEnd_2971130 := by
    simpa [prefixWord, tailWord_2971130, baseEnd_2971130] using wordTrace_append hprefix tailTrace_2971130
  have hstable : (prefixWord ++ tailWord_2971130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2971130).length < 2 ^ (prefixWord ++ tailWord_2971130).sum := by decide
  have hdescent : baseEnd_2971130 < baseStart_2971130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2971130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2971142 : List Nat := [6, 2, 1, 1, 2, 2, 1, 2, 2, 3]
def baseStart_2971142 : Nat := 118140960795 + 2971142 * 2 ^ 59
def prefixEnd_2971142 : Nat := 4983230072969 + 3 ^ 40 * 2971142 * 2
def baseEnd_2971142 : Nat := 1017082625840613084640649

theorem tailTrace_2971142 : CollatzResearch.WordTrace tailWord_2971142 prefixEnd_2971142 1017082625840613084640649 := by
  unfold tailWord_2971142
  simp only [CollatzResearch.WordTrace]
  refine ⟨3386451606314607484377865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 72244300934711626333394453 3386451606314607484377865)
  ·
    refine ⟨2539838704735955613283399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3386451606314607484377865 2539838704735955613283399)
    ·
      refine ⟨3809758057103933419925099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2539838704735955613283399 3809758057103933419925099)
      ·
        refine ⟨5714637085655900129887649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3809758057103933419925099 5714637085655900129887649)
        ·
          refine ⟨4285977814241925097415737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5714637085655900129887649 4285977814241925097415737)
          ·
            refine ⟨3214483360681443823061803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4285977814241925097415737 3214483360681443823061803)
            ·
              refine ⟨4821725041022165734592705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3214483360681443823061803 4821725041022165734592705)
              ·
                refine ⟨3616293780766624300944529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4821725041022165734592705 3616293780766624300944529)
                ·
                  refine ⟨2712220335574968225708397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3616293780766624300944529 2712220335574968225708397)
                  ·
                    refine ⟨1017082625840613084640649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2712220335574968225708397 1017082625840613084640649)
                    ·
                      rfl

theorem cell22_2971142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_2971142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2971142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2971142 prefixEnd_2971142 := by exact prefixLift 2971142
  have htrace : WordTrace (prefixWord ++ tailWord_2971142) baseStart_2971142 baseEnd_2971142 := by
    simpa [prefixWord, tailWord_2971142, baseEnd_2971142] using wordTrace_append hprefix tailTrace_2971142
  have hstable : (prefixWord ++ tailWord_2971142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2971142).length < 2 ^ (prefixWord ++ tailWord_2971142).sum := by decide
  have hdescent : baseEnd_2971142 < baseStart_2971142 := by decide
  rcases family_descends (prefixWord ++ tailWord_2971142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2971318 : List Nat := [5, 1, 3, 1, 1, 1, 3, 2, 5]
def baseStart_2971318 : Nat := 118140960795 + 2971318 * 2 ^ 59
def prefixEnd_2971318 : Nat := 4983230072969 + 3 ^ 40 * 2971318 * 2
def baseEnd_2971318 : Nat := 339047624745802430746703

theorem tailTrace_2971318 : CollatzResearch.WordTrace tailWord_2971318 prefixEnd_2971318 339047624745802430746703 := by
  unfold tailWord_2971318
  simp only [CollatzResearch.WordTrace]
  refine ⟨6773304415589363847406163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72248580432953214372332405 6773304415589363847406163)
  ·
    refine ⟨10159956623384045771109245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6773304415589363847406163 10159956623384045771109245)
    ·
      refine ⟨3809983733769017164165967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10159956623384045771109245 3809983733769017164165967)
      ·
        refine ⟨5714975600653525746248951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3809983733769017164165967 5714975600653525746248951)
        ·
          refine ⟨8572463400980288619373427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5714975600653525746248951 8572463400980288619373427)
          ·
            refine ⟨12858695101470432929060141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8572463400980288619373427 12858695101470432929060141)
            ·
              refine ⟨4822010663051412348397553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12858695101470432929060141 4822010663051412348397553)
              ·
                refine ⟨3616507997288559261298165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4822010663051412348397553 3616507997288559261298165)
                ·
                  refine ⟨339047624745802430746703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3616507997288559261298165 339047624745802430746703)
                  ·
                    rfl

theorem cell22_2971318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 2, 5].length) (baseStart_2971318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2971318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2971318 prefixEnd_2971318 := by exact prefixLift 2971318
  have htrace : WordTrace (prefixWord ++ tailWord_2971318) baseStart_2971318 baseEnd_2971318 := by
    simpa [prefixWord, tailWord_2971318, baseEnd_2971318] using wordTrace_append hprefix tailTrace_2971318
  have hstable : (prefixWord ++ tailWord_2971318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2971318).length < 2 ^ (prefixWord ++ tailWord_2971318).sum := by decide
  have hdescent : baseEnd_2971318 < baseStart_2971318 := by decide
  rcases family_descends (prefixWord ++ tailWord_2971318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
