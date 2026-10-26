import V185TrunkScan23Chunk0165

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_981962 : List Nat := [3, 1, 2, 1, 2, 1, 1, 5, 3, 1, 3]
def baseStart_981962 : Nat := 118140960795 + 981962 * 2 ^ 59
def prefixEnd_981962 : Nat := 4983230072969 + 3 ^ 40 * 981962 * 2
def baseEnd_981962 : Nat := 504218490450392302859045

theorem tailTrace_981962 : CollatzResearch.WordTrace tailWord_981962 prefixEnd_981962 504218490450392302859045 := by
  unfold tailWord_981962
  simp only [CollatzResearch.WordTrace]
  refine ⟨8953774117131713650743035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23876730979017903068648093 8953774117131713650743035)
  ·
    refine ⟨13430661175697570476114553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8953774117131713650743035 13430661175697570476114553)
    ·
      refine ⟨10072995881773177857085915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13430661175697570476114553 10072995881773177857085915)
      ·
        refine ⟨15109493822659766785628873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10072995881773177857085915 15109493822659766785628873)
        ·
          refine ⟨11332120366994825089221655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15109493822659766785628873 11332120366994825089221655)
          ·
            refine ⟨16998180550492237633832483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11332120366994825089221655 16998180550492237633832483)
            ·
              refine ⟨25497270825738356450748725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16998180550492237633832483 25497270825738356450748725)
              ·
                refine ⟨2390369139912970917257693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25497270825738356450748725 2390369139912970917257693)
                ·
                  refine ⟨896388427467364093971635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2390369139912970917257693 896388427467364093971635)
                  ·
                    refine ⟨1344582641201046140957453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 896388427467364093971635 1344582641201046140957453)
                    ·
                      refine ⟨504218490450392302859045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1344582641201046140957453 504218490450392302859045)
                      ·
                        rfl

theorem cell23_981962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 5, 3, 1, 3].length) (baseStart_981962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_981962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_981962 prefixEnd_981962 := by exact prefixLift 981962
  have htrace : WordTrace (prefixWord ++ tailWord_981962) baseStart_981962 baseEnd_981962 := by
    simpa [prefixWord, tailWord_981962, baseEnd_981962] using wordTrace_append hprefix tailTrace_981962
  have hstable : (prefixWord ++ tailWord_981962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981962).length < 2 ^ (prefixWord ++ tailWord_981962).sum := by decide
  have hdescent : baseEnd_981962 < baseStart_981962 := by decide
  rcases family_descends (prefixWord ++ tailWord_981962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981999 : List Nat := [1, 1, 2, 1, 4, 5, 2, 1, 1, 5]
def baseStart_981999 : Nat := 118140960795 + 981999 * 2 ^ 59
def prefixEnd_981999 : Nat := 4983230072969 + 3 ^ 40 * 981999 * 2
def baseEnd_981999 : Nat := 168079163078202886032125

theorem tailTrace_981999 : CollatzResearch.WordTrace tailWord_981999 prefixEnd_981999 168079163078202886032125 := by
  unfold tailWord_981999
  simp only [CollatzResearch.WordTrace]
  refine ⟨35816445969392809922069051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23877630646261873281379367 35816445969392809922069051)
  ·
    refine ⟨53724668954089214883103577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35816445969392809922069051 53724668954089214883103577)
    ·
      refine ⟨40293501715566911162327683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53724668954089214883103577 40293501715566911162327683)
      ·
        refine ⟨60440252573350366743491525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40293501715566911162327683 60440252573350366743491525)
        ·
          refine ⟨11332547357503193764404661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60440252573350366743491525 11332547357503193764404661)
          ·
            refine ⟨1062426314765924415412937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11332547357503193764404661 1062426314765924415412937)
            ·
              refine ⟨796819736074443311559703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1062426314765924415412937 796819736074443311559703)
              ·
                refine ⟨1195229604111664967339555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 796819736074443311559703 1195229604111664967339555)
                ·
                  refine ⟨1792844406167497451009333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1195229604111664967339555 1792844406167497451009333)
                  ·
                    refine ⟨168079163078202886032125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1792844406167497451009333 168079163078202886032125)
                    ·
                      rfl

theorem cell23_981999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 2, 1, 1, 5].length) (baseStart_981999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_981999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_981999 prefixEnd_981999 := by exact prefixLift 981999
  have htrace : WordTrace (prefixWord ++ tailWord_981999) baseStart_981999 baseEnd_981999 := by
    simpa [prefixWord, tailWord_981999, baseEnd_981999] using wordTrace_append hprefix tailTrace_981999
  have hstable : (prefixWord ++ tailWord_981999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981999).length < 2 ^ (prefixWord ++ tailWord_981999).sum := by decide
  have hdescent : baseEnd_981999 < baseStart_981999 := by decide
  rcases family_descends (prefixWord ++ tailWord_981999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982012 : List Nat := [2, 2, 2, 1, 2, 4, 1, 1, 4, 4]
def baseStart_982012 : Nat := 118140960795 + 982012 * 2 ^ 59
def prefixEnd_982012 : Nat := 4983230072969 + 3 ^ 40 * 982012 * 2
def baseEnd_982012 : Nat := 168081388161039035744605

theorem tailTrace_982012 : CollatzResearch.WordTrace tailWord_982012 prefixEnd_982012 168081388161039035744605 := by
  unfold tailWord_982012
  simp only [CollatzResearch.WordTrace]
  refine ⟨17908460059172856571146145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23877946745563808761528193 17908460059172856571146145)
  ·
    refine ⟨13431345044379642428359609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17908460059172856571146145 13431345044379642428359609)
    ·
      refine ⟨10073508783284731821269707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13431345044379642428359609 10073508783284731821269707)
      ·
        refine ⟨15110263174927097731904561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10073508783284731821269707 15110263174927097731904561)
        ·
          refine ⟨11332697381195323298928421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15110263174927097731904561 11332697381195323298928421)
          ·
            refine ⟨2124880758974123118549079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11332697381195323298928421 2124880758974123118549079)
            ·
              refine ⟨3187321138461184677823619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2124880758974123118549079 3187321138461184677823619)
              ·
                refine ⟨4780981707691777016735429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3187321138461184677823619 4780981707691777016735429)
                ·
                  refine ⟨896434070192208190637893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4780981707691777016735429 896434070192208190637893)
                  ·
                    refine ⟨168081388161039035744605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 896434070192208190637893 168081388161039035744605)
                    ·
                      rfl

theorem cell23_982012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 1, 4, 4].length) (baseStart_982012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_982012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_982012 prefixEnd_982012 := by exact prefixLift 982012
  have htrace : WordTrace (prefixWord ++ tailWord_982012) baseStart_982012 baseEnd_982012 := by
    simpa [prefixWord, tailWord_982012, baseEnd_982012] using wordTrace_append hprefix tailTrace_982012
  have hstable : (prefixWord ++ tailWord_982012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982012).length < 2 ^ (prefixWord ++ tailWord_982012).sum := by decide
  have hdescent : baseEnd_982012 < baseStart_982012 := by decide
  rcases family_descends (prefixWord ++ tailWord_982012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982039 : List Nat := [1, 1, 3, 5, 1, 1, 1, 4, 1, 2, 3]
def baseStart_982039 : Nat := 118140960795 + 982039 * 2 ^ 59
def prefixEnd_982039 : Nat := 4983230072969 + 3 ^ 40 * 982039 * 2
def baseEnd_982039 : Nat := 504258028460788501596191

theorem tailTrace_982039 : CollatzResearch.WordTrace tailWord_982039 prefixEnd_982039 504258028460788501596191 := by
  unfold tailWord_982039
  simp only [CollatzResearch.WordTrace]
  refine ⟨35817904889247896753525171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23878603259498597835683447 35817904889247896753525171)
  ·
    refine ⟨53726857333871845130287757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35817904889247896753525171 53726857333871845130287757)
    ·
      refine ⟨20147571500201941923857909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53726857333871845130287757 20147571500201941923857909)
      ·
        refine ⟨1888834828143932055361679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20147571500201941923857909 1888834828143932055361679)
        ·
          refine ⟨2833252242215898083042519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1888834828143932055361679 2833252242215898083042519)
          ·
            refine ⟨4249878363323847124563779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2833252242215898083042519 4249878363323847124563779)
            ·
              refine ⟨6374817544985770686845669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4249878363323847124563779 6374817544985770686845669)
              ·
                refine ⟨1195278289684832003783563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6374817544985770686845669 1195278289684832003783563)
                ·
                  refine ⟨1792917434527248005675345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1195278289684832003783563 1792917434527248005675345)
                  ·
                    refine ⟨1344688075895436004256509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1792917434527248005675345 1344688075895436004256509)
                    ·
                      refine ⟨504258028460788501596191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1344688075895436004256509 504258028460788501596191)
                      ·
                        rfl

theorem cell23_982039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_982039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_982039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_982039 prefixEnd_982039 := by exact prefixLift 982039
  have htrace : WordTrace (prefixWord ++ tailWord_982039) baseStart_982039 baseEnd_982039 := by
    simpa [prefixWord, tailWord_982039, baseEnd_982039] using wordTrace_append hprefix tailTrace_982039
  have hstable : (prefixWord ++ tailWord_982039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982039).length < 2 ^ (prefixWord ++ tailWord_982039).sum := by decide
  have hdescent : baseEnd_982039 < baseStart_982039 := by decide
  rcases family_descends (prefixWord ++ tailWord_982039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982065 : List Nat := [1, 2, 2, 3, 1, 2, 1, 2, 2, 2, 5]
def baseStart_982065 : Nat := 118140960795 + 982065 * 2 ^ 59
def prefixEnd_982065 : Nat := 4983230072969 + 3 ^ 40 * 982065 * 2
def baseEnd_982065 : Nat := 504271378957805399871071

theorem tailTrace_982065 : CollatzResearch.WordTrace tailWord_982065 prefixEnd_982065 504271378957805399871071 := by
  unfold tailWord_982065
  simp only [CollatzResearch.WordTrace]
  refine ⟨35818853187153703193971649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23879235458102468795981099 35818853187153703193971649)
  ·
    refine ⟨26864139890365277395478737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35818853187153703193971649 26864139890365277395478737)
    ·
      refine ⟨20148104917773958046609053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26864139890365277395478737 20148104917773958046609053)
      ·
        refine ⟨7555539344165234267478395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20148104917773958046609053 7555539344165234267478395)
        ·
          refine ⟨11333309016247851401217593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7555539344165234267478395 11333309016247851401217593)
          ·
            refine ⟨8499981762185888550913195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11333309016247851401217593 8499981762185888550913195)
            ·
              refine ⟨12749972643278832826369793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8499981762185888550913195 12749972643278832826369793)
              ·
                refine ⟨9562479482459124619777345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12749972643278832826369793 9562479482459124619777345)
                ·
                  refine ⟨7171859611844343464833009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9562479482459124619777345 7171859611844343464833009)
                  ·
                    refine ⟨5378894708883257598624757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7171859611844343464833009 5378894708883257598624757)
                    ·
                      refine ⟨504271378957805399871071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5378894708883257598624757 504271378957805399871071)
                      ·
                        rfl

theorem cell23_982065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_982065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_982065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_982065 prefixEnd_982065 := by exact prefixLift 982065
  have htrace : WordTrace (prefixWord ++ tailWord_982065) baseStart_982065 baseEnd_982065 := by
    simpa [prefixWord, tailWord_982065, baseEnd_982065] using wordTrace_append hprefix tailTrace_982065
  have hstable : (prefixWord ++ tailWord_982065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982065).length < 2 ^ (prefixWord ++ tailWord_982065).sum := by decide
  have hdescent : baseEnd_982065 < baseStart_982065 := by decide
  rcases family_descends (prefixWord ++ tailWord_982065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982069 : List Nat := [1, 3, 3, 1, 1, 1, 1, 6, 2, 1, 3]
def baseStart_982069 : Nat := 118140960795 + 982069 * 2 ^ 59
def prefixEnd_982069 : Nat := 4983230072969 + 3 ^ 40 * 982069 * 2
def baseEnd_982069 : Nat := 504273432880423384221053

theorem tailTrace_982069 : CollatzResearch.WordTrace tailWord_982069 prefixEnd_982069 504273432880423384221053 := by
  unfold tailWord_982069
  simp only [CollatzResearch.WordTrace]
  refine ⟨35818999079139211877117261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23879332719426141251411507 35818999079139211877117261)
  ·
    refine ⟨13432124654677204453918973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35818999079139211877117261 13432124654677204453918973)
    ·
      refine ⟨5037046745503951670219615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13432124654677204453918973 5037046745503951670219615)
      ·
        refine ⟨7555570118255927505329423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5037046745503951670219615 7555570118255927505329423)
        ·
          refine ⟨11333355177383891257994135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7555570118255927505329423 11333355177383891257994135)
          ·
            refine ⟨17000032766075836886991203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11333355177383891257994135 17000032766075836886991203)
            ·
              refine ⟨25500049149113755330486805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17000032766075836886991203 25500049149113755330486805)
              ·
                refine ⟨1195314803864707281116569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25500049149113755330486805 1195314803864707281116569)
                ·
                  refine ⟨896486102898530460837427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1195314803864707281116569 896486102898530460837427)
                  ·
                    refine ⟨1344729154347795691256141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 896486102898530460837427 1344729154347795691256141)
                    ·
                      refine ⟨504273432880423384221053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1344729154347795691256141 504273432880423384221053)
                      ·
                        rfl

theorem cell23_982069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 6, 2, 1, 3].length) (baseStart_982069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_982069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_982069 prefixEnd_982069 := by exact prefixLift 982069
  have htrace : WordTrace (prefixWord ++ tailWord_982069) baseStart_982069 baseEnd_982069 := by
    simpa [prefixWord, tailWord_982069, baseEnd_982069] using wordTrace_append hprefix tailTrace_982069
  have hstable : (prefixWord ++ tailWord_982069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982069).length < 2 ^ (prefixWord ++ tailWord_982069).sum := by decide
  have hdescent : baseEnd_982069 < baseStart_982069 := by decide
  rcases family_descends (prefixWord ++ tailWord_982069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982085 : List Nat := [1, 3, 1, 1, 1, 3, 2, 3, 2, 6]
def baseStart_982085 : Nat := 118140960795 + 982085 * 2 ^ 59
def prefixEnd_982085 : Nat := 4983230072969 + 3 ^ 40 * 982085 * 2
def baseEnd_982085 : Nat := 168093882856965107206993

theorem tailTrace_982085 : CollatzResearch.WordTrace tailWord_982085 prefixEnd_982085 168093882856965107206993 := by
  unfold tailWord_982085
  simp only [CollatzResearch.WordTrace]
  refine ⟨35819582647081246609699709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23879721764720831073133139 35819582647081246609699709)
  ·
    refine ⟨13432343492655467478637391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35819582647081246609699709 13432343492655467478637391)
    ·
      refine ⟨20148515238983201217956087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13432343492655467478637391 20148515238983201217956087)
      ·
        refine ⟨30222772858474801826934131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20148515238983201217956087 30222772858474801826934131)
        ·
          refine ⟨45334159287712202740401197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30222772858474801826934131 45334159287712202740401197)
          ·
            refine ⟨17000309732892076027650449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45334159287712202740401197 17000309732892076027650449)
            ·
              refine ⟨12750232299669057020737837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17000309732892076027650449 12750232299669057020737837)
              ·
                refine ⟨4781337112375896382776689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12750232299669057020737837 4781337112375896382776689)
                ·
                  refine ⟨3586002834281922287082517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4781337112375896382776689 3586002834281922287082517)
                  ·
                    refine ⟨168093882856965107206993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3586002834281922287082517 168093882856965107206993)
                    ·
                      rfl

theorem cell23_982085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 3, 2, 6].length) (baseStart_982085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_982085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_982085 prefixEnd_982085 := by exact prefixLift 982085
  have htrace : WordTrace (prefixWord ++ tailWord_982085) baseStart_982085 baseEnd_982085 := by
    simpa [prefixWord, tailWord_982085, baseEnd_982085] using wordTrace_append hprefix tailTrace_982085
  have hstable : (prefixWord ++ tailWord_982085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982085).length < 2 ^ (prefixWord ++ tailWord_982085).sum := by decide
  have hdescent : baseEnd_982085 < baseStart_982085 := by decide
  rcases family_descends (prefixWord ++ tailWord_982085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982105 : List Nat := [1, 2, 1, 2, 2, 1, 2, 1, 3, 4, 4]
def baseStart_982105 : Nat := 118140960795 + 982105 * 2 ^ 59
def prefixEnd_982105 : Nat := 4983230072969 + 3 ^ 40 * 982105 * 2
def baseEnd_982105 : Nat := 504291918183985243370887

theorem tailTrace_982105 : CollatzResearch.WordTrace tailWord_982105 prefixEnd_982105 504291918183985243370887 := by
  unfold tailWord_982105
  simp only [CollatzResearch.WordTrace]
  refine ⟨35820312107008790025427769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23880208071339193350285179 35820312107008790025427769)
  ·
    refine ⟨26865234080256592519070827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35820312107008790025427769 26865234080256592519070827)
    ·
      refine ⟨40297851120384888778606241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26865234080256592519070827 40297851120384888778606241)
      ·
        refine ⟨30223388340288666583954681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40297851120384888778606241 30223388340288666583954681)
        ·
          refine ⟨22667541255216499937966011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30223388340288666583954681 22667541255216499937966011)
          ·
            refine ⟨34001311882824749906949017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22667541255216499937966011 34001311882824749906949017)
            ·
              refine ⟨25500983912118562430211763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34001311882824749906949017 25500983912118562430211763)
              ·
                refine ⟨38251475868177843645317645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25500983912118562430211763 38251475868177843645317645)
                ·
                  refine ⟨14344303450566691366994117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38251475868177843645317645 14344303450566691366994117)
                  ·
                    refine ⟨2689556896981254631311397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14344303450566691366994117 2689556896981254631311397)
                    ·
                      refine ⟨504291918183985243370887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2689556896981254631311397 504291918183985243370887)
                      ·
                        rfl

theorem cell23_982105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 4, 4].length) (baseStart_982105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_982105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_982105 prefixEnd_982105 := by exact prefixLift 982105
  have htrace : WordTrace (prefixWord ++ tailWord_982105) baseStart_982105 baseEnd_982105 := by
    simpa [prefixWord, tailWord_982105, baseEnd_982105] using wordTrace_append hprefix tailTrace_982105
  have hstable : (prefixWord ++ tailWord_982105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982105).length < 2 ^ (prefixWord ++ tailWord_982105).sum := by decide
  have hdescent : baseEnd_982105 < baseStart_982105 := by decide
  rcases family_descends (prefixWord ++ tailWord_982105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982155 : List Nat := [1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 7]
def baseStart_982155 : Nat := 118140960795 + 982155 * 2 ^ 59
def prefixEnd_982155 : Nat := 4983230072969 + 3 ^ 40 * 982155 * 2
def baseEnd_982155 : Nat := 504317592216710047745657

theorem tailTrace_982155 : CollatzResearch.WordTrace tailWord_982155 prefixEnd_982155 504317592216710047745657 := by
  unfold tailWord_982155
  simp only [CollatzResearch.WordTrace]
  refine ⟨35822135756827648564747919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23881423837885099043165279 35822135756827648564747919)
  ·
    refine ⟨53733203635241472847121879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35822135756827648564747919 53733203635241472847121879)
    ·
      refine ⟨80599805452862209270682819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53733203635241472847121879 80599805452862209270682819)
      ·
        refine ⟨120899708179293313906024229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80599805452862209270682819 120899708179293313906024229)
        ·
          refine ⟨22668695283617496357379543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120899708179293313906024229 22668695283617496357379543)
          ·
            refine ⟨34003042925426244536069315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22668695283617496357379543 34003042925426244536069315)
            ·
              refine ⟨51004564388139366804103973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34003042925426244536069315 51004564388139366804103973)
              ·
                refine ⟨9563355822776131275769495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51004564388139366804103973 9563355822776131275769495)
                ·
                  refine ⟨14345033734164196913654243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9563355822776131275769495 14345033734164196913654243)
                  ·
                    refine ⟨21517550601246295370481365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14345033734164196913654243 21517550601246295370481365)
                    ·
                      refine ⟨504317592216710047745657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 21517550601246295370481365 504317592216710047745657)
                      ·
                        rfl

theorem cell23_982155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 7].length) (baseStart_982155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_982155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_982155 prefixEnd_982155 := by exact prefixLift 982155
  have htrace : WordTrace (prefixWord ++ tailWord_982155) baseStart_982155 baseEnd_982155 := by
    simpa [prefixWord, tailWord_982155, baseEnd_982155] using wordTrace_append hprefix tailTrace_982155
  have hstable : (prefixWord ++ tailWord_982155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982155).length < 2 ^ (prefixWord ++ tailWord_982155).sum := by decide
  have hdescent : baseEnd_982155 < baseStart_982155 := by decide
  rcases family_descends (prefixWord ++ tailWord_982155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982192 : List Nat := [2, 1, 1, 1, 2, 1, 2, 2, 7, 4]
def baseStart_982192 : Nat := 118140960795 + 982192 * 2 ^ 59
def prefixEnd_982192 : Nat := 4983230072969 + 3 ^ 40 * 982192 * 2
def baseEnd_982192 : Nat := 168112197000308800994329

theorem tailTrace_982192 : CollatzResearch.WordTrace tailWord_982192 prefixEnd_982192 168112197000308800994329 := by
  unfold tailWord_982192
  simp only [CollatzResearch.WordTrace]
  refine ⟨17911742628846801941922415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23882323505129069255896553 17911742628846801941922415)
  ·
    refine ⟨26867613943270202912883623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17911742628846801941922415 26867613943270202912883623)
    ·
      refine ⟨40301420914905304369325435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26867613943270202912883623 40301420914905304369325435)
      ·
        refine ⟨60452131372357956553988153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40301420914905304369325435 60452131372357956553988153)
        ·
          refine ⟨45339098529268467415491115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60452131372357956553988153 45339098529268467415491115)
          ·
            refine ⟨68008647793902701123236673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45339098529268467415491115 68008647793902701123236673)
            ·
              refine ⟨51006485845427025842427505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68008647793902701123236673 51006485845427025842427505)
              ·
                refine ⟨38254864384070269381820629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51006485845427025842427505 38254864384070269381820629)
                ·
                  refine ⟨896598384001646938636421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 38254864384070269381820629 896598384001646938636421)
                  ·
                    refine ⟨168112197000308800994329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 896598384001646938636421 168112197000308800994329)
                    ·
                      rfl

theorem cell23_982192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 7, 4].length) (baseStart_982192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_982192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_982192 prefixEnd_982192 := by exact prefixLift 982192
  have htrace : WordTrace (prefixWord ++ tailWord_982192) baseStart_982192 baseEnd_982192 := by
    simpa [prefixWord, tailWord_982192, baseEnd_982192] using wordTrace_append hprefix tailTrace_982192
  have hstable : (prefixWord ++ tailWord_982192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982192).length < 2 ^ (prefixWord ++ tailWord_982192).sum := by decide
  have hdescent : baseEnd_982192 < baseStart_982192 := by decide
  rcases family_descends (prefixWord ++ tailWord_982192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982199 : List Nat := [1, 1, 3, 1, 4, 1, 1, 3, 2, 4, 2]
def baseStart_982199 : Nat := 118140960795 + 982199 * 2 ^ 59
def prefixEnd_982199 : Nat := 4983230072969 + 3 ^ 40 * 982199 * 2
def baseEnd_982199 : Nat := 504340185365507875595455

theorem tailTrace_982199 : CollatzResearch.WordTrace tailWord_982199 prefixEnd_982199 504340185365507875595455 := by
  unfold tailWord_982199
  simp only [CollatzResearch.WordTrace]
  refine ⟨35823740568668244079349651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23882493712445496052899767 35823740568668244079349651)
  ·
    refine ⟨53735610853002366119024477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35823740568668244079349651 53735610853002366119024477)
    ·
      refine ⟨20150854069875887294634179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53735610853002366119024477 20150854069875887294634179)
      ·
        refine ⟨30226281104813830941951269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20150854069875887294634179 30226281104813830941951269)
        ·
          refine ⟨5667427707152593301615863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30226281104813830941951269 5667427707152593301615863)
          ·
            refine ⟨8501141560728889952423795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5667427707152593301615863 8501141560728889952423795)
            ·
              refine ⟨12751712341093334928635693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8501141560728889952423795 12751712341093334928635693)
              ·
                refine ⟨4781892127910000598238385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12751712341093334928635693 4781892127910000598238385)
                ·
                  refine ⟨3586419095932500448678789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4781892127910000598238385 3586419095932500448678789)
                  ·
                    refine ⟨672453580487343834127273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3586419095932500448678789 672453580487343834127273)
                    ·
                      refine ⟨504340185365507875595455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 672453580487343834127273 504340185365507875595455)
                      ·
                        rfl

theorem cell23_982199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 3, 2, 4, 2].length) (baseStart_982199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_982199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_982199 prefixEnd_982199 := by exact prefixLift 982199
  have htrace : WordTrace (prefixWord ++ tailWord_982199) baseStart_982199 baseEnd_982199 := by
    simpa [prefixWord, tailWord_982199, baseEnd_982199] using wordTrace_append hprefix tailTrace_982199
  have hstable : (prefixWord ++ tailWord_982199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982199).length < 2 ^ (prefixWord ++ tailWord_982199).sum := by decide
  have hdescent : baseEnd_982199 < baseStart_982199 := by decide
  rcases family_descends (prefixWord ++ tailWord_982199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982300 : List Nat := [2, 2, 3, 1, 1, 1, 6, 2, 1, 1, 3]
def baseStart_982300 : Nat := 118140960795 + 982300 * 2 ^ 59
def prefixEnd_982300 : Nat := 4983230072969 + 3 ^ 40 * 982300 * 2
def baseEnd_982300 : Nat := 504392046911611980432491

theorem tailTrace_982300 : CollatzResearch.WordTrace tailWord_982300 prefixEnd_982300 504392046911611980432491 := by
  unfold tailWord_982300
  simp only [CollatzResearch.WordTrace]
  refine ⟨17913712170651169164388177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23884949560868225552517569 17913712170651169164388177)
  ·
    refine ⟨13435284127988376873291133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17913712170651169164388177 13435284127988376873291133)
    ·
      refine ⟨5038231547995641327484175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13435284127988376873291133 5038231547995641327484175)
      ·
        refine ⟨7557347321993461991226263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5038231547995641327484175 7557347321993461991226263)
        ·
          refine ⟨11336020982990192986839395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7557347321993461991226263 11336020982990192986839395)
          ·
            refine ⟨17004031474485289480259093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11336020982990192986839395 17004031474485289480259093)
            ·
              refine ⟨797063975366497944387145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 17004031474485289480259093 797063975366497944387145)
              ·
                refine ⟨597797981524873458290359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 797063975366497944387145 597797981524873458290359)
                ·
                  refine ⟨896696972287310187435539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 597797981524873458290359 896696972287310187435539)
                  ·
                    refine ⟨1345045458430965281153309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 896696972287310187435539 1345045458430965281153309)
                    ·
                      refine ⟨504392046911611980432491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1345045458430965281153309 504392046911611980432491)
                      ·
                        rfl

theorem cell23_982300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 6, 2, 1, 1, 3].length) (baseStart_982300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_982300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_982300 prefixEnd_982300 := by exact prefixLift 982300
  have htrace : WordTrace (prefixWord ++ tailWord_982300) baseStart_982300 baseEnd_982300 := by
    simpa [prefixWord, tailWord_982300, baseEnd_982300] using wordTrace_append hprefix tailTrace_982300
  have hstable : (prefixWord ++ tailWord_982300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982300).length < 2 ^ (prefixWord ++ tailWord_982300).sum := by decide
  have hdescent : baseEnd_982300 < baseStart_982300 := by decide
  rcases family_descends (prefixWord ++ tailWord_982300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982323 : List Nat := [1, 1, 1, 2, 5, 3, 1, 2, 3, 2, 2]
def baseStart_982323 : Nat := 118140960795 + 982323 * 2 ^ 59
def prefixEnd_982323 : Nat := 4983230072969 + 3 ^ 40 * 982323 * 2
def baseEnd_982323 : Nat := 504403856966665390444885

theorem tailTrace_982323 : CollatzResearch.WordTrace tailWord_982323 prefixEnd_982323 504403856966665390444885 := by
  unfold tailWord_982323
  simp only [CollatzResearch.WordTrace]
  refine ⟨35828263220219013256863623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23885508813479342171242415 35828263220219013256863623)
  ·
    refine ⟨53742394830328519885295435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35828263220219013256863623 53742394830328519885295435)
    ·
      refine ⟨80613592245492779827943153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53742394830328519885295435 80613592245492779827943153)
      ·
        refine ⟨60460194184119584870957365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80613592245492779827943153 60460194184119584870957365)
        ·
          refine ⟨5668143204761211081652253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60460194184119584870957365 5668143204761211081652253)
          ·
            refine ⟨2125553701785454155619595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5668143204761211081652253 2125553701785454155619595)
            ·
              refine ⟨3188330552678181233429393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2125553701785454155619595 3188330552678181233429393)
              ·
                refine ⟨2391247914508635925072045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3188330552678181233429393 2391247914508635925072045)
                ·
                  refine ⟨896717967940738471902017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2391247914508635925072045 896717967940738471902017)
                  ·
                    refine ⟨672538475955553853926513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 896717967940738471902017 672538475955553853926513)
                    ·
                      refine ⟨504403856966665390444885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 672538475955553853926513 504403856966665390444885)
                      ·
                        rfl

theorem cell23_982323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 2, 3, 2, 2].length) (baseStart_982323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_982323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_982323 prefixEnd_982323 := by exact prefixLift 982323
  have htrace : WordTrace (prefixWord ++ tailWord_982323) baseStart_982323 baseEnd_982323 := by
    simpa [prefixWord, tailWord_982323, baseEnd_982323] using wordTrace_append hprefix tailTrace_982323
  have hstable : (prefixWord ++ tailWord_982323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982323).length < 2 ^ (prefixWord ++ tailWord_982323).sum := by decide
  have hdescent : baseEnd_982323 < baseStart_982323 := by decide
  rcases family_descends (prefixWord ++ tailWord_982323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982340 : List Nat := [2, 3, 4, 1, 1, 1, 4, 1, 1, 1, 4]
def baseStart_982340 : Nat := 118140960795 + 982340 * 2 ^ 59
def prefixEnd_982340 : Nat := 4983230072969 + 3 ^ 40 * 982340 * 2
def baseEnd_982340 : Nat := 504412586137791823932307

theorem tailTrace_982340 : CollatzResearch.WordTrace tailWord_982340 prefixEnd_982340 504412586137791823932307 := by
  unfold tailWord_982340
  simp only [CollatzResearch.WordTrace]
  refine ⟨17914441630578712580116237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23885922174104950106821649 17914441630578712580116237)
  ·
    refine ⟨6717915611467017217543589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17914441630578712580116237 6717915611467017217543589)
    ·
      refine ⟨1259609177150065728289423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6717915611467017217543589 1259609177150065728289423)
      ·
        refine ⟨1889413765725098592434135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1259609177150065728289423 1889413765725098592434135)
        ·
          refine ⟨2834120648587647888651203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1889413765725098592434135 2834120648587647888651203)
          ·
            refine ⟨4251180972881471832976805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2834120648587647888651203 4251180972881471832976805)
            ·
              refine ⟨797096432415275968683151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4251180972881471832976805 797096432415275968683151)
              ·
                refine ⟨1195644648622913953024727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 797096432415275968683151 1195644648622913953024727)
                ·
                  refine ⟨1793466972934370929537091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1195644648622913953024727 1793466972934370929537091)
                  ·
                    refine ⟨2690200459401556394305637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1793466972934370929537091 2690200459401556394305637)
                    ·
                      refine ⟨504412586137791823932307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2690200459401556394305637 504412586137791823932307)
                      ·
                        rfl

theorem cell23_982340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_982340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_982340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_982340 prefixEnd_982340 := by exact prefixLift 982340
  have htrace : WordTrace (prefixWord ++ tailWord_982340) baseStart_982340 baseEnd_982340 := by
    simpa [prefixWord, tailWord_982340, baseEnd_982340] using wordTrace_append hprefix tailTrace_982340
  have hstable : (prefixWord ++ tailWord_982340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982340).length < 2 ^ (prefixWord ++ tailWord_982340).sum := by decide
  have hdescent : baseEnd_982340 < baseStart_982340 := by decide
  rcases family_descends (prefixWord ++ tailWord_982340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982343 : List Nat := [1, 1, 4, 1, 2, 3, 4, 1, 1, 2, 3]
def baseStart_982343 : Nat := 118140960795 + 982343 * 2 ^ 59
def prefixEnd_982343 : Nat := 4983230072969 + 3 ^ 40 * 982343 * 2
def baseEnd_982343 : Nat := 504414126579755312194793

theorem tailTrace_982343 : CollatzResearch.WordTrace tailWord_982343 prefixEnd_982343 504414126579755312194793 := by
  unfold tailWord_982343
  simp only [CollatzResearch.WordTrace]
  refine ⟨35828992680146556672591683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23885995120097704448394455 35828992680146556672591683)
  ·
    refine ⟨53743489020219835008887525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35828992680146556672591683 53743489020219835008887525)
    ·
      refine ⟨10076904191291219064166411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53743489020219835008887525 10076904191291219064166411)
      ·
        refine ⟨15115356286936828596249617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10076904191291219064166411 15115356286936828596249617)
        ·
          refine ⟨11336517215202621447187213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15115356286936828596249617 11336517215202621447187213)
          ·
            refine ⟨4251193955700983042695205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11336517215202621447187213 4251193955700983042695205)
            ·
              refine ⟨797098866693934320505351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4251193955700983042695205 797098866693934320505351)
              ·
                refine ⟨1195648300040901480758027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 797098866693934320505351 1195648300040901480758027)
                ·
                  refine ⟨1793472450061352221137041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1195648300040901480758027 1793472450061352221137041)
                  ·
                    refine ⟨1345104337546014165852781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1793472450061352221137041 1345104337546014165852781)
                    ·
                      refine ⟨504414126579755312194793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1345104337546014165852781 504414126579755312194793)
                      ·
                        rfl

theorem cell23_982343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 4, 1, 1, 2, 3].length) (baseStart_982343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_982343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_982343 prefixEnd_982343 := by exact prefixLift 982343
  have htrace : WordTrace (prefixWord ++ tailWord_982343) baseStart_982343 baseEnd_982343 := by
    simpa [prefixWord, tailWord_982343, baseEnd_982343] using wordTrace_append hprefix tailTrace_982343
  have hstable : (prefixWord ++ tailWord_982343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982343).length < 2 ^ (prefixWord ++ tailWord_982343).sum := by decide
  have hdescent : baseEnd_982343 < baseStart_982343 := by decide
  rcases family_descends (prefixWord ++ tailWord_982343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982383 : List Nat := [1, 1, 2, 1, 3, 1, 6, 2, 1, 3, 2]
def baseStart_982383 : Nat := 118140960795 + 982383 * 2 ^ 59
def prefixEnd_982383 : Nat := 4983230072969 + 3 ^ 40 * 982383 * 2
def baseEnd_982383 : Nat := 504434665805935155694609

theorem tailTrace_982383 : CollatzResearch.WordTrace tailWord_982383 prefixEnd_982383 504434665805935155694609 := by
  unfold tailWord_982383
  simp only [CollatzResearch.WordTrace]
  refine ⟨35830451600001643504047803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23886967733334429002698535 35830451600001643504047803)
  ·
    refine ⟨53745677400002465256071705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35830451600001643504047803 53745677400002465256071705)
    ·
      refine ⟨40309258050001848942053779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53745677400002465256071705 40309258050001848942053779)
      ·
        refine ⟨60463887075002773413080669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40309258050001848942053779 60463887075002773413080669)
        ·
          refine ⟨22673957653126040029905251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60463887075002773413080669 22673957653126040029905251)
          ·
            refine ⟨34010936479689060044857877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22673957653126040029905251 34010936479689060044857877)
            ·
              refine ⟨1594262647485424689602713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 34010936479689060044857877 1594262647485424689602713)
              ·
                refine ⟨1195696985614068517202035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1594262647485424689602713 1195696985614068517202035)
                ·
                  refine ⟨1793545478421102775803053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1195696985614068517202035 1793545478421102775803053)
                  ·
                    refine ⟨672579554407913540926145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1793545478421102775803053 672579554407913540926145)
                    ·
                      refine ⟨504434665805935155694609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 672579554407913540926145 504434665805935155694609)
                      ·
                        rfl

theorem cell23_982383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 2, 1, 3, 2].length) (baseStart_982383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_982383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_982383 prefixEnd_982383 := by exact prefixLift 982383
  have htrace : WordTrace (prefixWord ++ tailWord_982383) baseStart_982383 baseEnd_982383 := by
    simpa [prefixWord, tailWord_982383, baseEnd_982383] using wordTrace_append hprefix tailTrace_982383
  have hstable : (prefixWord ++ tailWord_982383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982383).length < 2 ^ (prefixWord ++ tailWord_982383).sum := by decide
  have hdescent : baseEnd_982383 < baseStart_982383 := by decide
  rcases family_descends (prefixWord ++ tailWord_982383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982396 : List Nat := [2, 2, 2, 1, 1, 1, 4, 1, 3, 4, 2]
def baseStart_982396 : Nat := 118140960795 + 982396 * 2 ^ 59
def prefixEnd_982396 : Nat := 4983230072969 + 3 ^ 40 * 982396 * 2
def baseEnd_982396 : Nat := 504441341054443604832049

theorem tailTrace_982396 : CollatzResearch.WordTrace tailWord_982396 prefixEnd_982396 504441341054443604832049 := by
  unfold tailWord_982396
  simp only [CollatzResearch.WordTrace]
  refine ⟨17915462874477273362135521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23887283832636364482847361 17915462874477273362135521)
  ·
    refine ⟨13436597155857955021601641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17915462874477273362135521 13436597155857955021601641)
    ·
      refine ⟨10077447866893466266201231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13436597155857955021601641 10077447866893466266201231)
      ·
        refine ⟨15116171800340199399301847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10077447866893466266201231 15116171800340199399301847)
        ·
          refine ⟨22674257700510299098952771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15116171800340199399301847 22674257700510299098952771)
          ·
            refine ⟨34011386550765448648429157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22674257700510299098952771 34011386550765448648429157)
            ·
              refine ⟨6377134978268521621580467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34011386550765448648429157 6377134978268521621580467)
              ·
                refine ⟨9565702467402782432370701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6377134978268521621580467 9565702467402782432370701)
                ·
                  refine ⟨3587138425276043412139013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9565702467402782432370701 3587138425276043412139013)
                  ·
                    refine ⟨672588454739258139776065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3587138425276043412139013 672588454739258139776065)
                    ·
                      refine ⟨504441341054443604832049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 672588454739258139776065 504441341054443604832049)
                      ·
                        rfl

theorem cell23_982396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 3, 4, 2].length) (baseStart_982396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_982396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_982396 prefixEnd_982396 := by exact prefixLift 982396
  have htrace : WordTrace (prefixWord ++ tailWord_982396) baseStart_982396 baseEnd_982396 := by
    simpa [prefixWord, tailWord_982396, baseEnd_982396] using wordTrace_append hprefix tailTrace_982396
  have hstable : (prefixWord ++ tailWord_982396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982396).length < 2 ^ (prefixWord ++ tailWord_982396).sum := by decide
  have hdescent : baseEnd_982396 < baseStart_982396 := by decide
  rcases family_descends (prefixWord ++ tailWord_982396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982424 : List Nat := [2, 1, 2, 5, 3, 1, 2, 1, 2, 1, 3]
def baseStart_982424 : Nat := 118140960795 + 982424 * 2 ^ 59
def prefixEnd_982424 : Nat := 4983230072969 + 3 ^ 40 * 982424 * 2
def baseEnd_982424 : Nat := 504455718512769495281921

theorem tailTrace_982424 : CollatzResearch.WordTrace tailWord_982424 prefixEnd_982424 504455718512769495281921 := by
  unfold tailWord_982424
  simp only [CollatzResearch.WordTrace]
  refine ⟨17915973496426553753145163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23887964661902071670860217 17915973496426553753145163)
  ·
    refine ⟨26873960244639830629717745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17915973496426553753145163 26873960244639830629717745)
    ·
      refine ⟨20155470183479872972288309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26873960244639830629717745 20155470183479872972288309)
      ·
        refine ⟨1889575329701238091152029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20155470183479872972288309 1889575329701238091152029)
        ·
          refine ⟨708590748637964284182011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1889575329701238091152029 708590748637964284182011)
          ·
            refine ⟨1062886122956946426273017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 708590748637964284182011 1062886122956946426273017)
            ·
              refine ⟨797164592217709819704763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1062886122956946426273017 797164592217709819704763)
              ·
                refine ⟨1195746888326564729557145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 797164592217709819704763 1195746888326564729557145)
                ·
                  refine ⟨896810166244923547167859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1195746888326564729557145 896810166244923547167859)
                  ·
                    refine ⟨1345215249367385320751789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 896810166244923547167859 1345215249367385320751789)
                    ·
                      refine ⟨504455718512769495281921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1345215249367385320751789 504455718512769495281921)
                      ·
                        rfl

theorem cell23_982424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_982424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_982424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_982424 prefixEnd_982424 := by exact prefixLift 982424
  have htrace : WordTrace (prefixWord ++ tailWord_982424) baseStart_982424 baseEnd_982424 := by
    simpa [prefixWord, tailWord_982424, baseEnd_982424] using wordTrace_append hprefix tailTrace_982424
  have hstable : (prefixWord ++ tailWord_982424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982424).length < 2 ^ (prefixWord ++ tailWord_982424).sum := by decide
  have hdescent : baseEnd_982424 < baseStart_982424 := by decide
  rcases family_descends (prefixWord ++ tailWord_982424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982476 : List Nat := [2, 2, 1, 4, 2, 1, 2, 1, 1, 2, 5]
def baseStart_982476 : Nat := 118140960795 + 982476 * 2 ^ 59
def prefixEnd_982476 : Nat := 4983230072969 + 3 ^ 40 * 982476 * 2
def baseEnd_982476 : Nat := 504482419506803291831681

theorem tailTrace_982476 : CollatzResearch.WordTrace tailWord_982476 prefixEnd_982476 504482419506803291831681 := by
  unfold tailWord_982476
  simp only [CollatzResearch.WordTrace]
  refine ⟨17916921794332360193591641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23889229059109813591455521 17916921794332360193591641)
  ·
    refine ⟨13437691345749270145193731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17916921794332360193591641 13437691345749270145193731)
    ·
      refine ⟨20156537018623905217790597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13437691345749270145193731 20156537018623905217790597)
      ·
        refine ⟨3779350690991982228335737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20156537018623905217790597 3779350690991982228335737)
        ·
          refine ⟨2834513018243986671251803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3779350690991982228335737 2834513018243986671251803)
          ·
            refine ⟨4251769527365980006877705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2834513018243986671251803 4251769527365980006877705)
            ·
              refine ⟨3188827145524485005158279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4251769527365980006877705 3188827145524485005158279)
              ·
                refine ⟨4783240718286727507737419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3188827145524485005158279 4783240718286727507737419)
                ·
                  refine ⟨7174861077430091261606129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4783240718286727507737419 7174861077430091261606129)
                  ·
                    refine ⟨5381145808072568446204597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7174861077430091261606129 5381145808072568446204597)
                    ·
                      refine ⟨504482419506803291831681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5381145808072568446204597 504482419506803291831681)
                      ·
                        rfl

theorem cell23_982476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_982476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_982476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_982476 prefixEnd_982476 := by exact prefixLift 982476
  have htrace : WordTrace (prefixWord ++ tailWord_982476) baseStart_982476 baseEnd_982476 := by
    simpa [prefixWord, tailWord_982476, baseEnd_982476] using wordTrace_append hprefix tailTrace_982476
  have hstable : (prefixWord ++ tailWord_982476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982476).length < 2 ^ (prefixWord ++ tailWord_982476).sum := by decide
  have hdescent : baseEnd_982476 < baseStart_982476 := by decide
  rcases family_descends (prefixWord ++ tailWord_982476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982503 : List Nat := [1, 1, 5, 2, 1, 2, 3, 1, 2, 1, 4]
def baseStart_982503 : Nat := 118140960795 + 982503 * 2 ^ 59
def prefixEnd_982503 : Nat := 4983230072969 + 3 ^ 40 * 982503 * 2
def baseEnd_982503 : Nat := 504496283484474686194057

theorem tailTrace_982503 : CollatzResearch.WordTrace tailWord_982503 prefixEnd_982503 504496283484474686194057 := by
  unfold tailWord_982503
  simp only [CollatzResearch.WordTrace]
  refine ⟨35834828359566903998416163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23889885573044602665610775 35834828359566903998416163)
  ·
    refine ⟨53752242539350355997624245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35834828359566903998416163 53752242539350355997624245)
    ·
      refine ⟨5039272738064095874777273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53752242539350355997624245 5039272738064095874777273)
      ·
        refine ⟨3779454553548071906082955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5039272738064095874777273 3779454553548071906082955)
        ·
          refine ⟨5669181830322107859124433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3779454553548071906082955 5669181830322107859124433)
          ·
            refine ⟨4251886372741580894343325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5669181830322107859124433 4251886372741580894343325)
            ·
              refine ⟨1594457389778092835378747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4251886372741580894343325 1594457389778092835378747)
              ·
                refine ⟨2391686084667139253068121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1594457389778092835378747 2391686084667139253068121)
                ·
                  refine ⟨1793764563500354439801091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2391686084667139253068121 1793764563500354439801091)
                  ·
                    refine ⟨2690646845250531659701637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1793764563500354439801091 2690646845250531659701637)
                    ·
                      refine ⟨504496283484474686194057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2690646845250531659701637 504496283484474686194057)
                      ·
                        rfl

theorem cell23_982503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_982503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_982503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_982503 prefixEnd_982503 := by exact prefixLift 982503
  have htrace : WordTrace (prefixWord ++ tailWord_982503) baseStart_982503 baseEnd_982503 := by
    simpa [prefixWord, tailWord_982503, baseEnd_982503] using wordTrace_append hprefix tailTrace_982503
  have hstable : (prefixWord ++ tailWord_982503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982503).length < 2 ^ (prefixWord ++ tailWord_982503).sum := by decide
  have hdescent : baseEnd_982503 < baseStart_982503 := by decide
  rcases family_descends (prefixWord ++ tailWord_982503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982530 : List Nat := [3, 4, 1, 2, 1, 1, 1, 3, 3, 4]
def baseStart_982530 : Nat := 118140960795 + 982530 * 2 ^ 59
def prefixEnd_982530 : Nat := 4983230072969 + 3 ^ 40 * 982530 * 2
def baseEnd_982530 : Nat := 168170049154048693518811

theorem tailTrace_982530 : CollatzResearch.WordTrace tailWord_982530 prefixEnd_982530 168170049154048693518811 := by
  unfold tailWord_982530
  simp only [CollatzResearch.WordTrace]
  refine ⟨8958953282617271902412261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23890542086979391739766029 8958953282617271902412261)
  ·
    refine ⟨1679803740490738481702299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8958953282617271902412261 1679803740490738481702299)
    ·
      refine ⟨2519705610736107722553449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1679803740490738481702299 2519705610736107722553449)
      ·
        refine ⟨1889779208052080791915087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2519705610736107722553449 1889779208052080791915087)
        ·
          refine ⟨2834668812078121187872631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1889779208052080791915087 2834668812078121187872631)
          ·
            refine ⟨4252003218117181781808947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2834668812078121187872631 4252003218117181781808947)
            ·
              refine ⟨6378004827175772672713421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4252003218117181781808947 6378004827175772672713421)
              ·
                refine ⟨2391751810190914752267533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6378004827175772672713421 2391751810190914752267533)
                ·
                  refine ⟨896906928821593032100325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2391751810190914752267533 896906928821593032100325)
                  ·
                    refine ⟨168170049154048693518811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 896906928821593032100325 168170049154048693518811)
                    ·
                      rfl

theorem cell23_982530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_982530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_982530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_982530 prefixEnd_982530 := by exact prefixLift 982530
  have htrace : WordTrace (prefixWord ++ tailWord_982530) baseStart_982530 baseEnd_982530 := by
    simpa [prefixWord, tailWord_982530, baseEnd_982530] using wordTrace_append hprefix tailTrace_982530
  have hstable : (prefixWord ++ tailWord_982530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982530).length < 2 ^ (prefixWord ++ tailWord_982530).sum := by decide
  have hdescent : baseEnd_982530 < baseStart_982530 := by decide
  rcases family_descends (prefixWord ++ tailWord_982530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982576 : List Nat := [2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 4]
def baseStart_982576 : Nat := 118140960795 + 982576 * 2 ^ 59
def prefixEnd_982576 : Nat := 4983230072969 + 3 ^ 40 * 982576 * 2
def baseEnd_982576 : Nat := 504533767572252900581221

theorem tailTrace_982576 : CollatzResearch.WordTrace tailWord_982576 prefixEnd_982576 504533767572252900581221 := by
  unfold tailWord_982576
  simp only [CollatzResearch.WordTrace]
  refine ⟨17918745444151218732911791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23891660592201624977215721 17918745444151218732911791)
  ·
    refine ⟨26878118166226828099367687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17918745444151218732911791 26878118166226828099367687)
    ·
      refine ⟨40317177249340242149051531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26878118166226828099367687 40317177249340242149051531)
      ·
        refine ⟨60475765874010363223577297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40317177249340242149051531 60475765874010363223577297)
        ·
          refine ⟨45356824405507772417682973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60475765874010363223577297 45356824405507772417682973)
          ·
            refine ⟨17008809152065414656631115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45356824405507772417682973 17008809152065414656631115)
            ·
              refine ⟨25513213728098121984946673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17008809152065414656631115 25513213728098121984946673)
              ·
                refine ⟨19134910296073591488710005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25513213728098121984946673 19134910296073591488710005)
                ·
                  refine ⟨1793897840256899202066563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19134910296073591488710005 1793897840256899202066563)
                  ·
                    refine ⟨2690846760385348803099845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1793897840256899202066563 2690846760385348803099845)
                    ·
                      refine ⟨504533767572252900581221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2690846760385348803099845 504533767572252900581221)
                      ·
                        rfl

theorem cell23_982576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 4].length) (baseStart_982576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_982576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_982576 prefixEnd_982576 := by exact prefixLift 982576
  have htrace : WordTrace (prefixWord ++ tailWord_982576) baseStart_982576 baseEnd_982576 := by
    simpa [prefixWord, tailWord_982576, baseEnd_982576] using wordTrace_append hprefix tailTrace_982576
  have hstable : (prefixWord ++ tailWord_982576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982576).length < 2 ^ (prefixWord ++ tailWord_982576).sum := by decide
  have hdescent : baseEnd_982576 < baseStart_982576 := by decide
  rcases family_descends (prefixWord ++ tailWord_982576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982593 : List Nat := [1, 2, 5, 1, 1, 1, 2, 2, 3, 1, 4]
def baseStart_982593 : Nat := 118140960795 + 982593 * 2 ^ 59
def prefixEnd_982593 : Nat := 4983230072969 + 3 ^ 40 * 982593 * 2
def baseEnd_982593 : Nat := 504542496743379334068643

theorem tailTrace_982593 : CollatzResearch.WordTrace tailWord_982593 prefixEnd_982593 504542496743379334068643 := by
  unfold tailWord_982593
  simp only [CollatzResearch.WordTrace]
  refine ⟨35838110929240849369192433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23892073952827232912794955 35838110929240849369192433)
  ·
    refine ⟨26878583196930637026894325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35838110929240849369192433 26878583196930637026894325)
    ·
      refine ⟨2519867174712247221271343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26878583196930637026894325 2519867174712247221271343)
      ·
        refine ⟨3779800762068370831907015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2519867174712247221271343 3779800762068370831907015)
        ·
          refine ⟨5669701143102556247860523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3779800762068370831907015 5669701143102556247860523)
          ·
            refine ⟨8504551714653834371790785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5669701143102556247860523 8504551714653834371790785)
            ·
              refine ⟨6378413785990375778843089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8504551714653834371790785 6378413785990375778843089)
              ·
                refine ⟨4783810339492781834132317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6378413785990375778843089 4783810339492781834132317)
                ·
                  refine ⟨1793928877309793187799619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4783810339492781834132317 1793928877309793187799619)
                  ·
                    refine ⟨2690893315964689781699429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1793928877309793187799619 2690893315964689781699429)
                    ·
                      refine ⟨504542496743379334068643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2690893315964689781699429 504542496743379334068643)
                      ·
                        rfl

theorem cell23_982593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_982593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_982593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_982593 prefixEnd_982593 := by exact prefixLift 982593
  have htrace : WordTrace (prefixWord ++ tailWord_982593) baseStart_982593 baseEnd_982593 := by
    simpa [prefixWord, tailWord_982593, baseEnd_982593] using wordTrace_append hprefix tailTrace_982593
  have hstable : (prefixWord ++ tailWord_982593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982593).length < 2 ^ (prefixWord ++ tailWord_982593).sum := by decide
  have hdescent : baseEnd_982593 < baseStart_982593 := by decide
  rcases family_descends (prefixWord ++ tailWord_982593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982610 : List Nat := [3, 2, 2, 1, 2, 2, 3, 2, 1, 1, 4]
def baseStart_982610 : Nat := 118140960795 + 982610 * 2 ^ 59
def prefixEnd_982610 : Nat := 4983230072969 + 3 ^ 40 * 982610 * 2
def baseEnd_982610 : Nat := 504551225914505767556065

theorem tailTrace_982610 : CollatzResearch.WordTrace tailWord_982610 prefixEnd_982610 504551225914505767556065 := by
  unfold tailWord_982610
  simp only [CollatzResearch.WordTrace]
  refine ⟨8959682742544815318140321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23892487313452840848374189 8959682742544815318140321)
  ·
    refine ⟨6719762056908611488605241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8959682742544815318140321 6719762056908611488605241)
    ·
      refine ⟨5039821542681458616453931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6719762056908611488605241 5039821542681458616453931)
      ·
        refine ⟨7559732314022187924680897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5039821542681458616453931 7559732314022187924680897)
        ·
          refine ⟨5669799235516640943510673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7559732314022187924680897 5669799235516640943510673)
          ·
            refine ⟨4252349426637480707633005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5669799235516640943510673 4252349426637480707633005)
            ·
              refine ⟨1594631034989055265362377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4252349426637480707633005 1594631034989055265362377)
              ·
                refine ⟨1195973276241791449021783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1594631034989055265362377 1195973276241791449021783)
                ·
                  refine ⟨1793959914362687173532675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1195973276241791449021783 1793959914362687173532675)
                  ·
                    refine ⟨2690939871544030760299013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1793959914362687173532675 2690939871544030760299013)
                    ·
                      refine ⟨504551225914505767556065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2690939871544030760299013 504551225914505767556065)
                      ·
                        rfl

theorem cell23_982610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 2, 1, 1, 4].length) (baseStart_982610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_982610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_982610 prefixEnd_982610 := by exact prefixLift 982610
  have htrace : WordTrace (prefixWord ++ tailWord_982610) baseStart_982610 baseEnd_982610 := by
    simpa [prefixWord, tailWord_982610, baseEnd_982610] using wordTrace_append hprefix tailTrace_982610
  have hstable : (prefixWord ++ tailWord_982610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982610).length < 2 ^ (prefixWord ++ tailWord_982610).sum := by decide
  have hdescent : baseEnd_982610 < baseStart_982610 := by decide
  rcases family_descends (prefixWord ++ tailWord_982610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982637 : List Nat := [1, 5, 1, 1, 4, 1, 2, 2, 2, 4]
def baseStart_982637 : Nat := 118140960795 + 982637 * 2 ^ 59
def prefixEnd_982637 : Nat := 4983230072969 + 3 ^ 40 * 982637 * 2
def baseEnd_982637 : Nat := 168188363297392387306147

theorem tailTrace_982637 : CollatzResearch.WordTrace tailWord_982637 prefixEnd_982637 168188363297392387306147 := by
  unfold tailWord_982637
  simp only [CollatzResearch.WordTrace]
  refine ⟨35839715741081444883794165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23893143827387629922529443 35839715741081444883794165)
  ·
    refine ⟨3359973350726385457855703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35839715741081444883794165 3359973350726385457855703)
    ·
      refine ⟨5039960026089578186783555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3359973350726385457855703 5039960026089578186783555)
      ·
        refine ⟨7559940039134367280175333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5039960026089578186783555 7559940039134367280175333)
        ·
          refine ⟨1417488757337693865032875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7559940039134367280175333 1417488757337693865032875)
          ·
            refine ⟨2126233136006540797549313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1417488757337693865032875 2126233136006540797549313)
            ·
              refine ⟨1594674852004905598161985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2126233136006540797549313 1594674852004905598161985)
              ·
                refine ⟨1196006139003679198621489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1594674852004905598161985 1196006139003679198621489)
                ·
                  refine ⟨897004604252759398966117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1196006139003679198621489 897004604252759398966117)
                  ·
                    refine ⟨168188363297392387306147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 897004604252759398966117 168188363297392387306147)
                    ·
                      rfl

theorem cell23_982637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 2, 2, 4].length) (baseStart_982637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_982637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_982637 prefixEnd_982637 := by exact prefixLift 982637
  have htrace : WordTrace (prefixWord ++ tailWord_982637) baseStart_982637 baseEnd_982637 := by
    simpa [prefixWord, tailWord_982637, baseEnd_982637] using wordTrace_append hprefix tailTrace_982637
  have hstable : (prefixWord ++ tailWord_982637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982637).length < 2 ^ (prefixWord ++ tailWord_982637).sum := by decide
  have hdescent : baseEnd_982637 < baseStart_982637 := by decide
  rcases family_descends (prefixWord ++ tailWord_982637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982638 : List Nat := [4, 1, 2, 2, 4, 1, 2, 2, 1, 1, 3]
def baseStart_982638 : Nat := 118140960795 + 982638 * 2 ^ 59
def prefixEnd_982638 : Nat := 4983230072969 + 3 ^ 40 * 982638 * 2
def baseEnd_982638 : Nat := 504565603372831658005937

theorem tailTrace_982638 : CollatzResearch.WordTrace tailWord_982638 prefixEnd_982638 504565603372831658005937 := by
  unfold tailWord_982638
  simp only [CollatzResearch.WordTrace]
  refine ⟨4479969026759727756822571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23893168142718548036387045 4479969026759727756822571)
  ·
    refine ⟨6719953540139591635233857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4479969026759727756822571 6719953540139591635233857)
    ·
      refine ⟨5039965155104693726425393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6719953540139591635233857 5039965155104693726425393)
      ·
        refine ⟨3779973866328520294819045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5039965155104693726425393 3779973866328520294819045)
        ·
          refine ⟨708745099936597555278571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3779973866328520294819045 708745099936597555278571)
          ·
            refine ⟨1063117649904896332917857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 708745099936597555278571 1063117649904896332917857)
            ·
              refine ⟨797338237428672249688393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1063117649904896332917857 797338237428672249688393)
              ·
                refine ⟨598003678071504187266295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 797338237428672249688393 598003678071504187266295)
                ·
                  refine ⟨897005517107256280899443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 598003678071504187266295 897005517107256280899443)
                  ·
                    refine ⟨1345508275660884421349165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 897005517107256280899443 1345508275660884421349165)
                    ·
                      refine ⟨504565603372831658005937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1345508275660884421349165 504565603372831658005937)
                      ·
                        rfl

theorem cell23_982638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 2, 2, 1, 1, 3].length) (baseStart_982638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_982638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_982638 prefixEnd_982638 := by exact prefixLift 982638
  have htrace : WordTrace (prefixWord ++ tailWord_982638) baseStart_982638 baseEnd_982638 := by
    simpa [prefixWord, tailWord_982638, baseEnd_982638] using wordTrace_append hprefix tailTrace_982638
  have hstable : (prefixWord ++ tailWord_982638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982638).length < 2 ^ (prefixWord ++ tailWord_982638).sum := by decide
  have hdescent : baseEnd_982638 < baseStart_982638 := by decide
  rcases family_descends (prefixWord ++ tailWord_982638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982643 : List Nat := [1, 1, 1, 2, 2, 1, 1, 2, 8, 1, 3]
def baseStart_982643 : Nat := 118140960795 + 982643 * 2 ^ 59
def prefixEnd_982643 : Nat := 4983230072969 + 3 ^ 40 * 982643 * 2
def baseEnd_982643 : Nat := 504568170776104138443413

theorem tailTrace_982643 : CollatzResearch.WordTrace tailWord_982643 prefixEnd_982643 504568170776104138443413 := by
  unfold tailWord_982643
  simp only [CollatzResearch.WordTrace]
  refine ⟨35839934579059707908512583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23893289719373138605675055 35839934579059707908512583)
  ·
    refine ⟨53759901868589561862768875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35839934579059707908512583 53759901868589561862768875)
    ·
      refine ⟨80639852802884342794153313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53759901868589561862768875 80639852802884342794153313)
      ·
        refine ⟨60479889602163257095614985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80639852802884342794153313 60479889602163257095614985)
        ·
          refine ⟨45359917201622442821711239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60479889602163257095614985 45359917201622442821711239)
          ·
            refine ⟨68039875802433664232566859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45359917201622442821711239 68039875802433664232566859)
            ·
              refine ⟨102059813703650496348850289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68039875802433664232566859 102059813703650496348850289)
              ·
                refine ⟨76544860277737872261637717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102059813703650496348850289 76544860277737872261637717)
                ·
                  refine ⟨897010081379740690566067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 76544860277737872261637717 897010081379740690566067)
                  ·
                    refine ⟨1345515122069611035849101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 897010081379740690566067 1345515122069611035849101)
                    ·
                      refine ⟨504568170776104138443413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1345515122069611035849101 504568170776104138443413)
                      ·
                        rfl

theorem cell23_982643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 8, 1, 3].length) (baseStart_982643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_982643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_982643 prefixEnd_982643 := by exact prefixLift 982643
  have htrace : WordTrace (prefixWord ++ tailWord_982643) baseStart_982643 baseEnd_982643 := by
    simpa [prefixWord, tailWord_982643, baseEnd_982643] using wordTrace_append hprefix tailTrace_982643
  have hstable : (prefixWord ++ tailWord_982643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982643).length < 2 ^ (prefixWord ++ tailWord_982643).sum := by decide
  have hdescent : baseEnd_982643 < baseStart_982643 := by decide
  rcases family_descends (prefixWord ++ tailWord_982643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982713 : List Nat := [1, 2, 1, 4, 1, 1, 4, 1, 2, 2, 4]
def baseStart_982713 : Nat := 118140960795 + 982713 * 2 ^ 59
def prefixEnd_982713 : Nat := 4983230072969 + 3 ^ 40 * 982713 * 2
def baseEnd_982713 : Nat := 504604114421918864568091

theorem tailTrace_982713 : CollatzResearch.WordTrace tailWord_982713 prefixEnd_982713 504604114421918864568091 := by
  unfold tailWord_982713
  simp only [CollatzResearch.WordTrace]
  refine ⟨35842487688806109863560793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23894991792537406575707195 35842487688806109863560793)
  ·
    refine ⟨26881865766604582397670595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35842487688806109863560793 26881865766604582397670595)
    ·
      refine ⟨40322798649906873596505893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26881865766604582397670595 40322798649906873596505893)
      ·
        refine ⟨7560524746857538799344855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40322798649906873596505893 7560524746857538799344855)
        ·
          refine ⟨11340787120286308199017283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7560524746857538799344855 11340787120286308199017283)
          ·
            refine ⟨17011180680429462298525925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11340787120286308199017283 17011180680429462298525925)
            ·
              refine ⟨3189596377580524180973611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17011180680429462298525925 3189596377580524180973611)
              ·
                refine ⟨4784394566370786271460417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3189596377580524180973611 4784394566370786271460417)
                ·
                  refine ⟨3588295924778089703595313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4784394566370786271460417 3588295924778089703595313)
                  ·
                    refine ⟨2691221943583567277696485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3588295924778089703595313 2691221943583567277696485)
                    ·
                      refine ⟨504604114421918864568091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2691221943583567277696485 504604114421918864568091)
                      ·
                        rfl

theorem cell23_982713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_982713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_982713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_982713 prefixEnd_982713 := by exact prefixLift 982713
  have htrace : WordTrace (prefixWord ++ tailWord_982713) baseStart_982713 baseEnd_982713 := by
    simpa [prefixWord, tailWord_982713, baseEnd_982713] using wordTrace_append hprefix tailTrace_982713
  have hstable : (prefixWord ++ tailWord_982713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982713).length < 2 ^ (prefixWord ++ tailWord_982713).sum := by decide
  have hdescent : baseEnd_982713 < baseStart_982713 := by decide
  rcases family_descends (prefixWord ++ tailWord_982713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982757 : List Nat := [1, 3, 1, 4, 1, 1, 5, 2, 5]
def baseStart_982757 : Nat := 118140960795 + 982757 * 2 ^ 59
def prefixEnd_982757 : Nat := 4983230072969 + 3 ^ 40 * 982757 * 2
def baseEnd_982757 : Nat := 56069634174524076935321

theorem tailTrace_982757 : CollatzResearch.WordTrace tailWord_982757 prefixEnd_982757 56069634174524076935321 := by
  unfold tailWord_982757
  simp only [CollatzResearch.WordTrace]
  refine ⟨35844092500646705378162525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23896061667097803585441683 35844092500646705378162525)
  ·
    refine ⟨13441534687742514516810947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35844092500646705378162525 13441534687742514516810947)
    ·
      refine ⟨20162302031613771775216421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13441534687742514516810947 20162302031613771775216421)
      ·
        refine ⟨3780431630927582207853079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20162302031613771775216421 3780431630927582207853079)
        ·
          refine ⟨5670647446391373311779619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3780431630927582207853079 5670647446391373311779619)
          ·
            refine ⟨8505971169587059967669429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5670647446391373311779619 8505971169587059967669429)
            ·
              refine ⟨797434797148786871969009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8505971169587059967669429 797434797148786871969009)
              ·
                refine ⟨598076097861590153976757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 797434797148786871969009 598076097861590153976757)
                ·
                  refine ⟨56069634174524076935321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 598076097861590153976757 56069634174524076935321)
                  ·
                    rfl

theorem cell23_982757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 5, 2, 5].length) (baseStart_982757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_982757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_982757 prefixEnd_982757 := by exact prefixLift 982757
  have htrace : WordTrace (prefixWord ++ tailWord_982757) baseStart_982757 baseEnd_982757 := by
    simpa [prefixWord, tailWord_982757, baseEnd_982757] using wordTrace_append hprefix tailTrace_982757
  have hstable : (prefixWord ++ tailWord_982757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982757).length < 2 ^ (prefixWord ++ tailWord_982757).sum := by decide
  have hdescent : baseEnd_982757 < baseStart_982757 := by decide
  rcases family_descends (prefixWord ++ tailWord_982757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982841 : List Nat := [1, 2, 1, 7, 2, 1, 1, 1, 2, 1, 4]
def baseStart_982841 : Nat := 118140960795 + 982841 * 2 ^ 59
def prefixEnd_982841 : Nat := 4983230072969 + 3 ^ 40 * 982841 * 2
def baseEnd_982841 : Nat := 504669839945694363767503

theorem tailTrace_982841 : CollatzResearch.WordTrace tailWord_982841 prefixEnd_982841 504669839945694363767503 := by
  unfold tailWord_982841
  simp only [CollatzResearch.WordTrace]
  refine ⟨35847156232342387724220377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23898104154894925149480251 35847156232342387724220377)
  ·
    refine ⟨26885367174256790793165283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35847156232342387724220377 26885367174256790793165283)
    ·
      refine ⟨40328050761385186189747925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26885367174256790793165283 40328050761385186189747925)
      ·
        refine ⟨945188689719965301322217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 40328050761385186189747925 945188689719965301322217)
        ·
          refine ⟨708891517289973975991663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 945188689719965301322217 708891517289973975991663)
          ·
            refine ⟨1063337275934960963987495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 708891517289973975991663 1063337275934960963987495)
            ·
              refine ⟨1595005913902441445981243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1063337275934960963987495 1595005913902441445981243)
              ·
                refine ⟨2392508870853662168971865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1595005913902441445981243 2392508870853662168971865)
                ·
                  refine ⟨1794381653140246626728899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2392508870853662168971865 1794381653140246626728899)
                  ·
                    refine ⟨2691572479710369940093349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1794381653140246626728899 2691572479710369940093349)
                    ·
                      refine ⟨504669839945694363767503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2691572479710369940093349 504669839945694363767503)
                      ·
                        rfl

theorem cell23_982841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_982841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_982841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_982841 prefixEnd_982841 := by exact prefixLift 982841
  have htrace : WordTrace (prefixWord ++ tailWord_982841) baseStart_982841 baseEnd_982841 := by
    simpa [prefixWord, tailWord_982841, baseEnd_982841] using wordTrace_append hprefix tailTrace_982841
  have hstable : (prefixWord ++ tailWord_982841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982841).length < 2 ^ (prefixWord ++ tailWord_982841).sum := by decide
  have hdescent : baseEnd_982841 < baseStart_982841 := by decide
  rcases family_descends (prefixWord ++ tailWord_982841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982874 : List Nat := [3, 1, 1, 2, 1, 3, 1, 6, 1, 1, 3]
def baseStart_982874 : Nat := 118140960795 + 982874 * 2 ^ 59
def prefixEnd_982874 : Nat := 4983230072969 + 3 ^ 40 * 982874 * 2
def baseEnd_982874 : Nat := 504686784807292734654851

theorem tailTrace_982874 : CollatzResearch.WordTrace tailWord_982874 prefixEnd_982874 504686784807292734654851 := by
  unfold tailWord_982874
  simp only [CollatzResearch.WordTrace]
  refine ⟨8962089960305708590042919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23898906560815222906781117 8962089960305708590042919)
  ·
    refine ⟨13443134940458562885064379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8962089960305708590042919 13443134940458562885064379)
    ·
      refine ⟨20164702410687844327596569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13443134940458562885064379 20164702410687844327596569)
      ·
        refine ⟨15123526808015883245697427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20164702410687844327596569 15123526808015883245697427)
        ·
          refine ⟨22685290212023824868546141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15123526808015883245697427 22685290212023824868546141)
          ·
            refine ⟨8506983829508934325704803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22685290212023824868546141 8506983829508934325704803)
            ·
              refine ⟨12760475744263401488557205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8506983829508934325704803 12760475744263401488557205)
              ·
                refine ⟨598147300512346944776119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12760475744263401488557205 598147300512346944776119)
                ·
                  refine ⟨897220950768520417164179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 598147300512346944776119 897220950768520417164179)
                  ·
                    refine ⟨1345831426152780625746269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 897220950768520417164179 1345831426152780625746269)
                    ·
                      refine ⟨504686784807292734654851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1345831426152780625746269 504686784807292734654851)
                      ·
                        rfl

theorem cell23_982874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 6, 1, 1, 3].length) (baseStart_982874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_982874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_982874 prefixEnd_982874 := by exact prefixLift 982874
  have htrace : WordTrace (prefixWord ++ tailWord_982874) baseStart_982874 baseEnd_982874 := by
    simpa [prefixWord, tailWord_982874, baseEnd_982874] using wordTrace_append hprefix tailTrace_982874
  have hstable : (prefixWord ++ tailWord_982874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982874).length < 2 ^ (prefixWord ++ tailWord_982874).sum := by decide
  have hdescent : baseEnd_982874 < baseStart_982874 := by decide
  rcases family_descends (prefixWord ++ tailWord_982874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982894 : List Nat := [4, 1, 2, 3, 1, 2, 2, 2, 1, 5]
def baseStart_982894 : Nat := 118140960795 + 982894 * 2 ^ 59
def prefixEnd_982894 : Nat := 4983230072969 + 3 ^ 40 * 982894 * 2
def baseEnd_982894 : Nat := 168232351473460885468253

theorem tailTrace_982894 : CollatzResearch.WordTrace tailWord_982894 prefixEnd_982894 168232351473460885468253 := by
  unfold tailWord_982894
  simp only [CollatzResearch.WordTrace]
  refine ⟨4481136162643797221987467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23899392867433585183933157 4481136162643797221987467)
  ·
    refine ⟨6721704243965695832981201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4481136162643797221987467 6721704243965695832981201)
    ·
      refine ⟨5041278182974271874735901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6721704243965695832981201 5041278182974271874735901)
      ·
        refine ⟨1890479318615351953025963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5041278182974271874735901 1890479318615351953025963)
        ·
          refine ⟨2835718977923027929538945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1890479318615351953025963 2835718977923027929538945)
          ·
            refine ⟨2126789233442270947154209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2835718977923027929538945 2126789233442270947154209)
            ·
              refine ⟨1595091925081703210365657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2126789233442270947154209 1595091925081703210365657)
              ·
                refine ⟨1196318943811277407774243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1595091925081703210365657 1196318943811277407774243)
                ·
                  refine ⟨1794478415716916111661365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1196318943811277407774243 1794478415716916111661365)
                  ·
                    refine ⟨168232351473460885468253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1794478415716916111661365 168232351473460885468253)
                    ·
                      rfl

theorem cell23_982894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 2, 1, 5].length) (baseStart_982894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_982894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_982894 prefixEnd_982894 := by exact prefixLift 982894
  have htrace : WordTrace (prefixWord ++ tailWord_982894) baseStart_982894 baseEnd_982894 := by
    simpa [prefixWord, tailWord_982894, baseEnd_982894] using wordTrace_append hprefix tailTrace_982894
  have hstable : (prefixWord ++ tailWord_982894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982894).length < 2 ^ (prefixWord ++ tailWord_982894).sum := by decide
  have hdescent : baseEnd_982894 < baseStart_982894 := by decide
  rcases family_descends (prefixWord ++ tailWord_982894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982897 : List Nat := [1, 2, 2, 2, 1, 3, 4, 2, 1, 1, 4]
def baseStart_982897 : Nat := 118140960795 + 982897 * 2 ^ 59
def prefixEnd_982897 : Nat := 4983230072969 + 3 ^ 40 * 982897 * 2
def baseEnd_982897 : Nat := 504698594862346144667245

theorem tailTrace_982897 : CollatzResearch.WordTrace tailWord_982897 prefixEnd_982897 504698594862346144667245 := by
  unfold tailWord_982897
  simp only [CollatzResearch.WordTrace]
  refine ⟨35849198720139509288258945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23899465813426339525505963 35849198720139509288258945)
  ·
    refine ⟨26886899040104631966194209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35849198720139509288258945 26886899040104631966194209)
    ·
      refine ⟨20165174280078473974645657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26886899040104631966194209 20165174280078473974645657)
      ·
        refine ⟨15123880710058855480984243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20165174280078473974645657 15123880710058855480984243)
        ·
          refine ⟨22685821065088283221476365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15123880710058855480984243 22685821065088283221476365)
          ·
            refine ⟨8507182899408106208053637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22685821065088283221476365 8507182899408106208053637)
            ·
              refine ⟨1595096793639019914010057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8507182899408106208053637 1595096793639019914010057)
              ·
                refine ⟨1196322595229264935507543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1595096793639019914010057 1196322595229264935507543)
                ·
                  refine ⟨1794483892843897403261315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1196322595229264935507543 1794483892843897403261315)
                  ·
                    refine ⟨2691725839265846104891973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1794483892843897403261315 2691725839265846104891973)
                    ·
                      refine ⟨504698594862346144667245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2691725839265846104891973 504698594862346144667245)
                      ·
                        rfl

theorem cell23_982897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 2, 1, 1, 4].length) (baseStart_982897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_982897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_982897 prefixEnd_982897 := by exact prefixLift 982897
  have htrace : WordTrace (prefixWord ++ tailWord_982897) baseStart_982897 baseEnd_982897 := by
    simpa [prefixWord, tailWord_982897, baseEnd_982897] using wordTrace_append hprefix tailTrace_982897
  have hstable : (prefixWord ++ tailWord_982897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982897).length < 2 ^ (prefixWord ++ tailWord_982897).sum := by decide
  have hdescent : baseEnd_982897 < baseStart_982897 := by decide
  rcases family_descends (prefixWord ++ tailWord_982897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982917 : List Nat := [1, 3, 1, 1, 3, 2, 1, 5, 1, 2, 3]
def baseStart_982917 : Nat := 118140960795 + 982917 * 2 ^ 59
def prefixEnd_982917 : Nat := 4983230072969 + 3 ^ 40 * 982917 * 2
def baseEnd_982917 : Nat := 504708864475436066417153

theorem tailTrace_982917 : CollatzResearch.WordTrace tailWord_982917 prefixEnd_982917 504708864475436066417153 := by
  unfold tailWord_982917
  simp only [CollatzResearch.WordTrace]
  refine ⟨35849928180067052703987005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23899952120044701802658003 35849928180067052703987005)
  ·
    refine ⟨13443723067525144763995127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35849928180067052703987005 13443723067525144763995127)
    ·
      refine ⟨20165584601287717145992691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13443723067525144763995127 20165584601287717145992691)
      ·
        refine ⟨30248376901931575718989037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20165584601287717145992691 30248376901931575718989037)
        ·
          refine ⟨11343141338224340894620889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30248376901931575718989037 11343141338224340894620889)
          ·
            refine ⟨8507356003668255670965667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11343141338224340894620889 8507356003668255670965667)
            ·
              refine ⟨12761034005502383506448501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8507356003668255670965667 12761034005502383506448501)
              ·
                refine ⟨1196346938015848453729547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12761034005502383506448501 1196346938015848453729547)
                ·
                  refine ⟨1794520407023772680594321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1196346938015848453729547 1794520407023772680594321)
                  ·
                    refine ⟨1345890305267829510445741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1794520407023772680594321 1345890305267829510445741)
                    ·
                      refine ⟨504708864475436066417153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1345890305267829510445741 504708864475436066417153)
                      ·
                        rfl

theorem cell23_982917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 5, 1, 2, 3].length) (baseStart_982917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_982917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_982917 prefixEnd_982917 := by exact prefixLift 982917
  have htrace : WordTrace (prefixWord ++ tailWord_982917) baseStart_982917 baseEnd_982917 := by
    simpa [prefixWord, tailWord_982917, baseEnd_982917] using wordTrace_append hprefix tailTrace_982917
  have hstable : (prefixWord ++ tailWord_982917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982917).length < 2 ^ (prefixWord ++ tailWord_982917).sum := by decide
  have hdescent : baseEnd_982917 < baseStart_982917 := by decide
  rcases family_descends (prefixWord ++ tailWord_982917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982941 : List Nat := [1, 4, 2, 1, 2, 4, 2, 1, 2, 4]
def baseStart_982941 : Nat := 118140960795 + 982941 * 2 ^ 59
def prefixEnd_982941 : Nat := 4983230072969 + 3 ^ 40 * 982941 * 2
def baseEnd_982941 : Nat := 168240396003714657505681

theorem tailTrace_982941 : CollatzResearch.WordTrace tailWord_982941 prefixEnd_982941 168240396003714657505681 := by
  unfold tailWord_982941
  simp only [CollatzResearch.WordTrace]
  refine ⟨35850803531980104802860677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23900535687986736535240451 35850803531980104802860677)
  ·
    refine ⟨6722025662246269650536377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35850803531980104802860677 6722025662246269650536377)
    ·
      refine ⟨5041519246684702237902283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6722025662246269650536377 5041519246684702237902283)
      ·
        refine ⟨7562278870027053356853425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5041519246684702237902283 7562278870027053356853425)
        ·
          refine ⟨5671709152520290017640069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7562278870027053356853425 5671709152520290017640069)
          ·
            refine ⟨1063445466097554378307513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5671709152520290017640069 1063445466097554378307513)
            ·
              refine ⟨797584099573165783730635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1063445466097554378307513 797584099573165783730635)
              ·
                refine ⟨1196376149359748675595953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 797584099573165783730635 1196376149359748675595953)
                ·
                  refine ⟨897282112019811506696965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1196376149359748675595953 897282112019811506696965)
                  ·
                    refine ⟨168240396003714657505681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 897282112019811506696965 168240396003714657505681)
                    ·
                      rfl

theorem cell23_982941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 2, 1, 2, 4].length) (baseStart_982941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_982941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_982941 prefixEnd_982941 := by exact prefixLift 982941
  have htrace : WordTrace (prefixWord ++ tailWord_982941) baseStart_982941 baseEnd_982941 := by
    simpa [prefixWord, tailWord_982941, baseEnd_982941] using wordTrace_append hprefix tailTrace_982941
  have hstable : (prefixWord ++ tailWord_982941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982941).length < 2 ^ (prefixWord ++ tailWord_982941).sum := by decide
  have hdescent : baseEnd_982941 < baseStart_982941 := by decide
  rcases family_descends (prefixWord ++ tailWord_982941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982951 : List Nat := [1, 1, 6, 1, 2, 3, 1, 2, 1, 2, 3]
def baseStart_982951 : Nat := 118140960795 + 982951 * 2 ^ 59
def prefixEnd_982951 : Nat := 4983230072969 + 3 ^ 40 * 982951 * 2
def baseEnd_982951 : Nat := 504726322817688933391997

theorem tailTrace_982951 : CollatzResearch.WordTrace tailWord_982951 prefixEnd_982951 504726322817688933391997 := by
  unfold tailWord_982951
  simp only [CollatzResearch.WordTrace]
  refine ⟨35851168261943876510724707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23900778841295917673816471 35851168261943876510724707)
  ·
    refine ⟨53776752392915814766087061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35851168261943876510724707 53776752392915814766087061)
    ·
      refine ⟨2520785268417928817160331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 53776752392915814766087061 2520785268417928817160331)
      ·
        refine ⟨3781177902626893225740497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2520785268417928817160331 3781177902626893225740497)
        ·
          refine ⟨2835883426970169919305373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3781177902626893225740497 2835883426970169919305373)
          ·
            refine ⟨1063456285113813719739515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2835883426970169919305373 1063456285113813719739515)
            ·
              refine ⟨1595184427670720579609273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1063456285113813719739515 1595184427670720579609273)
              ·
                refine ⟨1196388320753040434706955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1595184427670720579609273 1196388320753040434706955)
                ·
                  refine ⟨1794582481129560652060433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1196388320753040434706955 1794582481129560652060433)
                  ·
                    refine ⟨1345936860847170489045325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1794582481129560652060433 1345936860847170489045325)
                    ·
                      refine ⟨504726322817688933391997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1345936860847170489045325 504726322817688933391997)
                      ·
                        rfl

theorem cell23_982951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_982951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_982951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_982951 prefixEnd_982951 := by exact prefixLift 982951
  have htrace : WordTrace (prefixWord ++ tailWord_982951) baseStart_982951 baseEnd_982951 := by
    simpa [prefixWord, tailWord_982951, baseEnd_982951] using wordTrace_append hprefix tailTrace_982951
  have hstable : (prefixWord ++ tailWord_982951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982951).length < 2 ^ (prefixWord ++ tailWord_982951).sum := by decide
  have hdescent : baseEnd_982951 < baseStart_982951 := by decide
  rcases family_descends (prefixWord ++ tailWord_982951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982987 : List Nat := [1, 1, 1, 1, 3, 4, 1, 2, 3, 4, 2]
def baseStart_982987 : Nat := 118140960795 + 982987 * 2 ^ 59
def prefixEnd_982987 : Nat := 4983230072969 + 3 ^ 40 * 982987 * 2
def baseEnd_982987 : Nat := 504744808121250792541831

theorem tailTrace_982987 : CollatzResearch.WordTrace tailWord_982987 prefixEnd_982987 504744808121250792541831 := by
  unfold tailWord_982987
  simp only [CollatzResearch.WordTrace]
  refine ⟨35852481289813454659035215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23901654193208969772690143 35852481289813454659035215)
  ·
    refine ⟨53778721934720181988552823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35852481289813454659035215 53778721934720181988552823)
    ·
      refine ⟨80668082902080272982829235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53778721934720181988552823 80668082902080272982829235)
      ·
        refine ⟨121002124353120409474243853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80668082902080272982829235 121002124353120409474243853)
        ·
          refine ⟨45375796632420153552841445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121002124353120409474243853 45375796632420153552841445)
          ·
            refine ⟨8507961868578778791157771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45375796632420153552841445 8507961868578778791157771)
            ·
              refine ⟨12761942802868168186736657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8507961868578778791157771 12761942802868168186736657)
              ·
                refine ⟨9571457102151126140052493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12761942802868168186736657 9571457102151126140052493)
                ·
                  refine ⟨3589296413306672302519685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9571457102151126140052493 3589296413306672302519685)
                  ·
                    refine ⟨672993077495001056722441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3589296413306672302519685 672993077495001056722441)
                    ·
                      refine ⟨504744808121250792541831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 672993077495001056722441 504744808121250792541831)
                      ·
                        rfl

theorem cell23_982987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 3, 4, 2].length) (baseStart_982987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_982987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_982987 prefixEnd_982987 := by exact prefixLift 982987
  have htrace : WordTrace (prefixWord ++ tailWord_982987) baseStart_982987 baseEnd_982987 := by
    simpa [prefixWord, tailWord_982987, baseEnd_982987] using wordTrace_append hprefix tailTrace_982987
  have hstable : (prefixWord ++ tailWord_982987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982987).length < 2 ^ (prefixWord ++ tailWord_982987).sum := by decide
  have hdescent : baseEnd_982987 < baseStart_982987 := by decide
  rcases family_descends (prefixWord ++ tailWord_982987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982997 : List Nat := [1, 3, 2, 3, 2, 2, 1, 1, 2, 6]
def baseStart_982997 : Nat := 118140960795 + 982997 * 2 ^ 59
def prefixEnd_982997 : Nat := 4983230072969 + 3 ^ 40 * 982997 * 2
def baseEnd_982997 : Nat := 168249980975931917805595

theorem tailTrace_982997 : CollatzResearch.WordTrace tailWord_982997 prefixEnd_982997 168249980975931917805595 := by
  unfold tailWord_982997
  simp only [CollatzResearch.WordTrace]
  refine ⟨35852846019777226366899245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23901897346518150911266163 35852846019777226366899245)
  ·
    refine ⟨13444817257416459887587217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35852846019777226366899245 13444817257416459887587217)
    ·
      refine ⟨10083612943062344915690413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13444817257416459887587217 10083612943062344915690413)
      ·
        refine ⟨3781354853648379343383905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10083612943062344915690413 3781354853648379343383905)
        ·
          refine ⟨2836016140236284507537929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3781354853648379343383905 2836016140236284507537929)
          ·
            refine ⟨2127012105177213380653447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2836016140236284507537929 2127012105177213380653447)
            ·
              refine ⟨3190518157765820070980171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2127012105177213380653447 3190518157765820070980171)
              ·
                refine ⟨4785777236648730106470257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3190518157765820070980171 4785777236648730106470257)
                ·
                  refine ⟨3589332927486547579852693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4785777236648730106470257 3589332927486547579852693)
                  ·
                    refine ⟨168249980975931917805595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3589332927486547579852693 168249980975931917805595)
                    ·
                      rfl

theorem cell23_982997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 1, 2, 6].length) (baseStart_982997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_982997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_982997 prefixEnd_982997 := by exact prefixLift 982997
  have htrace : WordTrace (prefixWord ++ tailWord_982997) baseStart_982997 baseEnd_982997 := by
    simpa [prefixWord, tailWord_982997, baseEnd_982997] using wordTrace_append hprefix tailTrace_982997
  have hstable : (prefixWord ++ tailWord_982997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982997).length < 2 ^ (prefixWord ++ tailWord_982997).sum := by decide
  have hdescent : baseEnd_982997 < baseStart_982997 := by decide
  rcases family_descends (prefixWord ++ tailWord_982997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983025 : List Nat := [1, 2, 2, 2, 6, 1, 2, 1, 1, 3, 2]
def baseStart_983025 : Nat := 118140960795 + 983025 * 2 ^ 59
def prefixEnd_983025 : Nat := 4983230072969 + 3 ^ 40 * 983025 * 2
def baseEnd_983025 : Nat := 504764320386121643866657

theorem tailTrace_983025 : CollatzResearch.WordTrace tailWord_983025 prefixEnd_983025 504764320386121643866657 := by
  unfold tailWord_983025
  simp only [CollatzResearch.WordTrace]
  refine ⟨35853867263675787148918529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23902578175783858099279019 35853867263675787148918529)
  ·
    refine ⟨26890400447756840361688897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35853867263675787148918529 26890400447756840361688897)
    ·
      refine ⟨20167800335817630271266673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26890400447756840361688897 20167800335817630271266673)
      ·
        refine ⟨15125850251863222703450005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20167800335817630271266673 15125850251863222703450005)
        ·
          refine ⟨709024230556088564224219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 15125850251863222703450005 709024230556088564224219)
          ·
            refine ⟨1063536345834132846336329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 709024230556088564224219 1063536345834132846336329)
            ·
              refine ⟨797652259375599634752247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1063536345834132846336329 797652259375599634752247)
              ·
                refine ⟨1196478389063399452128371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 797652259375599634752247 1196478389063399452128371)
                ·
                  refine ⟨1794717583595099178192557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1196478389063399452128371 1794717583595099178192557)
                  ·
                    refine ⟨673019093848162191822209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1794717583595099178192557 673019093848162191822209)
                    ·
                      refine ⟨504764320386121643866657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 673019093848162191822209 504764320386121643866657)
                      ·
                        rfl

theorem cell23_983025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 2, 1, 1, 3, 2].length) (baseStart_983025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_983025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_983025 prefixEnd_983025 := by exact prefixLift 983025
  have htrace : WordTrace (prefixWord ++ tailWord_983025) baseStart_983025 baseEnd_983025 := by
    simpa [prefixWord, tailWord_983025, baseEnd_983025] using wordTrace_append hprefix tailTrace_983025
  have hstable : (prefixWord ++ tailWord_983025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983025).length < 2 ^ (prefixWord ++ tailWord_983025).sum := by decide
  have hdescent : baseEnd_983025 < baseStart_983025 := by decide
  rcases family_descends (prefixWord ++ tailWord_983025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983037 : List Nat := [1, 4, 1, 1, 1, 2, 3, 2, 2, 3, 3]
def baseStart_983037 : Nat := 118140960795 + 983037 * 2 ^ 59
def prefixEnd_983037 : Nat := 4983230072969 + 3 ^ 40 * 983037 * 2
def baseEnd_983037 : Nat := 504770482153975596916601

theorem tailTrace_983037 : CollatzResearch.WordTrace tailWord_983037 prefixEnd_983037 504770482153975596916601 := by
  unfold tailWord_983037
  simp only [CollatzResearch.WordTrace]
  refine ⟨35854304939632313198355365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23902869959754875465570243 35854304939632313198355365)
  ·
    refine ⟨6722682176181058724691631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35854304939632313198355365 6722682176181058724691631)
    ·
      refine ⟨10084023264271588087037447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6722682176181058724691631 10084023264271588087037447)
      ·
        refine ⟨15126034896407382130556171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10084023264271588087037447 15126034896407382130556171)
        ·
          refine ⟨22689052344611073195834257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15126034896407382130556171 22689052344611073195834257)
          ·
            refine ⟨17016789258458304896875693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22689052344611073195834257 17016789258458304896875693)
            ·
              refine ⟨6381295971921864336328385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17016789258458304896875693 6381295971921864336328385)
              ·
                refine ⟨4785971978941398252246289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6381295971921864336328385 4785971978941398252246289)
                ·
                  refine ⟨3589478984206048689184717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4785971978941398252246289 3589478984206048689184717)
                  ·
                    refine ⟨1346054619077268258444269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3589478984206048689184717 1346054619077268258444269)
                    ·
                      refine ⟨504770482153975596916601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1346054619077268258444269 504770482153975596916601)
                      ·
                        rfl

theorem cell23_983037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 2, 2, 3, 3].length) (baseStart_983037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_983037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_983037 prefixEnd_983037 := by exact prefixLift 983037
  have htrace : WordTrace (prefixWord ++ tailWord_983037) baseStart_983037 baseEnd_983037 := by
    simpa [prefixWord, tailWord_983037, baseEnd_983037] using wordTrace_append hprefix tailTrace_983037
  have hstable : (prefixWord ++ tailWord_983037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983037).length < 2 ^ (prefixWord ++ tailWord_983037).sum := by decide
  have hdescent : baseEnd_983037 < baseStart_983037 := by decide
  rcases family_descends (prefixWord ++ tailWord_983037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983038 : List Nat := [4, 2, 2, 2, 1, 2, 1, 1, 4, 2, 2]
def baseStart_983038 : Nat := 118140960795 + 983038 * 2 ^ 59
def prefixEnd_983038 : Nat := 4983230072969 + 3 ^ 40 * 983038 * 2
def baseEnd_983038 : Nat := 504770995634630093004097

theorem tailTrace_983038 : CollatzResearch.WordTrace tailWord_983038 prefixEnd_983038 504770995634630093004097 := by
  unfold tailWord_983038
  simp only [CollatzResearch.WordTrace]
  refine ⟨4481792676578586296142721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23902894275085793579427845 4481792676578586296142721)
  ·
    refine ⟨3361344507433939722107041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4481792676578586296142721 3361344507433939722107041)
    ·
      refine ⟨2521008380575454791580281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3361344507433939722107041 2521008380575454791580281)
      ·
        refine ⟨1890756285431591093685211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2521008380575454791580281 1890756285431591093685211)
        ·
          refine ⟨2836134428147386640527817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1890756285431591093685211 2836134428147386640527817)
          ·
            refine ⟨2127100821110539980395863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2836134428147386640527817 2127100821110539980395863)
            ·
              refine ⟨3190651231665809970593795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2127100821110539980395863 3190651231665809970593795)
              ·
                refine ⟨4785976847498714955890693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3190651231665809970593795 4785976847498714955890693)
                ·
                  refine ⟨897370658906009054229505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4785976847498714955890693 897370658906009054229505)
                  ·
                    refine ⟨673027994179506790672129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 897370658906009054229505 673027994179506790672129)
                    ·
                      refine ⟨504770995634630093004097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 673027994179506790672129 504770995634630093004097)
                      ·
                        rfl

theorem cell23_983038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_983038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_983038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_983038 prefixEnd_983038 := by exact prefixLift 983038
  have htrace : WordTrace (prefixWord ++ tailWord_983038) baseStart_983038 baseEnd_983038 := by
    simpa [prefixWord, tailWord_983038, baseEnd_983038] using wordTrace_append hprefix tailTrace_983038
  have hstable : (prefixWord ++ tailWord_983038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983038).length < 2 ^ (prefixWord ++ tailWord_983038).sum := by decide
  have hdescent : baseEnd_983038 < baseStart_983038 := by decide
  rcases family_descends (prefixWord ++ tailWord_983038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983077 : List Nat := [1, 3, 1, 2, 2, 3, 2, 1, 1, 3, 4]
def baseStart_983077 : Nat := 118140960795 + 983077 * 2 ^ 59
def prefixEnd_983077 : Nat := 4983230072969 + 3 ^ 40 * 983077 * 2
def baseEnd_983077 : Nat := 504791021380155440416417

theorem tailTrace_983077 : CollatzResearch.WordTrace tailWord_983077 prefixEnd_983077 504791021380155440416417 := by
  unfold tailWord_983077
  simp only [CollatzResearch.WordTrace]
  refine ⟨35855763859487400029811485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23903842572991600019874323 35855763859487400029811485)
  ·
    refine ⟨13445911447307775011179307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35855763859487400029811485 13445911447307775011179307)
    ·
      refine ⟨20168867170961662516768961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13445911447307775011179307 20168867170961662516768961)
      ·
        refine ⟨15126650378221246887576721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20168867170961662516768961 15126650378221246887576721)
        ·
          refine ⟨11344987783665935165682541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15126650378221246887576721 11344987783665935165682541)
          ·
            refine ⟨4254370418874725687130953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11344987783665935165682541 4254370418874725687130953)
            ·
              refine ⟨3190777814156044265348215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4254370418874725687130953 3190777814156044265348215)
              ·
                refine ⟨4786166721234066398022323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3190777814156044265348215 4786166721234066398022323)
                ·
                  refine ⟨7179250081851099597033485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4786166721234066398022323 7179250081851099597033485)
                  ·
                    refine ⟨2692218780694162348887557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7179250081851099597033485 2692218780694162348887557)
                    ·
                      refine ⟨504791021380155440416417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2692218780694162348887557 504791021380155440416417)
                      ·
                        rfl

theorem cell23_983077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 1, 1, 3, 4].length) (baseStart_983077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_983077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_983077 prefixEnd_983077 := by exact prefixLift 983077
  have htrace : WordTrace (prefixWord ++ tailWord_983077) baseStart_983077 baseEnd_983077 := by
    simpa [prefixWord, tailWord_983077, baseEnd_983077] using wordTrace_append hprefix tailTrace_983077
  have hstable : (prefixWord ++ tailWord_983077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983077).length < 2 ^ (prefixWord ++ tailWord_983077).sum := by decide
  have hdescent : baseEnd_983077 < baseStart_983077 := by decide
  rcases family_descends (prefixWord ++ tailWord_983077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983104 : List Nat := [2, 1, 1, 2, 2, 4, 3, 1, 3, 4]
def baseStart_983104 : Nat := 118140960795 + 983104 * 2 ^ 59
def prefixEnd_983104 : Nat := 4983230072969 + 3 ^ 40 * 983104 * 2
def baseEnd_983104 : Nat := 168268295119275611592931

theorem tailTrace_983104 : CollatzResearch.WordTrace tailWord_983104 prefixEnd_983104 168268295119275611592931 := by
  unfold tailWord_983104
  simp only [CollatzResearch.WordTrace]
  refine ⟨17928374315194791820522183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23904499086926389094029577 17928374315194791820522183)
  ·
    refine ⟨26892561472792187730783275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17928374315194791820522183 26892561472792187730783275)
    ·
      refine ⟨40338842209188281596174913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26892561472792187730783275 40338842209188281596174913)
      ·
        refine ⟨30254131656891211197131185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40338842209188281596174913 30254131656891211197131185)
        ·
          refine ⟨22690598742668408397848389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30254131656891211197131185 22690598742668408397848389)
          ·
            refine ⟨4254487264250326574596573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22690598742668408397848389 4254487264250326574596573)
            ·
              refine ⟨1595432724093872465473715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4254487264250326574596573 1595432724093872465473715)
              ·
                refine ⟨2393149086140808698210573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1595432724093872465473715 2393149086140808698210573)
                ·
                  refine ⟨897430907302803261828965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2393149086140808698210573 897430907302803261828965)
                  ·
                    refine ⟨168268295119275611592931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 897430907302803261828965 168268295119275611592931)
                    ·
                      rfl

theorem cell23_983104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 1, 3, 4].length) (baseStart_983104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_983104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_983104 prefixEnd_983104 := by exact prefixLift 983104
  have htrace : WordTrace (prefixWord ++ tailWord_983104) baseStart_983104 baseEnd_983104 := by
    simpa [prefixWord, tailWord_983104, baseEnd_983104] using wordTrace_append hprefix tailTrace_983104
  have hstable : (prefixWord ++ tailWord_983104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983104).length < 2 ^ (prefixWord ++ tailWord_983104).sum := by decide
  have hdescent : baseEnd_983104 < baseStart_983104 := by decide
  rcases family_descends (prefixWord ++ tailWord_983104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983127 : List Nat := [1, 1, 3, 2, 2, 1, 2, 1, 2, 5, 3]
def baseStart_983127 : Nat := 118140960795 + 983127 * 2 ^ 59
def prefixEnd_983127 : Nat := 4983230072969 + 3 ^ 40 * 983127 * 2
def baseEnd_983127 : Nat := 504816695412880244791187

theorem tailTrace_983127 : CollatzResearch.WordTrace tailWord_983127 prefixEnd_983127 504816695412880244791187 := by
  unfold tailWord_983127
  simp only [CollatzResearch.WordTrace]
  refine ⟨35857587509306258569131635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23905058339537505712754423 35857587509306258569131635)
  ·
    refine ⟨53786381263959387853697453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35857587509306258569131635 53786381263959387853697453)
    ·
      refine ⟨20169892973984770445136545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53786381263959387853697453 20169892973984770445136545)
      ·
        refine ⟨15127419730488577833852409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20169892973984770445136545 15127419730488577833852409)
        ·
          refine ⟨11345564797866433375389307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15127419730488577833852409 11345564797866433375389307)
          ·
            refine ⟨17018347196799650063083961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11345564797866433375389307 17018347196799650063083961)
            ·
              refine ⟨12763760397599737547312971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17018347196799650063083961 12763760397599737547312971)
              ·
                refine ⟨19145640596399606320969457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12763760397599737547312971 19145640596399606320969457)
                ·
                  refine ⟨14359230447299704740727093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19145640596399606320969457 14359230447299704740727093)
                  ·
                    refine ⟨1346177854434347319443165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14359230447299704740727093 1346177854434347319443165)
                    ·
                      refine ⟨504816695412880244791187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1346177854434347319443165 504816695412880244791187)
                      ·
                        rfl

theorem cell23_983127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 5, 3].length) (baseStart_983127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_983127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_983127 prefixEnd_983127 := by exact prefixLift 983127
  have htrace : WordTrace (prefixWord ++ tailWord_983127) baseStart_983127 baseEnd_983127 := by
    simpa [prefixWord, tailWord_983127, baseEnd_983127] using wordTrace_append hprefix tailTrace_983127
  have hstable : (prefixWord ++ tailWord_983127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983127).length < 2 ^ (prefixWord ++ tailWord_983127).sum := by decide
  have hdescent : baseEnd_983127 < baseStart_983127 := by decide
  rcases family_descends (prefixWord ++ tailWord_983127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983184 : List Nat := [2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 4]
def baseStart_983184 : Nat := 118140960795 + 983184 * 2 ^ 59
def prefixEnd_983184 : Nat := 4983230072969 + 3 ^ 40 * 983184 * 2
def baseEnd_983184 : Nat := 504845963810186521778425

theorem tailTrace_983184 : CollatzResearch.WordTrace tailWord_983184 prefixEnd_983184 504845963810186521778425 := by
  unfold tailWord_983184
  simp only [CollatzResearch.WordTrace]
  refine ⟨17929833235049878651978303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23906444313399838202637737 17929833235049878651978303)
  ·
    refine ⟨26894749852574817977967455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17929833235049878651978303 26894749852574817977967455)
    ·
      refine ⟨40342124778862226966951183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26894749852574817977967455 40342124778862226966951183)
      ·
        refine ⟨60513187168293340450426775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40342124778862226966951183 60513187168293340450426775)
        ·
          refine ⟨90769780752440010675640163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60513187168293340450426775 90769780752440010675640163)
          ·
            refine ⟨136154671128660016013460245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90769780752440010675640163 136154671128660016013460245)
            ·
              refine ⟨6382250209155938250630949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 136154671128660016013460245 6382250209155938250630949)
              ·
                refine ⟨1196671914216738421993303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6382250209155938250630949 1196671914216738421993303)
                ·
                  refine ⟨1795007871325107632989955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1196671914216738421993303 1795007871325107632989955)
                  ·
                    refine ⟨2692511806987661449484933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1795007871325107632989955 2692511806987661449484933)
                    ·
                      refine ⟨504845963810186521778425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2692511806987661449484933 504845963810186521778425)
                      ·
                        rfl

theorem cell23_983184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 4].length) (baseStart_983184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_983184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_983184 prefixEnd_983184 := by exact prefixLift 983184
  have htrace : WordTrace (prefixWord ++ tailWord_983184) baseStart_983184 baseEnd_983184 := by
    simpa [prefixWord, tailWord_983184, baseEnd_983184] using wordTrace_append hprefix tailTrace_983184
  have hstable : (prefixWord ++ tailWord_983184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983184).length < 2 ^ (prefixWord ++ tailWord_983184).sum := by decide
  have hdescent : baseEnd_983184 < baseStart_983184 := by decide
  rcases family_descends (prefixWord ++ tailWord_983184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983198 : List Nat := [4, 3, 1, 1, 3, 1, 1, 3, 1, 5]
def baseStart_983198 : Nat := 118140960795 + 983198 * 2 ^ 59
def prefixEnd_983198 : Nat := 4983230072969 + 3 ^ 40 * 983198 * 2
def baseEnd_983198 : Nat := 168284384179783155667787

theorem tailTrace_983198 : CollatzResearch.WordTrace tailWord_983198 prefixEnd_983198 168284384179783155667787 := by
  unfold tailWord_983198
  simp only [CollatzResearch.WordTrace]
  refine ⟨4482522136506129711870781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23906784728032691796644165 4482522136506129711870781)
  ·
    refine ⟨1680945801189798641951543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4482522136506129711870781 1680945801189798641951543)
    ·
      refine ⟨2521418701784697962927315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1680945801189798641951543 2521418701784697962927315)
      ·
        refine ⟨3782128052677046944390973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2521418701784697962927315 3782128052677046944390973)
        ·
          refine ⟨1418298019753892604146615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3782128052677046944390973 1418298019753892604146615)
          ·
            refine ⟨2127447029630838906219923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1418298019753892604146615 2127447029630838906219923)
            ·
              refine ⟨3191170544446258359329885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2127447029630838906219923 3191170544446258359329885)
              ·
                refine ⟨1196688954167346884748707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3191170544446258359329885 1196688954167346884748707)
                ·
                  refine ⟨1795033431251020327123061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1196688954167346884748707 1795033431251020327123061)
                  ·
                    refine ⟨168284384179783155667787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1795033431251020327123061 168284384179783155667787)
                    ·
                      rfl

theorem cell23_983198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_983198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_983198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_983198 prefixEnd_983198 := by exact prefixLift 983198
  have htrace : WordTrace (prefixWord ++ tailWord_983198) baseStart_983198 baseEnd_983198 := by
    simpa [prefixWord, tailWord_983198, baseEnd_983198] using wordTrace_append hprefix tailTrace_983198
  have hstable : (prefixWord ++ tailWord_983198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983198).length < 2 ^ (prefixWord ++ tailWord_983198).sum := by decide
  have hdescent : baseEnd_983198 < baseStart_983198 := by decide
  rcases family_descends (prefixWord ++ tailWord_983198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983201 : List Nat := [1, 2, 3, 3, 1, 3, 1, 3, 1, 1, 4]
def baseStart_983201 : Nat := 118140960795 + 983201 * 2 ^ 59
def prefixEnd_983201 : Nat := 4983230072969 + 3 ^ 40 * 983201 * 2
def baseEnd_983201 : Nat := 504854692981312955265847

theorem tailTrace_983201 : CollatzResearch.WordTrace tailWord_983201 prefixEnd_983201 504854692981312955265847 := by
  unfold tailWord_983201
  simp only [CollatzResearch.WordTrace]
  refine ⟨35860286511038169207325457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23906857674025446138216971 35860286511038169207325457)
  ·
    refine ⟨26895214883278626905494093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35860286511038169207325457 26895214883278626905494093)
    ·
      refine ⟨10085705581229485089560285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26895214883278626905494093 10085705581229485089560285)
      ·
        refine ⟨3782139592961056908585107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10085705581229485089560285 3782139592961056908585107)
        ·
          refine ⟨5673209389441585362877661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3782139592961056908585107 5673209389441585362877661)
          ·
            refine ⟨2127453521040594511079123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5673209389441585362877661 2127453521040594511079123)
            ·
              refine ⟨3191180281560891766618685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2127453521040594511079123 3191180281560891766618685)
              ·
                refine ⟨1196692605585334412482007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3191180281560891766618685 1196692605585334412482007)
                ·
                  refine ⟨1795038908378001618723011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1196692605585334412482007 1795038908378001618723011)
                  ·
                    refine ⟨2692558362567002428084517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1795038908378001618723011 2692558362567002428084517)
                    ·
                      refine ⟨504854692981312955265847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2692558362567002428084517 504854692981312955265847)
                      ·
                        rfl

theorem cell23_983201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_983201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_983201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_983201 prefixEnd_983201 := by exact prefixLift 983201
  have htrace : WordTrace (prefixWord ++ tailWord_983201) baseStart_983201 baseEnd_983201 := by
    simpa [prefixWord, tailWord_983201, baseEnd_983201] using wordTrace_append hprefix tailTrace_983201
  have hstable : (prefixWord ++ tailWord_983201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983201).length < 2 ^ (prefixWord ++ tailWord_983201).sum := by decide
  have hdescent : baseEnd_983201 < baseStart_983201 := by decide
  rcases family_descends (prefixWord ++ tailWord_983201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983218 : List Nat := [3, 2, 1, 1, 1, 3, 4, 1, 3, 2, 2]
def baseStart_983218 : Nat := 118140960795 + 983218 * 2 ^ 59
def prefixEnd_983218 : Nat := 4983230072969 + 3 ^ 40 * 983218 * 2
def baseEnd_983218 : Nat := 504863422152439388753269

theorem tailTrace_983218 : CollatzResearch.WordTrace tailWord_983218 prefixEnd_983218 504863422152439388753269 := by
  unfold tailWord_983218
  simp only [CollatzResearch.WordTrace]
  refine ⟨8965226637994145277673577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23907271034651054073796205 8965226637994145277673577)
  ·
    refine ⟨6723919978495608958255183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8965226637994145277673577 6723919978495608958255183)
    ·
      refine ⟨10085879967743413437382775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6723919978495608958255183 10085879967743413437382775)
      ·
        refine ⟨15128819951615120156074163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10085879967743413437382775 15128819951615120156074163)
        ·
          refine ⟨22693229927422680234111245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15128819951615120156074163 22693229927422680234111245)
          ·
            refine ⟨8509961222783505087791717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22693229927422680234111245 8509961222783505087791717)
            ·
              refine ⟨1595617729271907203960947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8509961222783505087791717 1595617729271907203960947)
              ·
                refine ⟨2393426593907860805941421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1595617729271907203960947 2393426593907860805941421)
                ·
                  refine ⟨897534972715447802228033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2393426593907860805941421 897534972715447802228033)
                  ·
                    refine ⟨673151229536585851671025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 897534972715447802228033 673151229536585851671025)
                    ·
                      refine ⟨504863422152439388753269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 673151229536585851671025 504863422152439388753269)
                      ·
                        rfl

theorem cell23_983218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 1, 3, 2, 2].length) (baseStart_983218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_983218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_983218 prefixEnd_983218 := by exact prefixLift 983218
  have htrace : WordTrace (prefixWord ++ tailWord_983218) baseStart_983218 baseEnd_983218 := by
    simpa [prefixWord, tailWord_983218, baseEnd_983218] using wordTrace_append hprefix tailTrace_983218
  have hstable : (prefixWord ++ tailWord_983218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983218).length < 2 ^ (prefixWord ++ tailWord_983218).sum := by decide
  have hdescent : baseEnd_983218 < baseStart_983218 := by decide
  rcases family_descends (prefixWord ++ tailWord_983218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983228 : List Nat := [2, 2, 2, 3, 4, 1, 1, 1, 1, 6]
def baseStart_983228 : Nat := 118140960795 + 983228 * 2 ^ 59
def prefixEnd_983228 : Nat := 4983230072969 + 3 ^ 40 * 983228 * 2
def baseEnd_983228 : Nat := 168289518986328116542741

theorem tailTrace_983228 : CollatzResearch.WordTrace tailWord_983228 prefixEnd_983228 168289518986328116542741 := by
  unfold tailWord_983228
  simp only [CollatzResearch.WordTrace]
  refine ⟨17930635640970176409279169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23907514187960235212372225 17930635640970176409279169)
  ·
    refine ⟨13447976730727632306959377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17930635640970176409279169 13447976730727632306959377)
    ·
      refine ⟨10085982548045724230219533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13447976730727632306959377 10085982548045724230219533)
      ·
        refine ⟨3782243455517146586332325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10085982548045724230219533 3782243455517146586332325)
        ·
          refine ⟨709170647909464984937311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3782243455517146586332325 709170647909464984937311)
          ·
            refine ⟨1063755971864197477405967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 709170647909464984937311 1063755971864197477405967)
            ·
              refine ⟨1595633957796296216108951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1063755971864197477405967 1595633957796296216108951)
              ·
                refine ⟨2393450936694444324163427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1595633957796296216108951 2393450936694444324163427)
                ·
                  refine ⟨3590176405041666486245141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2393450936694444324163427 3590176405041666486245141)
                  ·
                    refine ⟨168289518986328116542741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3590176405041666486245141 168289518986328116542741)
                    ·
                      rfl

theorem cell23_983228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 1, 1, 6].length) (baseStart_983228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_983228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_983228 prefixEnd_983228 := by exact prefixLift 983228
  have htrace : WordTrace (prefixWord ++ tailWord_983228) baseStart_983228 baseEnd_983228 := by
    simpa [prefixWord, tailWord_983228, baseEnd_983228] using wordTrace_append hprefix tailTrace_983228
  have hstable : (prefixWord ++ tailWord_983228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983228).length < 2 ^ (prefixWord ++ tailWord_983228).sum := by decide
  have hdescent : baseEnd_983228 < baseStart_983228 := by decide
  rcases family_descends (prefixWord ++ tailWord_983228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983237 : List Nat := [1, 3, 1, 1, 1, 1, 4, 2, 2, 7]
def baseStart_983237 : Nat := 118140960795 + 983237 * 2 ^ 59
def prefixEnd_983237 : Nat := 4983230072969 + 3 ^ 40 * 983237 * 2
def baseEnd_983237 : Nat := 168291059428291604805227

theorem tailTrace_983237 : CollatzResearch.WordTrace tailWord_983237 prefixEnd_983237 168291059428291604805227 := by
  unfold tailWord_983237
  simp only [CollatzResearch.WordTrace]
  refine ⟨35861599538907747355635965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23907733025938498237090643 35861599538907747355635965)
  ·
    refine ⟨13448099827090405258363487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35861599538907747355635965 13448099827090405258363487)
    ·
      refine ⟨20172149740635607887545231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13448099827090405258363487 20172149740635607887545231)
      ·
        refine ⟨30258224610953411831317847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20172149740635607887545231 30258224610953411831317847)
        ·
          refine ⟨45387336916430117746976771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30258224610953411831317847 45387336916430117746976771)
          ·
            refine ⟨68081005374645176620465157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45387336916430117746976771 68081005374645176620465157)
            ·
              refine ⟨12765188507745970616337217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68081005374645176620465157 12765188507745970616337217)
              ·
                refine ⟨9573891380809477962252913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12765188507745970616337217 9573891380809477962252913)
                ·
                  refine ⟨7180418535607108471689685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9573891380809477962252913 7180418535607108471689685)
                  ·
                    refine ⟨168291059428291604805227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7180418535607108471689685 168291059428291604805227)
                    ·
                      rfl

theorem cell23_983237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 2, 7].length) (baseStart_983237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_983237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_983237 prefixEnd_983237 := by exact prefixLift 983237
  have htrace : WordTrace (prefixWord ++ tailWord_983237) baseStart_983237 baseEnd_983237 := by
    simpa [prefixWord, tailWord_983237, baseEnd_983237] using wordTrace_append hprefix tailTrace_983237
  have hstable : (prefixWord ++ tailWord_983237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983237).length < 2 ^ (prefixWord ++ tailWord_983237).sum := by decide
  have hdescent : baseEnd_983237 < baseStart_983237 := by decide
  rcases family_descends (prefixWord ++ tailWord_983237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983247 : List Nat := [1, 1, 2, 1, 1, 3, 3, 1, 1, 4, 5]
def baseStart_983247 : Nat := 118140960795 + 983247 * 2 ^ 59
def prefixEnd_983247 : Nat := 4983230072969 + 3 ^ 40 * 983247 * 2
def baseEnd_983247 : Nat := 504878313091419775290635

theorem tailTrace_983247 : CollatzResearch.WordTrace tailWord_983247 prefixEnd_983247 504878313091419775290635 := by
  unfold tailWord_983247
  simp only [CollatzResearch.WordTrace]
  refine ⟨35861964268871519063499995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23907976179247679375666663 35861964268871519063499995)
  ·
    refine ⟨53792946403307278595249993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35861964268871519063499995 53792946403307278595249993)
    ·
      refine ⟨40344709802480458946437495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53792946403307278595249993 40344709802480458946437495)
      ·
        refine ⟨60517064703720688419656243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40344709802480458946437495 60517064703720688419656243)
        ·
          refine ⟨90775597055581032629484365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60517064703720688419656243 90775597055581032629484365)
          ·
            refine ⟨34040848895842887236056637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90775597055581032629484365 34040848895842887236056637)
            ·
              refine ⟨12765318335941082713521239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34040848895842887236056637 12765318335941082713521239)
              ·
                refine ⟨19147977503911624070281859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12765318335941082713521239 19147977503911624070281859)
                ·
                  refine ⟨28721966255867436105422789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19147977503911624070281859 28721966255867436105422789)
                  ·
                    refine ⟨5385368672975144269766773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28721966255867436105422789 5385368672975144269766773)
                    ·
                      refine ⟨504878313091419775290635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5385368672975144269766773 504878313091419775290635)
                      ·
                        rfl

theorem cell23_983247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 4, 5].length) (baseStart_983247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_983247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_983247 prefixEnd_983247 := by exact prefixLift 983247
  have htrace : WordTrace (prefixWord ++ tailWord_983247) baseStart_983247 baseEnd_983247 := by
    simpa [prefixWord, tailWord_983247, baseEnd_983247] using wordTrace_append hprefix tailTrace_983247
  have hstable : (prefixWord ++ tailWord_983247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983247).length < 2 ^ (prefixWord ++ tailWord_983247).sum := by decide
  have hdescent : baseEnd_983247 < baseStart_983247 := by decide
  rcases family_descends (prefixWord ++ tailWord_983247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983274 : List Nat := [3, 1, 3, 1, 1, 2, 2, 1, 2, 3, 4]
def baseStart_983274 : Nat := 118140960795 + 983274 * 2 ^ 59
def prefixEnd_983274 : Nat := 4983230072969 + 3 ^ 40 * 983274 * 2
def baseEnd_983274 : Nat := 504892177069091169653011

theorem tailTrace_983274 : CollatzResearch.WordTrace tailWord_983274 prefixEnd_983274 504892177069091169653011 := by
  unfold tailWord_983274
  simp only [CollatzResearch.WordTrace]
  refine ⟨8965737259943425668683219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23908632693182468449821917 8965737259943425668683219)
  ·
    refine ⟨13448605889915138503024829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8965737259943425668683219 13448605889915138503024829)
    ·
      refine ⟨5043227208718176938634311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13448605889915138503024829 5043227208718176938634311)
      ·
        refine ⟨7564840813077265407951467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5043227208718176938634311 7564840813077265407951467)
        ·
          refine ⟨11347261219615898111927201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7564840813077265407951467 11347261219615898111927201)
          ·
            refine ⟨8510445914711923583945401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11347261219615898111927201 8510445914711923583945401)
            ·
              refine ⟨6382834436033942687959051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8510445914711923583945401 6382834436033942687959051)
              ·
                refine ⟨9574251654050914031938577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6382834436033942687959051 9574251654050914031938577)
                ·
                  refine ⟨7180688740538185523953933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9574251654050914031938577 7180688740538185523953933)
                  ·
                    refine ⟨2692758277701819571482725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7180688740538185523953933 2692758277701819571482725)
                    ·
                      refine ⟨504892177069091169653011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2692758277701819571482725 504892177069091169653011)
                      ·
                        rfl

theorem cell23_983274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_983274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_983274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_983274 prefixEnd_983274 := by exact prefixLift 983274
  have htrace : WordTrace (prefixWord ++ tailWord_983274) baseStart_983274 baseEnd_983274 := by
    simpa [prefixWord, tailWord_983274, baseEnd_983274] using wordTrace_append hprefix tailTrace_983274
  have hstable : (prefixWord ++ tailWord_983274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983274).length < 2 ^ (prefixWord ++ tailWord_983274).sum := by decide
  have hdescent : baseEnd_983274 < baseStart_983274 := by decide
  rcases family_descends (prefixWord ++ tailWord_983274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983331 : List Nat := [1, 1, 1, 4, 2, 2, 3, 4, 5]
def baseStart_983331 : Nat := 118140960795 + 983331 * 2 ^ 59
def prefixEnd_983331 : Nat := 4983230072969 + 3 ^ 40 * 983331 * 2
def baseEnd_983331 : Nat := 56102382829599716293361

theorem tailTrace_983331 : CollatzResearch.WordTrace tailWord_983331 prefixEnd_983331 56102382829599716293361 := by
  unfold tailWord_983331
  simp only [CollatzResearch.WordTrace]
  refine ⟨35865028000567201409557847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23910018667044800939705231 35865028000567201409557847)
  ·
    refine ⟨53797542000850802114336771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35865028000567201409557847 53797542000850802114336771)
    ·
      refine ⟨80696313001276203171505157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53797542000850802114336771 80696313001276203171505157)
      ·
        refine ⟨15130558687739288094657217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80696313001276203171505157 15130558687739288094657217)
        ·
          refine ⟨11347919015804466070992913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15130558687739288094657217 11347919015804466070992913)
          ·
            refine ⟨8510939261853349553244685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11347919015804466070992913 8510939261853349553244685)
            ·
              refine ⟨3191602223195006082466757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8510939261853349553244685 3191602223195006082466757)
              ·
                refine ⟨598425416849063640462517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3191602223195006082466757 598425416849063640462517)
                ·
                  refine ⟨56102382829599716293361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 598425416849063640462517 56102382829599716293361)
                  ·
                    rfl

theorem cell23_983331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 4, 5].length) (baseStart_983331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_983331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_983331 prefixEnd_983331 := by exact prefixLift 983331
  have htrace : WordTrace (prefixWord ++ tailWord_983331) baseStart_983331 baseEnd_983331 := by
    simpa [prefixWord, tailWord_983331, baseEnd_983331] using wordTrace_append hprefix tailTrace_983331
  have hstable : (prefixWord ++ tailWord_983331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983331).length < 2 ^ (prefixWord ++ tailWord_983331).sum := by decide
  have hdescent : baseEnd_983331 < baseStart_983331 := by decide
  rcases family_descends (prefixWord ++ tailWord_983331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983335 : List Nat := [1, 1, 8, 1, 1, 1, 1, 1, 2, 6]
def baseStart_983335 : Nat := 118140960795 + 983335 * 2 ^ 59
def prefixEnd_983335 : Nat := 4983230072969 + 3 ^ 40 * 983335 * 2
def baseEnd_983335 : Nat := 168307833129671810330077

theorem tailTrace_983335 : CollatzResearch.WordTrace tailWord_983335 prefixEnd_983335 168307833129671810330077 := by
  unfold tailWord_983335
  simp only [CollatzResearch.WordTrace]
  refine ⟨35865173892552710092703459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23910115928368473395135639 35865173892552710092703459)
  ·
    refine ⟨53797760838829065139055189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35865173892552710092703459 53797760838829065139055189)
    ·
      refine ⟨630442509830028107098303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 53797760838829065139055189 630442509830028107098303)
      ·
        refine ⟨945663764745042160647455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 630442509830028107098303 945663764745042160647455)
        ·
          refine ⟨1418495647117563240971183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 945663764745042160647455 1418495647117563240971183)
          ·
            refine ⟨2127743470676344861456775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1418495647117563240971183 2127743470676344861456775)
            ·
              refine ⟨3191615206014517292185163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2127743470676344861456775 3191615206014517292185163)
              ·
                refine ⟨4787422809021775938277745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3191615206014517292185163 4787422809021775938277745)
                ·
                  refine ⟨3590567106766331953708309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4787422809021775938277745 3590567106766331953708309)
                  ·
                    refine ⟨168307833129671810330077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3590567106766331953708309 168307833129671810330077)
                    ·
                      rfl

theorem cell23_983335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_983335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_983335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_983335 prefixEnd_983335 := by exact prefixLift 983335
  have htrace : WordTrace (prefixWord ++ tailWord_983335) baseStart_983335 baseEnd_983335 := by
    simpa [prefixWord, tailWord_983335, baseEnd_983335] using wordTrace_append hprefix tailTrace_983335
  have hstable : (prefixWord ++ tailWord_983335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983335).length < 2 ^ (prefixWord ++ tailWord_983335).sum := by decide
  have hdescent : baseEnd_983335 < baseStart_983335 := by decide
  rcases family_descends (prefixWord ++ tailWord_983335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983338 : List Nat := [3, 1, 4, 2, 2, 1, 1, 1, 2, 2, 4]
def baseStart_983338 : Nat := 118140960795 + 983338 * 2 ^ 59
def prefixEnd_983338 : Nat := 4983230072969 + 3 ^ 40 * 983338 * 2
def baseEnd_983338 : Nat := 504925039830978919252717

theorem tailTrace_983338 : CollatzResearch.WordTrace tailWord_983338 prefixEnd_983338 504925039830978919252717 := by
  unfold tailWord_983338
  simp only [CollatzResearch.WordTrace]
  refine ⟨8966320827885460401265667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23910188874361227736708445 8966320827885460401265667)
  ·
    refine ⟨13449481241828190601898501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8966320827885460401265667 13449481241828190601898501)
    ·
      refine ⟨2521777732842785737855969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13449481241828190601898501 2521777732842785737855969)
      ·
        refine ⟨1891333299632089303391977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2521777732842785737855969 1891333299632089303391977)
        ·
          refine ⟨1418499974724066977543983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1891333299632089303391977 1418499974724066977543983)
          ·
            refine ⟨2127749962086100466315975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1418499974724066977543983 2127749962086100466315975)
            ·
              refine ⟨3191624943129150699473963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2127749962086100466315975 3191624943129150699473963)
              ·
                refine ⟨4787437414693726049210945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3191624943129150699473963 4787437414693726049210945)
                ·
                  refine ⟨3590578061020294536908209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4787437414693726049210945 3590578061020294536908209)
                  ·
                    refine ⟨2692933545765220902681157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3590578061020294536908209 2692933545765220902681157)
                    ·
                      refine ⟨504925039830978919252717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2692933545765220902681157 504925039830978919252717)
                      ·
                        rfl

theorem cell23_983338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_983338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_983338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_983338 prefixEnd_983338 := by exact prefixLift 983338
  have htrace : WordTrace (prefixWord ++ tailWord_983338) baseStart_983338 baseEnd_983338 := by
    simpa [prefixWord, tailWord_983338, baseEnd_983338] using wordTrace_append hprefix tailTrace_983338
  have hstable : (prefixWord ++ tailWord_983338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983338).length < 2 ^ (prefixWord ++ tailWord_983338).sum := by decide
  have hdescent : baseEnd_983338 < baseStart_983338 := by decide
  rcases family_descends (prefixWord ++ tailWord_983338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983342 : List Nat := [4, 1, 3, 3, 1, 1, 2, 1, 1, 4, 2]
def baseStart_983342 : Nat := 118140960795 + 983342 * 2 ^ 59
def prefixEnd_983342 : Nat := 4983230072969 + 3 ^ 40 * 983342 * 2
def baseEnd_983342 : Nat := 504927093753596903602699

theorem tailTrace_983342 : CollatzResearch.WordTrace tailWord_983342 prefixEnd_983342 504927093753596903602699 := by
  unfold tailWord_983342
  simp only [CollatzResearch.WordTrace]
  refine ⟨4483178650440918786026035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23910286135684900192138853 4483178650440918786026035)
  ·
    refine ⟨6724767975661378179039053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4483178650440918786026035 6724767975661378179039053)
    ·
      refine ⟨2521787990873016817139645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6724767975661378179039053 2521787990873016817139645)
      ·
        refine ⟨945670496577381306427367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2521787990873016817139645 945670496577381306427367)
        ·
          refine ⟨1418505744866071959641051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 945670496577381306427367 1418505744866071959641051)
          ·
            refine ⟨2127758617299107939461577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1418505744866071959641051 2127758617299107939461577)
            ·
              refine ⟨1595818962974330954596183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2127758617299107939461577 1595818962974330954596183)
              ·
                refine ⟨2393728444461496431894275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1595818962974330954596183 2393728444461496431894275)
                ·
                  refine ⟨3590592666692244647841413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2393728444461496431894275 3590592666692244647841413)
                  ·
                    refine ⟨673236125004795871470265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3590592666692244647841413 673236125004795871470265)
                    ·
                      refine ⟨504927093753596903602699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 673236125004795871470265 504927093753596903602699)
                      ·
                        rfl

theorem cell23_983342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_983342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_983342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_983342 prefixEnd_983342 := by exact prefixLift 983342
  have htrace : WordTrace (prefixWord ++ tailWord_983342) baseStart_983342 baseEnd_983342 := by
    simpa [prefixWord, tailWord_983342, baseEnd_983342] using wordTrace_append hprefix tailTrace_983342
  have hstable : (prefixWord ++ tailWord_983342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983342).length < 2 ^ (prefixWord ++ tailWord_983342).sum := by decide
  have hdescent : baseEnd_983342 < baseStart_983342 := by decide
  rcases family_descends (prefixWord ++ tailWord_983342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983391 : List Nat := [1, 1, 2, 3, 1, 2, 3, 3, 3, 4]
def baseStart_983391 : Nat := 118140960795 + 983391 * 2 ^ 59
def prefixEnd_983391 : Nat := 4983230072969 + 3 ^ 40 * 983391 * 2
def baseEnd_983391 : Nat := 168317418101889070629991

theorem tailTrace_983391 : CollatzResearch.WordTrace tailWord_983391 prefixEnd_983391 168317418101889070629991 := by
  unfold tailWord_983391
  simp only [CollatzResearch.WordTrace]
  refine ⟨35867216380349831656742027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23911477586899887771161351 35867216380349831656742027)
  ·
    refine ⟨53800824570524747485113041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35867216380349831656742027 53800824570524747485113041)
    ·
      refine ⟨40350618427893560613834781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53800824570524747485113041 40350618427893560613834781)
      ·
        refine ⟨15131481910460085230188043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40350618427893560613834781 15131481910460085230188043)
        ·
          refine ⟨22697222865690127845282065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15131481910460085230188043 22697222865690127845282065)
          ·
            refine ⟨17022917149267595883961549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22697222865690127845282065 17022917149267595883961549)
            ·
              refine ⟨6383593930975348456485581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17022917149267595883961549 6383593930975348456485581)
              ·
                refine ⟨2393847724115755671182093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6383593930975348456485581 2393847724115755671182093)
                ·
                  refine ⟨897692896543408376693285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2393847724115755671182093 897692896543408376693285)
                  ·
                    refine ⟨168317418101889070629991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 897692896543408376693285 168317418101889070629991)
                    ·
                      rfl

theorem cell23_983391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 3, 3, 4].length) (baseStart_983391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_983391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_983391 prefixEnd_983391 := by exact prefixLift 983391
  have htrace : WordTrace (prefixWord ++ tailWord_983391) baseStart_983391 baseEnd_983391 := by
    simpa [prefixWord, tailWord_983391, baseEnd_983391] using wordTrace_append hprefix tailTrace_983391
  have hstable : (prefixWord ++ tailWord_983391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983391).length < 2 ^ (prefixWord ++ tailWord_983391).sum := by decide
  have hdescent : baseEnd_983391 < baseStart_983391 := by decide
  rcases family_descends (prefixWord ++ tailWord_983391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983481 : List Nat := [1, 2, 1, 4, 3, 1, 1, 1, 3, 6]
def baseStart_983481 : Nat := 118140960795 + 983481 * 2 ^ 59
def prefixEnd_983481 : Nat := 4983230072969 + 3 ^ 40 * 983481 * 2
def baseEnd_983481 : Nat := 168332822521523953254853

theorem tailTrace_983481 : CollatzResearch.WordTrace tailWord_983481 prefixEnd_983481 168332822521523953254853 := by
  unfold tailWord_983481
  simp only [CollatzResearch.WordTrace]
  refine ⟨35870498950023777027518297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23913665966682518018345531 35870498950023777027518297)
  ·
    refine ⟨26902874212517832770638723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35870498950023777027518297 26902874212517832770638723)
    ·
      refine ⟨40354311318776749155958085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26902874212517832770638723 40354311318776749155958085)
      ·
        refine ⟨7566433372270640466742141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40354311318776749155958085 7566433372270640466742141)
        ·
          refine ⟨2837412514601490175028303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7566433372270640466742141 2837412514601490175028303)
          ·
            refine ⟨4256118771902235262542455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2837412514601490175028303 4256118771902235262542455)
            ·
              refine ⟨6384178157853352893813683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4256118771902235262542455 6384178157853352893813683)
              ·
                refine ⟨9576267236780029340720525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6384178157853352893813683 9576267236780029340720525)
                ·
                  refine ⟨3591100213792511002770197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9576267236780029340720525 3591100213792511002770197)
                  ·
                    refine ⟨168332822521523953254853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3591100213792511002770197 168332822521523953254853)
                    ·
                      rfl

theorem cell23_983481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 3, 6].length) (baseStart_983481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_983481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_983481 prefixEnd_983481 := by exact prefixLift 983481
  have htrace : WordTrace (prefixWord ++ tailWord_983481) baseStart_983481 baseEnd_983481 := by
    simpa [prefixWord, tailWord_983481, baseEnd_983481] using wordTrace_append hprefix tailTrace_983481
  have hstable : (prefixWord ++ tailWord_983481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983481).length < 2 ^ (prefixWord ++ tailWord_983481).sum := by decide
  have hdescent : baseEnd_983481 < baseStart_983481 := by decide
  rcases family_descends (prefixWord ++ tailWord_983481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983485 : List Nat := [1, 4, 1, 2, 2, 3, 3, 1, 1, 5]
def baseStart_983485 : Nat := 118140960795 + 983485 * 2 ^ 59
def prefixEnd_983485 : Nat := 4983230072969 + 3 ^ 40 * 983485 * 2
def baseEnd_983485 : Nat := 168333507162396614704847

theorem tailTrace_983485 : CollatzResearch.WordTrace tailWord_983485 prefixEnd_983485 168333507162396614704847 := by
  unfold tailWord_983485
  simp only [CollatzResearch.WordTrace]
  refine ⟨35870644842009285710663909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23913763228006190473775939 35870644842009285710663909)
  ·
    refine ⟨6725745907876741070749483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35870644842009285710663909 6725745907876741070749483)
    ·
      refine ⟨10088618861815111606124225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6725745907876741070749483 10088618861815111606124225)
      ·
        refine ⟨7566464146361333704593169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10088618861815111606124225 7566464146361333704593169)
        ·
          refine ⟨5674848109771000278444877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7566464146361333704593169 5674848109771000278444877)
          ·
            refine ⟨2128068041164125104416829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5674848109771000278444877 2128068041164125104416829)
            ·
              refine ⟨798025515436546914156311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2128068041164125104416829 798025515436546914156311)
              ·
                refine ⟨1197038273154820371234467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 798025515436546914156311 1197038273154820371234467)
                ·
                  refine ⟨1795557409732230556851701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1197038273154820371234467 1795557409732230556851701)
                  ·
                    refine ⟨168333507162396614704847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1795557409732230556851701 168333507162396614704847)
                    ·
                      rfl

theorem cell23_983485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 3, 1, 1, 5].length) (baseStart_983485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_983485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_983485 prefixEnd_983485 := by exact prefixLift 983485
  have htrace : WordTrace (prefixWord ++ tailWord_983485) baseStart_983485 baseEnd_983485 := by
    simpa [prefixWord, tailWord_983485, baseEnd_983485] using wordTrace_append hprefix tailTrace_983485
  have hstable : (prefixWord ++ tailWord_983485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983485).length < 2 ^ (prefixWord ++ tailWord_983485).sum := by decide
  have hdescent : baseEnd_983485 < baseStart_983485 := by decide
  rcases family_descends (prefixWord ++ tailWord_983485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983528 : List Nat := [2, 1, 4, 1, 1, 4, 3, 7]
def baseStart_983528 : Nat := 118140960795 + 983528 * 2 ^ 59
def prefixEnd_983528 : Nat := 4983230072969 + 3 ^ 40 * 983528 * 2
def baseEnd_983528 : Nat := 18704540783530858365809

theorem tailTrace_983528 : CollatzResearch.WordTrace tailWord_983528 prefixEnd_983528 18704540783530858365809 := by
  unfold tailWord_983528
  simp only [CollatzResearch.WordTrace]
  refine ⟨17936106590426752027239619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23914808787235669369652825 17936106590426752027239619)
  ·
    refine ⟨26904159885640128040859429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17936106590426752027239619 26904159885640128040859429)
    ·
      refine ⟨5044529978557524007661143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26904159885640128040859429 5044529978557524007661143)
      ·
        refine ⟨7566794967836286011491715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5044529978557524007661143 7566794967836286011491715)
        ·
          refine ⟨11350192451754429017237573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7566794967836286011491715 11350192451754429017237573)
          ·
            refine ⟨2128161084703955440732045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11350192451754429017237573 2128161084703955440732045)
            ·
              refine ⟨798060406763983290274517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2128161084703955440732045 798060406763983290274517)
              ·
                refine ⟨18704540783530858365809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 798060406763983290274517 18704540783530858365809)
                ·
                  rfl

theorem cell23_983528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 3, 7].length) (baseStart_983528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_983528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_983528 prefixEnd_983528 := by exact prefixLift 983528
  have htrace : WordTrace (prefixWord ++ tailWord_983528) baseStart_983528 baseEnd_983528 := by
    simpa [prefixWord, tailWord_983528, baseEnd_983528] using wordTrace_append hprefix tailTrace_983528
  have hstable : (prefixWord ++ tailWord_983528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983528).length < 2 ^ (prefixWord ++ tailWord_983528).sum := by decide
  have hdescent : baseEnd_983528 < baseStart_983528 := by decide
  rcases family_descends (prefixWord ++ tailWord_983528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983561 : List Nat := [1, 2, 1, 1, 3, 1, 2, 3, 2, 3, 4]
def baseStart_983561 : Nat := 118140960795 + 983561 * 2 ^ 59
def prefixEnd_983561 : Nat := 4983230072969 + 3 ^ 40 * 983561 * 2
def baseEnd_983561 : Nat := 505039546016931546764191

theorem tailTrace_983561 : CollatzResearch.WordTrace tailWord_983561 prefixEnd_983561 505039546016931546764191 := by
  unfold tailWord_983561
  simp only [CollatzResearch.WordTrace]
  refine ⟨35873416789733950690430537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23915611193155967126953691 35873416789733950690430537)
  ·
    refine ⟨26905062592300463017822903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35873416789733950690430537 26905062592300463017822903)
    ·
      refine ⟨40357593888450694526734355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26905062592300463017822903 40357593888450694526734355)
      ·
        refine ⟨60536390832676041790101533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40357593888450694526734355 60536390832676041790101533)
        ·
          refine ⟨22701146562253515671288075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60536390832676041790101533 22701146562253515671288075)
          ·
            refine ⟨34051719843380273506932113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22701146562253515671288075 34051719843380273506932113)
            ·
              refine ⟨25538789882535205130199085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34051719843380273506932113 25538789882535205130199085)
              ·
                refine ⟨9577046205950701923824657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25538789882535205130199085 9577046205950701923824657)
                ·
                  refine ⟨7182784654463026442868493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9577046205950701923824657 7182784654463026442868493)
                  ·
                    refine ⟨2693544245423634916075685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7182784654463026442868493 2693544245423634916075685)
                    ·
                      refine ⟨505039546016931546764191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2693544245423634916075685 505039546016931546764191)
                      ·
                        rfl

theorem cell23_983561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 2, 3, 4].length) (baseStart_983561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_983561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_983561 prefixEnd_983561 := by exact prefixLift 983561
  have htrace : WordTrace (prefixWord ++ tailWord_983561) baseStart_983561 baseEnd_983561 := by
    simpa [prefixWord, tailWord_983561, baseEnd_983561] using wordTrace_append hprefix tailTrace_983561
  have hstable : (prefixWord ++ tailWord_983561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983561).length < 2 ^ (prefixWord ++ tailWord_983561).sum := by decide
  have hdescent : baseEnd_983561 < baseStart_983561 := by decide
  rcases family_descends (prefixWord ++ tailWord_983561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983571 : List Nat := [1, 1, 1, 2, 1, 5, 1, 3, 2, 6]
def baseStart_983571 : Nat := 118140960795 + 983571 * 2 ^ 59
def prefixEnd_983571 : Nat := 4983230072969 + 3 ^ 40 * 983571 * 2
def baseEnd_983571 : Nat := 168348226941158835879715

theorem tailTrace_983571 : CollatzResearch.WordTrace tailWord_983571 prefixEnd_983571 168348226941158835879715 := by
  unfold tailWord_983571
  simp only [CollatzResearch.WordTrace]
  refine ⟨35873781519697722398294567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23915854346465148265529711 35873781519697722398294567)
  ·
    refine ⟨53810672279546583597441851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35873781519697722398294567 53810672279546583597441851)
    ·
      refine ⟨80716008419319875396162777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53810672279546583597441851 80716008419319875396162777)
      ·
        refine ⟨60537006314489906547122083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80716008419319875396162777 60537006314489906547122083)
        ·
          refine ⟨90805509471734859820683125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60537006314489906547122083 90805509471734859820683125)
          ·
            refine ⟨8513016512975143108189043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90805509471734859820683125 8513016512975143108189043)
            ·
              refine ⟨12769524769462714662283565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8513016512975143108189043 12769524769462714662283565)
              ·
                refine ⟨4788571788548517998356337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12769524769462714662283565 4788571788548517998356337)
                ·
                  refine ⟨3591428841411388498767253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4788571788548517998356337 3591428841411388498767253)
                  ·
                    refine ⟨168348226941158835879715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3591428841411388498767253 168348226941158835879715)
                    ·
                      rfl

theorem cell23_983571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 3, 2, 6].length) (baseStart_983571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_983571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_983571 prefixEnd_983571 := by exact prefixLift 983571
  have htrace : WordTrace (prefixWord ++ tailWord_983571) baseStart_983571 baseEnd_983571 := by
    simpa [prefixWord, tailWord_983571, baseEnd_983571] using wordTrace_append hprefix tailTrace_983571
  have hstable : (prefixWord ++ tailWord_983571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983571).length < 2 ^ (prefixWord ++ tailWord_983571).sum := by decide
  have hdescent : baseEnd_983571 < baseStart_983571 := by decide
  rcases family_descends (prefixWord ++ tailWord_983571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983572 : List Nat := [2, 4, 3, 1, 1, 1, 3, 1, 1, 3, 3]
def baseStart_983572 : Nat := 118140960795 + 983572 * 2 ^ 59
def prefixEnd_983572 : Nat := 4983230072969 + 3 ^ 40 * 983572 * 2
def baseEnd_983572 : Nat := 505045194304131003726641

theorem tailTrace_983572 : CollatzResearch.WordTrace tailWord_983572 prefixEnd_983572 505045194304131003726641 := by
  unfold tailWord_983572
  simp only [CollatzResearch.WordTrace]
  refine ⟨17936908996347049784540485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23915878661796066379387313 17936908996347049784540485)
  ·
    refine ⟨3363170436815071834601341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17936908996347049784540485 3363170436815071834601341)
    ·
      refine ⟨1261188913805651937975503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3363170436815071834601341 1261188913805651937975503)
      ·
        refine ⟨1891783370708477906963255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1261188913805651937975503 1891783370708477906963255)
        ·
          refine ⟨2837675056062716860444883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1891783370708477906963255 2837675056062716860444883)
          ·
            refine ⟨4256512584094075290667325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2837675056062716860444883 4256512584094075290667325)
            ·
              refine ⟨1596192219035278234000247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4256512584094075290667325 1596192219035278234000247)
              ·
                refine ⟨2394288328552917351000371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1596192219035278234000247 2394288328552917351000371)
                ·
                  refine ⟨3591432492829376026500557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2394288328552917351000371 3591432492829376026500557)
                  ·
                    refine ⟨1346787184811016009937709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3591432492829376026500557 1346787184811016009937709)
                    ·
                      refine ⟨505045194304131003726641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1346787184811016009937709 505045194304131003726641)
                      ·
                        rfl

theorem cell23_983572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_983572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_983572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_983572 prefixEnd_983572 := by exact prefixLift 983572
  have htrace : WordTrace (prefixWord ++ tailWord_983572) baseStart_983572 baseEnd_983572 := by
    simpa [prefixWord, tailWord_983572, baseEnd_983572] using wordTrace_append hprefix tailTrace_983572
  have hstable : (prefixWord ++ tailWord_983572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983572).length < 2 ^ (prefixWord ++ tailWord_983572).sum := by decide
  have hdescent : baseEnd_983572 < baseStart_983572 := by decide
  rcases family_descends (prefixWord ++ tailWord_983572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983601 : List Nat := [1, 2, 2, 3, 1, 1, 2, 2, 9]
def baseStart_983601 : Nat := 118140960795 + 983601 * 2 ^ 59
def prefixEnd_983601 : Nat := 4983230072969 + 3 ^ 40 * 983601 * 2
def baseEnd_983601 : Nat := 56117787249234598918223

theorem tailTrace_983601 : CollatzResearch.WordTrace tailWord_983601 prefixEnd_983601 56117787249234598918223 := by
  unfold tailWord_983601
  simp only [CollatzResearch.WordTrace]
  refine ⟨35874875709589037521886657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23916583806392691681257771 35874875709589037521886657)
  ·
    refine ⟨26906156782191778141414993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35874875709589037521886657 26906156782191778141414993)
    ·
      refine ⟨20179617586643833606061245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26906156782191778141414993 20179617586643833606061245)
      ·
        refine ⟨7567356594991437602272967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20179617586643833606061245 7567356594991437602272967)
        ·
          refine ⟨11351034892487156403409451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7567356594991437602272967 11351034892487156403409451)
          ·
            refine ⟨17026552338730734605114177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11351034892487156403409451 17026552338730734605114177)
            ·
              refine ⟨12769914254048050953835633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17026552338730734605114177 12769914254048050953835633)
              ·
                refine ⟨9577435690536038215376725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12769914254048050953835633 9577435690536038215376725)
                ·
                  refine ⟨56117787249234598918223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 9577435690536038215376725 56117787249234598918223)
                  ·
                    rfl

theorem cell23_983601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 9].length) (baseStart_983601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_983601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_983601 prefixEnd_983601 := by exact prefixLift 983601
  have htrace : WordTrace (prefixWord ++ tailWord_983601) baseStart_983601 baseEnd_983601 := by
    simpa [prefixWord, tailWord_983601, baseEnd_983601] using wordTrace_append hprefix tailTrace_983601
  have hstable : (prefixWord ++ tailWord_983601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983601).length < 2 ^ (prefixWord ++ tailWord_983601).sum := by decide
  have hdescent : baseEnd_983601 < baseStart_983601 := by decide
  rcases family_descends (prefixWord ++ tailWord_983601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983612 : List Nat := [2, 2, 2, 2, 3, 1, 2, 1, 4, 2, 2]
def baseStart_983612 : Nat := 118140960795 + 983612 * 2 ^ 59
def prefixEnd_983612 : Nat := 4983230072969 + 3 ^ 40 * 983612 * 2
def baseEnd_983612 : Nat := 505065733530310847226457

theorem tailTrace_983612 : CollatzResearch.WordTrace tailWord_983612 prefixEnd_983612 505065733530310847226457 := by
  unfold tailWord_983612
  simp only [CollatzResearch.WordTrace]
  refine ⟨17937638456274593200268545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23916851275032790933691393 17937638456274593200268545)
  ·
    refine ⟨13453228842205944900201409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17937638456274593200268545 13453228842205944900201409)
    ·
      refine ⟨10089921631654458675151057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13453228842205944900201409 10089921631654458675151057)
      ·
        refine ⟨7567441223740844006363293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10089921631654458675151057 7567441223740844006363293)
        ·
          refine ⟨2837790458902816502386235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7567441223740844006363293 2837790458902816502386235)
          ·
            refine ⟨4256685688354224753579353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2837790458902816502386235 4256685688354224753579353)
            ·
              refine ⟨3192514266265668565184515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4256685688354224753579353 3192514266265668565184515)
              ·
                refine ⟨4788771399398502847776773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3192514266265668565184515 4788771399398502847776773)
                ·
                  refine ⟨897894637387219283958145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4788771399398502847776773 897894637387219283958145)
                  ·
                    refine ⟨673420978040414462968609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 897894637387219283958145 673420978040414462968609)
                    ·
                      refine ⟨505065733530310847226457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 673420978040414462968609 505065733530310847226457)
                      ·
                        rfl

theorem cell23_983612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 1, 4, 2, 2].length) (baseStart_983612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_983612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_983612 prefixEnd_983612 := by exact prefixLift 983612
  have htrace : WordTrace (prefixWord ++ tailWord_983612) baseStart_983612 baseEnd_983612 := by
    simpa [prefixWord, tailWord_983612, baseEnd_983612] using wordTrace_append hprefix tailTrace_983612
  have hstable : (prefixWord ++ tailWord_983612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983612).length < 2 ^ (prefixWord ++ tailWord_983612).sum := by decide
  have hdescent : baseEnd_983612 < baseStart_983612 := by decide
  rcases family_descends (prefixWord ++ tailWord_983612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983628 : List Nat := [2, 2, 1, 3, 1, 2, 2, 1, 1, 5, 3]
def baseStart_983628 : Nat := 118140960795 + 983628 * 2 ^ 59
def prefixEnd_983628 : Nat := 4983230072969 + 3 ^ 40 * 983628 * 2
def baseEnd_983628 : Nat := 505073949220782784626383

theorem tailTrace_983628 : CollatzResearch.WordTrace tailWord_983628 prefixEnd_983628 505073949220782784626383 := by
  unfold tailWord_983628
  simp only [CollatzResearch.WordTrace]
  refine ⟨17937930240245610566559769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23917240320327480755413025 17937930240245610566559769)
  ·
    refine ⟨13453447680184207924919827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17937930240245610566559769 13453447680184207924919827)
    ·
      refine ⟨20180171520276311887379741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13453447680184207924919827 20180171520276311887379741)
      ·
        refine ⟨7567564320103616957767403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20180171520276311887379741 7567564320103616957767403)
        ·
          refine ⟨11351346480155425436651105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7567564320103616957767403 11351346480155425436651105)
          ·
            refine ⟨8513509860116569077488329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11351346480155425436651105 8513509860116569077488329)
            ·
              refine ⟨6385132395087426808116247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8513509860116569077488329 6385132395087426808116247)
              ·
                refine ⟨9577698592631140212174371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6385132395087426808116247 9577698592631140212174371)
                ·
                  refine ⟨14366547888946710318261557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9577698592631140212174371 14366547888946710318261557)
                  ·
                    refine ⟨1346863864588754092337021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14366547888946710318261557 1346863864588754092337021)
                    ·
                      refine ⟨505073949220782784626383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1346863864588754092337021 505073949220782784626383)
                      ·
                        rfl

theorem cell23_983628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 1, 5, 3].length) (baseStart_983628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_983628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_983628 prefixEnd_983628 := by exact prefixLift 983628
  have htrace : WordTrace (prefixWord ++ tailWord_983628) baseStart_983628 baseEnd_983628 := by
    simpa [prefixWord, tailWord_983628, baseEnd_983628] using wordTrace_append hprefix tailTrace_983628
  have hstable : (prefixWord ++ tailWord_983628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983628).length < 2 ^ (prefixWord ++ tailWord_983628).sum := by decide
  have hdescent : baseEnd_983628 < baseStart_983628 := by decide
  rcases family_descends (prefixWord ++ tailWord_983628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983631 : List Nat := [1, 1, 2, 1, 1, 2, 4, 1, 3, 7]
def baseStart_983631 : Nat := 118140960795 + 983631 * 2 ^ 59
def prefixEnd_983631 : Nat := 4983230072969 + 3 ^ 40 * 983631 * 2
def baseEnd_983631 : Nat := 168358496554248757629623

theorem tailTrace_983631 : CollatzResearch.WordTrace tailWord_983631 prefixEnd_983631 168358496554248757629623 := by
  unfold tailWord_983631
  simp only [CollatzResearch.WordTrace]
  refine ⟨35875969899480352645478747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23917313266320235096985831 35875969899480352645478747)
  ·
    refine ⟨53813954849220528968218121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35875969899480352645478747 53813954849220528968218121)
    ·
      refine ⟨40360466136915396726163591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53813954849220528968218121 40360466136915396726163591)
      ·
        refine ⟨60540699205373095089245387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40360466136915396726163591 60540699205373095089245387)
        ·
          refine ⟨90811048808059642633868081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60540699205373095089245387 90811048808059642633868081)
          ·
            refine ⟨68108286606044731975401061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90811048808059642633868081 68108286606044731975401061)
            ·
              refine ⟨12770303738633387245387699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68108286606044731975401061 12770303738633387245387699)
              ·
                refine ⟨19155455607950080868081549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12770303738633387245387699 19155455607950080868081549)
                ·
                  refine ⟨7183295852981280325530581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19155455607950080868081549 7183295852981280325530581)
                  ·
                    refine ⟨168358496554248757629623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7183295852981280325530581 168358496554248757629623)
                    ·
                      rfl

theorem cell23_983631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 3, 7].length) (baseStart_983631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_983631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_983631 prefixEnd_983631 := by exact prefixLift 983631
  have htrace : WordTrace (prefixWord ++ tailWord_983631) baseStart_983631 baseEnd_983631 := by
    simpa [prefixWord, tailWord_983631, baseEnd_983631] using wordTrace_append hprefix tailTrace_983631
  have hstable : (prefixWord ++ tailWord_983631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983631).length < 2 ^ (prefixWord ++ tailWord_983631).sum := by decide
  have hdescent : baseEnd_983631 < baseStart_983631 := by decide
  rcases family_descends (prefixWord ++ tailWord_983631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983648 : List Nat := [2, 1, 1, 3, 2, 1, 3, 3, 2, 5]
def baseStart_983648 : Nat := 118140960795 + 983648 * 2 ^ 59
def prefixEnd_983648 : Nat := 4983230072969 + 3 ^ 40 * 983648 * 2
def baseEnd_983648 : Nat := 168361406277957568792097

theorem tailTrace_983648 : CollatzResearch.WordTrace tailWord_983648 prefixEnd_983648 168361406277957568792097 := by
  unfold tailWord_983648
  simp only [CollatzResearch.WordTrace]
  refine ⟨17938294970209382274423799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23917726626945843032565065 17938294970209382274423799)
  ·
    refine ⟨26907442455314073411635699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17938294970209382274423799 26907442455314073411635699)
    ·
      refine ⟨40361163682971110117453549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26907442455314073411635699 40361163682971110117453549)
      ·
        refine ⟨15135436381114166294045081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40361163682971110117453549 15135436381114166294045081)
        ·
          refine ⟨11351577285835624720533811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15135436381114166294045081 11351577285835624720533811)
          ·
            refine ⟨17027365928753437080800717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11351577285835624720533811 17027365928753437080800717)
            ·
              refine ⟨6385262223282538905300269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17027365928753437080800717 6385262223282538905300269)
              ·
                refine ⟨2394473333730952089487601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6385262223282538905300269 2394473333730952089487601)
                ·
                  refine ⟨1795855000298214067115701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2394473333730952089487601 1795855000298214067115701)
                  ·
                    refine ⟨168361406277957568792097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1795855000298214067115701 168361406277957568792097)
                    ·
                      rfl

theorem cell23_983648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 3, 2, 5].length) (baseStart_983648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_983648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_983648 prefixEnd_983648 := by exact prefixLift 983648
  have htrace : WordTrace (prefixWord ++ tailWord_983648) baseStart_983648 baseEnd_983648 := by
    simpa [prefixWord, tailWord_983648, baseEnd_983648] using wordTrace_append hprefix tailTrace_983648
  have hstable : (prefixWord ++ tailWord_983648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983648).length < 2 ^ (prefixWord ++ tailWord_983648).sum := by decide
  have hdescent : baseEnd_983648 < baseStart_983648 := by decide
  rcases family_descends (prefixWord ++ tailWord_983648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983658 : List Nat := [3, 1, 3, 2, 1, 1, 1, 1, 3, 2, 5]
def baseStart_983658 : Nat := 118140960795 + 983658 * 2 ^ 59
def prefixEnd_983658 : Nat := 4983230072969 + 3 ^ 40 * 983658 * 2
def baseEnd_983658 : Nat := 505089353640417667251245

theorem tailTrace_983658 : CollatzResearch.WordTrace tailWord_983658 prefixEnd_983658 505089353640417667251245 := by
  unfold tailWord_983658
  simp only [CollatzResearch.WordTrace]
  refine ⟨8969238667595634064177907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23917969780255024171141085 8969238667595634064177907)
  ·
    refine ⟨13453858001393451096266861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8969238667595634064177907 13453858001393451096266861)
    ·
      refine ⟨5045196750522544161100073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13453858001393451096266861 5045196750522544161100073)
      ·
        refine ⟨3783897562891908120825055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5045196750522544161100073 3783897562891908120825055)
        ·
          refine ⟨5675846344337862181237583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3783897562891908120825055 5675846344337862181237583)
          ·
            refine ⟨8513769516506793271856375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5675846344337862181237583 8513769516506793271856375)
            ·
              refine ⟨12770654274760189907784563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8513769516506793271856375 12770654274760189907784563)
              ·
                refine ⟨19155981412140284861676845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12770654274760189907784563 19155981412140284861676845)
                ·
                  refine ⟨7183493029552606823128817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19155981412140284861676845 7183493029552606823128817)
                  ·
                    refine ⟨5387619772164455117346613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7183493029552606823128817 5387619772164455117346613)
                    ·
                      refine ⟨505089353640417667251245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5387619772164455117346613 505089353640417667251245)
                      ·
                        rfl

theorem cell23_983658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_983658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_983658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_983658 prefixEnd_983658 := by exact prefixLift 983658
  have htrace : WordTrace (prefixWord ++ tailWord_983658) baseStart_983658 baseEnd_983658 := by
    simpa [prefixWord, tailWord_983658, baseEnd_983658] using wordTrace_append hprefix tailTrace_983658
  have hstable : (prefixWord ++ tailWord_983658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983658).length < 2 ^ (prefixWord ++ tailWord_983658).sum := by decide
  have hdescent : baseEnd_983658 < baseStart_983658 := by decide
  rcases family_descends (prefixWord ++ tailWord_983658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983685 : List Nat := [1, 3, 1, 1, 4, 2, 1, 1, 1, 6, 2]
def baseStart_983685 : Nat := 118140960795 + 983685 * 2 ^ 59
def prefixEnd_983685 : Nat := 4983230072969 + 3 ^ 40 * 983685 * 2
def baseEnd_983685 : Nat := 505103217618089061613621

theorem tailTrace_983685 : CollatzResearch.WordTrace tailWord_983685 prefixEnd_983685 505103217618089061613621 := by
  unfold tailWord_983685
  simp only [CollatzResearch.WordTrace]
  refine ⟨35877939441284719867944509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23918626294189813245296339 35877939441284719867944509)
  ·
    refine ⟨13454227290481769950479191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35877939441284719867944509 13454227290481769950479191)
    ·
      refine ⟨20181340935722654925718787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13454227290481769950479191 20181340935722654925718787)
      ·
        refine ⟨30272011403583982388578181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20181340935722654925718787 30272011403583982388578181)
        ·
          refine ⟨5676002138171996697858409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30272011403583982388578181 5676002138171996697858409)
          ·
            refine ⟨4257001603628997523393807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5676002138171996697858409 4257001603628997523393807)
            ·
              refine ⟨6385502405443496285090711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4257001603628997523393807 6385502405443496285090711)
              ·
                refine ⟨9578253608165244427636067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6385502405443496285090711 9578253608165244427636067)
                ·
                  refine ⟨14367380412247866641454101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9578253608165244427636067 14367380412247866641454101)
                  ·
                    refine ⟨673470956824118748818161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14367380412247866641454101 673470956824118748818161)
                    ·
                      refine ⟨505103217618089061613621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 673470956824118748818161 505103217618089061613621)
                      ·
                        rfl

theorem cell23_983685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 6, 2].length) (baseStart_983685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_983685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_983685 prefixEnd_983685 := by exact prefixLift 983685
  have htrace : WordTrace (prefixWord ++ tailWord_983685) baseStart_983685 baseEnd_983685 := by
    simpa [prefixWord, tailWord_983685, baseEnd_983685] using wordTrace_append hprefix tailTrace_983685
  have hstable : (prefixWord ++ tailWord_983685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983685).length < 2 ^ (prefixWord ++ tailWord_983685).sum := by decide
  have hdescent : baseEnd_983685 < baseStart_983685 := by decide
  rcases family_descends (prefixWord ++ tailWord_983685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983725 : List Nat := [1, 5, 2, 1, 1, 3, 1, 1, 8]
def baseStart_983725 : Nat := 118140960795 + 983725 * 2 ^ 59
def prefixEnd_983725 : Nat := 4983230072969 + 3 ^ 40 * 983725 * 2
def baseEnd_983725 : Nat := 56124861871585433901493

theorem tailTrace_983725 : CollatzResearch.WordTrace tailWord_983725 prefixEnd_983725 56124861871585433901493 := by
  unfold tailWord_983725
  simp only [CollatzResearch.WordTrace]
  refine ⟨35879398361139806699400629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23919598907426537799600419 35879398361139806699400629)
  ·
    refine ⟨3363693596356856878068809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35879398361139806699400629 3363693596356856878068809)
    ·
      refine ⟨2522770197267642658551607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3363693596356856878068809 2522770197267642658551607)
      ·
        refine ⟨3784155295901463987827411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2522770197267642658551607 3784155295901463987827411)
        ·
          refine ⟨5676232943852195981741117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3784155295901463987827411 5676232943852195981741117)
          ·
            refine ⟨2128587353944573493152919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5676232943852195981741117 2128587353944573493152919)
            ·
              refine ⟨3192881030916860239729379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2128587353944573493152919 3192881030916860239729379)
              ·
                refine ⟨4789321546375290359594069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3192881030916860239729379 4789321546375290359594069)
                ·
                  refine ⟨56124861871585433901493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4789321546375290359594069 56124861871585433901493)
                  ·
                    rfl

theorem cell23_983725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 1, 8].length) (baseStart_983725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_983725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_983725 prefixEnd_983725 := by exact prefixLift 983725
  have htrace : WordTrace (prefixWord ++ tailWord_983725) baseStart_983725 baseEnd_983725 := by
    simpa [prefixWord, tailWord_983725, baseEnd_983725] using wordTrace_append hprefix tailTrace_983725
  have hstable : (prefixWord ++ tailWord_983725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983725).length < 2 ^ (prefixWord ++ tailWord_983725).sum := by decide
  have hdescent : baseEnd_983725 < baseStart_983725 := by decide
  rcases family_descends (prefixWord ++ tailWord_983725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983729 : List Nat := [1, 2, 2, 6, 1, 1, 2, 1, 3, 4]
def baseStart_983729 : Nat := 118140960795 + 983729 * 2 ^ 59
def prefixEnd_983729 : Nat := 4983230072969 + 3 ^ 40 * 983729 * 2
def baseEnd_983729 : Nat := 168375270255628963154473

theorem tailTrace_983729 : CollatzResearch.WordTrace tailWord_983729 prefixEnd_983729 168375270255628963154473 := by
  unfold tailWord_983729
  simp only [CollatzResearch.WordTrace]
  refine ⟨35879544253125315382546241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23919696168750210255030827 35879544253125315382546241)
  ·
    refine ⟨26909658189843986536909681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35879544253125315382546241 26909658189843986536909681)
    ·
      refine ⟨20182243642382989902682261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26909658189843986536909681 20182243642382989902682261)
      ·
        refine ⟨946042670736702651688231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 20182243642382989902682261 946042670736702651688231)
        ·
          refine ⟨1419064006105053977532347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 946042670736702651688231 1419064006105053977532347)
          ·
            refine ⟨2128596009157580966298521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1419064006105053977532347 2128596009157580966298521)
            ·
              refine ⟨1596447006868185724723891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2128596009157580966298521 1596447006868185724723891)
              ·
                refine ⟨2394670510302278587085837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1596447006868185724723891 2394670510302278587085837)
                ·
                  refine ⟨898001441363354470157189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2394670510302278587085837 898001441363354470157189)
                  ·
                    refine ⟨168375270255628963154473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 898001441363354470157189 168375270255628963154473)
                    ·
                      rfl

theorem cell23_983729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 1, 3, 4].length) (baseStart_983729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_983729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_983729 prefixEnd_983729 := by exact prefixLift 983729
  have htrace : WordTrace (prefixWord ++ tailWord_983729) baseStart_983729 baseEnd_983729 := by
    simpa [prefixWord, tailWord_983729, baseEnd_983729] using wordTrace_append hprefix tailTrace_983729
  have hstable : (prefixWord ++ tailWord_983729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983729).length < 2 ^ (prefixWord ++ tailWord_983729).sum := by decide
  have hdescent : baseEnd_983729 < baseStart_983729 := by decide
  rcases family_descends (prefixWord ++ tailWord_983729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983742 : List Nat := [4, 2, 1, 1, 2, 1, 5, 1, 6]
def baseStart_983742 : Nat := 118140960795 + 983742 * 2 ^ 59
def prefixEnd_983742 : Nat := 4983230072969 + 3 ^ 40 * 983742 * 2
def baseEnd_983742 : Nat := 56125831779488370955651

theorem tailTrace_983742 : CollatzResearch.WordTrace tailWord_983742 prefixEnd_983742 56125831779488370955651 := by
  unfold tailWord_983742
  simp only [CollatzResearch.WordTrace]
  refine ⟨4485002300259777325346185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23920012268052145735179653 4485002300259777325346185)
  ·
    refine ⟨3363751725194832994009639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4485002300259777325346185 3363751725194832994009639)
    ·
      refine ⟨5045627587792249491014459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3363751725194832994009639 5045627587792249491014459)
      ·
        refine ⟨7568441381688374236521689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5045627587792249491014459 7568441381688374236521689)
        ·
          refine ⟨5676331036266280677391267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7568441381688374236521689 5676331036266280677391267)
          ·
            refine ⟨8514496554399421016086901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5676331036266280677391267 8514496554399421016086901)
            ·
              refine ⟨798234051974945720258147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8514496554399421016086901 798234051974945720258147)
              ·
                refine ⟨1197351077962418580387221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 798234051974945720258147 1197351077962418580387221)
                ·
                  refine ⟨56125831779488370955651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1197351077962418580387221 56125831779488370955651)
                  ·
                    rfl

theorem cell23_983742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 5, 1, 6].length) (baseStart_983742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_983742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_983742 prefixEnd_983742 := by exact prefixLift 983742
  have htrace : WordTrace (prefixWord ++ tailWord_983742) baseStart_983742 baseEnd_983742 := by
    simpa [prefixWord, tailWord_983742, baseEnd_983742] using wordTrace_append hprefix tailTrace_983742
  have hstable : (prefixWord ++ tailWord_983742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983742).length < 2 ^ (prefixWord ++ tailWord_983742).sum := by decide
  have hdescent : baseEnd_983742 < baseStart_983742 := by decide
  rcases family_descends (prefixWord ++ tailWord_983742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983752 : List Nat := [2, 1, 3, 1, 2, 3, 2, 2, 3, 1, 3]
def baseStart_983752 : Nat := 118140960795 + 983752 * 2 ^ 59
def prefixEnd_983752 : Nat := 4983230072969 + 3 ^ 40 * 983752 * 2
def baseEnd_983752 : Nat := 505137620821940299475813

theorem tailTrace_983752 : CollatzResearch.WordTrace tailWord_983752 prefixEnd_983752 505137620821940299475813 := by
  unfold tailWord_983752
  simp only [CollatzResearch.WordTrace]
  refine ⟨17940191566020995155316755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23920255421361326873755673 17940191566020995155316755)
  ·
    refine ⟨26910287349031492732975133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17940191566020995155316755 26910287349031492732975133)
    ·
      refine ⟨10091357755886809774865675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26910287349031492732975133 10091357755886809774865675)
      ·
        refine ⟨15137036633830214662298513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10091357755886809774865675 15137036633830214662298513)
        ·
          refine ⟨11352777475372660996723885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15137036633830214662298513 11352777475372660996723885)
          ·
            refine ⟨4257291553264747873771457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11352777475372660996723885 4257291553264747873771457)
            ·
              refine ⟨3192968664948560905328593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4257291553264747873771457 3192968664948560905328593)
              ·
                refine ⟨2394726498711420678996445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3192968664948560905328593 2394726498711420678996445)
                ·
                  refine ⟨898022437016782754623667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2394726498711420678996445 898022437016782754623667)
                  ·
                    refine ⟨1347033655525174131935501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 898022437016782754623667 1347033655525174131935501)
                    ·
                      refine ⟨505137620821940299475813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1347033655525174131935501 505137620821940299475813)
                      ·
                        rfl

theorem cell23_983752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 2, 3, 1, 3].length) (baseStart_983752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_983752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_983752 prefixEnd_983752 := by exact prefixLift 983752
  have htrace : WordTrace (prefixWord ++ tailWord_983752) baseStart_983752 baseEnd_983752 := by
    simpa [prefixWord, tailWord_983752, baseEnd_983752] using wordTrace_append hprefix tailTrace_983752
  have hstable : (prefixWord ++ tailWord_983752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983752).length < 2 ^ (prefixWord ++ tailWord_983752).sum := by decide
  have hdescent : baseEnd_983752 < baseStart_983752 := by decide
  rcases family_descends (prefixWord ++ tailWord_983752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983779 : List Nat := [1, 1, 1, 7, 1, 2, 1, 2, 2, 3, 2]
def baseStart_983779 : Nat := 118140960795 + 983779 * 2 ^ 59
def prefixEnd_983779 : Nat := 4983230072969 + 3 ^ 40 * 983779 * 2
def baseEnd_983779 : Nat := 505151484799611693838189

theorem tailTrace_983779 : CollatzResearch.WordTrace tailWord_983779 prefixEnd_983779 505151484799611693838189 := by
  unfold tailWord_983779
  simp only [CollatzResearch.WordTrace]
  refine ⟨35881367902944173921866391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23920911935296115947910927 35881367902944173921866391)
  ·
    refine ⟨53822051854416260882799587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35881367902944173921866391 53822051854416260882799587)
    ·
      refine ⟨80733077781624391324199381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53822051854416260882799587 80733077781624391324199381)
      ·
        refine ⟨1892181510506821671660923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 80733077781624391324199381 1892181510506821671660923)
        ·
          refine ⟨2838272265760232507491385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1892181510506821671660923 2838272265760232507491385)
          ·
            refine ⟨2128704199320174380618539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2838272265760232507491385 2128704199320174380618539)
            ·
              refine ⟨3193056298980261570927809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2128704199320174380618539 3193056298980261570927809)
              ·
                refine ⟨2394792224235196178195857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3193056298980261570927809 2394792224235196178195857)
                ·
                  refine ⟨1796094168176397133646893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2394792224235196178195857 1796094168176397133646893)
                  ·
                    refine ⟨673535313066148925117585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1796094168176397133646893 673535313066148925117585)
                    ·
                      refine ⟨505151484799611693838189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 673535313066148925117585 505151484799611693838189)
                      ·
                        rfl

theorem cell23_983779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_983779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_983779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_983779 prefixEnd_983779 := by exact prefixLift 983779
  have htrace : WordTrace (prefixWord ++ tailWord_983779) baseStart_983779 baseEnd_983779 := by
    simpa [prefixWord, tailWord_983779, baseEnd_983779] using wordTrace_append hprefix tailTrace_983779
  have hstable : (prefixWord ++ tailWord_983779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983779).length < 2 ^ (prefixWord ++ tailWord_983779).sum := by decide
  have hdescent : baseEnd_983779 < baseStart_983779 := by decide
  rcases family_descends (prefixWord ++ tailWord_983779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983785 : List Nat := [1, 2, 1, 1, 1, 2, 6, 1, 4, 4]
def baseStart_983785 : Nat := 118140960795 + 983785 * 2 ^ 59
def prefixEnd_983785 : Nat := 4983230072969 + 3 ^ 40 * 983785 * 2
def baseEnd_983785 : Nat := 168384855227846223454387

theorem tailTrace_983785 : CollatzResearch.WordTrace tailWord_983785 prefixEnd_983785 168384855227846223454387 := by
  unfold tailWord_983785
  simp only [CollatzResearch.WordTrace]
  refine ⟨35881586740922436946584809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23921057827281624631056539 35881586740922436946584809)
  ·
    refine ⟨26911190055691827709938607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35881586740922436946584809 26911190055691827709938607)
    ·
      refine ⟨40366785083537741564907911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26911190055691827709938607 40366785083537741564907911)
      ·
        refine ⟨60550177625306612347361867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40366785083537741564907911 60550177625306612347361867)
        ·
          refine ⟨90825266437959918521042801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60550177625306612347361867 90825266437959918521042801)
          ·
            refine ⟨68118949828469938890782101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90825266437959918521042801 68118949828469938890782101)
            ·
              refine ⟨3193075773209528385505411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 68118949828469938890782101 3193075773209528385505411)
              ·
                refine ⟨4789613659814292578258117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3193075773209528385505411 4789613659814292578258117)
                ·
                  refine ⟨898052561215179858423397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4789613659814292578258117 898052561215179858423397)
                  ·
                    refine ⟨168384855227846223454387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 898052561215179858423397 168384855227846223454387)
                    ·
                      rfl

theorem cell23_983785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 1, 4, 4].length) (baseStart_983785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_983785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_983785 prefixEnd_983785 := by exact prefixLift 983785
  have htrace : WordTrace (prefixWord ++ tailWord_983785) baseStart_983785 baseEnd_983785 := by
    simpa [prefixWord, tailWord_983785, baseEnd_983785] using wordTrace_append hprefix tailTrace_983785
  have hstable : (prefixWord ++ tailWord_983785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983785).length < 2 ^ (prefixWord ++ tailWord_983785).sum := by decide
  have hdescent : baseEnd_983785 < baseStart_983785 := by decide
  rcases family_descends (prefixWord ++ tailWord_983785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983795 : List Nat := [1, 1, 1, 2, 2, 3, 1, 4, 3, 2, 3]
def baseStart_983795 : Nat := 118140960795 + 983795 * 2 ^ 59
def prefixEnd_983795 : Nat := 4983230072969 + 3 ^ 40 * 983795 * 2
def baseEnd_983795 : Nat := 505159700490083631238115

theorem tailTrace_983795 : CollatzResearch.WordTrace tailWord_983795 prefixEnd_983795 505159700490083631238115 := by
  unfold tailWord_983795
  simp only [CollatzResearch.WordTrace]
  refine ⟨35881951470886208654448839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23921300980590805769632559 35881951470886208654448839)
  ·
    refine ⟨53822927206329312981673259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35881951470886208654448839 53822927206329312981673259)
    ·
      refine ⟨80734390809493969472509889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53822927206329312981673259 80734390809493969472509889)
      ·
        refine ⟨60550793107120477104382417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80734390809493969472509889 60550793107120477104382417)
        ·
          refine ⟨45413094830340357828286813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60550793107120477104382417 45413094830340357828286813)
          ·
            refine ⟨17029910561377634185607555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45413094830340357828286813 17029910561377634185607555)
            ·
              refine ⟨25544865842066451278411333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17029910561377634185607555 25544865842066451278411333)
              ·
                refine ⟨4789662345387459614702125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25544865842066451278411333 4789662345387459614702125)
                ·
                  refine ⟨1796123379520297355513297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4789662345387459614702125 1796123379520297355513297)
                  ·
                    refine ⟨1347092534640223016634973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1796123379520297355513297 1347092534640223016634973)
                    ·
                      refine ⟨505159700490083631238115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1347092534640223016634973 505159700490083631238115)
                      ·
                        rfl

theorem cell23_983795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 4, 3, 2, 3].length) (baseStart_983795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_983795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_983795 prefixEnd_983795 := by exact prefixLift 983795
  have htrace : WordTrace (prefixWord ++ tailWord_983795) baseStart_983795 baseEnd_983795 := by
    simpa [prefixWord, tailWord_983795, baseEnd_983795] using wordTrace_append hprefix tailTrace_983795
  have hstable : (prefixWord ++ tailWord_983795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983795).length < 2 ^ (prefixWord ++ tailWord_983795).sum := by decide
  have hdescent : baseEnd_983795 < baseStart_983795 := by decide
  rcases family_descends (prefixWord ++ tailWord_983795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983805 : List Nat := [1, 4, 1, 1, 1, 1, 4, 3, 1, 2, 4]
def baseStart_983805 : Nat := 118140960795 + 983805 * 2 ^ 59
def prefixEnd_983805 : Nat := 4983230072969 + 3 ^ 40 * 983805 * 2
def baseEnd_983805 : Nat := 505164835296628592113069

theorem tailTrace_983805 : CollatzResearch.WordTrace tailWord_983805 prefixEnd_983805 505164835296628592113069 := by
  unfold tailWord_983805
  simp only [CollatzResearch.WordTrace]
  refine ⟨35882316200849980362312869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23921544133899986908208579 35882316200849980362312869)
  ·
    refine ⟨6727934287659371317933663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35882316200849980362312869 6727934287659371317933663)
    ·
      refine ⟨10091901431489056976900495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6727934287659371317933663 10091901431489056976900495)
      ·
        refine ⟨15137852147233585465350743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10091901431489056976900495 15137852147233585465350743)
        ·
          refine ⟨22706778220850378198026115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15137852147233585465350743 22706778220850378198026115)
          ·
            refine ⟨34060167331275567297039173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22706778220850378198026115 34060167331275567297039173)
            ·
              refine ⟨6386281374614168868194845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34060167331275567297039173 6386281374614168868194845)
              ·
                refine ⟨2394855515480313325573067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6386281374614168868194845 2394855515480313325573067)
                ·
                  refine ⟨3592283273220469988359601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2394855515480313325573067 3592283273220469988359601)
                  ·
                    refine ⟨2694212454915352491269701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3592283273220469988359601 2694212454915352491269701)
                    ·
                      refine ⟨505164835296628592113069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2694212454915352491269701 505164835296628592113069)
                      ·
                        rfl

theorem cell23_983805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 3, 1, 2, 4].length) (baseStart_983805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_983805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_983805 prefixEnd_983805 := by exact prefixLift 983805
  have htrace : WordTrace (prefixWord ++ tailWord_983805) baseStart_983805 baseEnd_983805 := by
    simpa [prefixWord, tailWord_983805, baseEnd_983805] using wordTrace_append hprefix tailTrace_983805
  have hstable : (prefixWord ++ tailWord_983805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983805).length < 2 ^ (prefixWord ++ tailWord_983805).sum := by decide
  have hdescent : baseEnd_983805 < baseStart_983805 := by decide
  rcases family_descends (prefixWord ++ tailWord_983805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983812 : List Nat := [2, 3, 2, 2, 1, 1, 3, 1, 3, 2, 3]
def baseStart_983812 : Nat := 118140960795 + 983812 * 2 ^ 59
def prefixEnd_983812 : Nat := 4983230072969 + 3 ^ 40 * 983812 * 2
def baseEnd_983812 : Nat := 505168429661210064725537

theorem tailTrace_983812 : CollatzResearch.WordTrace tailWord_983812 prefixEnd_983812 505168429661210064725537 := by
  unfold tailWord_983812
  simp only [CollatzResearch.WordTrace]
  refine ⟨17941285755912310278908845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23921714341216413705211793 17941285755912310278908845)
  ·
    refine ⟨6727982158467116354590817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17941285755912310278908845 6727982158467116354590817)
    ·
      refine ⟨5045986618850337265943113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6727982158467116354590817 5045986618850337265943113)
      ·
        refine ⟨3784489964137752949457335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5045986618850337265943113 3784489964137752949457335)
        ·
          refine ⟨5676734946206629424186003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3784489964137752949457335 5676734946206629424186003)
          ·
            refine ⟨8515102419309944136279005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5676734946206629424186003 8515102419309944136279005)
            ·
              refine ⟨3193163407241229051104627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8515102419309944136279005 3193163407241229051104627)
              ·
                refine ⟨4789745110861843576656941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3193163407241229051104627 4789745110861843576656941)
                ·
                  refine ⟨1796154416573191341246353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4789745110861843576656941 1796154416573191341246353)
                  ·
                    refine ⟨1347115812429893505934765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1796154416573191341246353 1347115812429893505934765)
                    ·
                      refine ⟨505168429661210064725537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1347115812429893505934765 505168429661210064725537)
                      ·
                        rfl

theorem cell23_983812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_983812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_983812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_983812 prefixEnd_983812 := by exact prefixLift 983812
  have htrace : WordTrace (prefixWord ++ tailWord_983812) baseStart_983812 baseEnd_983812 := by
    simpa [prefixWord, tailWord_983812, baseEnd_983812] using wordTrace_append hprefix tailTrace_983812
  have hstable : (prefixWord ++ tailWord_983812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983812).length < 2 ^ (prefixWord ++ tailWord_983812).sum := by decide
  have hdescent : baseEnd_983812 < baseStart_983812 := by decide
  rcases family_descends (prefixWord ++ tailWord_983812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983815 : List Nat := [1, 1, 4, 4, 1, 1, 2, 9]
def baseStart_983815 : Nat := 118140960795 + 983815 * 2 ^ 59
def prefixEnd_983815 : Nat := 4983230072969 + 3 ^ 40 * 983815 * 2
def baseEnd_983815 : Nat := 18709998892710131592149

theorem tailTrace_983815 : CollatzResearch.WordTrace tailWord_983815 prefixEnd_983815 18709998892710131592149 := by
  unfold tailWord_983815
  simp only [CollatzResearch.WordTrace]
  refine ⟨35882680930813752070176899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23921787287209168046784599 35882680930813752070176899)
  ·
    refine ⟨53824021396220628105265349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35882680930813752070176899 53824021396220628105265349)
    ·
      refine ⟨10092004011791367769737253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53824021396220628105265349 10092004011791367769737253)
      ·
        refine ⟨1892250752210881456825735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10092004011791367769737253 1892250752210881456825735)
        ·
          refine ⟨2838376128316322185238603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1892250752210881456825735 2838376128316322185238603)
          ·
            refine ⟨4257564192474483277857905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2838376128316322185238603 4257564192474483277857905)
            ·
              refine ⟨3193173144355862458393429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4257564192474483277857905 3193173144355862458393429)
              ·
                refine ⟨18709998892710131592149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3193173144355862458393429 18709998892710131592149)
                ·
                  rfl

theorem cell23_983815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 9].length) (baseStart_983815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_983815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_983815 prefixEnd_983815 := by exact prefixLift 983815
  have htrace : WordTrace (prefixWord ++ tailWord_983815) baseStart_983815 baseEnd_983815 := by
    simpa [prefixWord, tailWord_983815, baseEnd_983815] using wordTrace_append hprefix tailTrace_983815
  have hstable : (prefixWord ++ tailWord_983815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983815).length < 2 ^ (prefixWord ++ tailWord_983815).sum := by decide
  have hdescent : baseEnd_983815 < baseStart_983815 := by decide
  rcases family_descends (prefixWord ++ tailWord_983815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983825 : List Nat := [1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 3]
def baseStart_983825 : Nat := 118140960795 + 983825 * 2 ^ 59
def prefixEnd_983825 : Nat := 4983230072969 + 3 ^ 40 * 983825 * 2
def baseEnd_983825 : Nat := 505175104909718513862977

theorem tailTrace_983825 : CollatzResearch.WordTrace tailWord_983825 prefixEnd_983825 505175104909718513862977 := by
  unfold tailWord_983825
  simp only [CollatzResearch.WordTrace]
  refine ⟨35883045660777523778040929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23922030440518349185360619 35883045660777523778040929)
  ·
    refine ⟨26912284245583142833530697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35883045660777523778040929 26912284245583142833530697)
    ·
      refine ⟨20184213184187357125148023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26912284245583142833530697 20184213184187357125148023)
      ·
        refine ⟨30276319776281035687722035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20184213184187357125148023 30276319776281035687722035)
        ·
          refine ⟨45414479664421553531583053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30276319776281035687722035 45414479664421553531583053)
          ·
            refine ⟨17030429874158082574343645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45414479664421553531583053 17030429874158082574343645)
            ·
              refine ⟨6386411202809280965378867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17030429874158082574343645 6386411202809280965378867)
              ·
                refine ⟨9579616804213921448068301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6386411202809280965378867 9579616804213921448068301)
                ·
                  refine ⟨3592356301580220543025613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9579616804213921448068301 3592356301580220543025613)
                  ·
                    refine ⟨1347133613092582703634605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3592356301580220543025613 1347133613092582703634605)
                    ·
                      refine ⟨505175104909718513862977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1347133613092582703634605 505175104909718513862977)
                      ·
                        rfl

theorem cell23_983825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 3].length) (baseStart_983825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_983825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_983825 prefixEnd_983825 := by exact prefixLift 983825
  have htrace : WordTrace (prefixWord ++ tailWord_983825) baseStart_983825 baseEnd_983825 := by
    simpa [prefixWord, tailWord_983825, baseEnd_983825] using wordTrace_append hprefix tailTrace_983825
  have hstable : (prefixWord ++ tailWord_983825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983825).length < 2 ^ (prefixWord ++ tailWord_983825).sum := by decide
  have hdescent : baseEnd_983825 < baseStart_983825 := by decide
  rcases family_descends (prefixWord ++ tailWord_983825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983829 : List Nat := [1, 3, 2, 1, 2, 2, 5, 1, 1, 2, 3]
def baseStart_983829 : Nat := 118140960795 + 983829 * 2 ^ 59
def prefixEnd_983829 : Nat := 4983230072969 + 3 ^ 40 * 983829 * 2
def baseEnd_983829 : Nat := 505177158832336498212959

theorem tailTrace_983829 : CollatzResearch.WordTrace tailWord_983829 prefixEnd_983829 505177158832336498212959 := by
  unfold tailWord_983829
  simp only [CollatzResearch.WordTrace]
  refine ⟨35883191552763032461186541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23922127701842021640791027 35883191552763032461186541)
  ·
    refine ⟨13456196832286137172944953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35883191552763032461186541 13456196832286137172944953)
    ·
      refine ⟨10092147624214602879708715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13456196832286137172944953 10092147624214602879708715)
      ·
        refine ⟨15138221436321904319563073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10092147624214602879708715 15138221436321904319563073)
        ·
          refine ⟨11353666077241428239672305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15138221436321904319563073 11353666077241428239672305)
          ·
            refine ⟨8515249557931071179754229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11353666077241428239672305 8515249557931071179754229)
            ·
              refine ⟨798304646056037923101959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8515249557931071179754229 798304646056037923101959)
              ·
                refine ⟨1197456969084056884652939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 798304646056037923101959 1197456969084056884652939)
                ·
                  refine ⟨1796185453626085326979409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1197456969084056884652939 1796185453626085326979409)
                  ·
                    refine ⟨1347139090219563995234557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1796185453626085326979409 1347139090219563995234557)
                    ·
                      refine ⟨505177158832336498212959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1347139090219563995234557 505177158832336498212959)
                      ·
                        rfl

theorem cell23_983829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 5, 1, 1, 2, 3].length) (baseStart_983829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_983829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_983829 prefixEnd_983829 := by exact prefixLift 983829
  have htrace : WordTrace (prefixWord ++ tailWord_983829) baseStart_983829 baseEnd_983829 := by
    simpa [prefixWord, tailWord_983829, baseEnd_983829] using wordTrace_append hprefix tailTrace_983829
  have hstable : (prefixWord ++ tailWord_983829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983829).length < 2 ^ (prefixWord ++ tailWord_983829).sum := by decide
  have hdescent : baseEnd_983829 < baseStart_983829 := by decide
  rcases family_descends (prefixWord ++ tailWord_983829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983837 : List Nat := [1, 4, 2, 4, 2, 1, 2, 2, 1, 1, 3]
def baseStart_983837 : Nat := 118140960795 + 983837 * 2 ^ 59
def prefixEnd_983837 : Nat := 4983230072969 + 3 ^ 40 * 983837 * 2
def baseEnd_983837 : Nat := 505181266677572466912923

theorem tailTrace_983837 : CollatzResearch.WordTrace tailWord_983837 prefixEnd_983837 505181266677572466912923 := by
  unfold tailWord_983837
  simp only [CollatzResearch.WordTrace]
  refine ⟨35883483336734049827477765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23922322224489366551651843 35883483336734049827477765)
  ·
    refine ⟨6728153125637634342652081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35883483336734049827477765 6728153125637634342652081)
    ·
      refine ⟨5046114844228225756989061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6728153125637634342652081 5046114844228225756989061)
      ·
        refine ⟨946146533292792329435449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5046114844228225756989061 946146533292792329435449)
        ·
          refine ⟨709609899969594247076587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 946146533292792329435449 709609899969594247076587)
          ·
            refine ⟨1064414849954391370614881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 709609899969594247076587 1064414849954391370614881)
            ·
              refine ⟨798311137465793527961161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1064414849954391370614881 798311137465793527961161)
              ·
                refine ⟨598733353099345145970871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 798311137465793527961161 598733353099345145970871)
                ·
                  refine ⟨898100029649017718956307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 598733353099345145970871 898100029649017718956307)
                  ·
                    refine ⟨1347150044473526578434461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 898100029649017718956307 1347150044473526578434461)
                    ·
                      refine ⟨505181266677572466912923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1347150044473526578434461 505181266677572466912923)
                      ·
                        rfl

theorem cell23_983837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_983837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_983837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_983837 prefixEnd_983837 := by exact prefixLift 983837
  have htrace : WordTrace (prefixWord ++ tailWord_983837) baseStart_983837 baseEnd_983837 := by
    simpa [prefixWord, tailWord_983837, baseEnd_983837] using wordTrace_append hprefix tailTrace_983837
  have hstable : (prefixWord ++ tailWord_983837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983837).length < 2 ^ (prefixWord ++ tailWord_983837).sum := by decide
  have hdescent : baseEnd_983837 < baseStart_983837 := by decide
  rcases family_descends (prefixWord ++ tailWord_983837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983852 : List Nat := [2, 2, 1, 1, 1, 4, 1, 1, 5, 3, 2]
def baseStart_983852 : Nat := 118140960795 + 983852 * 2 ^ 59
def prefixEnd_983852 : Nat := 4983230072969 + 3 ^ 40 * 983852 * 2
def baseEnd_983852 : Nat := 505188968887389908225353

theorem tailTrace_983852 : CollatzResearch.WordTrace tailWord_983852 prefixEnd_983852 505188968887389908225353 := by
  unfold tailWord_983852
  simp only [CollatzResearch.WordTrace]
  refine ⟨17942015215839853694636905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23922686954453138259515873 17942015215839853694636905)
  ·
    refine ⟨13456511411879890270977679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17942015215839853694636905 13456511411879890270977679)
    ·
      refine ⟨20184767117819835406466519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13456511411879890270977679 20184767117819835406466519)
      ·
        refine ⟨30277150676729753109699779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20184767117819835406466519 30277150676729753109699779)
        ·
          refine ⟨45415726015094629664549669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30277150676729753109699779 45415726015094629664549669)
          ·
            refine ⟨8515448627830243062103063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45415726015094629664549669 8515448627830243062103063)
            ·
              refine ⟨12773172941745364593154595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8515448627830243062103063 12773172941745364593154595)
              ·
                refine ⟨19159759412618046889731893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12773172941745364593154595 19159759412618046889731893)
                ·
                  refine ⟨1796227444932941895912365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19159759412618046889731893 1796227444932941895912365)
                  ·
                    refine ⟨673585291849853210967137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1796227444932941895912365 673585291849853210967137)
                    ·
                      refine ⟨505188968887389908225353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 673585291849853210967137 505188968887389908225353)
                      ·
                        rfl

theorem cell23_983852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 3, 2].length) (baseStart_983852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_983852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_983852 prefixEnd_983852 := by exact prefixLift 983852
  have htrace : WordTrace (prefixWord ++ tailWord_983852) baseStart_983852 baseEnd_983852 := by
    simpa [prefixWord, tailWord_983852, baseEnd_983852] using wordTrace_append hprefix tailTrace_983852
  have hstable : (prefixWord ++ tailWord_983852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983852).length < 2 ^ (prefixWord ++ tailWord_983852).sum := by decide
  have hdescent : baseEnd_983852 < baseStart_983852 := by decide
  rcases family_descends (prefixWord ++ tailWord_983852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983859 : List Nat := [1, 1, 1, 2, 6, 1, 2, 3, 2, 1, 3]
def baseStart_983859 : Nat := 118140960795 + 983859 * 2 ^ 59
def prefixEnd_983859 : Nat := 4983230072969 + 3 ^ 40 * 983859 * 2
def baseEnd_983859 : Nat := 505192563251971380837821

theorem tailTrace_983859 : CollatzResearch.WordTrace tailWord_983859 prefixEnd_983859 505192563251971380837821 := by
  unfold tailWord_983859
  simp only [CollatzResearch.WordTrace]
  refine ⟨35884285742654347584778631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23922857161769565056519087 35884285742654347584778631)
  ·
    refine ⟨53826428613981521377167947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35884285742654347584778631 53826428613981521377167947)
    ·
      refine ⟨80739642920972282065751921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53826428613981521377167947 80739642920972282065751921)
      ·
        refine ⟨60554732190729211549313941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80739642920972282065751921 60554732190729211549313941)
        ·
          refine ⟨2838503071440431791374091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 60554732190729211549313941 2838503071440431791374091)
          ·
            refine ⟨4257754607160647687061137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2838503071440431791374091 4257754607160647687061137)
            ·
              refine ⟨3193315955370485765295853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4257754607160647687061137 3193315955370485765295853)
              ·
                refine ⟨1197493483263932161985945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3193315955370485765295853 1197493483263932161985945)
                ·
                  refine ⟨898120112447949121489459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1197493483263932161985945 898120112447949121489459)
                  ·
                    refine ⟨1347180168671923682234189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 898120112447949121489459 1347180168671923682234189)
                    ·
                      refine ⟨505192563251971380837821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1347180168671923682234189 505192563251971380837821)
                      ·
                        rfl

theorem cell23_983859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 3, 2, 1, 3].length) (baseStart_983859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_983859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_983859 prefixEnd_983859 := by exact prefixLift 983859
  have htrace : WordTrace (prefixWord ++ tailWord_983859) baseStart_983859 baseEnd_983859 := by
    simpa [prefixWord, tailWord_983859, baseEnd_983859] using wordTrace_append hprefix tailTrace_983859
  have hstable : (prefixWord ++ tailWord_983859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983859).length < 2 ^ (prefixWord ++ tailWord_983859).sum := by decide
  have hdescent : baseEnd_983859 < baseStart_983859 := by decide
  rcases family_descends (prefixWord ++ tailWord_983859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983882 : List Nat := [3, 1, 2, 1, 1, 1, 2, 3, 3, 4, 2]
def baseStart_983882 : Nat := 118140960795 + 983882 * 2 ^ 59
def prefixEnd_983882 : Nat := 4983230072969 + 3 ^ 40 * 983882 * 2
def baseEnd_983882 : Nat := 505204373307024790850215

theorem tailTrace_983882 : CollatzResearch.WordTrace tailWord_983882 prefixEnd_983882 505204373307024790850215 := by
  unfold tailWord_983882
  simp only [CollatzResearch.WordTrace]
  refine ⟨8971281155392755628216475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23923416414380681675243933 8971281155392755628216475)
  ·
    refine ⟨13456921733089133442324713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8971281155392755628216475 13456921733089133442324713)
    ·
      refine ⟨10092691299816850081743535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13456921733089133442324713 10092691299816850081743535)
      ·
        refine ⟨15139036949725275122615303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10092691299816850081743535 15139036949725275122615303)
        ·
          refine ⟨22708555424587912683922955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15139036949725275122615303 22708555424587912683922955)
          ·
            refine ⟨34062833136881869025884433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22708555424587912683922955 34062833136881869025884433)
            ·
              refine ⟨25547124852661401769413325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34062833136881869025884433 25547124852661401769413325)
              ·
                refine ⟨9580171819748025663529997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25547124852661401769413325 9580171819748025663529997)
                ·
                  refine ⟨3592564432405509623823749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9580171819748025663529997 3592564432405509623823749)
                  ·
                    refine ⟨673605831076033054466953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3592564432405509623823749 673605831076033054466953)
                    ·
                      refine ⟨505204373307024790850215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 673605831076033054466953 505204373307024790850215)
                      ·
                        rfl

theorem cell23_983882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 3, 4, 2].length) (baseStart_983882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_983882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_983882 prefixEnd_983882 := by exact prefixLift 983882
  have htrace : WordTrace (prefixWord ++ tailWord_983882) baseStart_983882 baseEnd_983882 := by
    simpa [prefixWord, tailWord_983882, baseEnd_983882] using wordTrace_append hprefix tailTrace_983882
  have hstable : (prefixWord ++ tailWord_983882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983882).length < 2 ^ (prefixWord ++ tailWord_983882).sum := by decide
  have hdescent : baseEnd_983882 < baseStart_983882 := by decide
  rcases family_descends (prefixWord ++ tailWord_983882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983912 : List Nat := [2, 1, 4, 2, 1, 2, 2, 1, 2, 2, 4]
def baseStart_983912 : Nat := 118140960795 + 983912 * 2 ^ 59
def prefixEnd_983912 : Nat := 4983230072969 + 3 ^ 40 * 983912 * 2
def baseEnd_983912 : Nat := 505219777726659673475077

theorem tailTrace_983912 : CollatzResearch.WordTrace tailWord_983912 prefixEnd_983912 505219777726659673475077 := by
  unfold tailWord_983912
  simp only [CollatzResearch.WordTrace]
  refine ⟨17943109405731168818228995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23924145874308225090971993 17943109405731168818228995)
  ·
    refine ⟨26914664108596753227343493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17943109405731168818228995 26914664108596753227343493)
    ·
      refine ⟨5046499520361891230126905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26914664108596753227343493 5046499520361891230126905)
      ·
        refine ⟨3784874640271418422595179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5046499520361891230126905 3784874640271418422595179)
        ·
          refine ⟨5677311960407127633892769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3784874640271418422595179 5677311960407127633892769)
          ·
            refine ⟨4257983970305345725419577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5677311960407127633892769 4257983970305345725419577)
            ·
              refine ⟨3193487977729009294064683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4257983970305345725419577 3193487977729009294064683)
              ·
                refine ⟨4790231966593513941097025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3193487977729009294064683 4790231966593513941097025)
                ·
                  refine ⟨3592673974945135455822769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4790231966593513941097025 3592673974945135455822769)
                  ·
                    refine ⟨2694505481208851591867077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3592673974945135455822769 2694505481208851591867077)
                    ·
                      refine ⟨505219777726659673475077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2694505481208851591867077 505219777726659673475077)
                      ·
                        rfl

theorem cell23_983912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_983912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_983912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_983912 prefixEnd_983912 := by exact prefixLift 983912
  have htrace : WordTrace (prefixWord ++ tailWord_983912) baseStart_983912 baseEnd_983912 := by
    simpa [prefixWord, tailWord_983912, baseEnd_983912] using wordTrace_append hprefix tailTrace_983912
  have hstable : (prefixWord ++ tailWord_983912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983912).length < 2 ^ (prefixWord ++ tailWord_983912).sum := by decide
  have hdescent : baseEnd_983912 < baseStart_983912 := by decide
  rcases family_descends (prefixWord ++ tailWord_983912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983935 : List Nat := [1, 1, 2, 2, 1, 1, 6, 1, 1, 7]
def baseStart_983935 : Nat := 118140960795 + 983935 * 2 ^ 59
def prefixEnd_983935 : Nat := 4983230072969 + 3 ^ 40 * 983935 * 2
def baseEnd_983935 : Nat := 168410529260571027829157

theorem tailTrace_983935 : CollatzResearch.WordTrace tailWord_983935 prefixEnd_983935 168410529260571027829157 := by
  unfold tailWord_983935
  simp only [CollatzResearch.WordTrace]
  refine ⟨35887057690379012564545259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23924705126919341709696839 35887057690379012564545259)
  ·
    refine ⟨53830586535568518846817889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35887057690379012564545259 53830586535568518846817889)
    ·
      refine ⟨40372939901676389135113417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53830586535568518846817889 40372939901676389135113417)
      ·
        refine ⟨30279704926257291851335063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40372939901676389135113417 30279704926257291851335063)
        ·
          refine ⟨45419557389385937777002595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30279704926257291851335063 45419557389385937777002595)
          ·
            refine ⟨68129336084078906665503893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45419557389385937777002595 68129336084078906665503893)
            ·
              refine ⟨3193562628941198749945495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 68129336084078906665503893 3193562628941198749945495)
              ·
                refine ⟨4790343943411798124918243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3193562628941198749945495 4790343943411798124918243)
                ·
                  refine ⟨7185515915117697187377365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4790343943411798124918243 7185515915117697187377365)
                  ·
                    refine ⟨168410529260571027829157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7185515915117697187377365 168410529260571027829157)
                    ·
                      rfl

theorem cell23_983935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 1, 1, 7].length) (baseStart_983935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_983935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_983935 prefixEnd_983935 := by exact prefixLift 983935
  have htrace : WordTrace (prefixWord ++ tailWord_983935) baseStart_983935 baseEnd_983935 := by
    simpa [prefixWord, tailWord_983935, baseEnd_983935] using wordTrace_append hprefix tailTrace_983935
  have hstable : (prefixWord ++ tailWord_983935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983935).length < 2 ^ (prefixWord ++ tailWord_983935).sum := by decide
  have hdescent : baseEnd_983935 < baseStart_983935 := by decide
  rcases family_descends (prefixWord ++ tailWord_983935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983955 : List Nat := [1, 1, 1, 2, 1, 2, 1, 4, 3, 3, 4]
def baseStart_983955 : Nat := 118140960795 + 983955 * 2 ^ 59
def prefixEnd_983955 : Nat := 4983230072969 + 3 ^ 40 * 983955 * 2
def baseEnd_983955 : Nat := 505241857394803005237379

theorem tailTrace_983955 : CollatzResearch.WordTrace tailWord_983955 prefixEnd_983955 505241857394803005237379 := by
  unfold tailWord_983955
  simp only [CollatzResearch.WordTrace]
  refine ⟨35887787150306555980273319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23925191433537703986848879 35887787150306555980273319)
  ·
    refine ⟨53831680725459833970409979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35887787150306555980273319 53831680725459833970409979)
    ·
      refine ⟨80747521088189750955614969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53831680725459833970409979 80747521088189750955614969)
      ·
        refine ⟨60560640816142313216711227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80747521088189750955614969 60560640816142313216711227)
        ·
          refine ⟨90840961224213469825066841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60560640816142313216711227 90840961224213469825066841)
          ·
            refine ⟨68130720918160102368800131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90840961224213469825066841 68130720918160102368800131)
            ·
              refine ⟨102196081377240153553200197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68130720918160102368800131 102196081377240153553200197)
              ·
                refine ⟨19161765258232528791225037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102196081377240153553200197 19161765258232528791225037)
                ·
                  refine ⟨7185661971837198296709389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19161765258232528791225037 7185661971837198296709389)
                  ·
                    refine ⟨2694623239438949361266021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7185661971837198296709389 2694623239438949361266021)
                    ·
                      refine ⟨505241857394803005237379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2694623239438949361266021 505241857394803005237379)
                      ·
                        rfl

theorem cell23_983955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 3, 3, 4].length) (baseStart_983955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_983955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_983955 prefixEnd_983955 := by exact prefixLift 983955
  have htrace : WordTrace (prefixWord ++ tailWord_983955) baseStart_983955 baseEnd_983955 := by
    simpa [prefixWord, tailWord_983955, baseEnd_983955] using wordTrace_append hprefix tailTrace_983955
  have hstable : (prefixWord ++ tailWord_983955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983955).length < 2 ^ (prefixWord ++ tailWord_983955).sum := by decide
  have hdescent : baseEnd_983955 < baseStart_983955 := by decide
  rcases family_descends (prefixWord ++ tailWord_983955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983956 : List Nat := [2, 4, 2, 1, 1, 1, 5, 2, 5]
def baseStart_983956 : Nat := 118140960795 + 983956 * 2 ^ 59
def prefixEnd_983956 : Nat := 4983230072969 + 3 ^ 40 * 983956 * 2
def baseEnd_983956 : Nat := 56138041208384166813875

theorem tailTrace_983956 : CollatzResearch.WordTrace tailWord_983956 prefixEnd_983956 56138041208384166813875 := by
  unfold tailWord_983956
  simp only [CollatzResearch.WordTrace]
  refine ⟨17943911811651466575529861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23925215748868622100706481 17943911811651466575529861)
  ·
    refine ⟨3364483464684649982911849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17943911811651466575529861 3364483464684649982911849)
    ·
      refine ⟨2523362598513487487183887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3364483464684649982911849 2523362598513487487183887)
      ·
        refine ⟨3785043897770231230775831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2523362598513487487183887 3785043897770231230775831)
        ·
          refine ⟨5677565846655346846163747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3785043897770231230775831 5677565846655346846163747)
          ·
            refine ⟨8516348769983020269245621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5677565846655346846163747 8516348769983020269245621)
            ·
              refine ⟨798407697185908150241777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8516348769983020269245621 798407697185908150241777)
              ·
                refine ⟨598805772889431112681333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 798407697185908150241777 598805772889431112681333)
                ·
                  refine ⟨56138041208384166813875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 598805772889431112681333 56138041208384166813875)
                  ·
                    rfl

theorem cell23_983956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 5, 2, 5].length) (baseStart_983956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_983956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_983956 prefixEnd_983956 := by exact prefixLift 983956
  have htrace : WordTrace (prefixWord ++ tailWord_983956) baseStart_983956 baseEnd_983956 := by
    simpa [prefixWord, tailWord_983956, baseEnd_983956] using wordTrace_append hprefix tailTrace_983956
  have hstable : (prefixWord ++ tailWord_983956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983956).length < 2 ^ (prefixWord ++ tailWord_983956).sum := by decide
  have hdescent : baseEnd_983956 < baseStart_983956 := by decide
  rcases family_descends (prefixWord ++ tailWord_983956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983972 : List Nat := [2, 3, 1, 2, 1, 2, 1, 2, 4, 1, 4]
def baseStart_983972 : Nat := 118140960795 + 983972 * 2 ^ 59
def prefixEnd_983972 : Nat := 4983230072969 + 3 ^ 40 * 983972 * 2
def baseEnd_983972 : Nat := 505250586565929438724801

theorem tailTrace_983972 : CollatzResearch.WordTrace tailWord_983972 prefixEnd_983972 505250586565929438724801 := by
  unfold tailWord_983972
  simp only [CollatzResearch.WordTrace]
  refine ⟨17944203595622483941821085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23925604794163311922428113 17944203595622483941821085)
  ·
    refine ⟨6729076348358431478182907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17944203595622483941821085 6729076348358431478182907)
    ·
      refine ⟨10093614522537647217274361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6729076348358431478182907 10093614522537647217274361)
      ·
        refine ⟨7570210891903235412955771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10093614522537647217274361 7570210891903235412955771)
        ·
          refine ⟨11355316337854853119433657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7570210891903235412955771 11355316337854853119433657)
          ·
            refine ⟨8516487253391139839575243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11355316337854853119433657 8516487253391139839575243)
            ·
              refine ⟨12774730880086709759362865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8516487253391139839575243 12774730880086709759362865)
              ·
                refine ⟨9581048160065032319522149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12774730880086709759362865 9581048160065032319522149)
                ·
                  refine ⟨1796446530012193559910403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9581048160065032319522149 1796446530012193559910403)
                  ·
                    refine ⟨2694669795018290339865605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1796446530012193559910403 2694669795018290339865605)
                    ·
                      refine ⟨505250586565929438724801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2694669795018290339865605 505250586565929438724801)
                      ·
                        rfl

theorem cell23_983972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_983972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_983972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_983972 prefixEnd_983972 := by exact prefixLift 983972
  have htrace : WordTrace (prefixWord ++ tailWord_983972) baseStart_983972 baseEnd_983972 := by
    simpa [prefixWord, tailWord_983972, baseEnd_983972] using wordTrace_append hprefix tailTrace_983972
  have hstable : (prefixWord ++ tailWord_983972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983972).length < 2 ^ (prefixWord ++ tailWord_983972).sum := by decide
  have hdescent : baseEnd_983972 < baseStart_983972 := by decide
  rcases family_descends (prefixWord ++ tailWord_983972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983989 : List Nat := [1, 3, 3, 2, 1, 1, 4, 1, 2, 1, 4]
def baseStart_983989 : Nat := 118140960795 + 983989 * 2 ^ 59
def prefixEnd_983989 : Nat := 4983230072969 + 3 ^ 40 * 983989 * 2
def baseEnd_983989 : Nat := 505259315737055872212223

theorem tailTrace_983989 : CollatzResearch.WordTrace tailWord_983989 prefixEnd_983989 505259315737055872212223 := by
  unfold tailWord_983989
  simp only [CollatzResearch.WordTrace]
  refine ⟨35889027232183379787011021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23926018154788919858007347 35889027232183379787011021)
  ·
    refine ⟨13458385212068767420129133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35889027232183379787011021 13458385212068767420129133)
    ·
      refine ⟨5046894454525787782548425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13458385212068767420129133 5046894454525787782548425)
      ·
        refine ⟨3785170840894340836911319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5046894454525787782548425 3785170840894340836911319)
        ·
          refine ⟨5677756261341511255366979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3785170840894340836911319 5677756261341511255366979)
          ·
            refine ⟨8516634392012266883050469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5677756261341511255366979 8516634392012266883050469)
            ·
              refine ⟨1596868948502300040571963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8516634392012266883050469 1596868948502300040571963)
              ·
                refine ⟨2395303422753450060857945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1596868948502300040571963 2395303422753450060857945)
                ·
                  refine ⟨1796477567065087545643459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2395303422753450060857945 1796477567065087545643459)
                  ·
                    refine ⟨2694716350597631318465189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1796477567065087545643459 2694716350597631318465189)
                    ·
                      refine ⟨505259315737055872212223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2694716350597631318465189 505259315737055872212223)
                      ·
                        rfl

theorem cell23_983989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_983989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_983989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_983989 prefixEnd_983989 := by exact prefixLift 983989
  have htrace : WordTrace (prefixWord ++ tailWord_983989) baseStart_983989 baseEnd_983989 := by
    simpa [prefixWord, tailWord_983989, baseEnd_983989] using wordTrace_append hprefix tailTrace_983989
  have hstable : (prefixWord ++ tailWord_983989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983989).length < 2 ^ (prefixWord ++ tailWord_983989).sum := by decide
  have hdescent : baseEnd_983989 < baseStart_983989 := by decide
  rcases family_descends (prefixWord ++ tailWord_983989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984029 : List Nat := [1, 4, 3, 1, 2, 1, 2, 3, 6]
def baseStart_984029 : Nat := 118140960795 + 984029 * 2 ^ 59
def prefixEnd_984029 : Nat := 4983230072969 + 3 ^ 40 * 984029 * 2
def baseEnd_984029 : Nat := 56142206107026190634671

theorem tailTrace_984029 : CollatzResearch.WordTrace tailWord_984029 prefixEnd_984029 56142206107026190634671 := by
  unfold tailWord_984029
  simp only [CollatzResearch.WordTrace]
  refine ⟨35890486152038466618467141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23926990768025644412311427 35890486152038466618467141)
  ·
    refine ⟨6729466153507212490962589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35890486152038466618467141 6729466153507212490962589)
    ·
      refine ⟨2523549807565204684110971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6729466153507212490962589 2523549807565204684110971)
      ·
        refine ⟨3785324711347807026166457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2523549807565204684110971 3785324711347807026166457)
        ·
          refine ⟨2838993533510855269624843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3785324711347807026166457 2838993533510855269624843)
          ·
            refine ⟨4258490300266282904437265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2838993533510855269624843 4258490300266282904437265)
            ·
              refine ⟨3193867725199712178327949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4258490300266282904437265 3193867725199712178327949)
              ·
                refine ⟨1197700396949892066872981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3193867725199712178327949 1197700396949892066872981)
                ·
                  refine ⟨56142206107026190634671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1197700396949892066872981 56142206107026190634671)
                  ·
                    rfl

theorem cell23_984029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 3, 6].length) (baseStart_984029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_984029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_984029 prefixEnd_984029 := by exact prefixLift 984029
  have htrace : WordTrace (prefixWord ++ tailWord_984029) baseStart_984029 baseEnd_984029 := by
    simpa [prefixWord, tailWord_984029, baseEnd_984029] using wordTrace_append hprefix tailTrace_984029
  have hstable : (prefixWord ++ tailWord_984029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984029).length < 2 ^ (prefixWord ++ tailWord_984029).sum := by decide
  have hdescent : baseEnd_984029 < baseStart_984029 := by decide
  rcases family_descends (prefixWord ++ tailWord_984029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984050 : List Nat := [3, 2, 1, 5, 1, 1, 2, 3, 1, 4]
def baseStart_984050 : Nat := 118140960795 + 984050 * 2 ^ 59
def prefixEnd_984050 : Nat := 4983230072969 + 3 ^ 40 * 984050 * 2
def baseEnd_984050 : Nat := 168430212685660044516481

theorem tailTrace_984050 : CollatzResearch.WordTrace tailWord_984050 prefixEnd_984050 168430212685660044516481 := by
  unfold tailWord_984050
  simp only [CollatzResearch.WordTrace]
  refine ⟨8972813021240596801245401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23927501389974924803321069 8972813021240596801245401)
  ·
    refine ⟨6729609765930447600934051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8972813021240596801245401 6729609765930447600934051)
    ·
      refine ⟨10094414648895671401401077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6729609765930447600934051 10094414648895671401401077)
      ·
        refine ⟨946351373333969193881351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10094414648895671401401077 946351373333969193881351)
        ·
          refine ⟨1419527060000953790822027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 946351373333969193881351 1419527060000953790822027)
          ·
            refine ⟨2129290590001430686233041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1419527060000953790822027 2129290590001430686233041)
            ·
              refine ⟨1596967942501073014674781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2129290590001430686233041 1596967942501073014674781)
              ·
                refine ⟨598862978437902380503043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1596967942501073014674781 598862978437902380503043)
                ·
                  refine ⟨898294467656853570754565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 598862978437902380503043 898294467656853570754565)
                  ·
                    refine ⟨168430212685660044516481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 898294467656853570754565 168430212685660044516481)
                    ·
                      rfl

theorem cell23_984050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 3, 1, 4].length) (baseStart_984050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_984050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_984050 prefixEnd_984050 := by exact prefixLift 984050
  have htrace : WordTrace (prefixWord ++ tailWord_984050) baseStart_984050 baseEnd_984050 := by
    simpa [prefixWord, tailWord_984050, baseEnd_984050] using wordTrace_append hprefix tailTrace_984050
  have hstable : (prefixWord ++ tailWord_984050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984050).length < 2 ^ (prefixWord ++ tailWord_984050).sum := by decide
  have hdescent : baseEnd_984050 < baseStart_984050 := by decide
  rcases family_descends (prefixWord ++ tailWord_984050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984089 : List Nat := [1, 2, 1, 2, 1, 1, 4, 5, 2, 4]
def baseStart_984089 : Nat := 118140960795 + 984089 * 2 ^ 59
def prefixEnd_984089 : Nat := 4983230072969 + 3 ^ 40 * 984089 * 2
def baseEnd_984089 : Nat := 168436887934168493653921

theorem tailTrace_984089 : CollatzResearch.WordTrace tailWord_984089 prefixEnd_984089 168436887934168493653921 := by
  unfold tailWord_984089
  simp only [CollatzResearch.WordTrace]
  refine ⟨35892674531821096865651321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23928449687880731243767547 35892674531821096865651321)
  ·
    refine ⟨26919505898865822649238491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35892674531821096865651321 26919505898865822649238491)
    ·
      refine ⟨40379258848298733973857737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26919505898865822649238491 40379258848298733973857737)
      ·
        refine ⟨30284444136224050480393303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40379258848298733973857737 30284444136224050480393303)
        ·
          refine ⟨45426666204336075720589955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30284444136224050480393303 45426666204336075720589955)
          ·
            refine ⟨68139999306504113580884933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45426666204336075720589955 68139999306504113580884933)
            ·
              refine ⟨12776249869969521296415925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68139999306504113580884933 12776249869969521296415925)
              ·
                refine ⟨1197773425309642621538993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12776249869969521296415925 1197773425309642621538993)
                ·
                  refine ⟨898330068982231966154245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1197773425309642621538993 898330068982231966154245)
                  ·
                    refine ⟨168436887934168493653921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 898330068982231966154245 168436887934168493653921)
                    ·
                      rfl

theorem cell23_984089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 5, 2, 4].length) (baseStart_984089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_984089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_984089 prefixEnd_984089 := by exact prefixLift 984089
  have htrace : WordTrace (prefixWord ++ tailWord_984089) baseStart_984089 baseEnd_984089 := by
    simpa [prefixWord, tailWord_984089, baseEnd_984089] using wordTrace_append hprefix tailTrace_984089
  have hstable : (prefixWord ++ tailWord_984089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984089).length < 2 ^ (prefixWord ++ tailWord_984089).sum := by decide
  have hdescent : baseEnd_984089 < baseStart_984089 := by decide
  rcases family_descends (prefixWord ++ tailWord_984089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984116 : List Nat := [2, 5, 1, 2, 1, 1, 1, 3, 1, 1, 5]
def baseStart_984116 : Nat := 118140960795 + 984116 * 2 ^ 59
def prefixEnd_984116 : Nat := 4983230072969 + 3 ^ 40 * 984116 * 2
def baseEnd_984116 : Nat := 505324527780176875324139

theorem tailTrace_984116 : CollatzResearch.WordTrace tailWord_984116 prefixEnd_984116 505324527780176875324139 := by
  unfold tailWord_984116
  simp only [CollatzResearch.WordTrace]
  refine ⟨17946829651361640238442101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23929106201815520317922801 17946829651361640238442101)
  ·
    refine ⟨1682515279815153772353947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17946829651361640238442101 1682515279815153772353947)
    ·
      refine ⟨2523772919722730658530921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1682515279815153772353947 2523772919722730658530921)
      ·
        refine ⟨1892829689792047993898191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2523772919722730658530921 1892829689792047993898191)
        ·
          refine ⟨2839244534688071990847287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1892829689792047993898191 2839244534688071990847287)
          ·
            refine ⟨4258866802032107986270931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2839244534688071990847287 4258866802032107986270931)
            ·
              refine ⟨6388300203048161979406397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4258866802032107986270931 6388300203048161979406397)
              ·
                refine ⟨2395612576143060742277399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6388300203048161979406397 2395612576143060742277399)
                ·
                  refine ⟨3593418864214591113416099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2395612576143060742277399 3593418864214591113416099)
                  ·
                    refine ⟨5390128296321886670124149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3593418864214591113416099 5390128296321886670124149)
                    ·
                      refine ⟨505324527780176875324139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5390128296321886670124149 505324527780176875324139)
                      ·
                        rfl

theorem cell23_984116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_984116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_984116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_984116 prefixEnd_984116 := by exact prefixLift 984116
  have htrace : WordTrace (prefixWord ++ tailWord_984116) baseStart_984116 baseEnd_984116 := by
    simpa [prefixWord, tailWord_984116, baseEnd_984116] using wordTrace_append hprefix tailTrace_984116
  have hstable : (prefixWord ++ tailWord_984116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984116).length < 2 ^ (prefixWord ++ tailWord_984116).sum := by decide
  have hdescent : baseEnd_984116 < baseStart_984116 := by decide
  rcases family_descends (prefixWord ++ tailWord_984116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984150 : List Nat := [5, 2, 2, 1, 2, 1, 1, 1, 3, 2, 3]
def baseStart_984150 : Nat := 118140960795 + 984150 * 2 ^ 59
def prefixEnd_984150 : Nat := 4983230072969 + 3 ^ 40 * 984150 * 2
def baseEnd_984150 : Nat := 505341986122429742298983

theorem tailTrace_984150 : CollatzResearch.WordTrace tailWord_984150 prefixEnd_984150 505341986122429742298983 := by
  unfold tailWord_984150
  simp only [CollatzResearch.WordTrace]
  refine ⟨2243431211537506517726369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23929932923066736189081269 2243431211537506517726369)
  ·
    refine ⟨1682573408653129888294777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2243431211537506517726369 1682573408653129888294777)
    ·
      refine ⟨1261930056489847416221083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1682573408653129888294777 1261930056489847416221083)
      ·
        refine ⟨1892895084734771124331625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1261930056489847416221083 1892895084734771124331625)
        ·
          refine ⟨1419671313551078343248719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1892895084734771124331625 1419671313551078343248719)
          ·
            refine ⟨2129506970326617514873079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1419671313551078343248719 2129506970326617514873079)
            ·
              refine ⟨3194260455489926272309619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2129506970326617514873079 3194260455489926272309619)
              ·
                refine ⟨4791390683234889408464429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3194260455489926272309619 4791390683234889408464429)
                ·
                  refine ⟨1796771506213083528174161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4791390683234889408464429 1796771506213083528174161)
                  ·
                    refine ⟨1347578629659812646130621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1796771506213083528174161 1347578629659812646130621)
                    ·
                      refine ⟨505341986122429742298983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1347578629659812646130621 505341986122429742298983)
                      ·
                        rfl

theorem cell23_984150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_984150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_984150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_984150 prefixEnd_984150 := by exact prefixLift 984150
  have htrace : WordTrace (prefixWord ++ tailWord_984150) baseStart_984150 baseEnd_984150 := by
    simpa [prefixWord, tailWord_984150, baseEnd_984150] using wordTrace_append hprefix tailTrace_984150
  have hstable : (prefixWord ++ tailWord_984150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984150).length < 2 ^ (prefixWord ++ tailWord_984150).sum := by decide
  have hdescent : baseEnd_984150 < baseStart_984150 := by decide
  rcases family_descends (prefixWord ++ tailWord_984150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984181 : List Nat := [1, 3, 4, 3, 1, 2, 2, 2, 1, 2, 2]
def baseStart_984181 : Nat := 118140960795 + 984181 * 2 ^ 59
def prefixEnd_984181 : Nat := 4983230072969 + 3 ^ 40 * 984181 * 2
def baseEnd_984181 : Nat := 505357904022719121011341

theorem tailTrace_984181 : CollatzResearch.WordTrace tailWord_984181 prefixEnd_984181 505357904022719121011341 := by
  unfold tailWord_984181
  simp only [CollatzResearch.WordTrace]
  refine ⟨35896030047487796578000397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23930686698325197718666931 35896030047487796578000397)
  ·
    refine ⟨13461011267807923716750149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35896030047487796578000397 13461011267807923716750149)
    ·
      refine ⟨2523939612713985696890653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13461011267807923716750149 2523939612713985696890653)
      ·
        refine ⟨946477354767744636333995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2523939612713985696890653 946477354767744636333995)
        ·
          refine ⟨1419716032151616954500993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 946477354767744636333995 1419716032151616954500993)
          ·
            refine ⟨1064787024113712715875745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1419716032151616954500993 1064787024113712715875745)
            ·
              refine ⟨798590268085284536906809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1064787024113712715875745 798590268085284536906809)
              ·
                refine ⟨598942701063963402680107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 798590268085284536906809 598942701063963402680107)
                ·
                  refine ⟨898414051595945104020161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 598942701063963402680107 898414051595945104020161)
                  ·
                    refine ⟨673810538696958828015121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 898414051595945104020161 673810538696958828015121)
                    ·
                      refine ⟨505357904022719121011341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 673810538696958828015121 505357904022719121011341)
                      ·
                        rfl

theorem cell23_984181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_984181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_984181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_984181 prefixEnd_984181 := by exact prefixLift 984181
  have htrace : WordTrace (prefixWord ++ tailWord_984181) baseStart_984181 baseEnd_984181 := by
    simpa [prefixWord, tailWord_984181, baseEnd_984181] using wordTrace_append hprefix tailTrace_984181
  have hstable : (prefixWord ++ tailWord_984181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984181).length < 2 ^ (prefixWord ++ tailWord_984181).sum := by decide
  have hdescent : baseEnd_984181 < baseStart_984181 := by decide
  rcases family_descends (prefixWord ++ tailWord_984181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984189 : List Nat := [1, 4, 1, 1, 3, 1, 1, 1, 1, 6, 3]
def baseStart_984189 : Nat := 118140960795 + 984189 * 2 ^ 59
def prefixEnd_984189 : Nat := 4983230072969 + 3 ^ 40 * 984189 * 2
def baseEnd_984189 : Nat := 505362011867955089711303

theorem tailTrace_984189 : CollatzResearch.WordTrace tailWord_984189 prefixEnd_984189 505362011867955089711303 := by
  unfold tailWord_984189
  simp only [CollatzResearch.WordTrace]
  refine ⟨35896321831458813944291621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23930881220972542629527747 35896321831458813944291621)
  ·
    refine ⟨6730560343398527614554679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35896321831458813944291621 6730560343398527614554679)
    ·
      refine ⟨10095840515097791421832019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6730560343398527614554679 10095840515097791421832019)
      ·
        refine ⟨15143760772646687132748029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10095840515097791421832019 15143760772646687132748029)
        ·
          refine ⟨5678910289742507674780511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15143760772646687132748029 5678910289742507674780511)
          ·
            refine ⟨8518365434613761512170767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5678910289742507674780511 8518365434613761512170767)
            ·
              refine ⟨12777548151920642268256151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8518365434613761512170767 12777548151920642268256151)
              ·
                refine ⟨19166322227880963402384227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12777548151920642268256151 19166322227880963402384227)
                ·
                  refine ⟨28749483341821445103576341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19166322227880963402384227 28749483341821445103576341)
                  ·
                    refine ⟨1347632031647880239230141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28749483341821445103576341 1347632031647880239230141)
                    ·
                      refine ⟨505362011867955089711303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1347632031647880239230141 505362011867955089711303)
                      ·
                        rfl

theorem cell23_984189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 6, 3].length) (baseStart_984189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_984189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_984189 prefixEnd_984189 := by exact prefixLift 984189
  have htrace : WordTrace (prefixWord ++ tailWord_984189) baseStart_984189 baseEnd_984189 := by
    simpa [prefixWord, tailWord_984189, baseEnd_984189] using wordTrace_append hprefix tailTrace_984189
  have hstable : (prefixWord ++ tailWord_984189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984189).length < 2 ^ (prefixWord ++ tailWord_984189).sum := by decide
  have hdescent : baseEnd_984189 < baseStart_984189 := by decide
  rcases family_descends (prefixWord ++ tailWord_984189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984239 : List Nat := [1, 1, 2, 1, 2, 3, 2, 4, 2, 5]
def baseStart_984239 : Nat := 118140960795 + 984239 * 2 ^ 59
def prefixEnd_984239 : Nat := 4983230072969 + 3 ^ 40 * 984239 * 2
def baseEnd_984239 : Nat := 168462561966893298028691

theorem tailTrace_984239 : CollatzResearch.WordTrace tailWord_984239 prefixEnd_984239 168462561966893298028691 := by
  unfold tailWord_984239
  simp only [CollatzResearch.WordTrace]
  refine ⟨35898145481277672483611771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23932096987518448322407847 35898145481277672483611771)
  ·
    refine ⟨53847218221916508725417657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35898145481277672483611771 53847218221916508725417657)
    ·
      refine ⟨40385413666437381544063243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53847218221916508725417657 40385413666437381544063243)
      ·
        refine ⟨60578120499656072316094865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40385413666437381544063243 60578120499656072316094865)
        ·
          refine ⟨45433590374742054237071149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60578120499656072316094865 45433590374742054237071149)
          ·
            refine ⟨17037596390528270338901681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45433590374742054237071149 17037596390528270338901681)
            ·
              refine ⟨12778197292896202754176261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17037596390528270338901681 12778197292896202754176261)
              ·
                refine ⟨2395911992418038016408049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12778197292896202754176261 2395911992418038016408049)
                ·
                  refine ⟨1796933994313528512306037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2395911992418038016408049 1796933994313528512306037)
                  ·
                    refine ⟨168462561966893298028691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1796933994313528512306037 168462561966893298028691)
                    ·
                      rfl

theorem cell23_984239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 4, 2, 5].length) (baseStart_984239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_984239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_984239 prefixEnd_984239 := by exact prefixLift 984239
  have htrace : WordTrace (prefixWord ++ tailWord_984239) baseStart_984239 baseEnd_984239 := by
    simpa [prefixWord, tailWord_984239, baseEnd_984239] using wordTrace_append hprefix tailTrace_984239
  have hstable : (prefixWord ++ tailWord_984239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984239).length < 2 ^ (prefixWord ++ tailWord_984239).sum := by decide
  have hdescent : baseEnd_984239 < baseStart_984239 := by decide
  rcases family_descends (prefixWord ++ tailWord_984239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984259 : List Nat := [1, 1, 1, 3, 1, 1, 1, 3, 6, 1, 4]
def baseStart_984259 : Nat := 118140960795 + 984259 * 2 ^ 59
def prefixEnd_984259 : Nat := 4983230072969 + 3 ^ 40 * 984259 * 2
def baseEnd_984259 : Nat := 505397955513769815835981

theorem tailTrace_984259 : CollatzResearch.WordTrace tailWord_984259 prefixEnd_984259 505397955513769815835981 := by
  unfold tailWord_984259
  simp only [CollatzResearch.WordTrace]
  refine ⟨35898874941205215899339831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23932583294136810599559887 35898874941205215899339831)
  ·
    refine ⟨53848312411807823849009747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35898874941205215899339831 53848312411807823849009747)
    ·
      refine ⟨80772468617711735773514621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53848312411807823849009747 80772468617711735773514621)
      ·
        refine ⟨30289675731641900915067983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80772468617711735773514621 30289675731641900915067983)
        ·
          refine ⟨45434513597462851372601975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30289675731641900915067983 45434513597462851372601975)
          ·
            refine ⟨68151770396194277058902963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45434513597462851372601975 68151770396194277058902963)
            ·
              refine ⟨102227655594291415588354445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68151770396194277058902963 102227655594291415588354445)
              ·
                refine ⟨38335370847859280845632917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102227655594291415588354445 38335370847859280845632917)
                ·
                  refine ⟨1796970508493403789639043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 38335370847859280845632917 1796970508493403789639043)
                  ·
                    refine ⟨2695455762740105684458565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1796970508493403789639043 2695455762740105684458565)
                    ·
                      refine ⟨505397955513769815835981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2695455762740105684458565 505397955513769815835981)
                      ·
                        rfl

theorem cell23_984259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 6, 1, 4].length) (baseStart_984259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_984259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_984259 prefixEnd_984259 := by exact prefixLift 984259
  have htrace : WordTrace (prefixWord ++ tailWord_984259) baseStart_984259 baseEnd_984259 := by
    simpa [prefixWord, tailWord_984259, baseEnd_984259] using wordTrace_append hprefix tailTrace_984259
  have hstable : (prefixWord ++ tailWord_984259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984259).length < 2 ^ (prefixWord ++ tailWord_984259).sum := by decide
  have hdescent : baseEnd_984259 < baseStart_984259 := by decide
  rcases family_descends (prefixWord ++ tailWord_984259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984293 : List Nat := [1, 3, 1, 4, 3, 1, 1, 2, 2, 1, 4]
def baseStart_984293 : Nat := 118140960795 + 984293 * 2 ^ 59
def prefixEnd_984293 : Nat := 4983230072969 + 3 ^ 40 * 984293 * 2
def baseEnd_984293 : Nat := 505415413856022682810825

theorem tailTrace_984293 : CollatzResearch.WordTrace tailWord_984293 prefixEnd_984293 505415413856022682810825 := by
  unfold tailWord_984293
  simp only [CollatzResearch.WordTrace]
  refine ⟨35900115023082039706077533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23933410015388026470718355 35900115023082039706077533)
  ·
    refine ⟨13462543133655764889779075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35900115023082039706077533 13462543133655764889779075)
    ·
      refine ⟨20193814700483647334668613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13462543133655764889779075 20193814700483647334668613)
      ·
        refine ⟨3786340256340683875250365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20193814700483647334668613 3786340256340683875250365)
        ·
          refine ⟨1419877596127756453218887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3786340256340683875250365 1419877596127756453218887)
          ·
            refine ⟨2129816394191634679828331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1419877596127756453218887 2129816394191634679828331)
            ·
              refine ⟨3194724591287452019742497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2129816394191634679828331 3194724591287452019742497)
              ·
                refine ⟨2396043443465589014806873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3194724591287452019742497 2396043443465589014806873)
                ·
                  refine ⟨1797032582599191761105155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2396043443465589014806873 1797032582599191761105155)
                  ·
                    refine ⟨2695548873898787641657733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1797032582599191761105155 2695548873898787641657733)
                    ·
                      refine ⟨505415413856022682810825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2695548873898787641657733 505415413856022682810825)
                      ·
                        rfl

theorem cell23_984293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_984293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_984293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_984293 prefixEnd_984293 := by exact prefixLift 984293
  have htrace : WordTrace (prefixWord ++ tailWord_984293) baseStart_984293 baseEnd_984293 := by
    simpa [prefixWord, tailWord_984293, baseEnd_984293] using wordTrace_append hprefix tailTrace_984293
  have hstable : (prefixWord ++ tailWord_984293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984293).length < 2 ^ (prefixWord ++ tailWord_984293).sum := by decide
  have hdescent : baseEnd_984293 < baseStart_984293 := by decide
  rcases family_descends (prefixWord ++ tailWord_984293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984299 : List Nat := [1, 1, 1, 1, 2, 6, 2, 1, 8]
def baseStart_984299 : Nat := 118140960795 + 984299 * 2 ^ 59
def prefixEnd_984299 : Nat := 4983230072969 + 3 ^ 40 * 984299 * 2
def baseEnd_984299 : Nat := 56157610526661073259533

theorem tailTrace_984299 : CollatzResearch.WordTrace tailWord_984299 prefixEnd_984299 56157610526661073259533 := by
  unfold tailWord_984299
  simp only [CollatzResearch.WordTrace]
  refine ⟨35900333861060302730795951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23933555907373535153863967 35900333861060302730795951)
  ·
    refine ⟨53850500791590454096193927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35900333861060302730795951 53850500791590454096193927)
    ·
      refine ⟨80775751187385681144290891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53850500791590454096193927 80775751187385681144290891)
      ·
        refine ⟨121163626781078521716436337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80775751187385681144290891 121163626781078521716436337)
        ·
          refine ⟨90872720085808891287327253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121163626781078521716436337 90872720085808891287327253)
          ·
            refine ⟨4259658754022291779093465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 90872720085808891287327253 4259658754022291779093465)
            ·
              refine ⟨3194744065516718834320099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4259658754022291779093465 3194744065516718834320099)
              ·
                refine ⟨4792116098275078251480149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3194744065516718834320099 4792116098275078251480149)
                ·
                  refine ⟨56157610526661073259533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4792116098275078251480149 56157610526661073259533)
                  ·
                    rfl

theorem cell23_984299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 1, 8].length) (baseStart_984299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_984299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_984299 prefixEnd_984299 := by exact prefixLift 984299
  have htrace : WordTrace (prefixWord ++ tailWord_984299) baseStart_984299 baseEnd_984299 := by
    simpa [prefixWord, tailWord_984299, baseEnd_984299] using wordTrace_append hprefix tailTrace_984299
  have hstable : (prefixWord ++ tailWord_984299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984299).length < 2 ^ (prefixWord ++ tailWord_984299).sum := by decide
  have hdescent : baseEnd_984299 < baseStart_984299 := by decide
  rcases family_descends (prefixWord ++ tailWord_984299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984336 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 7, 5, 2]
def baseStart_984336 : Nat := 118140960795 + 984336 * 2 ^ 59
def prefixEnd_984336 : Nat := 4983230072969 + 3 ^ 40 * 984336 * 2
def baseEnd_984336 : Nat := 505437493524166014573127

theorem tailTrace_984336 : CollatzResearch.WordTrace tailWord_984336 prefixEnd_984336 505437493524166014573127 := by
  unfold tailWord_984336
  simp only [CollatzResearch.WordTrace]
  refine ⟨17950841680963129024946431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23934455574617505366595241 17950841680963129024946431)
  ·
    refine ⟨26926262521444693537419647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17950841680963129024946431 26926262521444693537419647)
    ·
      refine ⟨40389393782167040306129471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26926262521444693537419647 40389393782167040306129471)
      ·
        refine ⟨60584090673250560459194207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40389393782167040306129471 60584090673250560459194207)
        ·
          refine ⟨90876136009875840688791311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60584090673250560459194207 90876136009875840688791311)
          ·
            refine ⟨136314204014813761033186967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90876136009875840688791311 136314204014813761033186967)
            ·
              refine ⟨204471306022220641549780451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136314204014813761033186967 204471306022220641549780451)
              ·
                refine ⟨306706959033330962324670677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204471306022220641549780451 306706959033330962324670677)
                ·
                  refine ⟨7188444352343694429484469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 306706959033330962324670677 7188444352343694429484469)
                  ·
                    refine ⟨673916658032221352764169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7188444352343694429484469 673916658032221352764169)
                    ·
                      refine ⟨505437493524166014573127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 673916658032221352764169 505437493524166014573127)
                      ·
                        rfl

theorem cell23_984336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 7, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 7, 5, 2].length) (baseStart_984336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_984336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_984336 prefixEnd_984336 := by exact prefixLift 984336
  have htrace : WordTrace (prefixWord ++ tailWord_984336) baseStart_984336 baseEnd_984336 := by
    simpa [prefixWord, tailWord_984336, baseEnd_984336] using wordTrace_append hprefix tailTrace_984336
  have hstable : (prefixWord ++ tailWord_984336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984336).length < 2 ^ (prefixWord ++ tailWord_984336).sum := by decide
  have hdescent : baseEnd_984336 < baseStart_984336 := by decide
  rcases family_descends (prefixWord ++ tailWord_984336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984354 : List Nat := [3, 3, 1, 1, 4, 2, 2, 2, 1, 4]
def baseStart_984354 : Nat := 118140960795 + 984354 * 2 ^ 59
def prefixEnd_984354 : Nat := 4983230072969 + 3 ^ 40 * 984354 * 2
def baseEnd_984354 : Nat := 168482245391982314716015

theorem tailTrace_984354 : CollatzResearch.WordTrace tailWord_984354 prefixEnd_984354 168482245391982314716015 := by
  unfold tailWord_984354
  simp only [CollatzResearch.WordTrace]
  refine ⟨8975584968965261781012029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23934893250574031416032077 8975584968965261781012029)
  ·
    refine ⟨3365844363361973167879511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8975584968965261781012029 3365844363361973167879511)
    ·
      refine ⟨5048766545042959751819267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3365844363361973167879511 5048766545042959751819267)
      ·
        refine ⟨7573149817564439627728901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5048766545042959751819267 7573149817564439627728901)
        ·
          refine ⟨1419965590793332430199169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7573149817564439627728901 1419965590793332430199169)
          ·
            refine ⟨1064974193094999322649377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1419965590793332430199169 1064974193094999322649377)
            ·
              refine ⟨798730644821249491987033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1064974193094999322649377 798730644821249491987033)
              ·
                refine ⟨599047983615937118990275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 798730644821249491987033 599047983615937118990275)
                ·
                  refine ⟨898571975423905678485413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 599047983615937118990275 898571975423905678485413)
                  ·
                    refine ⟨168482245391982314716015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 898571975423905678485413 168482245391982314716015)
                    ·
                      rfl

theorem cell23_984354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 2, 2, 1, 4].length) (baseStart_984354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_984354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_984354 prefixEnd_984354 := by exact prefixLift 984354
  have htrace : WordTrace (prefixWord ++ tailWord_984354) baseStart_984354 baseEnd_984354 := by
    simpa [prefixWord, tailWord_984354, baseEnd_984354] using wordTrace_append hprefix tailTrace_984354
  have hstable : (prefixWord ++ tailWord_984354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984354).length < 2 ^ (prefixWord ++ tailWord_984354).sum := by decide
  have hdescent : baseEnd_984354 < baseStart_984354 := by decide
  rcases family_descends (prefixWord ++ tailWord_984354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984376 : List Nat := [2, 1, 2, 1, 3, 1, 1, 2, 6, 4]
def baseStart_984376 : Nat := 118140960795 + 984376 * 2 ^ 59
def prefixEnd_984376 : Nat := 4983230072969 + 3 ^ 40 * 984376 * 2
def baseEnd_984376 : Nat := 168486010916781952690981

theorem tailTrace_984376 : CollatzResearch.WordTrace tailWord_984376 prefixEnd_984376 168486010916781952690981 := by
  unfold tailWord_984376
  simp only [CollatzResearch.WordTrace]
  refine ⟨17951571140890672440674491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23935428187854229920899321 17951571140890672440674491)
  ·
    refine ⟨26927356711336008661011737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17951571140890672440674491 26927356711336008661011737)
    ·
      refine ⟨20195517533502006495758803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26927356711336008661011737 20195517533502006495758803)
      ·
        refine ⟨30293276300253009743638205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20195517533502006495758803 30293276300253009743638205)
        ·
          refine ⟨11359978612594878653864327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30293276300253009743638205 11359978612594878653864327)
          ·
            refine ⟨17039967918892317980796491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11359978612594878653864327 17039967918892317980796491)
            ·
              refine ⟨25559951878338476971194737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17039967918892317980796491 25559951878338476971194737)
              ·
                refine ⟨19169963908753857728396053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25559951878338476971194737 19169963908753857728396053)
                ·
                  refine ⟨898592058222837081018565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 19169963908753857728396053 898592058222837081018565)
                  ·
                    refine ⟨168486010916781952690981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 898592058222837081018565 168486010916781952690981)
                    ·
                      rfl

theorem cell23_984376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 6, 4].length) (baseStart_984376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_984376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_984376 prefixEnd_984376 := by exact prefixLift 984376
  have htrace : WordTrace (prefixWord ++ tailWord_984376) baseStart_984376 baseEnd_984376 := by
    simpa [prefixWord, tailWord_984376, baseEnd_984376] using wordTrace_append hprefix tailTrace_984376
  have hstable : (prefixWord ++ tailWord_984376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984376).length < 2 ^ (prefixWord ++ tailWord_984376).sum := by decide
  have hdescent : baseEnd_984376 < baseStart_984376 := by decide
  rcases family_descends (prefixWord ++ tailWord_984376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984379 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 7, 1, 6]
def baseStart_984379 : Nat := 118140960795 + 984379 * 2 ^ 59
def prefixEnd_984379 : Nat := 4983230072969 + 3 ^ 40 * 984379 * 2
def baseEnd_984379 : Nat := 505459573192309346335429

theorem tailTrace_984379 : CollatzResearch.WordTrace tailWord_984379 prefixEnd_984379 505459573192309346335429 := by
  unfold tailWord_984379
  simp only [CollatzResearch.WordTrace]
  refine ⟨35903251700770476393708191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23935501133846984262472127 35903251700770476393708191)
  ·
    refine ⟨53854877551155714590562287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35903251700770476393708191 53854877551155714590562287)
    ·
      refine ⟨80782316326733571885843431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53854877551155714590562287 80782316326733571885843431)
      ·
        refine ⟨121173474490100357828765147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80782316326733571885843431 121173474490100357828765147)
        ·
          refine ⟨181760211735150536743147721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121173474490100357828765147 181760211735150536743147721)
          ·
            refine ⟨136320158801362902557360791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181760211735150536743147721 136320158801362902557360791)
            ·
              refine ⟨204480238202044353836041187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136320158801362902557360791 204480238202044353836041187)
              ·
                refine ⟨306720357303066530754061781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204480238202044353836041187 306720357303066530754061781)
                ·
                  refine ⟨7188758374290621814548323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 306720357303066530754061781 7188758374290621814548323)
                  ·
                    refine ⟨10783137561435932721822485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7188758374290621814548323 10783137561435932721822485)
                    ·
                      refine ⟨505459573192309346335429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10783137561435932721822485 505459573192309346335429)
                      ·
                        rfl

theorem cell23_984379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 7, 1, 6].length) (baseStart_984379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_984379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_984379 prefixEnd_984379 := by exact prefixLift 984379
  have htrace : WordTrace (prefixWord ++ tailWord_984379) baseStart_984379 baseEnd_984379 := by
    simpa [prefixWord, tailWord_984379, baseEnd_984379] using wordTrace_append hprefix tailTrace_984379
  have hstable : (prefixWord ++ tailWord_984379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984379).length < 2 ^ (prefixWord ++ tailWord_984379).sum := by decide
  have hdescent : baseEnd_984379 < baseStart_984379 := by decide
  rcases family_descends (prefixWord ++ tailWord_984379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984389 : List Nat := [1, 3, 1, 1, 1, 2, 1, 13]
def baseStart_984389 : Nat := 118140960795 + 984389 * 2 ^ 59
def prefixEnd_984389 : Nat := 4983230072969 + 3 ^ 40 * 984389 * 2
def baseEnd_984389 : Nat := 18720915111068678044829

theorem tailTrace_984389 : CollatzResearch.WordTrace tailWord_984389 prefixEnd_984389 18720915111068678044829 := by
  unfold tailWord_984389
  simp only [CollatzResearch.WordTrace]
  refine ⟨35903616430734248101572221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23935744287156165401048147 35903616430734248101572221)
  ·
    refine ⟨13463856161525343038089583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35903616430734248101572221 13463856161525343038089583)
    ·
      refine ⟨20195784242288014557134375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13463856161525343038089583 20195784242288014557134375)
      ·
        refine ⟨30293676363432021835701563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20195784242288014557134375 30293676363432021835701563)
        ·
          refine ⟨45440514545148032753552345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30293676363432021835701563 45440514545148032753552345)
          ·
            refine ⟨34080385908861024565164259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45440514545148032753552345 34080385908861024565164259)
            ·
              refine ⟨51120578863291536847746389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34080385908861024565164259 51120578863291536847746389)
              ·
                refine ⟨18720915111068678044829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 51120578863291536847746389 18720915111068678044829)
                ·
                  rfl

theorem cell23_984389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 13].length) (baseStart_984389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_984389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_984389 prefixEnd_984389 := by exact prefixLift 984389
  have htrace : WordTrace (prefixWord ++ tailWord_984389) baseStart_984389 baseEnd_984389 := by
    simpa [prefixWord, tailWord_984389, baseEnd_984389] using wordTrace_append hprefix tailTrace_984389
  have hstable : (prefixWord ++ tailWord_984389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984389).length < 2 ^ (prefixWord ++ tailWord_984389).sum := by decide
  have hdescent : baseEnd_984389 < baseStart_984389 := by decide
  rcases family_descends (prefixWord ++ tailWord_984389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984397 : List Nat := [1, 6, 1, 3, 1, 1, 1, 3, 1, 5]
def baseStart_984397 : Nat := 118140960795 + 984397 * 2 ^ 59
def prefixEnd_984397 : Nat := 4983230072969 + 3 ^ 40 * 984397 * 2
def baseEnd_984397 : Nat := 168489605281363425303449

theorem tailTrace_984397 : CollatzResearch.WordTrace tailWord_984397 prefixEnd_984397 168489605281363425303449 := by
  unfold tailWord_984397
  simp only [CollatzResearch.WordTrace]
  refine ⟨35903908214705265467863445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23935938809803510311908963 35903908214705265467863445)
  ·
    refine ⟨1682995697564309318806099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 35903908214705265467863445 1682995697564309318806099)
    ·
      refine ⟨2524493546346463978209149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1682995697564309318806099 2524493546346463978209149)
      ·
        refine ⟨946685079879923991828431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2524493546346463978209149 946685079879923991828431)
        ·
          refine ⟨1420027619819885987742647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 946685079879923991828431 1420027619819885987742647)
          ·
            refine ⟨2130041429729828981613971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1420027619819885987742647 2130041429729828981613971)
            ·
              refine ⟨3195062144594743472420957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2130041429729828981613971 3195062144594743472420957)
              ·
                refine ⟨1198148304223028802157859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3195062144594743472420957 1198148304223028802157859)
                ·
                  refine ⟨1797222456334543203236789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1198148304223028802157859 1797222456334543203236789)
                  ·
                    refine ⟨168489605281363425303449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1797222456334543203236789 168489605281363425303449)
                    ·
                      rfl

theorem cell23_984397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_984397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_984397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_984397 prefixEnd_984397 := by exact prefixLift 984397
  have htrace : WordTrace (prefixWord ++ tailWord_984397) baseStart_984397 baseEnd_984397 := by
    simpa [prefixWord, tailWord_984397, baseEnd_984397] using wordTrace_append hprefix tailTrace_984397
  have hstable : (prefixWord ++ tailWord_984397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984397).length < 2 ^ (prefixWord ++ tailWord_984397).sum := by decide
  have hdescent : baseEnd_984397 < baseStart_984397 := by decide
  rcases family_descends (prefixWord ++ tailWord_984397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984399 : List Nat := [1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 7]
def baseStart_984399 : Nat := 118140960795 + 984399 * 2 ^ 59
def prefixEnd_984399 : Nat := 4983230072969 + 3 ^ 40 * 984399 * 2
def baseEnd_984399 : Nat := 505469842805399268085337

theorem tailTrace_984399 : CollatzResearch.WordTrace tailWord_984399 prefixEnd_984399 505469842805399268085337 := by
  unfold tailWord_984399
  simp only [CollatzResearch.WordTrace]
  refine ⟨35903981160698019809436251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23935987440465346539624167 35903981160698019809436251)
  ·
    refine ⟨53855971741047029714154377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35903981160698019809436251 53855971741047029714154377)
    ·
      refine ⟨40391978805785272285615783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53855971741047029714154377 40391978805785272285615783)
      ·
        refine ⟨60587968208677908428423675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40391978805785272285615783 60587968208677908428423675)
        ·
          refine ⟨90881952313016862642635513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60587968208677908428423675 90881952313016862642635513)
          ·
            refine ⟨68161464234762646981976635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90881952313016862642635513 68161464234762646981976635)
            ·
              refine ⟨102242196352143970472964953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68161464234762646981976635 102242196352143970472964953)
              ·
                refine ⟨76681647264107977854723715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102242196352143970472964953 76681647264107977854723715)
                ·
                  refine ⟨115022470896161966782085573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76681647264107977854723715 115022470896161966782085573)
                  ·
                    refine ⟨21566713293030368771641045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 115022470896161966782085573 21566713293030368771641045)
                    ·
                      refine ⟨505469842805399268085337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 21566713293030368771641045 505469842805399268085337)
                      ·
                        rfl

theorem cell23_984399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 7].length) (baseStart_984399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_984399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_984399 prefixEnd_984399 := by exact prefixLift 984399
  have htrace : WordTrace (prefixWord ++ tailWord_984399) baseStart_984399 baseEnd_984399 := by
    simpa [prefixWord, tailWord_984399, baseEnd_984399] using wordTrace_append hprefix tailTrace_984399
  have hstable : (prefixWord ++ tailWord_984399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984399).length < 2 ^ (prefixWord ++ tailWord_984399).sum := by decide
  have hdescent : baseEnd_984399 < baseStart_984399 := by decide
  rcases family_descends (prefixWord ++ tailWord_984399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984403 : List Nat := [1, 1, 1, 2, 1, 1, 7, 3, 1, 2, 3]
def baseStart_984403 : Nat := 118140960795 + 984403 * 2 ^ 59
def prefixEnd_984403 : Nat := 4983230072969 + 3 ^ 40 * 984403 * 2
def baseEnd_984403 : Nat := 505471896728017252435319

theorem tailTrace_984403 : CollatzResearch.WordTrace tailWord_984403 prefixEnd_984403 505471896728017252435319 := by
  unfold tailWord_984403
  simp only [CollatzResearch.WordTrace]
  refine ⟨35904127052683528492581863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23936084701789018995054575 35904127052683528492581863)
  ·
    refine ⟨53856190579025292738872795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35904127052683528492581863 53856190579025292738872795)
    ·
      refine ⟨80784285868537939108309193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53856190579025292738872795 80784285868537939108309193)
      ·
        refine ⟨60588214401403454331231895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80784285868537939108309193 60588214401403454331231895)
        ·
          refine ⟨90882321602105181496847843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60588214401403454331231895 90882321602105181496847843)
          ·
            refine ⟨136323482403157772245271765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90882321602105181496847843 136323482403157772245271765)
            ·
              refine ⟨3195081618824010286998557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 136323482403157772245271765 3195081618824010286998557)
              ·
                refine ⟨1198155607059003857624459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3195081618824010286998557 1198155607059003857624459)
                ·
                  refine ⟨1797233410588505786436689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1198155607059003857624459 1797233410588505786436689)
                  ·
                    refine ⟨1347925057941379339827517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1797233410588505786436689 1347925057941379339827517)
                    ·
                      refine ⟨505471896728017252435319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1347925057941379339827517 505471896728017252435319)
                      ·
                        rfl

theorem cell23_984403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 3, 1, 2, 3].length) (baseStart_984403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_984403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_984403 prefixEnd_984403 := by exact prefixLift 984403
  have htrace : WordTrace (prefixWord ++ tailWord_984403) baseStart_984403 baseEnd_984403 := by
    simpa [prefixWord, tailWord_984403, baseEnd_984403] using wordTrace_append hprefix tailTrace_984403
  have hstable : (prefixWord ++ tailWord_984403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984403).length < 2 ^ (prefixWord ++ tailWord_984403).sum := by decide
  have hdescent : baseEnd_984403 < baseStart_984403 := by decide
  rcases family_descends (prefixWord ++ tailWord_984403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984430 : List Nat := [4, 1, 2, 4, 1, 1, 1, 1, 1, 1, 6]
def baseStart_984430 : Nat := 118140960795 + 984430 * 2 ^ 59
def prefixEnd_984430 : Nat := 4983230072969 + 3 ^ 40 * 984430 * 2
def baseEnd_984430 : Nat := 505485760705688646797695

theorem tailTrace_984430 : CollatzResearch.WordTrace tailWord_984430 prefixEnd_984430 505485760705688646797695 := by
  unfold tailWord_984430
  simp only [CollatzResearch.WordTrace]
  refine ⟨4488138977948214012976843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23936741215723808069209829 4488138977948214012976843)
  ·
    refine ⟨6732208466922321019465265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4488138977948214012976843 6732208466922321019465265)
    ·
      refine ⟨5049156350191740764598949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6732208466922321019465265 5049156350191740764598949)
      ·
        refine ⟨946716815660951393362303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5049156350191740764598949 946716815660951393362303)
        ·
          refine ⟨1420075223491427090043455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 946716815660951393362303 1420075223491427090043455)
          ·
            refine ⟨2130112835237140635065183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1420075223491427090043455 2130112835237140635065183)
            ·
              refine ⟨3195169252855710952597775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2130112835237140635065183 3195169252855710952597775)
              ·
                refine ⟨4792753879283566428896663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3195169252855710952597775 4792753879283566428896663)
                ·
                  refine ⟨7189130818925349643344995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4792753879283566428896663 7189130818925349643344995)
                  ·
                    refine ⟨10783696228388024465017493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7189130818925349643344995 10783696228388024465017493)
                    ·
                      refine ⟨505485760705688646797695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10783696228388024465017493 505485760705688646797695)
                      ·
                        rfl

theorem cell23_984430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_984430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_984430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_984430 prefixEnd_984430 := by exact prefixLift 984430
  have htrace : WordTrace (prefixWord ++ tailWord_984430) baseStart_984430 baseEnd_984430 := by
    simpa [prefixWord, tailWord_984430, baseEnd_984430] using wordTrace_append hprefix tailTrace_984430
  have hstable : (prefixWord ++ tailWord_984430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984430).length < 2 ^ (prefixWord ++ tailWord_984430).sum := by decide
  have hdescent : baseEnd_984430 < baseStart_984430 := by decide
  rcases family_descends (prefixWord ++ tailWord_984430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984433 : List Nat := [1, 2, 2, 2, 1, 2, 5, 1, 1, 3, 3]
def baseStart_984433 : Nat := 118140960795 + 984433 * 2 ^ 59
def prefixEnd_984433 : Nat := 4983230072969 + 3 ^ 40 * 984433 * 2
def baseEnd_984433 : Nat := 505487301147652135060181

theorem tailTrace_984433 : CollatzResearch.WordTrace tailWord_984433 prefixEnd_984433 505487301147652135060181 := by
  unfold tailWord_984433
  simp only [CollatzResearch.WordTrace]
  refine ⟨35905221242574843616173953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23936814161716562410782635 35905221242574843616173953)
  ·
    refine ⟨26928915931931132712130465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35905221242574843616173953 26928915931931132712130465)
    ·
      refine ⟨20196686948948349534097849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26928915931931132712130465 20196686948948349534097849)
      ·
        refine ⟨15147515211711262150573387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20196686948948349534097849 15147515211711262150573387)
        ·
          refine ⟨22721272817566893225860081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15147515211711262150573387 22721272817566893225860081)
          ·
            refine ⟨17040954613175169919395061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22721272817566893225860081 17040954613175169919395061)
            ·
              refine ⟨1597589494985172179943287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17040954613175169919395061 1597589494985172179943287)
              ·
                refine ⟨2396384242477758269914931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1597589494985172179943287 2396384242477758269914931)
                ·
                  refine ⟨3594576363716637404872397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2396384242477758269914931 3594576363716637404872397)
                  ·
                    refine ⟨1347966136393739026827149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3594576363716637404872397 1347966136393739026827149)
                    ·
                      refine ⟨505487301147652135060181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1347966136393739026827149 505487301147652135060181)
                      ·
                        rfl

theorem cell23_984433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 1, 1, 3, 3].length) (baseStart_984433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_984433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_984433 prefixEnd_984433 := by exact prefixLift 984433
  have htrace : WordTrace (prefixWord ++ tailWord_984433) baseStart_984433 baseEnd_984433 := by
    simpa [prefixWord, tailWord_984433, baseEnd_984433] using wordTrace_append hprefix tailTrace_984433
  have hstable : (prefixWord ++ tailWord_984433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984433).length < 2 ^ (prefixWord ++ tailWord_984433).sum := by decide
  have hdescent : baseEnd_984433 < baseStart_984433 := by decide
  rcases family_descends (prefixWord ++ tailWord_984433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984437 : List Nat := [1, 3, 4, 1, 3, 1, 2, 2, 1, 2, 3]
def baseStart_984437 : Nat := 118140960795 + 984437 * 2 ^ 59
def prefixEnd_984437 : Nat := 4983230072969 + 3 ^ 40 * 984437 * 2
def baseEnd_984437 : Nat := 505489355070270119410163

theorem tailTrace_984437 : CollatzResearch.WordTrace tailWord_984437 prefixEnd_984437 505489355070270119410163 := by
  unfold tailWord_984437
  simp only [CollatzResearch.WordTrace]
  refine ⟨35905367134560352299319565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23936911423040234866213043 35905367134560352299319565)
  ·
    refine ⟨13464512675460132112244837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35905367134560352299319565 13464512675460132112244837)
    ·
      refine ⟨2524596126648774771045907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13464512675460132112244837 2524596126648774771045907)
      ·
        refine ⟨3786894189973162156568861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2524596126648774771045907 3786894189973162156568861)
        ·
          refine ⟨1420085321239935808713323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3786894189973162156568861 1420085321239935808713323)
          ·
            refine ⟨2130127981859903713069985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1420085321239935808713323 2130127981859903713069985)
            ·
              refine ⟨1597595986394927784802489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2130127981859903713069985 1597595986394927784802489)
              ·
                refine ⟨1198196989796195838601867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1597595986394927784802489 1198196989796195838601867)
                ·
                  refine ⟨1797295484694293757902801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1198196989796195838601867 1797295484694293757902801)
                  ·
                    refine ⟨1347971613520720318427101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1797295484694293757902801 1347971613520720318427101)
                    ·
                      refine ⟨505489355070270119410163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1347971613520720318427101 505489355070270119410163)
                      ·
                        rfl

theorem cell23_984437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_984437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_984437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_984437 prefixEnd_984437 := by exact prefixLift 984437
  have htrace : WordTrace (prefixWord ++ tailWord_984437) baseStart_984437 baseEnd_984437 := by
    simpa [prefixWord, tailWord_984437, baseEnd_984437] using wordTrace_append hprefix tailTrace_984437
  have hstable : (prefixWord ++ tailWord_984437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984437).length < 2 ^ (prefixWord ++ tailWord_984437).sum := by decide
  have hdescent : baseEnd_984437 < baseStart_984437 := by decide
  rcases family_descends (prefixWord ++ tailWord_984437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984460 : List Nat := [2, 2, 1, 2, 1, 3, 1, 5, 1, 3, 2]
def baseStart_984460 : Nat := 118140960795 + 984460 * 2 ^ 59
def prefixEnd_984460 : Nat := 4983230072969 + 3 ^ 40 * 984460 * 2
def baseEnd_984460 : Nat := 505501165125323529422557

theorem tailTrace_984460 : CollatzResearch.WordTrace tailWord_984460 prefixEnd_984460 505501165125323529422557 := by
  unfold tailWord_984460
  simp only [CollatzResearch.WordTrace]
  refine ⟨17953103006738513613703417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23937470675651351484937889 17953103006738513613703417)
  ·
    refine ⟨13464827255053885210277563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17953103006738513613703417 13464827255053885210277563)
    ·
      refine ⟨20197240882580827815416345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13464827255053885210277563 20197240882580827815416345)
      ·
        refine ⟨15147930661935620861562259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20197240882580827815416345 15147930661935620861562259)
        ·
          refine ⟨22721895992903431292343389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15147930661935620861562259 22721895992903431292343389)
          ·
            refine ⟨8520710997338786734628771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22721895992903431292343389 8520710997338786734628771)
            ·
              refine ⟨12781066496008180101943157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8520710997338786734628771 12781066496008180101943157)
              ·
                refine ⟨1198224984000766884557171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12781066496008180101943157 1198224984000766884557171)
                ·
                  refine ⟨1797337476001150326835757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1198224984000766884557171 1797337476001150326835757)
                  ·
                    refine ⟨674001553500431372563409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1797337476001150326835757 674001553500431372563409)
                    ·
                      refine ⟨505501165125323529422557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 674001553500431372563409 505501165125323529422557)
                      ·
                        rfl

theorem cell23_984460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 5, 1, 3, 2].length) (baseStart_984460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_984460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_984460 prefixEnd_984460 := by exact prefixLift 984460
  have htrace : WordTrace (prefixWord ++ tailWord_984460) baseStart_984460 baseEnd_984460 := by
    simpa [prefixWord, tailWord_984460, baseEnd_984460] using wordTrace_append hprefix tailTrace_984460
  have hstable : (prefixWord ++ tailWord_984460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984460).length < 2 ^ (prefixWord ++ tailWord_984460).sum := by decide
  have hdescent : baseEnd_984460 < baseStart_984460 := by decide
  rcases family_descends (prefixWord ++ tailWord_984460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984524 : List Nat := [2, 2, 1, 4, 2, 2, 2, 2, 2, 2, 2]
def baseStart_984524 : Nat := 118140960795 + 984524 * 2 ^ 59
def prefixEnd_984524 : Nat := 4983230072969 + 3 ^ 40 * 984524 * 2
def baseEnd_984524 : Nat := 505534027887211279022263

theorem tailTrace_984524 : CollatzResearch.WordTrace tailWord_984524 prefixEnd_984524 505534027887211279022263 := by
  unfold tailWord_984524
  simp only [CollatzResearch.WordTrace]
  refine ⟨17954270142622583078868313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23939026856830110771824417 17954270142622583078868313)
  ·
    refine ⟨13465702606966937309151235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17954270142622583078868313 13465702606966937309151235)
    ·
      refine ⟨20198553910450405963726853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13465702606966937309151235 20198553910450405963726853)
      ·
        refine ⟨3787228858209451118198785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20198553910450405963726853 3787228858209451118198785)
        ·
          refine ⟨2840421643657088338649089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3787228858209451118198785 2840421643657088338649089)
          ·
            refine ⟨2130316232742816253986817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2840421643657088338649089 2130316232742816253986817)
            ·
              refine ⟨1597737174557112190490113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2130316232742816253986817 1597737174557112190490113)
              ·
                refine ⟨1198302880917834142867585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1597737174557112190490113 1198302880917834142867585)
                ·
                  refine ⟨898727160688375607150689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1198302880917834142867585 898727160688375607150689)
                  ·
                    refine ⟨674045370516281705363017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 898727160688375607150689 674045370516281705363017)
                    ·
                      refine ⟨505534027887211279022263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 674045370516281705363017 505534027887211279022263)
                      ·
                        rfl

theorem cell23_984524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 2, 2, 2, 2].length) (baseStart_984524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_984524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_984524 prefixEnd_984524 := by exact prefixLift 984524
  have htrace : WordTrace (prefixWord ++ tailWord_984524) baseStart_984524 baseEnd_984524 := by
    simpa [prefixWord, tailWord_984524, baseEnd_984524] using wordTrace_append hprefix tailTrace_984524
  have hstable : (prefixWord ++ tailWord_984524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984524).length < 2 ^ (prefixWord ++ tailWord_984524).sum := by decide
  have hdescent : baseEnd_984524 < baseStart_984524 := by decide
  rcases family_descends (prefixWord ++ tailWord_984524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984556 : List Nat := [2, 2, 1, 1, 2, 1, 2, 1, 1, 10]
def baseStart_984556 : Nat := 118140960795 + 984556 * 2 ^ 59
def prefixEnd_984556 : Nat := 4983230072969 + 3 ^ 40 * 984556 * 2
def baseEnd_984556 : Nat := 168516819756051717940705

theorem tailTrace_984556 : CollatzResearch.WordTrace tailWord_984556 prefixEnd_984556 168516819756051717940705 := by
  unfold tailWord_984556
  simp only [CollatzResearch.WordTrace]
  refine ⟨17954853710564617811450761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23939804947419490415267681 17954853710564617811450761)
  ·
    refine ⟨13466140282923463358588071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17954853710564617811450761 13466140282923463358588071)
    ·
      refine ⟨20199210424385195037882107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13466140282923463358588071 20199210424385195037882107)
      ·
        refine ⟨30298815636577792556823161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20199210424385195037882107 30298815636577792556823161)
        ·
          refine ⟨22724111727433344417617371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30298815636577792556823161 22724111727433344417617371)
          ·
            refine ⟨34086167591150016626426057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22724111727433344417617371 34086167591150016626426057)
            ·
              refine ⟨25564625693362512469819543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34086167591150016626426057 25564625693362512469819543)
              ·
                refine ⟨38346938540043768704729315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25564625693362512469819543 38346938540043768704729315)
                ·
                  refine ⟨57520407810065653057093973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38346938540043768704729315 57520407810065653057093973)
                  ·
                    refine ⟨168516819756051717940705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 57520407810065653057093973 168516819756051717940705)
                    ·
                      rfl

theorem cell23_984556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 10].length) (baseStart_984556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_984556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_984556 prefixEnd_984556 := by exact prefixLift 984556
  have htrace : WordTrace (prefixWord ++ tailWord_984556) baseStart_984556 baseEnd_984556 := by
    simpa [prefixWord, tailWord_984556, baseEnd_984556] using wordTrace_append hprefix tailTrace_984556
  have hstable : (prefixWord ++ tailWord_984556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984556).length < 2 ^ (prefixWord ++ tailWord_984556).sum := by decide
  have hdescent : baseEnd_984556 < baseStart_984556 := by decide
  rcases family_descends (prefixWord ++ tailWord_984556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984560 : List Nat := [2, 1, 1, 1, 3, 6, 1, 1, 2, 5]
def baseStart_984560 : Nat := 118140960795 + 984560 * 2 ^ 59
def prefixEnd_984560 : Nat := 4983230072969 + 3 ^ 40 * 984560 * 2
def baseEnd_984560 : Nat := 168517504396924379390699

theorem tailTrace_984560 : CollatzResearch.WordTrace tailWord_984560 prefixEnd_984560 168517504396924379390699 := by
  unfold tailWord_984560
  simp only [CollatzResearch.WordTrace]
  refine ⟨17954926656557372153023567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23939902208743162870698089 17954926656557372153023567)
  ·
    refine ⟨26932389984836058229535351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17954926656557372153023567 26932389984836058229535351)
    ·
      refine ⟨40398584977254087344303027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26932389984836058229535351 40398584977254087344303027)
      ·
        refine ⟨60597877465881131016454541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40398584977254087344303027 60597877465881131016454541)
        ·
          refine ⟨22724204049705424131170453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60597877465881131016454541 22724204049705424131170453)
          ·
            refine ⟨1065197064829941756148615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 22724204049705424131170453 1065197064829941756148615)
            ·
              refine ⟨1597795597244912634222923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1065197064829941756148615 1597795597244912634222923)
              ·
                refine ⟨2396693395867368951334385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1597795597244912634222923 2396693395867368951334385)
                ·
                  refine ⟨1797520046900526713500789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2396693395867368951334385 1797520046900526713500789)
                  ·
                    refine ⟨168517504396924379390699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1797520046900526713500789 168517504396924379390699)
                    ·
                      rfl

theorem cell23_984560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 1, 2, 5].length) (baseStart_984560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_984560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_984560 prefixEnd_984560 := by exact prefixLift 984560
  have htrace : WordTrace (prefixWord ++ tailWord_984560) baseStart_984560 baseEnd_984560 := by
    simpa [prefixWord, tailWord_984560, baseEnd_984560] using wordTrace_append hprefix tailTrace_984560
  have hstable : (prefixWord ++ tailWord_984560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984560).length < 2 ^ (prefixWord ++ tailWord_984560).sum := by decide
  have hdescent : baseEnd_984560 < baseStart_984560 := by decide
  rcases family_descends (prefixWord ++ tailWord_984560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984563 : List Nat := [1, 1, 1, 2, 2, 2, 2, 5, 2, 1, 4]
def baseStart_984563 : Nat := 118140960795 + 984563 * 2 ^ 59
def prefixEnd_984563 : Nat := 4983230072969 + 3 ^ 40 * 984563 * 2
def baseEnd_984563 : Nat := 505554053632736626434583

theorem tailTrace_984563 : CollatzResearch.WordTrace tailWord_984563 prefixEnd_984563 505554053632736626434583 := by
  unfold tailWord_984563
  simp only [CollatzResearch.WordTrace]
  refine ⟨35909962732103875818406343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23939975154735917212270895 35909962732103875818406343)
  ·
    refine ⟨53864944098155813727609515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35909962732103875818406343 53864944098155813727609515)
    ·
      refine ⟨80797416147233720591414273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53864944098155813727609515 80797416147233720591414273)
      ·
        refine ⟨60598062110425290443560705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80797416147233720591414273 60598062110425290443560705)
        ·
          refine ⟨45448546582818967832670529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60598062110425290443560705 45448546582818967832670529)
          ·
            refine ⟨34086409937114225874502897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45448546582818967832670529 34086409937114225874502897)
            ·
              refine ⟨25564807452835669405877173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34086409937114225874502897 25564807452835669405877173)
              ·
                refine ⟨2396700698703344006800985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25564807452835669405877173 2396700698703344006800985)
                ·
                  refine ⟨1797525524027508005100739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2396700698703344006800985 1797525524027508005100739)
                  ·
                    refine ⟨2696288286041262007651109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1797525524027508005100739 2696288286041262007651109)
                    ·
                      refine ⟨505554053632736626434583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2696288286041262007651109 505554053632736626434583)
                      ·
                        rfl

theorem cell23_984563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5, 2, 1, 4].length) (baseStart_984563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_984563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_984563 prefixEnd_984563 := by exact prefixLift 984563
  have htrace : WordTrace (prefixWord ++ tailWord_984563) baseStart_984563 baseEnd_984563 := by
    simpa [prefixWord, tailWord_984563, baseEnd_984563] using wordTrace_append hprefix tailTrace_984563
  have hstable : (prefixWord ++ tailWord_984563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984563).length < 2 ^ (prefixWord ++ tailWord_984563).sum := by decide
  have hdescent : baseEnd_984563 < baseStart_984563 := by decide
  rcases family_descends (prefixWord ++ tailWord_984563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984613 : List Nat := [1, 3, 1, 2, 2, 1, 1, 1, 1, 7, 3]
def baseStart_984613 : Nat := 118140960795 + 984613 * 2 ^ 59
def prefixEnd_984613 : Nat := 4983230072969 + 3 ^ 40 * 984613 * 2
def baseEnd_984613 : Nat := 505579727665461430809353

theorem tailTrace_984613 : CollatzResearch.WordTrace tailWord_984613 prefixEnd_984613 505579727665461430809353 := by
  unfold tailWord_984613
  simp only [CollatzResearch.WordTrace]
  refine ⟨35911786381922734357726493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23941190921281822905150995 35911786381922734357726493)
  ·
    refine ⟨13466919893221025384147435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35911786381922734357726493 13466919893221025384147435)
    ·
      refine ⟨20200379839831538076221153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13466919893221025384147435 20200379839831538076221153)
      ·
        refine ⟨15150284879873653557165865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20200379839831538076221153 15150284879873653557165865)
        ·
          refine ⟨11362713659905240167874399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15150284879873653557165865 11362713659905240167874399)
          ·
            refine ⟨17044070489857860251811599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11362713659905240167874399 17044070489857860251811599)
            ·
              refine ⟨25566105734786790377717399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17044070489857860251811599 25566105734786790377717399)
              ·
                refine ⟨38349158602180185566576099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25566105734786790377717399 38349158602180185566576099)
                ·
                  refine ⟨57523737903270278349864149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38349158602180185566576099 57523737903270278349864149)
                  ·
                    refine ⟨1348212607107897148824941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57523737903270278349864149 1348212607107897148824941)
                    ·
                      refine ⟨505579727665461430809353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1348212607107897148824941 505579727665461430809353)
                      ·
                        rfl

theorem cell23_984613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 7, 3].length) (baseStart_984613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_984613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_984613 prefixEnd_984613 := by exact prefixLift 984613
  have htrace : WordTrace (prefixWord ++ tailWord_984613) baseStart_984613 baseEnd_984613 := by
    simpa [prefixWord, tailWord_984613, baseEnd_984613] using wordTrace_append hprefix tailTrace_984613
  have hstable : (prefixWord ++ tailWord_984613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984613).length < 2 ^ (prefixWord ++ tailWord_984613).sum := by decide
  have hdescent : baseEnd_984613 < baseStart_984613 := by decide
  rcases family_descends (prefixWord ++ tailWord_984613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984680 : List Nat := [2, 1, 4, 3, 1, 1, 1, 1, 3, 6]
def baseStart_984680 : Nat := 118140960795 + 984680 * 2 ^ 59
def prefixEnd_984680 : Nat := 4983230072969 + 3 ^ 40 * 984680 * 2
def baseEnd_984680 : Nat := 168538043623104222890515

theorem tailTrace_984680 : CollatzResearch.WordTrace tailWord_984680 prefixEnd_984680 168538043623104222890515 := by
  unfold tailWord_984680
  simp only [CollatzResearch.WordTrace]
  refine ⟨17957115036340002400207747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23942820048453336533610329 17957115036340002400207747)
  ·
    refine ⟨26935672554510003600311621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17957115036340002400207747 26935672554510003600311621)
    ·
      refine ⟨5050438603970625675058429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26935672554510003600311621 5050438603970625675058429)
      ·
        refine ⟨1893914476488984628146911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5050438603970625675058429 1893914476488984628146911)
        ·
          refine ⟨2840871714733476942220367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1893914476488984628146911 2840871714733476942220367)
          ·
            refine ⟨4261307572100215413330551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2840871714733476942220367 4261307572100215413330551)
            ·
              refine ⟨6391961358150323119995827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4261307572100215413330551 6391961358150323119995827)
              ·
                refine ⟨9587942037225484679993741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6391961358150323119995827 9587942037225484679993741)
                ·
                  refine ⟨3595478263959556754997653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9587942037225484679993741 3595478263959556754997653)
                  ·
                    refine ⟨168538043623104222890515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3595478263959556754997653 168538043623104222890515)
                    ·
                      rfl

theorem cell23_984680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 3, 6].length) (baseStart_984680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_984680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_984680 prefixEnd_984680 := by exact prefixLift 984680
  have htrace : WordTrace (prefixWord ++ tailWord_984680) baseStart_984680 baseEnd_984680 := by
    simpa [prefixWord, tailWord_984680, baseEnd_984680] using wordTrace_append hprefix tailTrace_984680
  have hstable : (prefixWord ++ tailWord_984680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984680).length < 2 ^ (prefixWord ++ tailWord_984680).sum := by decide
  have hdescent : baseEnd_984680 < baseStart_984680 := by decide
  rcases family_descends (prefixWord ++ tailWord_984680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984697 : List Nat := [1, 2, 1, 3, 3, 1, 4, 2, 2, 4]
def baseStart_984697 : Nat := 118140960795 + 984697 * 2 ^ 59
def prefixEnd_984697 : Nat := 4983230072969 + 3 ^ 40 * 984697 * 2
def baseEnd_984697 : Nat := 168540953346813034052989

theorem tailTrace_984697 : CollatzResearch.WordTrace tailWord_984697 prefixEnd_984697 168540953346813034052989 := by
  unfold tailWord_984697
  simp only [CollatzResearch.WordTrace]
  refine ⟨35914850113618416703784345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23943233409078944469189563 35914850113618416703784345)
  ·
    refine ⟨26936137585213812527838259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35914850113618416703784345 26936137585213812527838259)
    ·
      refine ⟨40404206377820718791757389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26936137585213812527838259 40404206377820718791757389)
      ·
        refine ⟨15151577391682769546909021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40404206377820718791757389 15151577391682769546909021)
        ·
          refine ⟨5681841521881038580090883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15151577391682769546909021 5681841521881038580090883)
          ·
            refine ⟨8522762282821557870136325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5681841521881038580090883 8522762282821557870136325)
            ·
              refine ⟨1598017928029042100650561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8522762282821557870136325 1598017928029042100650561)
              ·
                refine ⟨1198513446021781575487921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1598017928029042100650561 1198513446021781575487921)
                ·
                  refine ⟨898885084516336181615941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1198513446021781575487921 898885084516336181615941)
                  ·
                    refine ⟨168540953346813034052989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 898885084516336181615941 168540953346813034052989)
                    ·
                      rfl

theorem cell23_984697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 2, 2, 4].length) (baseStart_984697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_984697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_984697 prefixEnd_984697 := by exact prefixLift 984697
  have htrace : WordTrace (prefixWord ++ tailWord_984697) baseStart_984697 baseEnd_984697 := by
    simpa [prefixWord, tailWord_984697, baseEnd_984697] using wordTrace_append hprefix tailTrace_984697
  have hstable : (prefixWord ++ tailWord_984697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984697).length < 2 ^ (prefixWord ++ tailWord_984697).sum := by decide
  have hdescent : baseEnd_984697 < baseStart_984697 := by decide
  rcases family_descends (prefixWord ++ tailWord_984697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984713 : List Nat := [1, 2, 1, 1, 4, 1, 2, 1, 2, 2, 6]
def baseStart_984713 : Nat := 118140960795 + 984713 * 2 ^ 59
def prefixEnd_984713 : Nat := 4983230072969 + 3 ^ 40 * 984713 * 2
def baseEnd_984713 : Nat := 505631075730911039558893

theorem tailTrace_984713 : CollatzResearch.WordTrace tailWord_984713 prefixEnd_984713 505631075730911039558893 := by
  unfold tailWord_984713
  simp only [CollatzResearch.WordTrace]
  refine ⟨35915433681560451436366793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23943622454373634290911195 35915433681560451436366793)
  ·
    refine ⟨26936575261170338577275095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35915433681560451436366793 26936575261170338577275095)
    ·
      refine ⟨40404862891755507865912643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26936575261170338577275095 40404862891755507865912643)
      ·
        refine ⟨60607294337633261798868965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40404862891755507865912643 60607294337633261798868965)
        ·
          refine ⟨11363867688306236587287931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60607294337633261798868965 11363867688306236587287931)
          ·
            refine ⟨17045801532459354880931897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11363867688306236587287931 17045801532459354880931897)
            ·
              refine ⟨12784351149344516160698923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17045801532459354880931897 12784351149344516160698923)
              ·
                refine ⟨19176526724016774241048385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12784351149344516160698923 19176526724016774241048385)
                ·
                  refine ⟨14382395043012580680786289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19176526724016774241048385 14382395043012580680786289)
                  ·
                    refine ⟨10786796282259435510589717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14382395043012580680786289 10786796282259435510589717)
                    ·
                      refine ⟨505631075730911039558893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10786796282259435510589717 505631075730911039558893)
                      ·
                        rfl

theorem cell23_984713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 2, 6].length) (baseStart_984713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_984713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_984713 prefixEnd_984713 := by exact prefixLift 984713
  have htrace : WordTrace (prefixWord ++ tailWord_984713) baseStart_984713 baseEnd_984713 := by
    simpa [prefixWord, tailWord_984713, baseEnd_984713] using wordTrace_append hprefix tailTrace_984713
  have hstable : (prefixWord ++ tailWord_984713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984713).length < 2 ^ (prefixWord ++ tailWord_984713).sum := by decide
  have hdescent : baseEnd_984713 < baseStart_984713 := by decide
  rcases family_descends (prefixWord ++ tailWord_984713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984737 : List Nat := [1, 2, 3, 3, 2, 1, 2, 2, 1, 3, 3]
def baseStart_984737 : Nat := 118140960795 + 984737 * 2 ^ 59
def prefixEnd_984737 : Nat := 4983230072969 + 3 ^ 40 * 984737 * 2
def baseEnd_984737 : Nat := 505643399266618945658783

theorem tailTrace_984737 : CollatzResearch.WordTrace tailWord_984737 prefixEnd_984737 505643399266618945658783 := by
  unfold tailWord_984737
  simp only [CollatzResearch.WordTrace]
  refine ⟨35916309033473503535240465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23944206022315669023493643 35916309033473503535240465)
  ·
    refine ⟨26937231775105127651430349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35916309033473503535240465 26937231775105127651430349)
    ·
      refine ⟨10101461915664422869286381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26937231775105127651430349 10101461915664422869286381)
      ·
        refine ⟨3788048218374158575982393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10101461915664422869286381 3788048218374158575982393)
        ·
          refine ⟨2841036163780618931986795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3788048218374158575982393 2841036163780618931986795)
          ·
            refine ⟨4261554245670928397980193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2841036163780618931986795 4261554245670928397980193)
            ·
              refine ⟨3196165684253196298485145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4261554245670928397980193 3196165684253196298485145)
              ·
                refine ⟨2397124263189897223863859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3196165684253196298485145 2397124263189897223863859)
                ·
                  refine ⟨3595686394784845835795789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2397124263189897223863859 3595686394784845835795789)
                  ·
                    refine ⟨1348382398044317188423421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3595686394784845835795789 1348382398044317188423421)
                    ·
                      refine ⟨505643399266618945658783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1348382398044317188423421 505643399266618945658783)
                      ·
                        rfl

theorem cell23_984737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_984737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_984737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_984737 prefixEnd_984737 := by exact prefixLift 984737
  have htrace : WordTrace (prefixWord ++ tailWord_984737) baseStart_984737 baseEnd_984737 := by
    simpa [prefixWord, tailWord_984737, baseEnd_984737] using wordTrace_append hprefix tailTrace_984737
  have hstable : (prefixWord ++ tailWord_984737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984737).length < 2 ^ (prefixWord ++ tailWord_984737).sum := by decide
  have hdescent : baseEnd_984737 < baseStart_984737 := by decide
  rcases family_descends (prefixWord ++ tailWord_984737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984738 : List Nat := [3, 3, 1, 4, 1, 2, 2, 1, 1, 1, 4]
def baseStart_984738 : Nat := 118140960795 + 984738 * 2 ^ 59
def prefixEnd_984738 : Nat := 4983230072969 + 3 ^ 40 * 984738 * 2
def baseEnd_984738 : Nat := 505643912747273441746279

theorem tailTrace_984738 : CollatzResearch.WordTrace tailWord_984738 prefixEnd_984738 505643912747273441746279 := by
  unfold tailWord_984738
  simp only [CollatzResearch.WordTrace]
  refine ⟨8979086376617470176506717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23944230337646587137351245 8979086376617470176506717)
  ·
    refine ⟨3367157391231551316190019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8979086376617470176506717 3367157391231551316190019)
    ·
      refine ⟨5050736086847326974285029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3367157391231551316190019 5050736086847326974285029)
      ·
        refine ⟨947013016283873807678443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5050736086847326974285029 947013016283873807678443)
        ·
          refine ⟨1420519524425810711517665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 947013016283873807678443 1420519524425810711517665)
          ·
            refine ⟨1065389643319358033638249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1420519524425810711517665 1065389643319358033638249)
            ·
              refine ⟨799042232489518525228687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1065389643319358033638249 799042232489518525228687)
              ·
                refine ⟨1198563348734277787843031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 799042232489518525228687 1198563348734277787843031)
                ·
                  refine ⟨1797845023101416681764547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1198563348734277787843031 1797845023101416681764547)
                  ·
                    refine ⟨2696767534652125022646821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1797845023101416681764547 2696767534652125022646821)
                    ·
                      refine ⟨505643912747273441746279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2696767534652125022646821 505643912747273441746279)
                      ·
                        rfl

theorem cell23_984738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_984738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_984738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_984738 prefixEnd_984738 := by exact prefixLift 984738
  have htrace : WordTrace (prefixWord ++ tailWord_984738) baseStart_984738 baseEnd_984738 := by
    simpa [prefixWord, tailWord_984738, baseEnd_984738] using wordTrace_append hprefix tailTrace_984738
  have hstable : (prefixWord ++ tailWord_984738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984738).length < 2 ^ (prefixWord ++ tailWord_984738).sum := by decide
  have hdescent : baseEnd_984738 < baseStart_984738 := by decide
  rcases family_descends (prefixWord ++ tailWord_984738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984744 : List Nat := [2, 1, 7, 1, 1, 1, 10]
def baseStart_984744 : Nat := 118140960795 + 984744 * 2 ^ 59
def prefixEnd_984744 : Nat := 4983230072969 + 3 ^ 40 * 984744 * 2
def baseEnd_984744 : Nat := 6242555476928400225571

theorem tailTrace_984744 : CollatzResearch.WordTrace tailWord_984744 prefixEnd_984744 6242555476928400225571 := by
  unfold tailWord_984744
  simp only [CollatzResearch.WordTrace]
  refine ⟨17958282172224071865372643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23944376229632095820496857 17958282172224071865372643)
  ·
    refine ⟨26937423258336107798058965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17958282172224071865372643 26937423258336107798058965)
    ·
      refine ⟨631345857617252526517007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 26937423258336107798058965 631345857617252526517007)
      ·
        refine ⟨947018786425878789775511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 631345857617252526517007 947018786425878789775511)
        ·
          refine ⟨1420528179638818184663267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 947018786425878789775511 1420528179638818184663267)
          ·
            refine ⟨2130792269458227276994901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1420528179638818184663267 2130792269458227276994901)
            ·
              refine ⟨6242555476928400225571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2130792269458227276994901 6242555476928400225571)
              ·
                rfl

theorem cell23_984744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 10].length) (baseStart_984744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_984744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_984744 prefixEnd_984744 := by exact prefixLift 984744
  have htrace : WordTrace (prefixWord ++ tailWord_984744) baseStart_984744 baseEnd_984744 := by
    simpa [prefixWord, tailWord_984744, baseEnd_984744] using wordTrace_append hprefix tailTrace_984744
  have hstable : (prefixWord ++ tailWord_984744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984744).length < 2 ^ (prefixWord ++ tailWord_984744).sum := by decide
  have hdescent : baseEnd_984744 < baseStart_984744 := by decide
  rcases family_descends (prefixWord ++ tailWord_984744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984754 : List Nat := [3, 2, 1, 1, 1, 2, 5, 2, 2, 1, 3]
def baseStart_984754 : Nat := 118140960795 + 984754 * 2 ^ 59
def prefixEnd_984754 : Nat := 4983230072969 + 3 ^ 40 * 984754 * 2
def baseEnd_984754 : Nat := 505652128437745379146205

theorem tailTrace_984754 : CollatzResearch.WordTrace tailWord_984754 prefixEnd_984754 505652128437745379146205 := by
  unfold tailWord_984754
  simp only [CollatzResearch.WordTrace]
  refine ⟨8979232268602978859652329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23944619382941276959072877 8979232268602978859652329)
  ·
    refine ⟨6734424201452234144739247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8979232268602978859652329 6734424201452234144739247)
    ·
      refine ⟨10101636302178351217108871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6734424201452234144739247 10101636302178351217108871)
      ·
        refine ⟨15152454453267526825663307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10101636302178351217108871 15152454453267526825663307)
        ·
          refine ⟨22728681679901290238494961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15152454453267526825663307 22728681679901290238494961)
          ·
            refine ⟨17046511259925967678871221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22728681679901290238494961 17046511259925967678871221)
            ·
              refine ⟨1598110430618059469894177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17046511259925967678871221 1598110430618059469894177)
              ·
                refine ⟨1198582822963544602420633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1598110430618059469894177 1198582822963544602420633)
                ·
                  refine ⟨898937117222658451815475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1198582822963544602420633 898937117222658451815475)
                  ·
                    refine ⟨1348405675833987677723213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 898937117222658451815475 1348405675833987677723213)
                    ·
                      refine ⟨505652128437745379146205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1348405675833987677723213 505652128437745379146205)
                      ·
                        rfl

theorem cell23_984754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 2, 2, 1, 3].length) (baseStart_984754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_984754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_984754 prefixEnd_984754 := by exact prefixLift 984754
  have htrace : WordTrace (prefixWord ++ tailWord_984754) baseStart_984754 baseEnd_984754 := by
    simpa [prefixWord, tailWord_984754, baseEnd_984754] using wordTrace_append hprefix tailTrace_984754
  have hstable : (prefixWord ++ tailWord_984754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984754).length < 2 ^ (prefixWord ++ tailWord_984754).sum := by decide
  have hdescent : baseEnd_984754 < baseStart_984754 := by decide
  rcases family_descends (prefixWord ++ tailWord_984754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984794 : List Nat := [3, 1, 1, 2, 2, 3, 1, 2, 4, 2, 2]
def baseStart_984794 : Nat := 118140960795 + 984794 * 2 ^ 59
def prefixEnd_984794 : Nat := 4983230072969 + 3 ^ 40 * 984794 * 2
def baseEnd_984794 : Nat := 505672667663925222646021

theorem tailTrace_984794 : CollatzResearch.WordTrace tailWord_984794 prefixEnd_984794 505672667663925222646021 := by
  unfold tailWord_984794
  simp only [CollatzResearch.WordTrace]
  refine ⟨8979596998566750567516359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23945591996178001513376957 8979596998566750567516359)
  ·
    refine ⟨13469395497850125851274539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8979596998566750567516359 13469395497850125851274539)
    ·
      refine ⟨20204093246775188776911809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13469395497850125851274539 20204093246775188776911809)
      ·
        refine ⟨15153069935081391582683857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20204093246775188776911809 15153069935081391582683857)
        ·
          refine ⟨11364802451311043687012893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15153069935081391582683857 11364802451311043687012893)
          ·
            refine ⟨4261800919241641382629835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11364802451311043687012893 4261800919241641382629835)
            ·
              refine ⟨6392701378862462073944753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4261800919241641382629835 6392701378862462073944753)
              ·
                refine ⟨4794526034146846555458565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6392701378862462073944753 4794526034146846555458565)
                ·
                  refine ⟨898973631402533729148481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4794526034146846555458565 898973631402533729148481)
                  ·
                    refine ⟨674230223551900296861361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 898973631402533729148481 674230223551900296861361)
                    ·
                      refine ⟨505672667663925222646021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 674230223551900296861361 505672667663925222646021)
                      ·
                        rfl

theorem cell23_984794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 2, 4, 2, 2].length) (baseStart_984794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_984794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_984794 prefixEnd_984794 := by exact prefixLift 984794
  have htrace : WordTrace (prefixWord ++ tailWord_984794) baseStart_984794 baseEnd_984794 := by
    simpa [prefixWord, tailWord_984794, baseEnd_984794] using wordTrace_append hprefix tailTrace_984794
  have hstable : (prefixWord ++ tailWord_984794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984794).length < 2 ^ (prefixWord ++ tailWord_984794).sum := by decide
  have hdescent : baseEnd_984794 < baseStart_984794 := by decide
  rcases family_descends (prefixWord ++ tailWord_984794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984817 : List Nat := [1, 2, 2, 2, 2, 5, 1, 1, 7]
def baseStart_984817 : Nat := 118140960795 + 984817 * 2 ^ 59
def prefixEnd_984817 : Nat := 4983230072969 + 3 ^ 40 * 984817 * 2
def baseEnd_984817 : Nat := 56187164190997625850935

theorem tailTrace_984817 : CollatzResearch.WordTrace tailWord_984817 prefixEnd_984817 56187164190997625850935 := by
  unfold tailWord_984817
  simp only [CollatzResearch.WordTrace]
  refine ⟨35919226873183677198152705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23946151248789118132101803 35919226873183677198152705)
  ·
    refine ⟨26939420154887757898614529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35919226873183677198152705 26939420154887757898614529)
    ·
      refine ⟨20204565116165818423960897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26939420154887757898614529 20204565116165818423960897)
      ·
        refine ⟨15153423837124363817970673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20204565116165818423960897 15153423837124363817970673)
        ·
          refine ⟨11365067877843272863478005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15153423837124363817970673 11365067877843272863478005)
          ·
            refine ⟨1065475113547806830951063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11365067877843272863478005 1065475113547806830951063)
            ·
              refine ⟨1598212670321710246426595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1065475113547806830951063 1598212670321710246426595)
              ·
                refine ⟨2397319005482565369639893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1598212670321710246426595 2397319005482565369639893)
                ·
                  refine ⟨56187164190997625850935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2397319005482565369639893 56187164190997625850935)
                  ·
                    rfl

theorem cell23_984817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 1, 7].length) (baseStart_984817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_984817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_984817 prefixEnd_984817 := by exact prefixLift 984817
  have htrace : WordTrace (prefixWord ++ tailWord_984817) baseStart_984817 baseEnd_984817 := by
    simpa [prefixWord, tailWord_984817, baseEnd_984817] using wordTrace_append hprefix tailTrace_984817
  have hstable : (prefixWord ++ tailWord_984817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984817).length < 2 ^ (prefixWord ++ tailWord_984817).sum := by decide
  have hdescent : baseEnd_984817 < baseStart_984817 := by decide
  rcases family_descends (prefixWord ++ tailWord_984817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984840 : List Nat := [2, 1, 3, 2, 2, 1, 1, 2, 1, 1, 7]
def baseStart_984840 : Nat := 118140960795 + 984840 * 2 ^ 59
def prefixEnd_984840 : Nat := 4983230072969 + 3 ^ 40 * 984840 * 2
def baseEnd_984840 : Nat := 505696287774032042670809

theorem tailTrace_984840 : CollatzResearch.WordTrace tailWord_984840 prefixEnd_984840 505696287774032042670809 := by
  unfold tailWord_984840
  simp only [CollatzResearch.WordTrace]
  refine ⟨17960032876050176063119987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23946710501400234750826649 17960032876050176063119987)
  ·
    refine ⟨26940049314075264094679981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17960032876050176063119987 26940049314075264094679981)
    ·
      refine ⟨10102518492778224035504993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26940049314075264094679981 10102518492778224035504993)
      ·
        refine ⟨7576888869583668026628745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10102518492778224035504993 7576888869583668026628745)
        ·
          refine ⟨5682666652187751019971559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7576888869583668026628745 5682666652187751019971559)
          ·
            refine ⟨8523999978281626529957339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5682666652187751019971559 8523999978281626529957339)
            ·
              refine ⟨12785999967422439794936009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8523999978281626529957339 12785999967422439794936009)
              ·
                refine ⟨9589499975566829846202007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12785999967422439794936009 9589499975566829846202007)
                ·
                  refine ⟨14384249963350244769303011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9589499975566829846202007 14384249963350244769303011)
                  ·
                    refine ⟨21576374945025367153954517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14384249963350244769303011 21576374945025367153954517)
                    ·
                      refine ⟨505696287774032042670809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 21576374945025367153954517 505696287774032042670809)
                      ·
                        rfl

theorem cell23_984840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_984840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_984840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_984840 prefixEnd_984840 := by exact prefixLift 984840
  have htrace : WordTrace (prefixWord ++ tailWord_984840) baseStart_984840 baseEnd_984840 := by
    simpa [prefixWord, tailWord_984840, baseEnd_984840] using wordTrace_append hprefix tailTrace_984840
  have hstable : (prefixWord ++ tailWord_984840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984840).length < 2 ^ (prefixWord ++ tailWord_984840).sum := by decide
  have hdescent : baseEnd_984840 < baseStart_984840 := by decide
  rcases family_descends (prefixWord ++ tailWord_984840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984862 : List Nat := [4, 3, 2, 2, 1, 1, 2, 2, 2, 2, 2]
def baseStart_984862 : Nat := 118140960795 + 984862 * 2 ^ 59
def prefixEnd_984862 : Nat := 4983230072969 + 3 ^ 40 * 984862 * 2
def baseEnd_984862 : Nat := 505707584348430956595709

theorem tailTrace_984862 : CollatzResearch.WordTrace tailWord_984862 prefixEnd_984862 505707584348430956595709 := by
  unfold tailWord_984862
  simp only [CollatzResearch.WordTrace]
  refine ⟨4490108519752581235442605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23947245438680433255693893 4490108519752581235442605)
  ·
    refine ⟨1683790694907217963290977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4490108519752581235442605 1683790694907217963290977)
    ·
      refine ⟨1262843021180413472468233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1683790694907217963290977 1262843021180413472468233)
      ·
        refine ⟨947132265885310104351175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1262843021180413472468233 947132265885310104351175)
        ·
          refine ⟨1420698398827965156526763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 947132265885310104351175 1420698398827965156526763)
          ·
            refine ⟨2131047598241947734790145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1420698398827965156526763 2131047598241947734790145)
            ·
              refine ⟨1598285698681460801092609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2131047598241947734790145 1598285698681460801092609)
              ·
                refine ⟨1198714274011095600819457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1598285698681460801092609 1198714274011095600819457)
                ·
                  refine ⟨899035705508321700614593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1198714274011095600819457 899035705508321700614593)
                  ·
                    refine ⟨674276779131241275460945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 899035705508321700614593 674276779131241275460945)
                    ·
                      refine ⟨505707584348430956595709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 674276779131241275460945 505707584348430956595709)
                      ·
                        rfl

theorem cell23_984862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_984862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_984862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_984862 prefixEnd_984862 := by exact prefixLift 984862
  have htrace : WordTrace (prefixWord ++ tailWord_984862) baseStart_984862 baseEnd_984862 := by
    simpa [prefixWord, tailWord_984862, baseEnd_984862] using wordTrace_append hprefix tailTrace_984862
  have hstable : (prefixWord ++ tailWord_984862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984862).length < 2 ^ (prefixWord ++ tailWord_984862).sum := by decide
  have hdescent : baseEnd_984862 < baseStart_984862 := by decide
  rcases family_descends (prefixWord ++ tailWord_984862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984867 : List Nat := [1, 1, 1, 4, 2, 1, 4, 2, 2, 1, 4]
def baseStart_984867 : Nat := 118140960795 + 984867 * 2 ^ 59
def prefixEnd_984867 : Nat := 4983230072969 + 3 ^ 40 * 984867 * 2
def baseEnd_984867 : Nat := 505710151751703437033185

theorem tailTrace_984867 : CollatzResearch.WordTrace tailWord_984867 prefixEnd_984867 505710151751703437033185 := by
  unfold tailWord_984867
  simp only [CollatzResearch.WordTrace]
  refine ⟨35921050523002535737472855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23947367015335023824981903 35921050523002535737472855)
  ·
    refine ⟨53881575784503803606209283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35921050523002535737472855 53881575784503803606209283)
    ·
      refine ⟨80822363676755705409313925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53881575784503803606209283 80822363676755705409313925)
      ·
        refine ⟨15154193189391694764246361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80822363676755705409313925 15154193189391694764246361)
        ·
          refine ⟨11365644892043771073184771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15154193189391694764246361 11365644892043771073184771)
          ·
            refine ⟨17048467338065656609777157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11365644892043771073184771 17048467338065656609777157)
            ·
              refine ⟨3196587625887310614333217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17048467338065656609777157 3196587625887310614333217)
              ·
                refine ⟨2397440719415482960749913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3196587625887310614333217 2397440719415482960749913)
                ·
                  refine ⟨1798080539561612220562435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2397440719415482960749913 1798080539561612220562435)
                  ·
                    refine ⟨2697120809342418330843653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1798080539561612220562435 2697120809342418330843653)
                    ·
                      refine ⟨505710151751703437033185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2697120809342418330843653 505710151751703437033185)
                      ·
                        rfl

theorem cell23_984867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 2, 2, 1, 4].length) (baseStart_984867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_984867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_984867 prefixEnd_984867 := by exact prefixLift 984867
  have htrace : WordTrace (prefixWord ++ tailWord_984867) baseStart_984867 baseEnd_984867 := by
    simpa [prefixWord, tailWord_984867, baseEnd_984867] using wordTrace_append hprefix tailTrace_984867
  have hstable : (prefixWord ++ tailWord_984867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984867).length < 2 ^ (prefixWord ++ tailWord_984867).sum := by decide
  have hdescent : baseEnd_984867 < baseStart_984867 := by decide
  rcases family_descends (prefixWord ++ tailWord_984867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984880 : List Nat := [2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 4]
def baseStart_984880 : Nat := 118140960795 + 984880 * 2 ^ 59
def prefixEnd_984880 : Nat := 4983230072969 + 3 ^ 40 * 984880 * 2
def baseEnd_984880 : Nat := 505716827000211886170625

theorem tailTrace_984880 : CollatzResearch.WordTrace tailWord_984880 prefixEnd_984880 505716827000211886170625 := by
  unfold tailWord_984880
  simp only [CollatzResearch.WordTrace]
  refine ⟨17960762335977719478848047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23947683114636959305130729 17960762335977719478848047)
  ·
    refine ⟨26941143503966579218272071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17960762335977719478848047 26941143503966579218272071)
    ·
      refine ⟨40411715255949868827408107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26941143503966579218272071 40411715255949868827408107)
      ·
        refine ⟨60617572883924803241112161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40411715255949868827408107 60617572883924803241112161)
        ·
          refine ⟨45463179662943602430834121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60617572883924803241112161 45463179662943602430834121)
          ·
            refine ⟨34097384747207701823125591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45463179662943602430834121 34097384747207701823125591)
            ·
              refine ⟨51146077120811552734688387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34097384747207701823125591 51146077120811552734688387)
              ·
                refine ⟨76719115681217329102032581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51146077120811552734688387 76719115681217329102032581)
                ·
                  refine ⟨14384834190228249206631109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76719115681217329102032581 14384834190228249206631109)
                  ·
                    refine ⟨2697156410667796726243333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14384834190228249206631109 2697156410667796726243333)
                    ·
                      refine ⟨505716827000211886170625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2697156410667796726243333 505716827000211886170625)
                      ·
                        rfl

theorem cell23_984880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 4].length) (baseStart_984880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_984880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_984880 prefixEnd_984880 := by exact prefixLift 984880
  have htrace : WordTrace (prefixWord ++ tailWord_984880) baseStart_984880 baseEnd_984880 := by
    simpa [prefixWord, tailWord_984880, baseEnd_984880] using wordTrace_append hprefix tailTrace_984880
  have hstable : (prefixWord ++ tailWord_984880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984880).length < 2 ^ (prefixWord ++ tailWord_984880).sum := by decide
  have hdescent : baseEnd_984880 < baseStart_984880 := by decide
  rcases family_descends (prefixWord ++ tailWord_984880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984894 : List Nat := [4, 2, 1, 2, 2, 1, 1, 1, 5, 4]
def baseStart_984894 : Nat := 118140960795 + 984894 * 2 ^ 59
def prefixEnd_984894 : Nat := 4983230072969 + 3 ^ 40 * 984894 * 2
def baseEnd_984894 : Nat := 168574671909791610465187

theorem tailTrace_984894 : CollatzResearch.WordTrace tailWord_984894 prefixEnd_984894 168574671909791610465187 := by
  unfold tailWord_984894
  simp only [CollatzResearch.WordTrace]
  refine ⟨4490254411738089918588217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23948023529269812899137157 4490254411738089918588217)
  ·
    refine ⟨3367690808803567438941163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4490254411738089918588217 3367690808803567438941163)
    ·
      refine ⟨5051536213205351158411745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3367690808803567438941163 5051536213205351158411745)
      ·
        refine ⟨3788652159904013368808809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5051536213205351158411745 3788652159904013368808809)
        ·
          refine ⟨2841489119928010026606607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3788652159904013368808809 2841489119928010026606607)
          ·
            refine ⟨4262233679892015039909911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2841489119928010026606607 4262233679892015039909911)
            ·
              refine ⟨6393350519838022559864867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4262233679892015039909911 6393350519838022559864867)
              ·
                refine ⟨9590025779757033839797301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6393350519838022559864867 9590025779757033839797301)
                ·
                  refine ⟨899064916852221922480997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9590025779757033839797301 899064916852221922480997)
                  ·
                    refine ⟨168574671909791610465187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 899064916852221922480997 168574671909791610465187)
                    ·
                      rfl

theorem cell23_984894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 5, 4].length) (baseStart_984894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_984894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_984894 prefixEnd_984894 := by exact prefixLift 984894
  have htrace : WordTrace (prefixWord ++ tailWord_984894) baseStart_984894 baseEnd_984894 := by
    simpa [prefixWord, tailWord_984894, baseEnd_984894] using wordTrace_append hprefix tailTrace_984894
  have hstable : (prefixWord ++ tailWord_984894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984894).length < 2 ^ (prefixWord ++ tailWord_984894).sum := by decide
  have hdescent : baseEnd_984894 < baseStart_984894 := by decide
  rcases family_descends (prefixWord ++ tailWord_984894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984904 : List Nat := [2, 1, 3, 1, 1, 4, 3, 1, 2, 2, 3]
def baseStart_984904 : Nat := 118140960795 + 984904 * 2 ^ 59
def prefixEnd_984904 : Nat := 4983230072969 + 3 ^ 40 * 984904 * 2
def baseEnd_984904 : Nat := 505729150535919792270515

theorem tailTrace_984904 : CollatzResearch.WordTrace tailWord_984904 prefixEnd_984904 505729150535919792270515 := by
  unfold tailWord_984904
  simp only [CollatzResearch.WordTrace]
  refine ⟨17961200011934245528284883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23948266682578994037713177 17961200011934245528284883)
  ·
    refine ⟨26941800017901368292427325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17961200011934245528284883 26941800017901368292427325)
    ·
      refine ⟨10103175006713013109660247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26941800017901368292427325 10103175006713013109660247)
      ·
        refine ⟨15154762510069519664490371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10103175006713013109660247 15154762510069519664490371)
        ·
          refine ⟨22732143765104279496735557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15154762510069519664490371 22732143765104279496735557)
          ·
            refine ⟨4262276955957052405637917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22732143765104279496735557 4262276955957052405637917)
            ·
              refine ⟨1598353858483894652114219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4262276955957052405637917 1598353858483894652114219)
              ·
                refine ⟨2397530787725841978171329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1598353858483894652114219 2397530787725841978171329)
                ·
                  refine ⟨1798148090794381483628497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2397530787725841978171329 1798148090794381483628497)
                  ·
                    refine ⟨1348611068095786112721373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1798148090794381483628497 1348611068095786112721373)
                    ·
                      refine ⟨505729150535919792270515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1348611068095786112721373 505729150535919792270515)
                      ·
                        rfl

theorem cell23_984904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 1, 2, 2, 3].length) (baseStart_984904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_984904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_984904 prefixEnd_984904 := by exact prefixLift 984904
  have htrace : WordTrace (prefixWord ++ tailWord_984904) baseStart_984904 baseEnd_984904 := by
    simpa [prefixWord, tailWord_984904, baseEnd_984904] using wordTrace_append hprefix tailTrace_984904
  have hstable : (prefixWord ++ tailWord_984904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984904).length < 2 ^ (prefixWord ++ tailWord_984904).sum := by decide
  have hdescent : baseEnd_984904 < baseStart_984904 := by decide
  rcases family_descends (prefixWord ++ tailWord_984904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984924 : List Nat := [2, 2, 4, 2, 2, 1, 1, 1, 8]
def baseStart_984924 : Nat := 118140960795 + 984924 * 2 ^ 59
def prefixEnd_984924 : Nat := 4983230072969 + 3 ^ 40 * 984924 * 2
def baseEnd_984924 : Nat := 56193268905445523780047

theorem tailTrace_984924 : CollatzResearch.WordTrace tailWord_984924 prefixEnd_984924 56193268905445523780047 := by
  unfold tailWord_984924
  simp only [CollatzResearch.WordTrace]
  refine ⟨17961564741898017236148913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23948752989197356314865217 17961564741898017236148913)
  ·
    refine ⟨13471173556423512927111685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17961564741898017236148913 13471173556423512927111685)
    ·
      refine ⟨2525845041829408673833441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13471173556423512927111685 2525845041829408673833441)
      ·
        refine ⟨1894383781372056505375081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2525845041829408673833441 1894383781372056505375081)
        ·
          refine ⟨1420787836029042379031311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1894383781372056505375081 1420787836029042379031311)
          ·
            refine ⟨2131181754043563568546967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1420787836029042379031311 2131181754043563568546967)
            ·
              refine ⟨3196772631065345352820451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2131181754043563568546967 3196772631065345352820451)
              ·
                refine ⟨4795158946598018029230677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3196772631065345352820451 4795158946598018029230677)
                ·
                  refine ⟨56193268905445523780047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4795158946598018029230677 56193268905445523780047)
                  ·
                    rfl

theorem cell23_984924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 1, 8].length) (baseStart_984924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_984924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_984924 prefixEnd_984924 := by exact prefixLift 984924
  have htrace : WordTrace (prefixWord ++ tailWord_984924) baseStart_984924 baseEnd_984924 := by
    simpa [prefixWord, tailWord_984924, baseEnd_984924] using wordTrace_append hprefix tailTrace_984924
  have hstable : (prefixWord ++ tailWord_984924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984924).length < 2 ^ (prefixWord ++ tailWord_984924).sum := by decide
  have hdescent : baseEnd_984924 < baseStart_984924 := by decide
  rcases family_descends (prefixWord ++ tailWord_984924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984977 : List Nat := [1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 5]
def baseStart_984977 : Nat := 118140960795 + 984977 * 2 ^ 59
def prefixEnd_984977 : Nat := 4983230072969 + 3 ^ 40 * 984977 * 2
def baseEnd_984977 : Nat := 505766634623698006657679

theorem tailTrace_984977 : CollatzResearch.WordTrace tailWord_984977 prefixEnd_984977 505766634623698006657679 := by
  unfold tailWord_984977
  simp only [CollatzResearch.WordTrace]
  refine ⟨35925062552604024523977185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23950041701736016349318123 35925062552604024523977185)
  ·
    refine ⟨26943796914453018392982889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35925062552604024523977185 26943796914453018392982889)
    ·
      refine ⟨20207847685839763794737167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26943796914453018392982889 20207847685839763794737167)
      ·
        refine ⟨30311771528759645692105751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20207847685839763794737167 30311771528759645692105751)
        ·
          refine ⟨45467657293139468538158627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30311771528759645692105751 45467657293139468538158627)
          ·
            refine ⟨68201485939709202807237941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45467657293139468538158627 68201485939709202807237941)
            ·
              refine ⟨6393889306847737763178557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68201485939709202807237941 6393889306847737763178557)
              ·
                refine ⟨2397708490067901661191959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6393889306847737763178557 2397708490067901661191959)
                ·
                  refine ⟨3596562735101852491787939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2397708490067901661191959 3596562735101852491787939)
                  ·
                    refine ⟨5394844102652778737681909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3596562735101852491787939 5394844102652778737681909)
                    ·
                      refine ⟨505766634623698006657679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5394844102652778737681909 505766634623698006657679)
                      ·
                        rfl

theorem cell23_984977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 5].length) (baseStart_984977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_984977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_984977 prefixEnd_984977 := by exact prefixLift 984977
  have htrace : WordTrace (prefixWord ++ tailWord_984977) baseStart_984977 baseEnd_984977 := by
    simpa [prefixWord, tailWord_984977, baseEnd_984977] using wordTrace_append hprefix tailTrace_984977
  have hstable : (prefixWord ++ tailWord_984977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984977).length < 2 ^ (prefixWord ++ tailWord_984977).sum := by decide
  have hdescent : baseEnd_984977 < baseStart_984977 := by decide
  rcases family_descends (prefixWord ++ tailWord_984977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984978 : List Nat := [3, 2, 3, 2, 1, 2, 1, 2, 2, 3, 2]
def baseStart_984978 : Nat := 118140960795 + 984978 * 2 ^ 59
def prefixEnd_984978 : Nat := 4983230072969 + 3 ^ 40 * 984978 * 2
def baseEnd_984978 : Nat := 505767148104352502745175

theorem tailTrace_984978 : CollatzResearch.WordTrace tailWord_984978 prefixEnd_984978 505767148104352502745175 := by
  unfold tailWord_984978
  simp only [CollatzResearch.WordTrace]
  refine ⟨8981274756400100423690897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23950066017066934463175725 8981274756400100423690897)
  ·
    refine ⟨6735956067300075317768173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8981274756400100423690897 6735956067300075317768173)
    ·
      refine ⟨2525983525237528244163065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6735956067300075317768173 2525983525237528244163065)
      ·
        refine ⟨1894487643928146183122299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2525983525237528244163065 1894487643928146183122299)
        ·
          refine ⟨2841731465892219274683449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1894487643928146183122299 2841731465892219274683449)
          ·
            refine ⟨2131298599419164456012587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2841731465892219274683449 2131298599419164456012587)
            ·
              refine ⟨3196947899128746684018881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2131298599419164456012587 3196947899128746684018881)
              ·
                refine ⟨2397710924346560013014161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3196947899128746684018881 2397710924346560013014161)
                ·
                  refine ⟨1798283193259920009760621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2397710924346560013014161 1798283193259920009760621)
                  ·
                    refine ⟨674356197472470003660233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1798283193259920009760621 674356197472470003660233)
                    ·
                      refine ⟨505767148104352502745175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 674356197472470003660233 505767148104352502745175)
                      ·
                        rfl

theorem cell23_984978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_984978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_984978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_984978 prefixEnd_984978 := by exact prefixLift 984978
  have htrace : WordTrace (prefixWord ++ tailWord_984978) baseStart_984978 baseEnd_984978 := by
    simpa [prefixWord, tailWord_984978, baseEnd_984978] using wordTrace_append hprefix tailTrace_984978
  have hstable : (prefixWord ++ tailWord_984978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984978).length < 2 ^ (prefixWord ++ tailWord_984978).sum := by decide
  have hdescent : baseEnd_984978 < baseStart_984978 := by decide
  rcases family_descends (prefixWord ++ tailWord_984978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985024 : List Nat := [2, 1, 1, 2, 3, 2, 3, 2, 1, 3, 3]
def baseStart_985024 : Nat := 118140960795 + 985024 * 2 ^ 59
def prefixEnd_985024 : Nat := 4983230072969 + 3 ^ 40 * 985024 * 2
def baseEnd_985024 : Nat := 505790768214459322769963

theorem tailTrace_985024 : CollatzResearch.WordTrace tailWord_985024 prefixEnd_985024 505790768214459322769963 := by
  unfold tailWord_985024
  simp only [CollatzResearch.WordTrace]
  refine ⟨17963388391716875775469063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23951184522289167700625417 17963388391716875775469063)
  ·
    refine ⟨26945082587575313663203595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17963388391716875775469063 26945082587575313663203595)
    ·
      refine ⟨40417623881362970494805393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26945082587575313663203595 40417623881362970494805393)
      ·
        refine ⟨30313217911022227871104045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40417623881362970494805393 30313217911022227871104045)
        ·
          refine ⟨11367456716633335451664017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30313217911022227871104045 11367456716633335451664017)
          ·
            refine ⟨8525592537475001588748013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11367456716633335451664017 8525592537475001588748013)
            ·
              refine ⟨3197097201553125595780505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8525592537475001588748013 3197097201553125595780505)
              ·
                refine ⟨2397822901164844196835379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3197097201553125595780505 2397822901164844196835379)
                ·
                  refine ⟨3596734351747266295253069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2397822901164844196835379 3596734351747266295253069)
                  ·
                    refine ⟨1348775381905224860719901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3596734351747266295253069 1348775381905224860719901)
                    ·
                      refine ⟨505790768214459322769963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1348775381905224860719901 505790768214459322769963)
                      ·
                        rfl

theorem cell23_985024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 2, 1, 3, 3].length) (baseStart_985024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_985024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_985024 prefixEnd_985024 := by exact prefixLift 985024
  have htrace : WordTrace (prefixWord ++ tailWord_985024) baseStart_985024 baseEnd_985024 := by
    simpa [prefixWord, tailWord_985024, baseEnd_985024] using wordTrace_append hprefix tailTrace_985024
  have hstable : (prefixWord ++ tailWord_985024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985024).length < 2 ^ (prefixWord ++ tailWord_985024).sum := by decide
  have hdescent : baseEnd_985024 < baseStart_985024 := by decide
  rcases family_descends (prefixWord ++ tailWord_985024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985042 : List Nat := [3, 2, 2, 3, 2, 1, 1, 4, 1, 2, 2]
def baseStart_985042 : Nat := 118140960795 + 985042 * 2 ^ 59
def prefixEnd_985042 : Nat := 4983230072969 + 3 ^ 40 * 985042 * 2
def baseEnd_985042 : Nat := 505800010866240252344881

theorem tailTrace_985042 : CollatzResearch.WordTrace tailWord_985042 prefixEnd_985042 505800010866240252344881 := by
  unfold tailWord_985042
  simp only [CollatzResearch.WordTrace]
  refine ⟨8981858324342135156273345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23951622198245693750062253 8981858324342135156273345)
  ·
    refine ⟨6736393743256601367205009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8981858324342135156273345 6736393743256601367205009)
    ·
      refine ⟨5052295307442451025403757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6736393743256601367205009 5052295307442451025403757)
      ·
        refine ⟨1894610740290919134526409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5052295307442451025403757 1894610740290919134526409)
        ·
          refine ⟨1420958055218189350894807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1894610740290919134526409 1420958055218189350894807)
          ·
            refine ⟨2131437082827284026342211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1420958055218189350894807 2131437082827284026342211)
            ·
              refine ⟨3197155624240926039513317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2131437082827284026342211 3197155624240926039513317)
              ·
                refine ⟨599466679545173632408747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3197155624240926039513317 599466679545173632408747)
                ·
                  refine ⟨899200019317760448613121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 599466679545173632408747 899200019317760448613121)
                  ·
                    refine ⟨674400014488320336459841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 899200019317760448613121 674400014488320336459841)
                    ·
                      refine ⟨505800010866240252344881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 674400014488320336459841 505800010866240252344881)
                      ·
                        rfl

theorem cell23_985042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_985042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_985042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_985042 prefixEnd_985042 := by exact prefixLift 985042
  have htrace : WordTrace (prefixWord ++ tailWord_985042) baseStart_985042 baseEnd_985042 := by
    simpa [prefixWord, tailWord_985042, baseEnd_985042] using wordTrace_append hprefix tailTrace_985042
  have hstable : (prefixWord ++ tailWord_985042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985042).length < 2 ^ (prefixWord ++ tailWord_985042).sum := by decide
  have hdescent : baseEnd_985042 < baseStart_985042 := by decide
  rcases family_descends (prefixWord ++ tailWord_985042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985047 : List Nat := [1, 1, 3, 2, 1, 1, 3, 1, 1, 5, 4]
def baseStart_985047 : Nat := 118140960795 + 985047 * 2 ^ 59
def prefixEnd_985047 : Nat := 4983230072969 + 3 ^ 40 * 985047 * 2
def baseEnd_985047 : Nat := 505802578269512732782357

theorem tailTrace_985047 : CollatzResearch.WordTrace tailWord_985047 prefixEnd_985047 505802578269512732782357 := by
  unfold tailWord_985047
  simp only [CollatzResearch.WordTrace]
  refine ⟨35927615662350426479025395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23951743774900284319350263 35927615662350426479025395)
  ·
    refine ⟨53891423493525639718538093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35927615662350426479025395 53891423493525639718538093)
    ·
      refine ⟨20209283810072114894451785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53891423493525639718538093 20209283810072114894451785)
      ·
        refine ⟨15156962857554086170838839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20209283810072114894451785 15156962857554086170838839)
        ·
          refine ⟨22735444286331129256258259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15156962857554086170838839 22735444286331129256258259)
          ·
            refine ⟨34103166429496693884387389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22735444286331129256258259 34103166429496693884387389)
            ·
              refine ⟨12788687411061260206645271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34103166429496693884387389 12788687411061260206645271)
              ·
                refine ⟨19183031116591890309967907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12788687411061260206645271 19183031116591890309967907)
                ·
                  refine ⟨28774546674887835464951861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19183031116591890309967907 28774546674887835464951861)
                  ·
                    refine ⟨2697613750770734574839237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28774546674887835464951861 2697613750770734574839237)
                    ·
                      refine ⟨505802578269512732782357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2697613750770734574839237 505802578269512732782357)
                      ·
                        rfl

theorem cell23_985047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 5, 4].length) (baseStart_985047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_985047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_985047 prefixEnd_985047 := by exact prefixLift 985047
  have htrace : WordTrace (prefixWord ++ tailWord_985047) baseStart_985047 baseEnd_985047 := by
    simpa [prefixWord, tailWord_985047, baseEnd_985047] using wordTrace_append hprefix tailTrace_985047
  have hstable : (prefixWord ++ tailWord_985047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985047).length < 2 ^ (prefixWord ++ tailWord_985047).sum := by decide
  have hdescent : baseEnd_985047 < baseStart_985047 := by decide
  rcases family_descends (prefixWord ++ tailWord_985047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985057 : List Nat := [1, 2, 3, 1, 2, 1, 3, 1, 1, 8]
def baseStart_985057 : Nat := 118140960795 + 985057 * 2 ^ 59
def prefixEnd_985057 : Nat := 4983230072969 + 3 ^ 40 * 985057 * 2
def baseEnd_985057 : Nat := 168602571025352564552437

theorem tailTrace_985057 : CollatzResearch.WordTrace tailWord_985057 prefixEnd_985057 168602571025352564552437 := by
  unfold tailWord_985057
  simp only [CollatzResearch.WordTrace]
  refine ⟨35927980392314198186889425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23951986928209465457926283 35927980392314198186889425)
  ·
    refine ⟨26945985294235648640167069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35927980392314198186889425 26945985294235648640167069)
    ·
      refine ⟨10104744485338368240062651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26945985294235648640167069 10104744485338368240062651)
      ·
        refine ⟨15157116728007552360093977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10104744485338368240062651 15157116728007552360093977)
        ·
          refine ⟨11367837546005664270070483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15157116728007552360093977 11367837546005664270070483)
          ·
            refine ⟨17051756319008496405105725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11367837546005664270070483 17051756319008496405105725)
            ·
              refine ⟨6394408619628186151914647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17051756319008496405105725 6394408619628186151914647)
              ·
                refine ⟨9591612929442279227871971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6394408619628186151914647 9591612929442279227871971)
                ·
                  refine ⟨14387419394163418841807957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9591612929442279227871971 14387419394163418841807957)
                  ·
                    refine ⟨168602571025352564552437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 14387419394163418841807957 168602571025352564552437)
                    ·
                      rfl

theorem cell23_985057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 8].length) (baseStart_985057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_985057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_985057 prefixEnd_985057 := by exact prefixLift 985057
  have htrace : WordTrace (prefixWord ++ tailWord_985057) baseStart_985057 baseEnd_985057 := by
    simpa [prefixWord, tailWord_985057, baseEnd_985057] using wordTrace_append hprefix tailTrace_985057
  have hstable : (prefixWord ++ tailWord_985057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985057).length < 2 ^ (prefixWord ++ tailWord_985057).sum := by decide
  have hdescent : baseEnd_985057 < baseStart_985057 := by decide
  rcases family_descends (prefixWord ++ tailWord_985057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985067 : List Nat := [1, 1, 1, 1, 2, 3, 1, 3, 4, 1, 5]
def baseStart_985067 : Nat := 118140960795 + 985067 * 2 ^ 59
def prefixEnd_985067 : Nat := 4983230072969 + 3 ^ 40 * 985067 * 2
def baseEnd_985067 : Nat := 505812847882602654532265

theorem tailTrace_985067 : CollatzResearch.WordTrace tailWord_985067 prefixEnd_985067 505812847882602654532265 := by
  unfold tailWord_985067
  simp only [CollatzResearch.WordTrace]
  refine ⟨35928345122277969894753455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23952230081518646596502303 35928345122277969894753455)
  ·
    refine ⟨53892517683416954842130183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35928345122277969894753455 53892517683416954842130183)
    ·
      refine ⟨80838776525125432263195275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53892517683416954842130183 80838776525125432263195275)
      ·
        refine ⟨121258164787688148394792913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80838776525125432263195275 121258164787688148394792913)
        ·
          refine ⟨90943623590766111296094685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121258164787688148394792913 90943623590766111296094685)
          ·
            refine ⟨34103858846537291736035507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90943623590766111296094685 34103858846537291736035507)
            ·
              refine ⟨51155788269805937604053261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34103858846537291736035507 51155788269805937604053261)
              ·
                refine ⟨19183420601177226601519973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51155788269805937604053261 19183420601177226601519973)
                ·
                  refine ⟨3596891362720729987784995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19183420601177226601519973 3596891362720729987784995)
                  ·
                    refine ⟨5395337044081094981677493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3596891362720729987784995 5395337044081094981677493)
                    ·
                      refine ⟨505812847882602654532265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5395337044081094981677493 505812847882602654532265)
                      ·
                        rfl

theorem cell23_985067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 4, 1, 5].length) (baseStart_985067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_985067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_985067 prefixEnd_985067 := by exact prefixLift 985067
  have htrace : WordTrace (prefixWord ++ tailWord_985067) baseStart_985067 baseEnd_985067 := by
    simpa [prefixWord, tailWord_985067, baseEnd_985067] using wordTrace_append hprefix tailTrace_985067
  have hstable : (prefixWord ++ tailWord_985067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985067).length < 2 ^ (prefixWord ++ tailWord_985067).sum := by decide
  have hdescent : baseEnd_985067 < baseStart_985067 := by decide
  rcases family_descends (prefixWord ++ tailWord_985067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985081 : List Nat := [1, 2, 1, 3, 1, 4, 2, 2, 1, 4, 2]
def baseStart_985081 : Nat := 118140960795 + 985081 * 2 ^ 59
def prefixEnd_985081 : Nat := 4983230072969 + 3 ^ 40 * 985081 * 2
def baseEnd_985081 : Nat := 505820036611765599757201

theorem tailTrace_985081 : CollatzResearch.WordTrace tailWord_985081 prefixEnd_985081 505820036611765599757201 := by
  unfold tailWord_985081
  simp only [CollatzResearch.WordTrace]
  refine ⟨35928855744227250285763097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23952570496151500190508731 35928855744227250285763097)
  ·
    refine ⟨26946641808170437714322323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35928855744227250285763097 26946641808170437714322323)
    ·
      refine ⟨40419962712255656571483485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26946641808170437714322323 40419962712255656571483485)
      ·
        refine ⟨15157486017095871214306307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40419962712255656571483485 15157486017095871214306307)
        ·
          refine ⟨22736229025643806821459461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15157486017095871214306307 22736229025643806821459461)
          ·
            refine ⟨4263042942308213779023649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22736229025643806821459461 4263042942308213779023649)
            ·
              refine ⟨3197282206731160334267737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4263042942308213779023649 3197282206731160334267737)
              ·
                refine ⟨2397961655048370250700803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3197282206731160334267737 2397961655048370250700803)
                ·
                  refine ⟨3596942482572555376051205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2397961655048370250700803 3596942482572555376051205)
                  ·
                    refine ⟨674426715482354133009601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3596942482572555376051205 674426715482354133009601)
                    ·
                      refine ⟨505820036611765599757201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 674426715482354133009601 505820036611765599757201)
                      ·
                        rfl

theorem cell23_985081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 2, 1, 4, 2].length) (baseStart_985081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_985081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_985081 prefixEnd_985081 := by exact prefixLift 985081
  have htrace : WordTrace (prefixWord ++ tailWord_985081) baseStart_985081 baseEnd_985081 := by
    simpa [prefixWord, tailWord_985081, baseEnd_985081] using wordTrace_append hprefix tailTrace_985081
  have hstable : (prefixWord ++ tailWord_985081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985081).length < 2 ^ (prefixWord ++ tailWord_985081).sum := by decide
  have hdescent : baseEnd_985081 < baseStart_985081 := by decide
  rcases family_descends (prefixWord ++ tailWord_985081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985092 : List Nat := [2, 3, 2, 4, 1, 2, 1, 2, 2, 1, 3]
def baseStart_985092 : Nat := 118140960795 + 985092 * 2 ^ 59
def prefixEnd_985092 : Nat := 4983230072969 + 3 ^ 40 * 985092 * 2
def baseEnd_985092 : Nat := 505825684898965056719651

theorem tailTrace_985092 : CollatzResearch.WordTrace tailWord_985092 prefixEnd_985092 505825684898965056719651 := by
  unfold tailWord_985092
  simp only [CollatzResearch.WordTrace]
  refine ⟨17964628473593699582206765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23952837964791599442942353 17964628473593699582206765)
  ·
    refine ⟨6736735677597637343327537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17964628473593699582206765 6736735677597637343327537)
    ·
      refine ⟨5052551758198228007495653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6736735677597637343327537 5052551758198228007495653)
      ·
        refine ⟨947353454662167751405435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5052551758198228007495653 947353454662167751405435)
        ·
          refine ⟨1421030181993251627108153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 947353454662167751405435 1421030181993251627108153)
          ·
            refine ⟨1065772636494938720331115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1421030181993251627108153 1065772636494938720331115)
            ·
              refine ⟨1598658954742408080496673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1065772636494938720331115 1598658954742408080496673)
              ·
                refine ⟨1198994216056806060372505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1598658954742408080496673 1198994216056806060372505)
                ·
                  refine ⟨899245662042604545279379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1198994216056806060372505 899245662042604545279379)
                  ·
                    refine ⟨1348868493063906817919069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 899245662042604545279379 1348868493063906817919069)
                    ·
                      refine ⟨505825684898965056719651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1348868493063906817919069 505825684898965056719651)
                      ·
                        rfl

theorem cell23_985092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_985092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_985092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_985092 prefixEnd_985092 := by exact prefixLift 985092
  have htrace : WordTrace (prefixWord ++ tailWord_985092) baseStart_985092 baseEnd_985092 := by
    simpa [prefixWord, tailWord_985092, baseEnd_985092] using wordTrace_append hprefix tailTrace_985092
  have hstable : (prefixWord ++ tailWord_985092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985092).length < 2 ^ (prefixWord ++ tailWord_985092).sum := by decide
  have hdescent : baseEnd_985092 < baseStart_985092 := by decide
  rcases family_descends (prefixWord ++ tailWord_985092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985138 : List Nat := [3, 2, 1, 1, 2, 5, 1, 3, 5]
def baseStart_985138 : Nat := 118140960795 + 985138 * 2 ^ 59
def prefixEnd_985138 : Nat := 4983230072969 + 3 ^ 40 * 985138 * 2
def baseEnd_985138 : Nat := 56205478334341319638271

theorem tailTrace_985138 : CollatzResearch.WordTrace tailWord_985138 prefixEnd_985138 56205478334341319638271 := by
  unfold tailWord_985138
  simp only [CollatzResearch.WordTrace]
  refine ⟨8982733676255187255147017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23953956470013832680392045 8982733676255187255147017)
  ·
    refine ⟨6737050257191390441360263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8982733676255187255147017 6737050257191390441360263)
    ·
      refine ⟨10105575385787085662040395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6737050257191390441360263 10105575385787085662040395)
      ·
        refine ⟨15158363078680628493060593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10105575385787085662040395 15158363078680628493060593)
        ·
          refine ⟨11368772309010471369795445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15158363078680628493060593 11368772309010471369795445)
          ·
            refine ⟨1065822403969731690918323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11368772309010471369795445 1065822403969731690918323)
            ·
              refine ⟨1598733605954597536377485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1065822403969731690918323 1598733605954597536377485)
              ·
                refine ⟨599525102232974076141557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1598733605954597536377485 599525102232974076141557)
                ·
                  refine ⟨56205478334341319638271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 599525102232974076141557 56205478334341319638271)
                  ·
                    rfl

theorem cell23_985138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 3, 5].length) (baseStart_985138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_985138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_985138 prefixEnd_985138 := by exact prefixLift 985138
  have htrace : WordTrace (prefixWord ++ tailWord_985138) baseStart_985138 baseEnd_985138 := by
    simpa [prefixWord, tailWord_985138, baseEnd_985138] using wordTrace_append hprefix tailTrace_985138
  have hstable : (prefixWord ++ tailWord_985138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985138).length < 2 ^ (prefixWord ++ tailWord_985138).sum := by decide
  have hdescent : baseEnd_985138 < baseStart_985138 := by decide
  rcases family_descends (prefixWord ++ tailWord_985138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985147 : List Nat := [1, 1, 1, 1, 1, 2, 1, 4, 1, 10]
def baseStart_985147 : Nat := 118140960795 + 985147 * 2 ^ 59
def prefixEnd_985147 : Nat := 4983230072969 + 3 ^ 40 * 985147 * 2
def baseEnd_985147 : Nat := 168617975444987447177299

theorem tailTrace_985147 : CollatzResearch.WordTrace tailWord_985147 prefixEnd_985147 168617975444987447177299 := by
  unfold tailWord_985147
  simp only [CollatzResearch.WordTrace]
  refine ⟨35931262961988143557665695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23954175307992095705110463 35931262961988143557665695)
  ·
    refine ⟨53896894442982215336498543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35931262961988143557665695 53896894442982215336498543)
    ·
      refine ⟨80845341664473323004747815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53896894442982215336498543 80845341664473323004747815)
      ·
        refine ⟨121268012496709984507121723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80845341664473323004747815 121268012496709984507121723)
        ·
          refine ⟨181902018745064976760682585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121268012496709984507121723 181902018745064976760682585)
          ·
            refine ⟨136426514058798732570511939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181902018745064976760682585 136426514058798732570511939)
            ·
              refine ⟨204639771088198098855767909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136426514058798732570511939 204639771088198098855767909)
              ·
                refine ⟨38369957079037143535456483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 204639771088198098855767909 38369957079037143535456483)
                ·
                  refine ⟨57554935618555715303184725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38369957079037143535456483 57554935618555715303184725)
                  ·
                    refine ⟨168617975444987447177299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 57554935618555715303184725 168617975444987447177299)
                    ·
                      rfl

theorem cell23_985147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 10].length) (baseStart_985147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_985147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_985147 prefixEnd_985147 := by exact prefixLift 985147
  have htrace : WordTrace (prefixWord ++ tailWord_985147) baseStart_985147 baseEnd_985147 := by
    simpa [prefixWord, tailWord_985147, baseEnd_985147] using wordTrace_append hprefix tailTrace_985147
  have hstable : (prefixWord ++ tailWord_985147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985147).length < 2 ^ (prefixWord ++ tailWord_985147).sum := by decide
  have hdescent : baseEnd_985147 < baseStart_985147 := by decide
  rcases family_descends (prefixWord ++ tailWord_985147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985242 : List Nat := [3, 1, 1, 5, 3, 1, 1, 1, 2, 2, 3]
def baseStart_985242 : Nat := 118140960795 + 985242 * 2 ^ 59
def prefixEnd_985242 : Nat := 4983230072969 + 3 ^ 40 * 985242 * 2
def baseEnd_985242 : Nat := 505902706997139469843961

theorem tailTrace_985242 : CollatzResearch.WordTrace tailWord_985242 prefixEnd_985242 505902706997139469843961 := by
  unfold tailWord_985242
  simp only [CollatzResearch.WordTrace]
  refine ⟨8983681974160993695593495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23956485264429316521582653 8983681974160993695593495)
  ·
    refine ⟨13475522961241490543390243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8983681974160993695593495 13475522961241490543390243)
    ·
      refine ⟨20213284441862235815085365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13475522961241490543390243 20213284441862235815085365)
      ·
        refine ⟨1894995416424584607664253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20213284441862235815085365 1894995416424584607664253)
        ·
          refine ⟨710623281159219227874095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1894995416424584607664253 710623281159219227874095)
          ·
            refine ⟨1065934921738828841811143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 710623281159219227874095 1065934921738828841811143)
            ·
              refine ⟨1598902382608243262716715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1065934921738828841811143 1598902382608243262716715)
              ·
                refine ⟨2398353573912364894075073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1598902382608243262716715 2398353573912364894075073)
                ·
                  refine ⟨1798765180434273670556305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2398353573912364894075073 1798765180434273670556305)
                  ·
                    refine ⟨1349073885325705252917229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1798765180434273670556305 1349073885325705252917229)
                    ·
                      refine ⟨505902706997139469843961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1349073885325705252917229 505902706997139469843961)
                      ·
                        rfl

theorem cell23_985242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_985242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_985242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_985242 prefixEnd_985242 := by exact prefixLift 985242
  have htrace : WordTrace (prefixWord ++ tailWord_985242) baseStart_985242 baseEnd_985242 := by
    simpa [prefixWord, tailWord_985242, baseEnd_985242] using wordTrace_append hprefix tailTrace_985242
  have hstable : (prefixWord ++ tailWord_985242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985242).length < 2 ^ (prefixWord ++ tailWord_985242).sum := by decide
  have hdescent : baseEnd_985242 < baseStart_985242 := by decide
  rcases family_descends (prefixWord ++ tailWord_985242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985248 : List Nat := [2, 1, 1, 4, 2, 3, 1, 1, 1, 5, 2]
def baseStart_985248 : Nat := 118140960795 + 985248 * 2 ^ 59
def prefixEnd_985248 : Nat := 4983230072969 + 3 ^ 40 * 985248 * 2
def baseEnd_985248 : Nat := 505905787881066446368933

theorem tailTrace_985248 : CollatzResearch.WordTrace tailWord_985248 prefixEnd_985248 505905787881066446368933 := by
  unfold tailWord_985248
  simp only [CollatzResearch.WordTrace]
  refine ⟨17967473367311118903546199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23956631156414825204728265 17967473367311118903546199)
  ·
    refine ⟨26951210050966678355319299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17967473367311118903546199 26951210050966678355319299)
    ·
      refine ⟨40426815076450017532978949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26951210050966678355319299 40426815076450017532978949)
      ·
        refine ⟨7580027826834378287433553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40426815076450017532978949 7580027826834378287433553)
        ·
          refine ⟨5685020870125783715575165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7580027826834378287433553 5685020870125783715575165)
          ·
            refine ⟨2131882826297168893340687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5685020870125783715575165 2131882826297168893340687)
            ·
              refine ⟨3197824239445753340011031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2131882826297168893340687 3197824239445753340011031)
              ·
                refine ⟨4796736359168630010016547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3197824239445753340011031 4796736359168630010016547)
                ·
                  refine ⟨7195104538752945015024821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4796736359168630010016547 7195104538752945015024821)
                  ·
                    refine ⟨674541050508088595158577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7195104538752945015024821 674541050508088595158577)
                    ·
                      refine ⟨505905787881066446368933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 674541050508088595158577 505905787881066446368933)
                      ·
                        rfl

theorem cell23_985248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 1, 1, 5, 2].length) (baseStart_985248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_985248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_985248 prefixEnd_985248 := by exact prefixLift 985248
  have htrace : WordTrace (prefixWord ++ tailWord_985248) baseStart_985248 baseEnd_985248 := by
    simpa [prefixWord, tailWord_985248, baseEnd_985248] using wordTrace_append hprefix tailTrace_985248
  have hstable : (prefixWord ++ tailWord_985248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985248).length < 2 ^ (prefixWord ++ tailWord_985248).sum := by decide
  have hdescent : baseEnd_985248 < baseStart_985248 := by decide
  rcases family_descends (prefixWord ++ tailWord_985248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985262 : List Nat := [4, 1, 4, 2, 1, 2, 1, 2, 6]
def baseStart_985262 : Nat := 118140960795 + 985262 * 2 ^ 59
def prefixEnd_985262 : Nat := 4983230072969 + 3 ^ 40 * 985262 * 2
def baseEnd_985262 : Nat := 56212552956692154621541

theorem tailTrace_985262 : CollatzResearch.WordTrace tailWord_985262 prefixEnd_985262 56212552956692154621541 := by
  unfold tailWord_985262
  simp only [CollatzResearch.WordTrace]
  refine ⟨4491932169571439774762755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23956971571047678798734693 4491932169571439774762755)
  ·
    refine ⟨6737898254357159662144133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4491932169571439774762755 6737898254357159662144133)
    ·
      refine ⟨1263355922691967436652025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6737898254357159662144133 1263355922691967436652025)
      ·
        refine ⟨947516942018975577489019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1263355922691967436652025 947516942018975577489019)
        ·
          refine ⟨1421275413028463366233529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 947516942018975577489019 1421275413028463366233529)
          ·
            refine ⟨1065956559771347524675147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1421275413028463366233529 1065956559771347524675147)
            ·
              refine ⟨1598934839657021287012721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1065956559771347524675147 1598934839657021287012721)
              ·
                refine ⟨1199201129742765965259541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1598934839657021287012721 1199201129742765965259541)
                ·
                  refine ⟨56212552956692154621541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1199201129742765965259541 56212552956692154621541)
                  ·
                    rfl

theorem cell23_985262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 2, 6].length) (baseStart_985262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_985262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_985262 prefixEnd_985262 := by exact prefixLift 985262
  have htrace : WordTrace (prefixWord ++ tailWord_985262) baseStart_985262 baseEnd_985262 := by
    simpa [prefixWord, tailWord_985262, baseEnd_985262] using wordTrace_append hprefix tailTrace_985262
  have hstable : (prefixWord ++ tailWord_985262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985262).length < 2 ^ (prefixWord ++ tailWord_985262).sum := by decide
  have hdescent : baseEnd_985262 < baseStart_985262 := by decide
  rcases family_descends (prefixWord ++ tailWord_985262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985282 : List Nat := [3, 5, 1, 1, 1, 1, 1, 2, 1, 5, 2]
def baseStart_985282 : Nat := 118140960795 + 985282 * 2 ^ 59
def prefixEnd_985282 : Nat := 4983230072969 + 3 ^ 40 * 985282 * 2
def baseEnd_985282 : Nat := 505923246223319313343777

theorem tailTrace_985282 : CollatzResearch.WordTrace tailWord_985282 prefixEnd_985282 505923246223319313343777 := by
  unfold tailWord_985282
  simp only [CollatzResearch.WordTrace]
  refine ⟨8984046704124765403457525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23957457877666041075886733 8984046704124765403457525)
  ·
    refine ⟨842254378511696756574143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8984046704124765403457525 842254378511696756574143)
    ·
      refine ⟨1263381567767545134861215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 842254378511696756574143 1263381567767545134861215)
      ·
        refine ⟨1895072351651317702291823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1263381567767545134861215 1895072351651317702291823)
        ·
          refine ⟨2842608527476976553437735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1895072351651317702291823 2842608527476976553437735)
          ·
            refine ⟨4263912791215464830156603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2842608527476976553437735 4263912791215464830156603)
            ·
              refine ⟨6395869186823197245234905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4263912791215464830156603 6395869186823197245234905)
              ·
                refine ⟨4796901890117397933926179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6395869186823197245234905 4796901890117397933926179)
                ·
                  refine ⟨7195352835176096900889269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4796901890117397933926179 7195352835176096900889269)
                  ·
                    refine ⟨674564328297759084458369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7195352835176096900889269 674564328297759084458369)
                    ·
                      refine ⟨505923246223319313343777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 674564328297759084458369 505923246223319313343777)
                      ·
                        rfl

theorem cell23_985282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_985282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_985282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_985282 prefixEnd_985282 := by exact prefixLift 985282
  have htrace : WordTrace (prefixWord ++ tailWord_985282) baseStart_985282 baseEnd_985282 := by
    simpa [prefixWord, tailWord_985282, baseEnd_985282] using wordTrace_append hprefix tailTrace_985282
  have hstable : (prefixWord ++ tailWord_985282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985282).length < 2 ^ (prefixWord ++ tailWord_985282).sum := by decide
  have hdescent : baseEnd_985282 < baseStart_985282 := by decide
  rcases family_descends (prefixWord ++ tailWord_985282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985311 : List Nat := [1, 1, 2, 3, 2, 1, 1, 3, 3, 3, 3]
def baseStart_985311 : Nat := 118140960795 + 985311 * 2 ^ 59
def prefixEnd_985311 : Nat := 4983230072969 + 3 ^ 40 * 985311 * 2
def baseEnd_985311 : Nat := 505938137162299699881143

theorem tailTrace_985311 : CollatzResearch.WordTrace tailWord_985311 prefixEnd_985311 505938137162299699881143 := by
  unfold tailWord_985311
  simp only [CollatzResearch.WordTrace]
  refine ⟨35937244533393999566635787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23958163022262666377757191 35937244533393999566635787)
  ·
    refine ⟨53905866800090999349953681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35937244533393999566635787 53905866800090999349953681)
    ·
      refine ⟨40429400100068249512465261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53905866800090999349953681 40429400100068249512465261)
      ·
        refine ⟨15161025037525593567174473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40429400100068249512465261 15161025037525593567174473)
        ·
          refine ⟨11370768778144195175380855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15161025037525593567174473 11370768778144195175380855)
          ·
            refine ⟨17056153167216292763071283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11370768778144195175380855 17056153167216292763071283)
            ·
              refine ⟨25584229750824439144606925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17056153167216292763071283 25584229750824439144606925)
              ·
                refine ⟨9594086156559164679227597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25584229750824439144606925 9594086156559164679227597)
                ·
                  refine ⟨3597782308709686754710349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9594086156559164679227597 3597782308709686754710349)
                  ·
                    refine ⟨1349168365766132533016381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3597782308709686754710349 1349168365766132533016381)
                    ·
                      refine ⟨505938137162299699881143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1349168365766132533016381 505938137162299699881143)
                      ·
                        rfl

theorem cell23_985311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 3, 3, 3].length) (baseStart_985311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_985311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_985311 prefixEnd_985311 := by exact prefixLift 985311
  have htrace : WordTrace (prefixWord ++ tailWord_985311) baseStart_985311 baseEnd_985311 := by
    simpa [prefixWord, tailWord_985311, baseEnd_985311] using wordTrace_append hprefix tailTrace_985311
  have hstable : (prefixWord ++ tailWord_985311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985311).length < 2 ^ (prefixWord ++ tailWord_985311).sum := by decide
  have hdescent : baseEnd_985311 < baseStart_985311 := by decide
  rcases family_descends (prefixWord ++ tailWord_985311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985315 : List Nat := [1, 1, 1, 8, 1, 1, 2, 1, 1, 1, 5]
def baseStart_985315 : Nat := 118140960795 + 985315 * 2 ^ 59
def prefixEnd_985315 : Nat := 4983230072969 + 3 ^ 40 * 985315 * 2
def baseEnd_985315 : Nat := 505940191084917684231125

theorem tailTrace_985315 : CollatzResearch.WordTrace tailWord_985315 prefixEnd_985315 505940191084917684231125 := by
  unfold tailWord_985315
  simp only [CollatzResearch.WordTrace]
  refine ⟨35937390425379508249781399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23958260283586338833187599 35937390425379508249781399)
  ·
    refine ⟨53906085638069262374672099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35937390425379508249781399 53906085638069262374672099)
    ·
      refine ⟨80859128457103893562008149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53906085638069262374672099 80859128457103893562008149)
      ·
        refine ⟨947567911606686252679783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 80859128457103893562008149 947567911606686252679783)
        ·
          refine ⟨1421351867410029379019675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 947567911606686252679783 1421351867410029379019675)
          ·
            refine ⟨2132027801115044068529513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1421351867410029379019675 2132027801115044068529513)
            ·
              refine ⟨1599020850836283051397135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2132027801115044068529513 1599020850836283051397135)
              ·
                refine ⟨2398531276254424577095703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1599020850836283051397135 2398531276254424577095703)
                ·
                  refine ⟨3597796914381636865643555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2398531276254424577095703 3597796914381636865643555)
                  ·
                    refine ⟨5396695371572455298465333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3597796914381636865643555 5396695371572455298465333)
                    ·
                      refine ⟨505940191084917684231125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5396695371572455298465333 505940191084917684231125)
                      ·
                        rfl

theorem cell23_985315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_985315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_985315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_985315 prefixEnd_985315 := by exact prefixLift 985315
  have htrace : WordTrace (prefixWord ++ tailWord_985315) baseStart_985315 baseEnd_985315 := by
    simpa [prefixWord, tailWord_985315, baseEnd_985315] using wordTrace_append hprefix tailTrace_985315
  have hstable : (prefixWord ++ tailWord_985315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985315).length < 2 ^ (prefixWord ++ tailWord_985315).sum := by decide
  have hdescent : baseEnd_985315 < baseStart_985315 := by decide
  rcases family_descends (prefixWord ++ tailWord_985315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985345 : List Nat := [1, 2, 4, 1, 1, 2, 3, 3, 2, 1, 3]
def baseStart_985345 : Nat := 118140960795 + 985345 * 2 ^ 59
def prefixEnd_985345 : Nat := 4983230072969 + 3 ^ 40 * 985345 * 2
def baseEnd_985345 : Nat := 505955595504552566855987

theorem tailTrace_985345 : CollatzResearch.WordTrace tailWord_985345 prefixEnd_985345 505955595504552566855987 := by
  unfold tailWord_985345
  simp only [CollatzResearch.WordTrace]
  refine ⟨35938484615270823373373489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23958989743513882248915659 35938484615270823373373489)
  ·
    refine ⟨26953863461453117530030117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35938484615270823373373489 26953863461453117530030117)
    ·
      refine ⟨5053849399022459536880647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26953863461453117530030117 5053849399022459536880647)
      ·
        refine ⟨7580774098533689305320971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5053849399022459536880647 7580774098533689305320971)
        ·
          refine ⟨11371161147800533957981457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7580774098533689305320971 11371161147800533957981457)
          ·
            refine ⟨8528370860850400468486093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11371161147800533957981457 8528370860850400468486093)
            ·
              refine ⟨3198139072818900175682285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8528370860850400468486093 3198139072818900175682285)
              ·
                refine ⟨1199302152307087565880857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3198139072818900175682285 1199302152307087565880857)
                ·
                  refine ⟨899476614230315674410643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1199302152307087565880857 899476614230315674410643)
                  ·
                    refine ⟨1349214921345473511615965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 899476614230315674410643 1349214921345473511615965)
                    ·
                      refine ⟨505955595504552566855987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1349214921345473511615965 505955595504552566855987)
                      ·
                        rfl

theorem cell23_985345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 3, 2, 1, 3].length) (baseStart_985345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_985345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_985345 prefixEnd_985345 := by exact prefixLift 985345
  have htrace : WordTrace (prefixWord ++ tailWord_985345) baseStart_985345 baseEnd_985345 := by
    simpa [prefixWord, tailWord_985345, baseEnd_985345] using wordTrace_append hprefix tailTrace_985345
  have hstable : (prefixWord ++ tailWord_985345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985345).length < 2 ^ (prefixWord ++ tailWord_985345).sum := by decide
  have hdescent : baseEnd_985345 < baseStart_985345 := by decide
  rcases family_descends (prefixWord ++ tailWord_985345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985371 : List Nat := [1, 1, 1, 1, 1, 1, 8, 1, 2, 1, 5]
def baseStart_985371 : Nat := 118140960795 + 985371 * 2 ^ 59
def prefixEnd_985371 : Nat := 4983230072969 + 3 ^ 40 * 985371 * 2
def baseEnd_985371 : Nat := 505968946001569465130867

theorem tailTrace_985371 : CollatzResearch.WordTrace tailWord_985371 prefixEnd_985371 505968946001569465130867 := by
  unfold tailWord_985371
  simp only [CollatzResearch.WordTrace]
  refine ⟨35939432913176629813819967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23959621942117753209213311 35939432913176629813819967)
  ·
    refine ⟨53909149369764944720729951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35939432913176629813819967 53909149369764944720729951)
    ·
      refine ⟨80863724054647417081094927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53909149369764944720729951 80863724054647417081094927)
      ·
        refine ⟨121295586081971125621642391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80863724054647417081094927 121295586081971125621642391)
        ·
          refine ⟨181943379122956688432463587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121295586081971125621642391 181943379122956688432463587)
          ·
            refine ⟨272915068684435032648695381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181943379122956688432463587 272915068684435032648695381)
            ·
              refine ⟨3198223461145723038851899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 272915068684435032648695381 3198223461145723038851899)
              ·
                refine ⟨4797335191718584558277849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3198223461145723038851899 4797335191718584558277849)
                ·
                  refine ⟨3598001393788938418708387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4797335191718584558277849 3598001393788938418708387)
                  ·
                    refine ⟨5397002090683407628062581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3598001393788938418708387 5397002090683407628062581)
                    ·
                      refine ⟨505968946001569465130867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5397002090683407628062581 505968946001569465130867)
                      ·
                        rfl

theorem cell23_985371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 1, 2, 1, 5].length) (baseStart_985371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_985371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_985371 prefixEnd_985371 := by exact prefixLift 985371
  have htrace : WordTrace (prefixWord ++ tailWord_985371) baseStart_985371 baseEnd_985371 := by
    simpa [prefixWord, tailWord_985371, baseEnd_985371] using wordTrace_append hprefix tailTrace_985371
  have hstable : (prefixWord ++ tailWord_985371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985371).length < 2 ^ (prefixWord ++ tailWord_985371).sum := by decide
  have hdescent : baseEnd_985371 < baseStart_985371 := by decide
  rcases family_descends (prefixWord ++ tailWord_985371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985402 : List Nat := [3, 1, 1, 1, 4, 2, 2, 3, 2, 2, 2]
def baseStart_985402 : Nat := 118140960795 + 985402 * 2 ^ 59
def prefixEnd_985402 : Nat := 4983230072969 + 3 ^ 40 * 985402 * 2
def baseEnd_985402 : Nat := 505984863901858843843225

theorem tailTrace_985402 : CollatzResearch.WordTrace tailWord_985402 prefixEnd_985402 505984863901858843843225 := by
  unfold tailWord_985402
  simp only [CollatzResearch.WordTrace]
  refine ⟨8985140894016080527049615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23960375717376214738798973 8985140894016080527049615)
  ·
    refine ⟨13477711341024120790574423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8985140894016080527049615 13477711341024120790574423)
    ·
      refine ⟨20216567011536181185861635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13477711341024120790574423 20216567011536181185861635)
      ·
        refine ⟨30324850517304271778792453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20216567011536181185861635 30324850517304271778792453)
        ·
          refine ⟨5685909471994550958523585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30324850517304271778792453 5685909471994550958523585)
          ·
            refine ⟨4264432103995913218892689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5685909471994550958523585 4264432103995913218892689)
            ·
              refine ⟨3198324077996934914169517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4264432103995913218892689 3198324077996934914169517)
              ·
                refine ⟨1199371529248850592813569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3198324077996934914169517 1199371529248850592813569)
                ·
                  refine ⟨899528646936637944610177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1199371529248850592813569 899528646936637944610177)
                  ·
                    refine ⟨674646485202478458457633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 899528646936637944610177 674646485202478458457633)
                    ·
                      refine ⟨505984863901858843843225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 674646485202478458457633 505984863901858843843225)
                      ·
                        rfl

theorem cell23_985402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 3, 2, 2, 2].length) (baseStart_985402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_985402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_985402 prefixEnd_985402 := by exact prefixLift 985402
  have htrace : WordTrace (prefixWord ++ tailWord_985402) baseStart_985402 baseEnd_985402 := by
    simpa [prefixWord, tailWord_985402, baseEnd_985402] using wordTrace_append hprefix tailTrace_985402
  have hstable : (prefixWord ++ tailWord_985402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985402).length < 2 ^ (prefixWord ++ tailWord_985402).sum := by decide
  have hdescent : baseEnd_985402 < baseStart_985402 := by decide
  rcases family_descends (prefixWord ++ tailWord_985402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985425 : List Nat := [1, 2, 2, 1, 4, 3, 2, 3, 5]
def baseStart_985425 : Nat := 118140960795 + 985425 * 2 ^ 59
def prefixEnd_985425 : Nat := 4983230072969 + 3 ^ 40 * 985425 * 2
def baseEnd_985425 : Nat := 56221852661879139317291

theorem tailTrace_985425 : CollatzResearch.WordTrace tailWord_985425 prefixEnd_985425 56221852661879139317291 := by
  unfold tailWord_985425
  simp only [CollatzResearch.WordTrace]
  refine ⟨35941402454980997036285729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23960934969987331357523819 35941402454980997036285729)
  ·
    refine ⟨26956051841235747777214297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35941402454980997036285729 26956051841235747777214297)
    ·
      refine ⟨20217038880926810832910723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26956051841235747777214297 20217038880926810832910723)
      ·
        refine ⟨30325558321390216249366085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20217038880926810832910723 30325558321390216249366085)
        ·
          refine ⟨5686042185260665546756141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30325558321390216249366085 5686042185260665546756141)
          ·
            refine ⟨2132265819472749580033553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5686042185260665546756141 2132265819472749580033553)
            ·
              refine ⟨1599199364604562185025165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2132265819472749580033553 1599199364604562185025165)
              ·
                refine ⟨599699761726710819384437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1599199364604562185025165 599699761726710819384437)
                ·
                  refine ⟨56221852661879139317291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 599699761726710819384437 56221852661879139317291)
                  ·
                    rfl

theorem cell23_985425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 3, 5].length) (baseStart_985425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_985425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_985425 prefixEnd_985425 := by exact prefixLift 985425
  have htrace : WordTrace (prefixWord ++ tailWord_985425) baseStart_985425 baseEnd_985425 := by
    simpa [prefixWord, tailWord_985425, baseEnd_985425] using wordTrace_append hprefix tailTrace_985425
  have hstable : (prefixWord ++ tailWord_985425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985425).length < 2 ^ (prefixWord ++ tailWord_985425).sum := by decide
  have hdescent : baseEnd_985425 < baseStart_985425 := by decide
  rcases family_descends (prefixWord ++ tailWord_985425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985458 : List Nat := [3, 2, 1, 2, 1, 3, 1, 2, 1, 3, 4]
def baseStart_985458 : Nat := 118140960795 + 985458 * 2 ^ 59
def prefixEnd_985458 : Nat := 4983230072969 + 3 ^ 40 * 985458 * 2
def baseEnd_985458 : Nat := 506013618818510624742967

theorem tailTrace_985458 : CollatzResearch.WordTrace tailWord_985458 prefixEnd_985458 506013618818510624742967 := by
  unfold tailWord_985458
  simp only [CollatzResearch.WordTrace]
  refine ⟨8985651515965360918059257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23961737375907629114824685 8985651515965360918059257)
  ·
    refine ⟨6739238636974020688544443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8985651515965360918059257 6739238636974020688544443)
    ·
      refine ⟨10108857955461031032816665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6739238636974020688544443 10108857955461031032816665)
      ·
        refine ⟨7581643466595773274612499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10108857955461031032816665 7581643466595773274612499)
        ·
          refine ⟨11372465199893659911918749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7581643466595773274612499 11372465199893659911918749)
          ·
            refine ⟨4264674449960122466969531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11372465199893659911918749 4264674449960122466969531)
            ·
              refine ⟨6397011674940183700454297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4264674449960122466969531 6397011674940183700454297)
              ·
                refine ⟨4797758756205137775340723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6397011674940183700454297 4797758756205137775340723)
                ·
                  refine ⟨7196638134307706663011085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4797758756205137775340723 7196638134307706663011085)
                  ·
                    refine ⟨2698739300365389998629157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7196638134307706663011085 2698739300365389998629157)
                    ·
                      refine ⟨506013618818510624742967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2698739300365389998629157 506013618818510624742967)
                      ·
                        rfl

theorem cell23_985458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_985458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_985458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_985458 prefixEnd_985458 := by exact prefixLift 985458
  have htrace : WordTrace (prefixWord ++ tailWord_985458) baseStart_985458 baseEnd_985458 := by
    simpa [prefixWord, tailWord_985458, baseEnd_985458] using wordTrace_append hprefix tailTrace_985458
  have hstable : (prefixWord ++ tailWord_985458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985458).length < 2 ^ (prefixWord ++ tailWord_985458).sum := by decide
  have hdescent : baseEnd_985458 < baseStart_985458 := by decide
  rcases family_descends (prefixWord ++ tailWord_985458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985468 : List Nat := [2, 2, 2, 1, 1, 1, 2, 3, 5, 4]
def baseStart_985468 : Nat := 118140960795 + 985468 * 2 ^ 59
def prefixEnd_985468 : Nat := 4983230072969 + 3 ^ 40 * 985468 * 2
def baseEnd_985468 : Nat := 168672917875018528539307

theorem tailTrace_985468 : CollatzResearch.WordTrace tailWord_985468 prefixEnd_985468 168672917875018528539307 := by
  unfold tailWord_985468
  simp only [CollatzResearch.WordTrace]
  refine ⟨17971485396912607690050529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23961980529216810253400705 17971485396912607690050529)
  ·
    refine ⟨13478614047684455767537897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17971485396912607690050529 13478614047684455767537897)
    ·
      refine ⟨10108960535763341825653423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13478614047684455767537897 10108960535763341825653423)
      ·
        refine ⟨15163440803645012738480135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10108960535763341825653423 15163440803645012738480135)
        ·
          refine ⟨22745161205467519107720203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15163440803645012738480135 22745161205467519107720203)
          ·
            refine ⟨34117741808201278661580305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22745161205467519107720203 34117741808201278661580305)
            ·
              refine ⟨25588306356150958996185229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34117741808201278661580305 25588306356150958996185229)
              ·
                refine ⟨9595614883556609623569461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25588306356150958996185229 9595614883556609623569461)
                ·
                  refine ⟨899588895333432152209637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9595614883556609623569461 899588895333432152209637)
                  ·
                    refine ⟨168672917875018528539307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 899588895333432152209637 168672917875018528539307)
                    ·
                      rfl

theorem cell23_985468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 5, 4].length) (baseStart_985468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_985468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_985468 prefixEnd_985468 := by exact prefixLift 985468
  have htrace : WordTrace (prefixWord ++ tailWord_985468) baseStart_985468 baseEnd_985468 := by
    simpa [prefixWord, tailWord_985468, baseEnd_985468] using wordTrace_append hprefix tailTrace_985468
  have hstable : (prefixWord ++ tailWord_985468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985468).length < 2 ^ (prefixWord ++ tailWord_985468).sum := by decide
  have hdescent : baseEnd_985468 < baseStart_985468 := by decide
  rcases family_descends (prefixWord ++ tailWord_985468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985471 : List Nat := [1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 6]
def baseStart_985471 : Nat := 118140960795 + 985471 * 2 ^ 59
def prefixEnd_985471 : Nat := 4983230072969 + 3 ^ 40 * 985471 * 2
def baseEnd_985471 : Nat := 506020294067019073880407

theorem tailTrace_985471 : CollatzResearch.WordTrace tailWord_985471 prefixEnd_985471 506020294067019073880407 := by
  unfold tailWord_985471
  simp only [CollatzResearch.WordTrace]
  refine ⟨35943080212814346892460267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23962053475209564594973511 35943080212814346892460267)
  ·
    refine ⟨53914620319221520338690401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35943080212814346892460267 53914620319221520338690401)
    ·
      refine ⟨40435965239416140254017801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53914620319221520338690401 40435965239416140254017801)
      ·
        refine ⟨30326973929562105190513351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40435965239416140254017801 30326973929562105190513351)
        ·
          refine ⟨45490460894343157785770027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30326973929562105190513351 45490460894343157785770027)
          ·
            refine ⟨68235691341514736678655041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45490460894343157785770027 68235691341514736678655041)
            ·
              refine ⟨51176768506136052508991281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68235691341514736678655041 51176768506136052508991281)
              ·
                refine ⟨38382576379602039381743461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51176768506136052508991281 38382576379602039381743461)
                ·
                  refine ⟨7196733071175382384076899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38382576379602039381743461 7196733071175382384076899)
                  ·
                    refine ⟨10795099606763073576115349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7196733071175382384076899 10795099606763073576115349)
                    ·
                      refine ⟨506020294067019073880407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10795099606763073576115349 506020294067019073880407)
                      ·
                        rfl

theorem cell23_985471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 6].length) (baseStart_985471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_985471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_985471 prefixEnd_985471 := by exact prefixLift 985471
  have htrace : WordTrace (prefixWord ++ tailWord_985471) baseStart_985471 baseEnd_985471 := by
    simpa [prefixWord, tailWord_985471, baseEnd_985471] using wordTrace_append hprefix tailTrace_985471
  have hstable : (prefixWord ++ tailWord_985471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985471).length < 2 ^ (prefixWord ++ tailWord_985471).sum := by decide
  have hdescent : baseEnd_985471 < baseStart_985471 := by decide
  rcases family_descends (prefixWord ++ tailWord_985471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985492 : List Nat := [2, 4, 2, 1, 3, 1, 1, 2, 2, 1, 4]
def baseStart_985492 : Nat := 118140960795 + 985492 * 2 ^ 59
def prefixEnd_985492 : Nat := 4983230072969 + 3 ^ 40 * 985492 * 2
def baseEnd_985492 : Nat := 506031077160763491717811

theorem tailTrace_985492 : CollatzResearch.WordTrace tailWord_985492 prefixEnd_985492 506031077160763491717811 := by
  unfold tailWord_985492
  simp only [CollatzResearch.WordTrace]
  refine ⟨17971923072869133739487365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23962564097158844985983153 17971923072869133739487365)
  ·
    refine ⟨3369735576162962576153881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17971923072869133739487365 3369735576162962576153881)
    ·
      refine ⟨2527301682122221932115411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3369735576162962576153881 2527301682122221932115411)
      ·
        refine ⟨3790952523183332898173117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2527301682122221932115411 3790952523183332898173117)
        ·
          refine ⟨1421607196193749836814919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3790952523183332898173117 1421607196193749836814919)
          ·
            refine ⟨2132410794290624755222379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1421607196193749836814919 2132410794290624755222379)
            ·
              refine ⟨3198616191435937132833569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2132410794290624755222379 3198616191435937132833569)
              ·
                refine ⟨2398962143576952849625177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3198616191435937132833569 2398962143576952849625177)
                ·
                  refine ⟨1799221607682714637218883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2398962143576952849625177 1799221607682714637218883)
                  ·
                    refine ⟨2698832411524071955828325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1799221607682714637218883 2698832411524071955828325)
                    ·
                      refine ⟨506031077160763491717811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2698832411524071955828325 506031077160763491717811)
                      ·
                        rfl

theorem cell23_985492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_985492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_985492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_985492 prefixEnd_985492 := by exact prefixLift 985492
  have htrace : WordTrace (prefixWord ++ tailWord_985492) baseStart_985492 baseEnd_985492 := by
    simpa [prefixWord, tailWord_985492, baseEnd_985492] using wordTrace_append hprefix tailTrace_985492
  have hstable : (prefixWord ++ tailWord_985492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985492).length < 2 ^ (prefixWord ++ tailWord_985492).sum := by decide
  have hdescent : baseEnd_985492 < baseStart_985492 := by decide
  rcases family_descends (prefixWord ++ tailWord_985492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985498 : List Nat := [3, 1, 1, 4, 1, 2, 2, 1, 8]
def baseStart_985498 : Nat := 118140960795 + 985498 * 2 ^ 59
def prefixEnd_985498 : Nat := 4983230072969 + 3 ^ 40 * 985498 * 2
def baseEnd_985498 : Nat := 56226017560521163138087

theorem tailTrace_985498 : CollatzResearch.WordTrace tailWord_985498 prefixEnd_985498 56226017560521163138087 := by
  unfold tailWord_985498
  simp only [CollatzResearch.WordTrace]
  refine ⟨8986016245929132625923287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23962709989144353669128765 8986016245929132625923287)
  ·
    refine ⟨13479024368893698938884931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8986016245929132625923287 13479024368893698938884931)
    ·
      refine ⟨20218536553340548408327397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13479024368893698938884931 20218536553340548408327397)
      ·
        refine ⟨3790975603751352826561387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20218536553340548408327397 3790975603751352826561387)
        ·
          refine ⟨5686463405627029239842081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3790975603751352826561387 5686463405627029239842081)
          ·
            refine ⟨4264847554220271929881561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5686463405627029239842081 4264847554220271929881561)
            ·
              refine ⟨3198635665665203947411171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4264847554220271929881561 3198635665665203947411171)
              ·
                refine ⟨4797953498497805921116757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3198635665665203947411171 4797953498497805921116757)
                ·
                  refine ⟨56226017560521163138087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4797953498497805921116757 56226017560521163138087)
                  ·
                    rfl

theorem cell23_985498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 1, 8].length) (baseStart_985498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_985498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_985498 prefixEnd_985498 := by exact prefixLift 985498
  have htrace : WordTrace (prefixWord ++ tailWord_985498) baseStart_985498 baseEnd_985498 := by
    simpa [prefixWord, tailWord_985498, baseEnd_985498] using wordTrace_append hprefix tailTrace_985498
  have hstable : (prefixWord ++ tailWord_985498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985498).length < 2 ^ (prefixWord ++ tailWord_985498).sum := by decide
  have hdescent : baseEnd_985498 < baseStart_985498 := by decide
  rcases family_descends (prefixWord ++ tailWord_985498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985565 : List Nat := [1, 4, 3, 1, 1, 1, 1, 1, 5, 1, 4]
def baseStart_985565 : Nat := 118140960795 + 985565 * 2 ^ 59
def prefixEnd_985565 : Nat := 4983230072969 + 3 ^ 40 * 985565 * 2
def baseEnd_985565 : Nat := 506068561248541706104975

theorem tailTrace_985565 : CollatzResearch.WordTrace tailWord_985565 prefixEnd_985565 506068561248541706104975 := by
  unfold tailWord_985565
  simp only [CollatzResearch.WordTrace]
  refine ⟨35946508674473800946382149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23964339116315867297588099 35946508674473800946382149)
  ·
    refine ⟨6739970376463837677446653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35946508674473800946382149 6739970376463837677446653)
    ·
      refine ⟨2527488891173939129042495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6739970376463837677446653 2527488891173939129042495)
      ·
        refine ⟨3791233336760908693563743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2527488891173939129042495 3791233336760908693563743)
        ·
          refine ⟨5686850005141363040345615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3791233336760908693563743 5686850005141363040345615)
          ·
            refine ⟨8530275007712044560518423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5686850005141363040345615 8530275007712044560518423)
            ·
              refine ⟨12795412511568066840777635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8530275007712044560518423 12795412511568066840777635)
              ·
                refine ⟨19193118767352100261166453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12795412511568066840777635 19193118767352100261166453)
                ·
                  refine ⟨1799354884439259399484355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19193118767352100261166453 1799354884439259399484355)
                  ·
                    refine ⟨2699032326658889099226533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1799354884439259399484355 2699032326658889099226533)
                    ·
                      refine ⟨506068561248541706104975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2699032326658889099226533 506068561248541706104975)
                      ·
                        rfl

theorem cell23_985565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_985565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_985565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_985565 prefixEnd_985565 := by exact prefixLift 985565
  have htrace : WordTrace (prefixWord ++ tailWord_985565) baseStart_985565 baseEnd_985565 := by
    simpa [prefixWord, tailWord_985565, baseEnd_985565] using wordTrace_append hprefix tailTrace_985565
  have hstable : (prefixWord ++ tailWord_985565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985565).length < 2 ^ (prefixWord ++ tailWord_985565).sum := by decide
  have hdescent : baseEnd_985565 < baseStart_985565 := by decide
  rcases family_descends (prefixWord ++ tailWord_985565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985568 : List Nat := [2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 5]
def baseStart_985568 : Nat := 118140960795 + 985568 * 2 ^ 59
def prefixEnd_985568 : Nat := 4983230072969 + 3 ^ 40 * 985568 * 2
def baseEnd_985568 : Nat := 506070101690505194367461

theorem tailTrace_985568 : CollatzResearch.WordTrace tailWord_985568 prefixEnd_985568 506070101690505194367461 := by
  unfold tailWord_985568
  simp only [CollatzResearch.WordTrace]
  refine ⟨17973309046731466229370679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23964412062308621639160905 17973309046731466229370679)
  ·
    refine ⟨26959963570097199344056019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17973309046731466229370679 26959963570097199344056019)
    ·
      refine ⟨40439945355145799016084029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26959963570097199344056019 40439945355145799016084029)
      ·
        refine ⟨15164979508179674631031511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40439945355145799016084029 15164979508179674631031511)
        ·
          refine ⟨22747469262269511946547267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15164979508179674631031511 22747469262269511946547267)
          ·
            refine ⟨34121203893404267919820901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22747469262269511946547267 34121203893404267919820901)
            ·
              refine ⟨6397725730013300234966419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34121203893404267919820901 6397725730013300234966419)
              ·
                refine ⟨9596588595019950352449629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6397725730013300234966419 9596588595019950352449629)
                ·
                  refine ⟨3598720723132481382168611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9596588595019950352449629 3598720723132481382168611)
                  ·
                    refine ⟨5398081084698722073252917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3598720723132481382168611 5398081084698722073252917)
                    ·
                      refine ⟨506070101690505194367461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5398081084698722073252917 506070101690505194367461)
                      ·
                        rfl

theorem cell23_985568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 5].length) (baseStart_985568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_985568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_985568 prefixEnd_985568 := by exact prefixLift 985568
  have htrace : WordTrace (prefixWord ++ tailWord_985568) baseStart_985568 baseEnd_985568 := by
    simpa [prefixWord, tailWord_985568, baseEnd_985568] using wordTrace_append hprefix tailTrace_985568
  have hstable : (prefixWord ++ tailWord_985568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985568).length < 2 ^ (prefixWord ++ tailWord_985568).sum := by decide
  have hdescent : baseEnd_985568 < baseStart_985568 := by decide
  rcases family_descends (prefixWord ++ tailWord_985568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985575 : List Nat := [1, 1, 5, 2, 1, 1, 4, 1, 1, 6]
def baseStart_985575 : Nat := 118140960795 + 985575 * 2 ^ 59
def prefixEnd_985575 : Nat := 4983230072969 + 3 ^ 40 * 985575 * 2
def baseEnd_985575 : Nat := 168691232018362222326643

theorem tailTrace_985575 : CollatzResearch.WordTrace tailWord_985575 prefixEnd_985575 168691232018362222326643 := by
  unfold tailWord_985575
  simp only [CollatzResearch.WordTrace]
  refine ⟨35946873404437572654246179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23964582269625048436164119 35946873404437572654246179)
  ·
    refine ⟨53920310106656358981369269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35946873404437572654246179 53920310106656358981369269)
    ·
      refine ⟨5055029072499033654503369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53920310106656358981369269 5055029072499033654503369)
      ·
        refine ⟨3791271804374275240877527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5055029072499033654503369 3791271804374275240877527)
        ·
          refine ⟨5686907706561412861316291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3791271804374275240877527 5686907706561412861316291)
          ·
            refine ⟨8530361559842119291974437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5686907706561412861316291 8530361559842119291974437)
            ·
              refine ⟨1599442792470397367245207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8530361559842119291974437 1599442792470397367245207)
              ·
                refine ⟨2399164188705596050867811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1599442792470397367245207 2399164188705596050867811)
                ·
                  refine ⟨3598746283058394076301717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2399164188705596050867811 3598746283058394076301717)
                  ·
                    refine ⟨168691232018362222326643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3598746283058394076301717 168691232018362222326643)
                    ·
                      rfl

theorem cell23_985575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 1, 1, 6].length) (baseStart_985575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_985575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_985575 prefixEnd_985575 := by exact prefixLift 985575
  have htrace : WordTrace (prefixWord ++ tailWord_985575) baseStart_985575 baseEnd_985575 := by
    simpa [prefixWord, tailWord_985575, baseEnd_985575] using wordTrace_append hprefix tailTrace_985575
  have hstable : (prefixWord ++ tailWord_985575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985575).length < 2 ^ (prefixWord ++ tailWord_985575).sum := by decide
  have hdescent : baseEnd_985575 < baseStart_985575 := by decide
  rcases family_descends (prefixWord ++ tailWord_985575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985585 : List Nat := [1, 2, 2, 2, 3, 1, 1, 3, 3, 2, 3]
def baseStart_985585 : Nat := 118140960795 + 985585 * 2 ^ 59
def prefixEnd_985585 : Nat := 4983230072969 + 3 ^ 40 * 985585 * 2
def baseEnd_985585 : Nat := 506078830861631627854883

theorem tailTrace_985585 : CollatzResearch.WordTrace tailWord_985585 prefixEnd_985585 506078830861631627854883 := by
  unfold tailWord_985585
  simp only [CollatzResearch.WordTrace]
  refine ⟨35947238134401344362110209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23964825422934229574740139 35947238134401344362110209)
  ·
    refine ⟨26960428600801008271582657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35947238134401344362110209 26960428600801008271582657)
    ·
      refine ⟨20220321450600756203686993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26960428600801008271582657 20220321450600756203686993)
      ·
        refine ⟨15165241087950567152765245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20220321450600756203686993 15165241087950567152765245)
        ·
          refine ⟨5686965407981462682286967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15165241087950567152765245 5686965407981462682286967)
          ·
            refine ⟨8530448111972194023430451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5686965407981462682286967 8530448111972194023430451)
            ·
              refine ⟨12795672167958291035145677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8530448111972194023430451 12795672167958291035145677)
              ·
                refine ⟨4798377062984359138179629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12795672167958291035145677 4798377062984359138179629)
                ·
                  refine ⟨1799391398619134676817361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4798377062984359138179629 1799391398619134676817361)
                  ·
                    refine ⟨1349543548964351007613021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1799391398619134676817361 1349543548964351007613021)
                    ·
                      refine ⟨506078830861631627854883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1349543548964351007613021 506078830861631627854883)
                      ·
                        rfl

theorem cell23_985585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 3, 3, 2, 3].length) (baseStart_985585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_985585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_985585 prefixEnd_985585 := by exact prefixLift 985585
  have htrace : WordTrace (prefixWord ++ tailWord_985585) baseStart_985585 baseEnd_985585 := by
    simpa [prefixWord, tailWord_985585, baseEnd_985585] using wordTrace_append hprefix tailTrace_985585
  have hstable : (prefixWord ++ tailWord_985585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985585).length < 2 ^ (prefixWord ++ tailWord_985585).sum := by decide
  have hdescent : baseEnd_985585 < baseStart_985585 := by decide
  rcases family_descends (prefixWord ++ tailWord_985585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985586 : List Nat := [3, 2, 1, 4, 2, 2, 1, 1, 2, 3, 2]
def baseStart_985586 : Nat := 118140960795 + 985586 * 2 ^ 59
def prefixEnd_985586 : Nat := 4983230072969 + 3 ^ 40 * 985586 * 2
def baseEnd_985586 : Nat := 506079344342286123942379

theorem tailTrace_985586 : CollatzResearch.WordTrace tailWord_985586 prefixEnd_985586 506079344342286123942379 := by
  unfold tailWord_985586
  simp only [CollatzResearch.WordTrace]
  refine ⟨8986818651849430383224153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23964849738265147688597741 8986818651849430383224153)
  ·
    refine ⟨6740113988887072787418115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8986818651849430383224153 6740113988887072787418115)
    ·
      refine ⟨10110170983330609181127173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6740113988887072787418115 10110170983330609181127173)
      ·
        refine ⟨1895657059374489221461345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10110170983330609181127173 1895657059374489221461345)
        ·
          refine ⟨1421742794530866916096009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1895657059374489221461345 1421742794530866916096009)
          ·
            refine ⟨1066307095898150187072007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1421742794530866916096009 1066307095898150187072007)
            ·
              refine ⟨1599460643847225280608011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1066307095898150187072007 1599460643847225280608011)
              ·
                refine ⟨2399190965770837920912017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1599460643847225280608011 2399190965770837920912017)
                ·
                  refine ⟨1799393224328128440684013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2399190965770837920912017 1799393224328128440684013)
                  ·
                    refine ⟨674772459123048165256505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1799393224328128440684013 674772459123048165256505)
                    ·
                      refine ⟨506079344342286123942379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 674772459123048165256505 506079344342286123942379)
                      ·
                        rfl

theorem cell23_985586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_985586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_985586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_985586 prefixEnd_985586 := by exact prefixLift 985586
  have htrace : WordTrace (prefixWord ++ tailWord_985586) baseStart_985586 baseEnd_985586 := by
    simpa [prefixWord, tailWord_985586, baseEnd_985586] using wordTrace_append hprefix tailTrace_985586
  have hstable : (prefixWord ++ tailWord_985586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985586).length < 2 ^ (prefixWord ++ tailWord_985586).sum := by decide
  have hdescent : baseEnd_985586 < baseStart_985586 := by decide
  rcases family_descends (prefixWord ++ tailWord_985586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985608 : List Nat := [2, 1, 3, 2, 1, 1, 1, 2, 2, 2, 6]
def baseStart_985608 : Nat := 118140960795 + 985608 * 2 ^ 59
def prefixEnd_985608 : Nat := 4983230072969 + 3 ^ 40 * 985608 * 2
def baseEnd_985608 : Nat := 506090640916685037867277

theorem tailTrace_985608 : CollatzResearch.WordTrace tailWord_985608 prefixEnd_985608 506090640916685037867277 := by
  unfold tailWord_985608
  simp only [CollatzResearch.WordTrace]
  refine ⟨17974038506659009645098739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23965384675545346193464985 17974038506659009645098739)
  ·
    refine ⟨26961057759988514467648109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17974038506659009645098739 26961057759988514467648109)
    ·
      refine ⟨10110396659995692925368041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26961057759988514467648109 10110396659995692925368041)
      ·
        refine ⟨7582797494996769694026031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10110396659995692925368041 7582797494996769694026031)
        ·
          refine ⟨11374196242495154541039047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7582797494996769694026031 11374196242495154541039047)
          ·
            refine ⟨17061294363742731811558571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11374196242495154541039047 17061294363742731811558571)
            ·
              refine ⟨25591941545614097717337857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17061294363742731811558571 25591941545614097717337857)
              ·
                refine ⟨19193956159210573288003393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25591941545614097717337857 19193956159210573288003393)
                ·
                  refine ⟨14395467119407929966002545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19193956159210573288003393 14395467119407929966002545)
                  ·
                    refine ⟨10796600339555947474501909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14395467119407929966002545 10796600339555947474501909)
                    ·
                      refine ⟨506090640916685037867277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10796600339555947474501909 506090640916685037867277)
                      ·
                        rfl

theorem cell23_985608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_985608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_985608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_985608 prefixEnd_985608 := by exact prefixLift 985608
  have htrace : WordTrace (prefixWord ++ tailWord_985608) baseStart_985608 baseEnd_985608 := by
    simpa [prefixWord, tailWord_985608, baseEnd_985608] using wordTrace_append hprefix tailTrace_985608
  have hstable : (prefixWord ++ tailWord_985608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985608).length < 2 ^ (prefixWord ++ tailWord_985608).sum := by decide
  have hdescent : baseEnd_985608 < baseStart_985608 := by decide
  rcases family_descends (prefixWord ++ tailWord_985608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985636 : List Nat := [2, 3, 1, 5, 1, 1, 2, 2, 1, 2, 3]
def baseStart_985636 : Nat := 118140960795 + 985636 * 2 ^ 59
def prefixEnd_985636 : Nat := 4983230072969 + 3 ^ 40 * 985636 * 2
def baseEnd_985636 : Nat := 506105018375010928317149

theorem tailTrace_985636 : CollatzResearch.WordTrace tailWord_985636 prefixEnd_985636 506105018375010928317149 := by
  unfold tailWord_985636
  simp only [CollatzResearch.WordTrace]
  refine ⟨17974549128608290036108381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23966065504811053381477841 17974549128608290036108381)
  ·
    refine ⟨6740455923228108763540643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17974549128608290036108381 6740455923228108763540643)
    ·
      refine ⟨10110683884842163145310965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6740455923228108763540643 10110683884842163145310965)
      ·
        refine ⟨947876614203952794872903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10110683884842163145310965 947876614203952794872903)
        ·
          refine ⟨1421814921305929192309355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 947876614203952794872903 1421814921305929192309355)
          ·
            refine ⟨2132722381958893788464033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1421814921305929192309355 2132722381958893788464033)
            ·
              refine ⟨1599541786469170341348025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2132722381958893788464033 1599541786469170341348025)
              ·
                refine ⟨1199656339851877756011019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1599541786469170341348025 1199656339851877756011019)
                ·
                  refine ⟨1799484509777816634016529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1199656339851877756011019 1799484509777816634016529)
                  ·
                    refine ⟨1349613382333362475512397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1799484509777816634016529 1349613382333362475512397)
                    ·
                      refine ⟨506105018375010928317149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1349613382333362475512397 506105018375010928317149)
                      ·
                        rfl

theorem cell23_985636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_985636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_985636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_985636 prefixEnd_985636 := by exact prefixLift 985636
  have htrace : WordTrace (prefixWord ++ tailWord_985636) baseStart_985636 baseEnd_985636 := by
    simpa [prefixWord, tailWord_985636, baseEnd_985636] using wordTrace_append hprefix tailTrace_985636
  have hstable : (prefixWord ++ tailWord_985636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985636).length < 2 ^ (prefixWord ++ tailWord_985636).sum := by decide
  have hdescent : baseEnd_985636 < baseStart_985636 := by decide
  rcases family_descends (prefixWord ++ tailWord_985636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985648 : List Nat := [2, 1, 1, 1, 2, 3, 2, 2, 1, 8]
def baseStart_985648 : Nat := 118140960795 + 985648 * 2 ^ 59
def prefixEnd_985648 : Nat := 4983230072969 + 3 ^ 40 * 985648 * 2
def baseEnd_985648 : Nat := 168703726714288293789031

theorem tailTrace_985648 : CollatzResearch.WordTrace tailWord_985648 prefixEnd_985648 168703726714288293789031 := by
  unfold tailWord_985648
  simp only [CollatzResearch.WordTrace]
  refine ⟨17974767966586553060826799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23966357288782070747769065 17974767966586553060826799)
  ·
    refine ⟨26962151949879829591240199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17974767966586553060826799 26962151949879829591240199)
    ·
      refine ⟨40443227924819744386860299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26962151949879829591240199 40443227924819744386860299)
      ·
        refine ⟨60664841887229616580290449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40443227924819744386860299 60664841887229616580290449)
        ·
          refine ⟨45498631415422212435217837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60664841887229616580290449 45498631415422212435217837)
          ·
            refine ⟨17061986780783329663206689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45498631415422212435217837 17061986780783329663206689)
            ·
              refine ⟨12796490085587497247405017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17061986780783329663206689 12796490085587497247405017)
              ·
                refine ⟨9597367564190622935553763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12796490085587497247405017 9597367564190622935553763)
                ·
                  refine ⟨14396051346285934403330645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9597367564190622935553763 14396051346285934403330645)
                  ·
                    refine ⟨168703726714288293789031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 14396051346285934403330645 168703726714288293789031)
                    ·
                      rfl

theorem cell23_985648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 1, 8].length) (baseStart_985648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_985648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_985648 prefixEnd_985648 := by exact prefixLift 985648
  have htrace : WordTrace (prefixWord ++ tailWord_985648) baseStart_985648 baseEnd_985648 := by
    simpa [prefixWord, tailWord_985648, baseEnd_985648] using wordTrace_append hprefix tailTrace_985648
  have hstable : (prefixWord ++ tailWord_985648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985648).length < 2 ^ (prefixWord ++ tailWord_985648).sum := by decide
  have hdescent : baseEnd_985648 < baseStart_985648 := by decide
  rcases family_descends (prefixWord ++ tailWord_985648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985685 : List Nat := [1, 3, 2, 2, 1, 1, 2, 3, 2, 2, 4]
def baseStart_985685 : Nat := 118140960795 + 985685 * 2 ^ 59
def prefixEnd_985685 : Nat := 4983230072969 + 3 ^ 40 * 985685 * 2
def baseEnd_985685 : Nat := 506130178927081236604423

theorem tailTrace_985685 : CollatzResearch.WordTrace tailWord_985685 prefixEnd_985685 506130178927081236604423 := by
  unfold tailWord_985685
  simp only [CollatzResearch.WordTrace]
  refine ⟨35950885434039061440750509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23967256956026040960500339 35950885434039061440750509)
  ·
    refine ⟨13481582037764648040281441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35950885434039061440750509 13481582037764648040281441)
    ·
      refine ⟨10111186528323486030211081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13481582037764648040281441 10111186528323486030211081)
      ·
        refine ⟨7583389896242614522658311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10111186528323486030211081 7583389896242614522658311)
        ·
          refine ⟨11375084844363921783987467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7583389896242614522658311 11375084844363921783987467)
          ·
            refine ⟨17062627266545882675981201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11375084844363921783987467 17062627266545882675981201)
            ·
              refine ⟨12796970449909412006985901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17062627266545882675981201 12796970449909412006985901)
              ·
                refine ⟨4798863918716029502619713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12796970449909412006985901 4798863918716029502619713)
                ·
                  refine ⟨3599147939037022126964785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4798863918716029502619713 3599147939037022126964785)
                  ·
                    refine ⟨2699360954277766595223589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3599147939037022126964785 2699360954277766595223589)
                    ·
                      refine ⟨506130178927081236604423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2699360954277766595223589 506130178927081236604423)
                      ·
                        rfl

theorem cell23_985685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_985685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_985685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_985685 prefixEnd_985685 := by exact prefixLift 985685
  have htrace : WordTrace (prefixWord ++ tailWord_985685) baseStart_985685 baseEnd_985685 := by
    simpa [prefixWord, tailWord_985685, baseEnd_985685] using wordTrace_append hprefix tailTrace_985685
  have hstable : (prefixWord ++ tailWord_985685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985685).length < 2 ^ (prefixWord ++ tailWord_985685).sum := by decide
  have hdescent : baseEnd_985685 < baseStart_985685 := by decide
  rcases family_descends (prefixWord ++ tailWord_985685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985705 : List Nat := [1, 2, 1, 1, 1, 4, 1, 2, 4, 3, 3]
def baseStart_985705 : Nat := 118140960795 + 985705 * 2 ^ 59
def prefixEnd_985705 : Nat := 4983230072969 + 3 ^ 40 * 985705 * 2
def baseEnd_985705 : Nat := 506140448540171158354331

theorem tailTrace_985705 : CollatzResearch.WordTrace tailWord_985705 prefixEnd_985705 506140448540171158354331 := by
  unfold tailWord_985705
  simp only [CollatzResearch.WordTrace]
  refine ⟨35951614893966604856478569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23967743262644403237652379 35951614893966604856478569)
  ·
    refine ⟨26963711170474953642358927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35951614893966604856478569 26963711170474953642358927)
    ·
      refine ⟨40445566755712430463538391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26963711170474953642358927 40445566755712430463538391)
      ·
        refine ⟨60668350133568645695307587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40445566755712430463538391 60668350133568645695307587)
        ·
          refine ⟨91002525200352968542961381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60668350133568645695307587 91002525200352968542961381)
          ·
            refine ⟨17062973475066181601805259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91002525200352968542961381 17062973475066181601805259)
            ·
              refine ⟨25594460212599272402707889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17062973475066181601805259 25594460212599272402707889)
              ·
                refine ⟨19195845159449454302030917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25594460212599272402707889 19195845159449454302030917)
                ·
                  refine ⟨3599220967396772681630797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19195845159449454302030917 3599220967396772681630797)
                  ·
                    refine ⟨1349707862773789755611549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3599220967396772681630797 1349707862773789755611549)
                    ·
                      refine ⟨506140448540171158354331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1349707862773789755611549 506140448540171158354331)
                      ·
                        rfl

theorem cell23_985705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 4, 3, 3].length) (baseStart_985705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_985705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_985705 prefixEnd_985705 := by exact prefixLift 985705
  have htrace : WordTrace (prefixWord ++ tailWord_985705) baseStart_985705 baseEnd_985705 := by
    simpa [prefixWord, tailWord_985705, baseEnd_985705] using wordTrace_append hprefix tailTrace_985705
  have hstable : (prefixWord ++ tailWord_985705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985705).length < 2 ^ (prefixWord ++ tailWord_985705).sum := by decide
  have hdescent : baseEnd_985705 < baseStart_985705 := by decide
  rcases family_descends (prefixWord ++ tailWord_985705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985735 : List Nat := [1, 1, 4, 2, 1, 2, 1, 3, 1, 2, 5]
def baseStart_985735 : Nat := 118140960795 + 985735 * 2 ^ 59
def prefixEnd_985735 : Nat := 4983230072969 + 3 ^ 40 * 985735 * 2
def baseEnd_985735 : Nat := 506155852959806040979193

theorem tailTrace_985735 : CollatzResearch.WordTrace tailWord_985735 prefixEnd_985735 506155852959806040979193 := by
  unfold tailWord_985735
  simp only [CollatzResearch.WordTrace]
  refine ⟨35952709083857919980070659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23968472722571946653380439 35952709083857919980070659)
  ·
    refine ⟨53929063625786879970105989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35952709083857919980070659 53929063625786879970105989)
    ·
      refine ⟨10111699429835039994394873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53929063625786879970105989 10111699429835039994394873)
      ·
        refine ⟨7583774572376279995796155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10111699429835039994394873 7583774572376279995796155)
        ·
          refine ⟨11375661858564419993694233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7583774572376279995796155 11375661858564419993694233)
          ·
            refine ⟨8531746393923314995270675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11375661858564419993694233 8531746393923314995270675)
            ·
              refine ⟨12797619590884972492906013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8531746393923314995270675 12797619590884972492906013)
              ·
                refine ⟨4799107346581864684839755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12797619590884972492906013 4799107346581864684839755)
                ·
                  refine ⟨7198661019872797027259633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4799107346581864684839755 7198661019872797027259633)
                  ·
                    refine ⟨5398995764904597770444725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7198661019872797027259633 5398995764904597770444725)
                    ·
                      refine ⟨506155852959806040979193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5398995764904597770444725 506155852959806040979193)
                      ·
                        rfl

theorem cell23_985735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_985735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_985735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_985735 prefixEnd_985735 := by exact prefixLift 985735
  have htrace : WordTrace (prefixWord ++ tailWord_985735) baseStart_985735 baseEnd_985735 := by
    simpa [prefixWord, tailWord_985735, baseEnd_985735] using wordTrace_append hprefix tailTrace_985735
  have hstable : (prefixWord ++ tailWord_985735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985735).length < 2 ^ (prefixWord ++ tailWord_985735).sum := by decide
  have hdescent : baseEnd_985735 < baseStart_985735 := by decide
  rcases family_descends (prefixWord ++ tailWord_985735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985775 : List Nat := [1, 1, 2, 1, 2, 5, 1, 1, 2, 1, 6]
def baseStart_985775 : Nat := 118140960795 + 985775 * 2 ^ 59
def prefixEnd_985775 : Nat := 4983230072969 + 3 ^ 40 * 985775 * 2
def baseEnd_985775 : Nat := 506176392185985884479009

theorem tailTrace_985775 : CollatzResearch.WordTrace tailWord_985775 prefixEnd_985775 506176392185985884479009 := by
  unfold tailWord_985775
  simp only [CollatzResearch.WordTrace]
  refine ⟨35954168003713006811526779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23969445335808671207684519 35954168003713006811526779)
  ·
    refine ⟨53931252005569510217290169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35954168003713006811526779 53931252005569510217290169)
    ·
      refine ⟨40448439004177132662967627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53931252005569510217290169 40448439004177132662967627)
      ·
        refine ⟨60672658506265698994451441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40448439004177132662967627 60672658506265698994451441)
        ·
          refine ⟨45504493879699274245838581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60672658506265698994451441 45504493879699274245838581)
          ·
            refine ⟨4266046301221806960547367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45504493879699274245838581 4266046301221806960547367)
            ·
              refine ⟨6399069451832710440821051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4266046301221806960547367 6399069451832710440821051)
              ·
                refine ⟨9598604177749065661231577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6399069451832710440821051 9598604177749065661231577)
                ·
                  refine ⟨7198953133311799245923683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9598604177749065661231577 7198953133311799245923683)
                  ·
                    refine ⟨10798429699967698868885525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7198953133311799245923683 10798429699967698868885525)
                    ·
                      refine ⟨506176392185985884479009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10798429699967698868885525 506176392185985884479009)
                      ·
                        rfl

theorem cell23_985775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 2, 1, 6].length) (baseStart_985775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_985775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_985775 prefixEnd_985775 := by exact prefixLift 985775
  have htrace : WordTrace (prefixWord ++ tailWord_985775) baseStart_985775 baseEnd_985775 := by
    simpa [prefixWord, tailWord_985775, baseEnd_985775] using wordTrace_append hprefix tailTrace_985775
  have hstable : (prefixWord ++ tailWord_985775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985775).length < 2 ^ (prefixWord ++ tailWord_985775).sum := by decide
  have hdescent : baseEnd_985775 < baseStart_985775 := by decide
  rcases family_descends (prefixWord ++ tailWord_985775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985789 : List Nat := [1, 4, 1, 2, 1, 4, 2, 1, 3, 4]
def baseStart_985789 : Nat := 118140960795 + 985789 * 2 ^ 59
def prefixEnd_985789 : Nat := 4983230072969 + 3 ^ 40 * 985789 * 2
def baseEnd_985789 : Nat := 168727860305049609901315

theorem tailTrace_985789 : CollatzResearch.WordTrace tailWord_985789 prefixEnd_985789 168727860305049609901315 := by
  unfold tailWord_985789
  simp only [CollatzResearch.WordTrace]
  refine ⟨35954678625662287202536421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23969785750441524801690947 35954678625662287202536421)
  ·
    refine ⟨6741502242311678850475579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35954678625662287202536421 6741502242311678850475579)
    ·
      refine ⟨10112253363467518275713369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6741502242311678850475579 10112253363467518275713369)
      ·
        refine ⟨7584190022600638706785027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10112253363467518275713369 7584190022600638706785027)
        ·
          refine ⟨11376285033900958060177541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7584190022600638706785027 11376285033900958060177541)
          ·
            refine ⟨2133053443856429636283289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11376285033900958060177541 2133053443856429636283289)
            ·
              refine ⟨1599790082892322227212467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2133053443856429636283289 1599790082892322227212467)
              ·
                refine ⟨2399685124338483340818701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1599790082892322227212467 2399685124338483340818701)
                ·
                  refine ⟨899881921626931252807013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2399685124338483340818701 899881921626931252807013)
                  ·
                    refine ⟨168727860305049609901315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 899881921626931252807013 168727860305049609901315)
                    ·
                      rfl

theorem cell23_985789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 1, 3, 4].length) (baseStart_985789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_985789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_985789 prefixEnd_985789 := by exact prefixLift 985789
  have htrace : WordTrace (prefixWord ++ tailWord_985789) baseStart_985789 baseEnd_985789 := by
    simpa [prefixWord, tailWord_985789, baseEnd_985789] using wordTrace_append hprefix tailTrace_985789
  have hstable : (prefixWord ++ tailWord_985789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985789).length < 2 ^ (prefixWord ++ tailWord_985789).sum := by decide
  have hdescent : baseEnd_985789 < baseStart_985789 := by decide
  rcases family_descends (prefixWord ++ tailWord_985789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985839 : List Nat := [1, 1, 2, 1, 5, 2, 1, 1, 4, 3, 2]
def baseStart_985839 : Nat := 118140960795 + 985839 * 2 ^ 59
def prefixEnd_985839 : Nat := 4983230072969 + 3 ^ 40 * 985839 * 2
def baseEnd_985839 : Nat := 506209254947873634078715

theorem tailTrace_985839 : CollatzResearch.WordTrace tailWord_985839 prefixEnd_985839 506209254947873634078715 := by
  unfold tailWord_985839
  simp only [CollatzResearch.WordTrace]
  refine ⟨35956502275481145741856571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23971001516987430494571047 35956502275481145741856571)
  ·
    refine ⟨53934753413221718612784857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35956502275481145741856571 53934753413221718612784857)
    ·
      refine ⟨40451065059916288959588643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53934753413221718612784857 40451065059916288959588643)
      ·
        refine ⟨60676597589874433439382965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40451065059916288959588643 60676597589874433439382965)
        ·
          refine ⟨5688431024050728134942153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60676597589874433439382965 5688431024050728134942153)
          ·
            refine ⟨4266323268038046101206615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5688431024050728134942153 4266323268038046101206615)
            ·
              refine ⟨6399484902057069151809923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4266323268038046101206615 6399484902057069151809923)
              ·
                refine ⟨9599227353085603727714885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6399484902057069151809923 9599227353085603727714885)
                ·
                  refine ⟨1799855128703550698946541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9599227353085603727714885 1799855128703550698946541)
                  ·
                    refine ⟨674945673263831512104953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1799855128703550698946541 674945673263831512104953)
                    ·
                      refine ⟨506209254947873634078715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 674945673263831512104953 506209254947873634078715)
                      ·
                        rfl

theorem cell23_985839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 4, 3, 2].length) (baseStart_985839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_985839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_985839 prefixEnd_985839 := by exact prefixLift 985839
  have htrace : WordTrace (prefixWord ++ tailWord_985839) baseStart_985839 baseEnd_985839 := by
    simpa [prefixWord, tailWord_985839, baseEnd_985839] using wordTrace_append hprefix tailTrace_985839
  have hstable : (prefixWord ++ tailWord_985839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985839).length < 2 ^ (prefixWord ++ tailWord_985839).sum := by decide
  have hdescent : baseEnd_985839 < baseStart_985839 := by decide
  rcases family_descends (prefixWord ++ tailWord_985839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985875 : List Nat := [1, 1, 1, 2, 1, 3, 3, 11]
def baseStart_985875 : Nat := 118140960795 + 985875 * 2 ^ 59
def prefixEnd_985875 : Nat := 4983230072969 + 3 ^ 40 * 985875 * 2
def baseEnd_985875 : Nat := 18749175564867981230687

theorem tailTrace_985875 : CollatzResearch.WordTrace tailWord_985875 prefixEnd_985875 18749175564867981230687 := by
  unfold tailWord_985875
  simp only [CollatzResearch.WordTrace]
  refine ⟨35957815303350723890167079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23971876868900482593444719 35957815303350723890167079)
  ·
    refine ⟨53936722955026085835250619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35957815303350723890167079 53936722955026085835250619)
    ·
      refine ⟨80905084432539128752875929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53936722955026085835250619 80905084432539128752875929)
      ·
        refine ⟨60678813324404346564656947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80905084432539128752875929 60678813324404346564656947)
        ·
          refine ⟨91018219986606519846985421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60678813324404346564656947 91018219986606519846985421)
          ·
            refine ⟨34131832494977444942619533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91018219986606519846985421 34131832494977444942619533)
            ·
              refine ⟨12799437185616541853482325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34131832494977444942619533 12799437185616541853482325)
              ·
                refine ⟨18749175564867981230687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 12799437185616541853482325 18749175564867981230687)
                ·
                  rfl

theorem cell23_985875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 11].length) (baseStart_985875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_985875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_985875 prefixEnd_985875 := by exact prefixLift 985875
  have htrace : WordTrace (prefixWord ++ tailWord_985875) baseStart_985875 baseEnd_985875 := by
    simpa [prefixWord, tailWord_985875, baseEnd_985875] using wordTrace_append hprefix tailTrace_985875
  have hstable : (prefixWord ++ tailWord_985875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985875).length < 2 ^ (prefixWord ++ tailWord_985875).sum := by decide
  have hdescent : baseEnd_985875 < baseStart_985875 := by decide
  rcases family_descends (prefixWord ++ tailWord_985875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985879 : List Nat := [1, 1, 3, 4, 3, 1, 1, 2, 1, 6]
def baseStart_985879 : Nat := 118140960795 + 985879 * 2 ^ 59
def prefixEnd_985879 : Nat := 4983230072969 + 3 ^ 40 * 985879 * 2
def baseEnd_985879 : Nat := 168743264724684492526177

theorem tailTrace_985879 : CollatzResearch.WordTrace tailWord_985879 prefixEnd_985879 168743264724684492526177 := by
  unfold tailWord_985879
  simp only [CollatzResearch.WordTrace]
  refine ⟨35957961195336232573312691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23971974130224155048875127 35957961195336232573312691)
  ·
    refine ⟨53936941793004348859969037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35957961195336232573312691 53936941793004348859969037)
    ·
      refine ⟨20226353172376630822488389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53936941793004348859969037 20226353172376630822488389)
      ·
        refine ⟨3792441219820618279216573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20226353172376630822488389 3792441219820618279216573)
        ·
          refine ⟨1422165457432731854706215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3792441219820618279216573 1422165457432731854706215)
          ·
            refine ⟨2133248186149097782059323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1422165457432731854706215 2133248186149097782059323)
            ·
              refine ⟨3199872279223646673088985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2133248186149097782059323 3199872279223646673088985)
              ·
                refine ⟨2399904209417735004816739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3199872279223646673088985 2399904209417735004816739)
                ·
                  refine ⟨3599856314126602507225109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2399904209417735004816739 3599856314126602507225109)
                  ·
                    refine ⟨168743264724684492526177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3599856314126602507225109 168743264724684492526177)
                    ·
                      rfl

theorem cell23_985879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 2, 1, 6].length) (baseStart_985879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_985879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_985879 prefixEnd_985879 := by exact prefixLift 985879
  have htrace : WordTrace (prefixWord ++ tailWord_985879) baseStart_985879 baseEnd_985879 := by
    simpa [prefixWord, tailWord_985879, baseEnd_985879] using wordTrace_append hprefix tailTrace_985879
  have hstable : (prefixWord ++ tailWord_985879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985879).length < 2 ^ (prefixWord ++ tailWord_985879).sum := by decide
  have hdescent : baseEnd_985879 < baseStart_985879 := by decide
  rcases family_descends (prefixWord ++ tailWord_985879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985892 : List Nat := [2, 3, 1, 3, 3, 11]
def baseStart_985892 : Nat := 118140960795 + 985892 * 2 ^ 59
def prefixEnd_985892 : Nat := 4983230072969 + 3 ^ 40 * 985892 * 2
def baseEnd_985892 : Nat := 2083277651944699286897

theorem tailTrace_985892 : CollatzResearch.WordTrace tailWord_985892 prefixEnd_985892 2083277651944699286897 := by
  unfold tailWord_985892
  simp only [CollatzResearch.WordTrace]
  refine ⟨17979217672144567896767965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23972290229526090529023953 17979217672144567896767965)
  ·
    refine ⟨6742206627054212961287987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17979217672144567896767965 6742206627054212961287987)
    ·
      refine ⟨10113309940581319441931981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6742206627054212961287987 10113309940581319441931981)
      ·
        refine ⟨3792491227717994790724493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10113309940581319441931981 3792491227717994790724493)
        ·
          refine ⟨1422184210394248046521685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3792491227717994790724493 1422184210394248046521685)
          ·
            refine ⟨2083277651944699286897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 1422184210394248046521685 2083277651944699286897)
            ·
              rfl

theorem cell23_985892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 11].length) (baseStart_985892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_985892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_985892 prefixEnd_985892 := by exact prefixLift 985892
  have htrace : WordTrace (prefixWord ++ tailWord_985892) baseStart_985892 baseEnd_985892 := by
    simpa [prefixWord, tailWord_985892, baseEnd_985892] using wordTrace_append hprefix tailTrace_985892
  have hstable : (prefixWord ++ tailWord_985892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985892).length < 2 ^ (prefixWord ++ tailWord_985892).sum := by decide
  have hdescent : baseEnd_985892 < baseStart_985892 := by decide
  rcases family_descends (prefixWord ++ tailWord_985892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985896 : List Nat := [2, 1, 5, 1, 1, 1, 4, 2, 2, 4]
def baseStart_985896 : Nat := 118140960795 + 985896 * 2 ^ 59
def prefixEnd_985896 : Nat := 4983230072969 + 3 ^ 40 * 985896 * 2
def baseEnd_985896 : Nat := 168746174448393303688651

theorem tailTrace_985896 : CollatzResearch.WordTrace tailWord_985896 prefixEnd_985896 168746174448393303688651 := by
  unfold tailWord_985896
  simp only [CollatzResearch.WordTrace]
  refine ⟨17979290618137322238340771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23972387490849762984454361 17979290618137322238340771)
  ·
    refine ⟨26968935927205983357511157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17979290618137322238340771 26968935927205983357511157)
    ·
      refine ⟨2528337743175560939766671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26968935927205983357511157 2528337743175560939766671)
      ·
        refine ⟨3792506614763341409650007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2528337743175560939766671 3792506614763341409650007)
        ·
          refine ⟨5688759922145012114475011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3792506614763341409650007 5688759922145012114475011)
          ·
            refine ⟨8533139883217518171712517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5688759922145012114475011 8533139883217518171712517)
            ·
              refine ⟨1599963728103284657196097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8533139883217518171712517 1599963728103284657196097)
              ·
                refine ⟨1199972796077463492897073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1599963728103284657196097 1199972796077463492897073)
                ·
                  refine ⟨899979597058097619672805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1199972796077463492897073 899979597058097619672805)
                  ·
                    refine ⟨168746174448393303688651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 899979597058097619672805 168746174448393303688651)
                    ·
                      rfl

theorem cell23_985896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_985896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_985896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_985896 prefixEnd_985896 := by exact prefixLift 985896
  have htrace : WordTrace (prefixWord ++ tailWord_985896) baseStart_985896 baseEnd_985896 := by
    simpa [prefixWord, tailWord_985896, baseEnd_985896] using wordTrace_append hprefix tailTrace_985896
  have hstable : (prefixWord ++ tailWord_985896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985896).length < 2 ^ (prefixWord ++ tailWord_985896).sum := by decide
  have hdescent : baseEnd_985896 < baseStart_985896 := by decide
  rcases family_descends (prefixWord ++ tailWord_985896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985909 : List Nat := [1, 3, 3, 1, 3, 3, 1, 8]
def baseStart_985909 : Nat := 118140960795 + 985909 * 2 ^ 59
def prefixEnd_985909 : Nat := 4983230072969 + 3 ^ 40 * 985909 * 2
def baseEnd_985909 : Nat := 18749822170136605933459

theorem tailTrace_985909 : CollatzResearch.WordTrace tailWord_985909 prefixEnd_985909 18749822170136605933459 := by
  unfold tailWord_985909
  simp only [CollatzResearch.WordTrace]
  refine ⟨35959055385227547696904781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23972703590151698464603187 35959055385227547696904781)
  ·
    refine ⟨13484645769460330386339293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35959055385227547696904781 13484645769460330386339293)
    ·
      refine ⟨5056742163547623894877235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13484645769460330386339293 5056742163547623894877235)
      ·
        refine ⟨7585113245321435842315853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5056742163547623894877235 7585113245321435842315853)
        ·
          refine ⟨2844417466995538440868445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7585113245321435842315853 2844417466995538440868445)
          ·
            refine ⟨1066656550123326915325667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2844417466995538440868445 1066656550123326915325667)
            ·
              refine ⟨1599984825184990372988501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1066656550123326915325667 1599984825184990372988501)
              ·
                refine ⟨18749822170136605933459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1599984825184990372988501 18749822170136605933459)
                ·
                  rfl

theorem cell23_985909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 8].length) (baseStart_985909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_985909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_985909 prefixEnd_985909 := by exact prefixLift 985909
  have htrace : WordTrace (prefixWord ++ tailWord_985909) baseStart_985909 baseEnd_985909 := by
    simpa [prefixWord, tailWord_985909, baseEnd_985909] using wordTrace_append hprefix tailTrace_985909
  have hstable : (prefixWord ++ tailWord_985909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985909).length < 2 ^ (prefixWord ++ tailWord_985909).sum := by decide
  have hdescent : baseEnd_985909 < baseStart_985909 := by decide
  rcases family_descends (prefixWord ++ tailWord_985909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985919 : List Nat := [1, 1, 2, 2, 5, 1, 1, 3, 1, 3, 3]
def baseStart_985919 : Nat := 118140960795 + 985919 * 2 ^ 59
def prefixEnd_985919 : Nat := 4983230072969 + 3 ^ 40 * 985919 * 2
def baseEnd_985919 : Nat := 506250333400233321078347

theorem tailTrace_985919 : CollatzResearch.WordTrace tailWord_985919 prefixEnd_985919 506250333400233321078347 := by
  unfold tailWord_985919
  simp only [CollatzResearch.WordTrace]
  refine ⟨35959420115191319404768811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23972946743460879603179207 35959420115191319404768811)
  ·
    refine ⟨53939130172786979107153217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35959420115191319404768811 53939130172786979107153217)
    ·
      refine ⟨40454347629590234330364913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53939130172786979107153217 40454347629590234330364913)
      ·
        refine ⟨30340760722192675747773685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40454347629590234330364913 30340760722192675747773685)
        ·
          refine ⟨2844446317705563351353783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30340760722192675747773685 2844446317705563351353783)
          ·
            refine ⟨4266669476558345027030675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2844446317705563351353783 4266669476558345027030675)
            ·
              refine ⟨6400004214837517540546013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4266669476558345027030675 6400004214837517540546013)
              ·
                refine ⟨2400001580564069077704755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6400004214837517540546013 2400001580564069077704755)
                ·
                  refine ⟨3600002370846103616557133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2400001580564069077704755 3600002370846103616557133)
                  ·
                    refine ⟨1350000889067288856208925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3600002370846103616557133 1350000889067288856208925)
                    ·
                      refine ⟨506250333400233321078347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1350000889067288856208925 506250333400233321078347)
                      ·
                        rfl

theorem cell23_985919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 3, 1, 3, 3].length) (baseStart_985919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_985919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_985919 prefixEnd_985919 := by exact prefixLift 985919
  have htrace : WordTrace (prefixWord ++ tailWord_985919) baseStart_985919 baseEnd_985919 := by
    simpa [prefixWord, tailWord_985919, baseEnd_985919] using wordTrace_append hprefix tailTrace_985919
  have hstable : (prefixWord ++ tailWord_985919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985919).length < 2 ^ (prefixWord ++ tailWord_985919).sum := by decide
  have hdescent : baseEnd_985919 < baseStart_985919 := by decide
  rcases family_descends (prefixWord ++ tailWord_985919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985940 : List Nat := [2, 4, 1, 1, 4, 2, 2, 1, 1, 2, 3]
def baseStart_985940 : Nat := 118140960795 + 985940 * 2 ^ 59
def prefixEnd_985940 : Nat := 4983230072969 + 3 ^ 40 * 985940 * 2
def baseEnd_985940 : Nat := 506261116493977738915751

theorem tailTrace_985940 : CollatzResearch.WordTrace tailWord_985940 prefixEnd_985940 506261116493977738915751 := by
  unfold tailWord_985940
  simp only [CollatzResearch.WordTrace]
  refine ⟨17980093024057619995641637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23973457365410159994188849 17980093024057619995641637)
  ·
    refine ⟨3371267442010803749182807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17980093024057619995641637 3371267442010803749182807)
    ·
      refine ⟨5056901163016205623774211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3371267442010803749182807 5056901163016205623774211)
      ·
        refine ⟨7585351744524308435661317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5056901163016205623774211 7585351744524308435661317)
        ·
          refine ⟨1422253452098307831686497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7585351744524308435661317 1422253452098307831686497)
          ·
            refine ⟨1066690089073730873764873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1422253452098307831686497 1066690089073730873764873)
            ·
              refine ⟨800017566805298155323655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1066690089073730873764873 800017566805298155323655)
              ·
                refine ⟨1200026350207947232985483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 800017566805298155323655 1200026350207947232985483)
                ·
                  refine ⟨1800039525311920849478225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1200026350207947232985483 1800039525311920849478225)
                  ·
                    refine ⟨1350029643983940637108669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1800039525311920849478225 1350029643983940637108669)
                    ·
                      refine ⟨506261116493977738915751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1350029643983940637108669 506261116493977738915751)
                      ·
                        rfl

theorem cell23_985940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 2, 1, 1, 2, 3].length) (baseStart_985940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_985940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_985940 prefixEnd_985940 := by exact prefixLift 985940
  have htrace : WordTrace (prefixWord ++ tailWord_985940) baseStart_985940 baseEnd_985940 := by
    simpa [prefixWord, tailWord_985940, baseEnd_985940] using wordTrace_append hprefix tailTrace_985940
  have hstable : (prefixWord ++ tailWord_985940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985940).length < 2 ^ (prefixWord ++ tailWord_985940).sum := by decide
  have hdescent : baseEnd_985940 < baseStart_985940 := by decide
  rcases family_descends (prefixWord ++ tailWord_985940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985952 : List Nat := [2, 1, 1, 3, 3, 1, 1, 1, 4, 6]
def baseStart_985952 : Nat := 118140960795 + 985952 * 2 ^ 59
def prefixEnd_985952 : Nat := 4983230072969 + 3 ^ 40 * 985952 * 2
def baseEnd_985952 : Nat := 168755759420610563988565

theorem tailTrace_985952 : CollatzResearch.WordTrace tailWord_985952 prefixEnd_985952 168755759420610563988565 := by
  unfold tailWord_985952
  simp only [CollatzResearch.WordTrace]
  refine ⟨17980311862035883020360055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23973749149381177360480073 17980311862035883020360055)
  ·
    refine ⟨26970467793053824530540083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17980311862035883020360055 26970467793053824530540083)
    ·
      refine ⟨40455701689580736795810125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26970467793053824530540083 40455701689580736795810125)
      ·
        refine ⟨15170888133592776298428797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40455701689580736795810125 15170888133592776298428797)
        ·
          refine ⟨5689083050097291111910799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15170888133592776298428797 5689083050097291111910799)
          ·
            refine ⟨8533624575145936667866199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5689083050097291111910799 8533624575145936667866199)
            ·
              refine ⟨12800436862718905001799299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8533624575145936667866199 12800436862718905001799299)
              ·
                refine ⟨19200655294078357502698949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12800436862718905001799299 19200655294078357502698949)
                ·
                  refine ⟨3600122867639692031756053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19200655294078357502698949 3600122867639692031756053)
                  ·
                    refine ⟨168755759420610563988565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3600122867639692031756053 168755759420610563988565)
                    ·
                      rfl

theorem cell23_985952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 4, 6].length) (baseStart_985952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_985952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_985952 prefixEnd_985952 := by exact prefixLift 985952
  have htrace : WordTrace (prefixWord ++ tailWord_985952) baseStart_985952 baseEnd_985952 := by
    simpa [prefixWord, tailWord_985952, baseEnd_985952] using wordTrace_append hprefix tailTrace_985952
  have hstable : (prefixWord ++ tailWord_985952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985952).length < 2 ^ (prefixWord ++ tailWord_985952).sum := by decide
  have hdescent : baseEnd_985952 < baseStart_985952 := by decide
  rcases family_descends (prefixWord ++ tailWord_985952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986046 : List Nat := [4, 2, 1, 1, 1, 2, 4, 1, 2, 5]
def baseStart_986046 : Nat := 118140960795 + 986046 * 2 ^ 59
def prefixEnd_986046 : Nat := 4983230072969 + 3 ^ 40 * 986046 * 2
def baseEnd_986046 : Nat := 168771848481118108063421

theorem tailTrace_986046 : CollatzResearch.WordTrace tailWord_986046 prefixEnd_986046 168771848481118108063421 := by
  unfold tailWord_986046
  simp only [CollatzResearch.WordTrace]
  refine ⟨4495506523216402511830249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23976034790487480063094661 4495506523216402511830249)
  ·
    refine ⟨3371629892412301883872687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4495506523216402511830249 3371629892412301883872687)
    ·
      refine ⟨5057444838618452825809031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3371629892412301883872687 5057444838618452825809031)
      ·
        refine ⟨7586167257927679238713547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5057444838618452825809031 7586167257927679238713547)
        ·
          refine ⟨11379250886891518858070321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7586167257927679238713547 11379250886891518858070321)
          ·
            refine ⟨8534438165168639143552741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11379250886891518858070321 8534438165168639143552741)
            ·
              refine ⟨1600207155969119839416139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8534438165168639143552741 1600207155969119839416139)
              ·
                refine ⟨2400310733953679759124209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1600207155969119839416139 2400310733953679759124209)
                ·
                  refine ⟨1800233050465259819343157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2400310733953679759124209 1800233050465259819343157)
                  ·
                    refine ⟨168771848481118108063421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1800233050465259819343157 168771848481118108063421)
                    ·
                      rfl

theorem cell23_986046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 1, 2, 5].length) (baseStart_986046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_986046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_986046 prefixEnd_986046 := by exact prefixLift 986046
  have htrace : WordTrace (prefixWord ++ tailWord_986046) baseStart_986046 baseEnd_986046 := by
    simpa [prefixWord, tailWord_986046, baseEnd_986046] using wordTrace_append hprefix tailTrace_986046
  have hstable : (prefixWord ++ tailWord_986046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986046).length < 2 ^ (prefixWord ++ tailWord_986046).sum := by decide
  have hdescent : baseEnd_986046 < baseStart_986046 := by decide
  rcases family_descends (prefixWord ++ tailWord_986046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986061 : List Nat := [1, 6, 3, 1, 1, 1, 2, 2, 2, 2, 2]
def baseStart_986061 : Nat := 118140960795 + 986061 * 2 ^ 59
def prefixEnd_986061 : Nat := 4983230072969 + 3 ^ 40 * 986061 * 2
def baseEnd_986061 : Nat := 506323247653171765502695

theorem tailTrace_986061 : CollatzResearch.WordTrace tailWord_986061 prefixEnd_986061 506323247653171765502695 := by
  unfold tailWord_986061
  simp only [CollatzResearch.WordTrace]
  refine ⟨35964599280676877656438037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23976399520451251770958691 35964599280676877656438037)
  ·
    refine ⟨1685840591281728640145533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 35964599280676877656438037 1685840591281728640145533)
    ·
      refine ⟨632190221730648240054575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1685840591281728640145533 632190221730648240054575)
      ·
        refine ⟨948285332595972360081863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 632190221730648240054575 948285332595972360081863)
        ·
          refine ⟨1422427998893958540122795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 948285332595972360081863 1422427998893958540122795)
          ·
            refine ⟨2133641998340937810184193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1422427998893958540122795 2133641998340937810184193)
            ·
              refine ⟨1600231498755703357638145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2133641998340937810184193 1600231498755703357638145)
              ·
                refine ⟨1200173624066777518228609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1600231498755703357638145 1200173624066777518228609)
                ·
                  refine ⟨900130218050083138671457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1200173624066777518228609 900130218050083138671457)
                  ·
                    refine ⟨675097663537562354003593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 900130218050083138671457 675097663537562354003593)
                    ·
                      refine ⟨506323247653171765502695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 675097663537562354003593 506323247653171765502695)
                      ·
                        rfl

theorem cell23_986061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_986061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_986061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_986061 prefixEnd_986061 := by exact prefixLift 986061
  have htrace : WordTrace (prefixWord ++ tailWord_986061) baseStart_986061 baseEnd_986061 := by
    simpa [prefixWord, tailWord_986061, baseEnd_986061] using wordTrace_append hprefix tailTrace_986061
  have hstable : (prefixWord ++ tailWord_986061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986061).length < 2 ^ (prefixWord ++ tailWord_986061).sum := by decide
  have hdescent : baseEnd_986061 < baseStart_986061 := by decide
  rcases family_descends (prefixWord ++ tailWord_986061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986133 : List Nat := [1, 3, 2, 1, 4, 1, 1, 3, 3, 1, 3]
def baseStart_986133 : Nat := 118140960795 + 986133 * 2 ^ 59
def prefixEnd_986133 : Nat := 4983230072969 + 3 ^ 40 * 986133 * 2
def baseEnd_986133 : Nat := 506360218260295483802363

theorem tailTrace_986133 : CollatzResearch.WordTrace tailWord_986133 prefixEnd_986133 506360218260295483802363 := by
  unfold tailWord_986133
  simp only [CollatzResearch.WordTrace]
  refine ⟨35967225336416033953059053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23978150224277355968706035 35967225336416033953059053)
  ·
    refine ⟨13487709501156012732397145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35967225336416033953059053 13487709501156012732397145)
    ·
      refine ⟨10115782125867009549297859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13487709501156012732397145 10115782125867009549297859)
      ·
        refine ⟨15173673188800514323946789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10115782125867009549297859 15173673188800514323946789)
        ·
          refine ⟨2845063722900096435740023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15173673188800514323946789 2845063722900096435740023)
          ·
            refine ⟨4267595584350144653610035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2845063722900096435740023 4267595584350144653610035)
            ·
              refine ⟨6401393376525216980415053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4267595584350144653610035 6401393376525216980415053)
              ·
                refine ⟨2400522516196956367655645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6401393376525216980415053 2400522516196956367655645)
                ·
                  refine ⟨900195943573858637870867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2400522516196956367655645 900195943573858637870867)
                  ·
                    refine ⟨1350293915360787956806301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 900195943573858637870867 1350293915360787956806301)
                    ·
                      refine ⟨506360218260295483802363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1350293915360787956806301 506360218260295483802363)
                      ·
                        rfl

theorem cell23_986133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 3, 3, 1, 3].length) (baseStart_986133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_986133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_986133 prefixEnd_986133 := by exact prefixLift 986133
  have htrace : WordTrace (prefixWord ++ tailWord_986133) baseStart_986133 baseEnd_986133 := by
    simpa [prefixWord, tailWord_986133, baseEnd_986133] using wordTrace_append hprefix tailTrace_986133
  have hstable : (prefixWord ++ tailWord_986133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986133).length < 2 ^ (prefixWord ++ tailWord_986133).sum := by decide
  have hdescent : baseEnd_986133 < baseStart_986133 := by decide
  rcases family_descends (prefixWord ++ tailWord_986133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986156 : List Nat := [2, 2, 1, 1, 1, 2, 3, 1, 2, 6, 2]
def baseStart_986156 : Nat := 118140960795 + 986156 * 2 ^ 59
def prefixEnd_986156 : Nat := 4983230072969 + 3 ^ 40 * 986156 * 2
def baseEnd_986156 : Nat := 506372028315348893814757

theorem tailTrace_986156 : CollatzResearch.WordTrace tailWord_986156 prefixEnd_986156 506372028315348893814757 := by
  unfold tailWord_986156
  simp only [CollatzResearch.WordTrace]
  refine ⟨17984032107666354440573161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23978709476888472587430881 17984032107666354440573161)
  ·
    refine ⟨13488024080749765830429871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17984032107666354440573161 13488024080749765830429871)
    ·
      refine ⟨20232036121124648745644807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13488024080749765830429871 20232036121124648745644807)
      ·
        refine ⟨30348054181686973118467211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20232036121124648745644807 30348054181686973118467211)
        ·
          refine ⟨45522081272530459677700817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30348054181686973118467211 45522081272530459677700817)
          ·
            refine ⟨34141560954397844758275613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45522081272530459677700817 34141560954397844758275613)
            ·
              refine ⟨12803085357899191784353355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34141560954397844758275613 12803085357899191784353355)
              ·
                refine ⟨19204628036848787676530033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12803085357899191784353355 19204628036848787676530033)
                ·
                  refine ⟨14403471027636590757397525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19204628036848787676530033 14403471027636590757397525)
                  ·
                    refine ⟨675162704420465191753009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14403471027636590757397525 675162704420465191753009)
                    ·
                      refine ⟨506372028315348893814757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 675162704420465191753009 506372028315348893814757)
                      ·
                        rfl

theorem cell23_986156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 6, 2].length) (baseStart_986156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_986156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_986156 prefixEnd_986156 := by exact prefixLift 986156
  have htrace : WordTrace (prefixWord ++ tailWord_986156) baseStart_986156 baseEnd_986156 := by
    simpa [prefixWord, tailWord_986156, baseEnd_986156] using wordTrace_append hprefix tailTrace_986156
  have hstable : (prefixWord ++ tailWord_986156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986156).length < 2 ^ (prefixWord ++ tailWord_986156).sum := by decide
  have hdescent : baseEnd_986156 < baseStart_986156 := by decide
  rcases family_descends (prefixWord ++ tailWord_986156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986173 : List Nat := [1, 4, 1, 3, 1, 2, 2, 3, 1, 1, 4]
def baseStart_986173 : Nat := 118140960795 + 986173 * 2 ^ 59
def prefixEnd_986173 : Nat := 4983230072969 + 3 ^ 40 * 986173 * 2
def baseEnd_986173 : Nat := 506380757486475327302179

theorem tailTrace_986173 : CollatzResearch.WordTrace tailWord_986173 prefixEnd_986173 506380757486475327302179 := by
  unfold tailWord_986173
  simp only [CollatzResearch.WordTrace]
  refine ⟨35968684256271120784515173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23979122837514080523010115 35968684256271120784515173)
  ·
    refine ⟨6744128298050835147096595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35968684256271120784515173 6744128298050835147096595)
    ·
      refine ⟨10116192447076252720644893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6744128298050835147096595 10116192447076252720644893)
      ·
        refine ⟨3793572167653594770241835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10116192447076252720644893 3793572167653594770241835)
        ·
          refine ⟨5690358251480392155362753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3793572167653594770241835 5690358251480392155362753)
          ·
            refine ⟨4267768688610294116522065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5690358251480392155362753 4267768688610294116522065)
            ·
              refine ⟨3200826516457720587391549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4267768688610294116522065 3200826516457720587391549)
              ·
                refine ⟨1200309943671645220271831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3200826516457720587391549 1200309943671645220271831)
                ·
                  refine ⟨1800464915507467830407747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1200309943671645220271831 1800464915507467830407747)
                  ·
                    refine ⟨2700697373261201745611621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1800464915507467830407747 2700697373261201745611621)
                    ·
                      refine ⟨506380757486475327302179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2700697373261201745611621 506380757486475327302179)
                      ·
                        rfl

theorem cell23_986173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_986173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_986173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_986173 prefixEnd_986173 := by exact prefixLift 986173
  have htrace : WordTrace (prefixWord ++ tailWord_986173) baseStart_986173 baseEnd_986173 := by
    simpa [prefixWord, tailWord_986173, baseEnd_986173] using wordTrace_append hprefix tailTrace_986173
  have hstable : (prefixWord ++ tailWord_986173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986173).length < 2 ^ (prefixWord ++ tailWord_986173).sum := by decide
  have hdescent : baseEnd_986173 < baseStart_986173 := by decide
  rcases family_descends (prefixWord ++ tailWord_986173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986176 : List Nat := [2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 5]
def baseStart_986176 : Nat := 118140960795 + 986176 * 2 ^ 59
def prefixEnd_986176 : Nat := 4983230072969 + 3 ^ 40 * 986176 * 2
def baseEnd_986176 : Nat := 506382297928438815564665

theorem tailTrace_986176 : CollatzResearch.WordTrace tailWord_986176 prefixEnd_986176 506382297928438815564665 := by
  unfold tailWord_986176
  simp only [CollatzResearch.WordTrace]
  refine ⟨17984396837630126148437191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23979195783506834864582921 17984396837630126148437191)
  ·
    refine ⟨26976595256445189222655787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17984396837630126148437191 26976595256445189222655787)
    ·
      refine ⟨40464892884667783833983681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26976595256445189222655787 40464892884667783833983681)
      ·
        refine ⟨30348669663500837875487761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40464892884667783833983681 30348669663500837875487761)
        ·
          refine ⟨22761502247625628406615821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30348669663500837875487761 22761502247625628406615821)
          ·
            refine ⟨8535563342859610652480933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22761502247625628406615821 8535563342859610652480933)
            ·
              refine ⟨1600418126786176997340175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8535563342859610652480933 1600418126786176997340175)
              ·
                refine ⟨2400627190179265496010263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1600418126786176997340175 2400627190179265496010263)
                ·
                  refine ⟨3600940785268898244015395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2400627190179265496010263 3600940785268898244015395)
                  ·
                    refine ⟨5401411177903347366023093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3600940785268898244015395 5401411177903347366023093)
                    ·
                      refine ⟨506382297928438815564665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5401411177903347366023093 506382297928438815564665)
                      ·
                        rfl

theorem cell23_986176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 5].length) (baseStart_986176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_986176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_986176 prefixEnd_986176 := by exact prefixLift 986176
  have htrace : WordTrace (prefixWord ++ tailWord_986176) baseStart_986176 baseEnd_986176 := by
    simpa [prefixWord, tailWord_986176, baseEnd_986176] using wordTrace_append hprefix tailTrace_986176
  have hstable : (prefixWord ++ tailWord_986176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986176).length < 2 ^ (prefixWord ++ tailWord_986176).sum := by decide
  have hdescent : baseEnd_986176 < baseStart_986176 := by decide
  rcases family_descends (prefixWord ++ tailWord_986176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986199 : List Nat := [1, 1, 3, 2, 2, 1, 1, 1, 1, 4, 6]
def baseStart_986199 : Nat := 118140960795 + 986199 * 2 ^ 59
def prefixEnd_986199 : Nat := 4983230072969 + 3 ^ 40 * 986199 * 2
def baseEnd_986199 : Nat := 506394107983492225577059

theorem tailTrace_986199 : CollatzResearch.WordTrace tailWord_986199 prefixEnd_986199 506394107983492225577059 := by
  unfold tailWord_986199
  simp only [CollatzResearch.WordTrace]
  refine ⟨35969632554176927224961651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23979755036117951483307767 35969632554176927224961651)
  ·
    refine ⟨53954448831265390837442477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35969632554176927224961651 53954448831265390837442477)
    ·
      refine ⟨20232918311724521564040929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53954448831265390837442477 20232918311724521564040929)
      ·
        refine ⟨15174688733793391173030697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20232918311724521564040929 15174688733793391173030697)
        ·
          refine ⟨11381016550345043379773023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15174688733793391173030697 11381016550345043379773023)
          ·
            refine ⟨17071524825517565069659535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11381016550345043379773023 17071524825517565069659535)
            ·
              refine ⟨25607287238276347604489303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17071524825517565069659535 25607287238276347604489303)
              ·
                refine ⟨38410930857414521406733955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25607287238276347604489303 38410930857414521406733955)
                ·
                  refine ⟨57616396286121782110100933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38410930857414521406733955 57616396286121782110100933)
                  ·
                    refine ⟨10803074303647834145643925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57616396286121782110100933 10803074303647834145643925)
                    ·
                      refine ⟨506394107983492225577059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10803074303647834145643925 506394107983492225577059)
                      ·
                        rfl

theorem cell23_986199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 4, 6].length) (baseStart_986199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_986199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_986199 prefixEnd_986199 := by exact prefixLift 986199
  have htrace : WordTrace (prefixWord ++ tailWord_986199) baseStart_986199 baseEnd_986199 := by
    simpa [prefixWord, tailWord_986199, baseEnd_986199] using wordTrace_append hprefix tailTrace_986199
  have hstable : (prefixWord ++ tailWord_986199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986199).length < 2 ^ (prefixWord ++ tailWord_986199).sum := by decide
  have hdescent : baseEnd_986199 < baseStart_986199 := by decide
  rcases family_descends (prefixWord ++ tailWord_986199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986210 : List Nat := [3, 3, 2, 2, 1, 2, 1, 1, 3, 2, 3]
def baseStart_986210 : Nat := 118140960795 + 986210 * 2 ^ 59
def prefixEnd_986210 : Nat := 4983230072969 + 3 ^ 40 * 986210 * 2
def baseEnd_986210 : Nat := 506399756270691682539509

theorem tailTrace_986210 : CollatzResearch.WordTrace tailWord_986210 prefixEnd_986210 506399756270691682539509 := by
  unfold tailWord_986210
  simp only [CollatzResearch.WordTrace]
  refine ⟨8992508439284269025903021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23980022504758050735741389 8992508439284269025903021)
  ·
    refine ⟨3372190664731600884713633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8992508439284269025903021 3372190664731600884713633)
    ·
      refine ⟨2529142998548700663535225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3372190664731600884713633 2529142998548700663535225)
      ·
        refine ⟨1896857248911525497651419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2529142998548700663535225 1896857248911525497651419)
        ·
          refine ⟨2845285873367288246477129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1896857248911525497651419 2845285873367288246477129)
          ·
            refine ⟨2133964405025466184857847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2845285873367288246477129 2133964405025466184857847)
            ·
              refine ⟨3200946607538199277286771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2133964405025466184857847 3200946607538199277286771)
              ·
                refine ⟨4801419911307298915930157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3200946607538199277286771 4801419911307298915930157)
                ·
                  refine ⟨1800532466740237093473809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4801419911307298915930157 1800532466740237093473809)
                  ·
                    refine ⟨1350399350055177820105357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1800532466740237093473809 1350399350055177820105357)
                    ·
                      refine ⟨506399756270691682539509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1350399350055177820105357 506399756270691682539509)
                      ·
                        rfl

theorem cell23_986210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_986210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_986210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_986210 prefixEnd_986210 := by exact prefixLift 986210
  have htrace : WordTrace (prefixWord ++ tailWord_986210) baseStart_986210 baseEnd_986210 := by
    simpa [prefixWord, tailWord_986210, baseEnd_986210] using wordTrace_append hprefix tailTrace_986210
  have hstable : (prefixWord ++ tailWord_986210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986210).length < 2 ^ (prefixWord ++ tailWord_986210).sum := by decide
  have hdescent : baseEnd_986210 < baseStart_986210 := by decide
  rcases family_descends (prefixWord ++ tailWord_986210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986239 : List Nat := [1, 1, 2, 2, 1, 1, 1, 1, 5, 8]
def baseStart_986239 : Nat := 118140960795 + 986239 * 2 ^ 59
def prefixEnd_986239 : Nat := 4983230072969 + 3 ^ 40 * 986239 * 2
def baseEnd_986239 : Nat := 168804882403224023025625

theorem tailTrace_986239 : CollatzResearch.WordTrace tailWord_986239 prefixEnd_986239 168804882403224023025625 := by
  unfold tailWord_986239
  simp only [CollatzResearch.WordTrace]
  refine ⟨35971091474032014056417771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23980727649354676037611847 35971091474032014056417771)
  ·
    refine ⟨53956637211048021084626657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35971091474032014056417771 53956637211048021084626657)
    ·
      refine ⟨40467477908286015813469993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53956637211048021084626657 40467477908286015813469993)
      ·
        refine ⟨30350608431214511860102495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40467477908286015813469993 30350608431214511860102495)
        ·
          refine ⟨45525912646821767790153743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30350608431214511860102495 45525912646821767790153743)
          ·
            refine ⟨68288868970232651685230615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45525912646821767790153743 68288868970232651685230615)
            ·
              refine ⟨102433303455348977527845923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68288868970232651685230615 102433303455348977527845923)
              ·
                refine ⟨153649955183023466291768885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102433303455348977527845923 153649955183023466291768885)
                ·
                  refine ⟨14404683298408449964853333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 153649955183023466291768885 14404683298408449964853333)
                  ·
                    refine ⟨168804882403224023025625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 14404683298408449964853333 168804882403224023025625)
                    ·
                      rfl

theorem cell23_986239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 8].length) (baseStart_986239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_986239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_986239 prefixEnd_986239 := by exact prefixLift 986239
  have htrace : WordTrace (prefixWord ++ tailWord_986239) baseStart_986239 baseEnd_986239 := by
    simpa [prefixWord, tailWord_986239, baseEnd_986239] using wordTrace_append hprefix tailTrace_986239
  have hstable : (prefixWord ++ tailWord_986239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986239).length < 2 ^ (prefixWord ++ tailWord_986239).sum := by decide
  have hdescent : baseEnd_986239 < baseStart_986239 := by decide
  rcases family_descends (prefixWord ++ tailWord_986239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986241 : List Nat := [1, 2, 4, 2, 2, 3, 2, 2, 1, 2, 2]
def baseStart_986241 : Nat := 118140960795 + 986241 * 2 ^ 59
def prefixEnd_986241 : Nat := 4983230072969 + 3 ^ 40 * 986241 * 2
def baseEnd_986241 : Nat := 506415674170981061251867

theorem tailTrace_986241 : CollatzResearch.WordTrace tailWord_986241 prefixEnd_986241 506415674170981061251867 := by
  unfold tailWord_986241
  simp only [CollatzResearch.WordTrace]
  refine ⟨35971164420024768397990577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23980776280016512265327051 35971164420024768397990577)
  ·
    refine ⟨26978373315018576298492933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35971164420024768397990577 26978373315018576298492933)
    ·
      refine ⟨5058444996565983055967425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26978373315018576298492933 5058444996565983055967425)
      ·
        refine ⟨3793833747424487291975569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5058444996565983055967425 3793833747424487291975569)
        ·
          refine ⟨2845375310568365468981677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3793833747424487291975569 2845375310568365468981677)
          ·
            refine ⟨1067015741463137050868129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2845375310568365468981677 1067015741463137050868129)
            ·
              refine ⟨800261806097352788151097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1067015741463137050868129 800261806097352788151097)
              ·
                refine ⟨600196354573014591113323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 800261806097352788151097 600196354573014591113323)
                ·
                  refine ⟨900294531859521886669985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 600196354573014591113323 900294531859521886669985)
                  ·
                    refine ⟨675220898894641415002489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 900294531859521886669985 675220898894641415002489)
                    ·
                      refine ⟨506415674170981061251867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 675220898894641415002489 506415674170981061251867)
                      ·
                        rfl

theorem cell23_986241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 2, 2, 1, 2, 2].length) (baseStart_986241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_986241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_986241 prefixEnd_986241 := by exact prefixLift 986241
  have htrace : WordTrace (prefixWord ++ tailWord_986241) baseStart_986241 baseEnd_986241 := by
    simpa [prefixWord, tailWord_986241, baseEnd_986241] using wordTrace_append hprefix tailTrace_986241
  have hstable : (prefixWord ++ tailWord_986241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986241).length < 2 ^ (prefixWord ++ tailWord_986241).sum := by decide
  have hdescent : baseEnd_986241 < baseStart_986241 := by decide
  rcases family_descends (prefixWord ++ tailWord_986241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986297 : List Nat := [1, 2, 1, 4, 1, 3, 3, 2, 2, 2, 2]
def baseStart_986297 : Nat := 118140960795 + 986297 * 2 ^ 59
def prefixEnd_986297 : Nat := 4983230072969 + 3 ^ 40 * 986297 * 2
def baseEnd_986297 : Nat := 506444429087632842151609

theorem tailTrace_986297 : CollatzResearch.WordTrace tailWord_986297 prefixEnd_986297 506444429087632842151609 := by
  unfold tailWord_986297
  simp only [CollatzResearch.WordTrace]
  refine ⟨35973206907821889962029145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23982137938547926641352763 35973206907821889962029145)
  ·
    refine ⟨26979905180866417471521859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35973206907821889962029145 26979905180866417471521859)
    ·
      refine ⟨40469857771299626207282789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26979905180866417471521859 40469857771299626207282789)
      ·
        refine ⟨7588098332118679913865523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40469857771299626207282789 7588098332118679913865523)
        ·
          refine ⟨11382147498178019870798285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7588098332118679913865523 11382147498178019870798285)
          ·
            refine ⟨4268305311816757451549357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11382147498178019870798285 4268305311816757451549357)
            ·
              refine ⟨1600614491931284044331009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4268305311816757451549357 1600614491931284044331009)
              ·
                refine ⟨1200460868948463033248257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1600614491931284044331009 1200460868948463033248257)
                ·
                  refine ⟨900345651711347274936193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1200460868948463033248257 900345651711347274936193)
                  ·
                    refine ⟨675259238783510456202145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 900345651711347274936193 675259238783510456202145)
                    ·
                      refine ⟨506444429087632842151609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 675259238783510456202145 506444429087632842151609)
                      ·
                        rfl

theorem cell23_986297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 2, 2, 2, 2].length) (baseStart_986297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_986297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_986297 prefixEnd_986297 := by exact prefixLift 986297
  have htrace : WordTrace (prefixWord ++ tailWord_986297) baseStart_986297 baseEnd_986297 := by
    simpa [prefixWord, tailWord_986297, baseEnd_986297] using wordTrace_append hprefix tailTrace_986297
  have hstable : (prefixWord ++ tailWord_986297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986297).length < 2 ^ (prefixWord ++ tailWord_986297).sum := by decide
  have hdescent : baseEnd_986297 < baseStart_986297 := by decide
  rcases family_descends (prefixWord ++ tailWord_986297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986303 : List Nat := [1, 1, 2, 2, 2, 2, 4, 4, 5]
def baseStart_986303 : Nat := 118140960795 + 986303 * 2 ^ 59
def prefixEnd_986303 : Nat := 4983230072969 + 3 ^ 40 * 986303 * 2
def baseEnd_986303 : Nat := 56271945552395535408509

theorem tailTrace_986303 : CollatzResearch.WordTrace tailWord_986303 prefixEnd_986303 56271945552395535408509 := by
  unfold tailWord_986303
  simp only [CollatzResearch.WordTrace]
  refine ⟨35973425745800152986747563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23982283830533435324498375 35973425745800152986747563)
  ·
    refine ⟨53960138618700229480121345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35973425745800152986747563 53960138618700229480121345)
    ·
      refine ⟨40470103964025172110091009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53960138618700229480121345 40470103964025172110091009)
      ·
        refine ⟨30352577973018879082568257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40470103964025172110091009 30352577973018879082568257)
        ·
          refine ⟨22764433479764159311926193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30352577973018879082568257 22764433479764159311926193)
          ·
            refine ⟨17073325109823119483944645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22764433479764159311926193 17073325109823119483944645)
            ·
              refine ⟨3201248458091834903239621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17073325109823119483944645 3201248458091834903239621)
              ·
                refine ⟨600234085892219044357429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3201248458091834903239621 600234085892219044357429)
                ·
                  refine ⟨56271945552395535408509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 600234085892219044357429 56271945552395535408509)
                  ·
                    rfl

theorem cell23_986303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 4, 5].length) (baseStart_986303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_986303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_986303 prefixEnd_986303 := by exact prefixLift 986303
  have htrace : WordTrace (prefixWord ++ tailWord_986303) baseStart_986303 baseEnd_986303 := by
    simpa [prefixWord, tailWord_986303, baseEnd_986303] using wordTrace_append hprefix tailTrace_986303
  have hstable : (prefixWord ++ tailWord_986303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986303).length < 2 ^ (prefixWord ++ tailWord_986303).sum := by decide
  have hdescent : baseEnd_986303 < baseStart_986303 := by decide
  rcases family_descends (prefixWord ++ tailWord_986303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986314 : List Nat := [3, 1, 2, 1, 3, 3, 3, 1, 2, 2, 2]
def baseStart_986314 : Nat := 118140960795 + 986314 * 2 ^ 59
def prefixEnd_986314 : Nat := 4983230072969 + 3 ^ 40 * 986314 * 2
def baseEnd_986314 : Nat := 506453158258759275639031

theorem tailTrace_986314 : CollatzResearch.WordTrace tailWord_986314 prefixEnd_986314 506453158258759275639031 := by
  unfold tailWord_986314
  simp only [CollatzResearch.WordTrace]
  refine ⟨8993456737190075466349499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23982551299173534576931997 8993456737190075466349499)
  ·
    refine ⟨13490185105785113199524249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8993456737190075466349499 13490185105785113199524249)
    ·
      refine ⟨10117638829338834899643187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13490185105785113199524249 10117638829338834899643187)
      ·
        refine ⟨15176458244008252349464781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10117638829338834899643187 15176458244008252349464781)
        ·
          refine ⟨5691171841503094631049293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15176458244008252349464781 5691171841503094631049293)
          ·
            refine ⟨2134189440563660486643485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5691171841503094631049293 2134189440563660486643485)
            ·
              refine ⟨800321040211372682491307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2134189440563660486643485 800321040211372682491307)
              ·
                refine ⟨1200481560317059023736961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 800321040211372682491307 1200481560317059023736961)
                ·
                  refine ⟨900361170237794267802721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1200481560317059023736961 900361170237794267802721)
                  ·
                    refine ⟨675270877678345700852041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 900361170237794267802721 675270877678345700852041)
                    ·
                      refine ⟨506453158258759275639031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 675270877678345700852041 506453158258759275639031)
                      ·
                        rfl

theorem cell23_986314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 3, 1, 2, 2, 2].length) (baseStart_986314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_986314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_986314 prefixEnd_986314 := by exact prefixLift 986314
  have htrace : WordTrace (prefixWord ++ tailWord_986314) baseStart_986314 baseEnd_986314 := by
    simpa [prefixWord, tailWord_986314, baseEnd_986314] using wordTrace_append hprefix tailTrace_986314
  have hstable : (prefixWord ++ tailWord_986314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986314).length < 2 ^ (prefixWord ++ tailWord_986314).sum := by decide
  have hdescent : baseEnd_986314 < baseStart_986314 := by decide
  rcases family_descends (prefixWord ++ tailWord_986314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986373 : List Nat := [1, 3, 1, 1, 2, 1, 3, 2, 4, 2, 3]
def baseStart_986373 : Nat := 118140960795 + 986373 * 2 ^ 59
def prefixEnd_986373 : Nat := 4983230072969 + 3 ^ 40 * 986373 * 2
def baseEnd_986373 : Nat := 506483453617374544801259

theorem tailTrace_986373 : CollatzResearch.WordTrace tailWord_986373 prefixEnd_986373 506483453617374544801259 := by
  unfold tailWord_986373
  simp only [CollatzResearch.WordTrace]
  refine ⟨35975978855546554941795773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23983985903697703294530515 35975978855546554941795773)
  ·
    refine ⟨13490992070829958103173415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35975978855546554941795773 13490992070829958103173415)
    ·
      refine ⟨20236488106244937154760123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13490992070829958103173415 20236488106244937154760123)
      ·
        refine ⟨30354732159367405732140185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20236488106244937154760123 30354732159367405732140185)
        ·
          refine ⟨22766049119525554299105139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30354732159367405732140185 22766049119525554299105139)
          ·
            refine ⟨34149073679288331448657709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22766049119525554299105139 34149073679288331448657709)
            ·
              refine ⟨12805902629733124293246641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34149073679288331448657709 12805902629733124293246641)
              ·
                refine ⟨9604426972299843219934981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12805902629733124293246641 9604426972299843219934981)
                ·
                  refine ⟨1800830057306220603737809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9604426972299843219934981 1800830057306220603737809)
                  ·
                    refine ⟨1350622542979665452803357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1800830057306220603737809 1350622542979665452803357)
                    ·
                      refine ⟨506483453617374544801259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1350622542979665452803357 506483453617374544801259)
                      ·
                        rfl

theorem cell23_986373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 4, 2, 3].length) (baseStart_986373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_986373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_986373 prefixEnd_986373 := by exact prefixLift 986373
  have htrace : WordTrace (prefixWord ++ tailWord_986373) baseStart_986373 baseEnd_986373 := by
    simpa [prefixWord, tailWord_986373, baseEnd_986373] using wordTrace_append hprefix tailTrace_986373
  have hstable : (prefixWord ++ tailWord_986373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986373).length < 2 ^ (prefixWord ++ tailWord_986373).sum := by decide
  have hdescent : baseEnd_986373 < baseStart_986373 := by decide
  rcases family_descends (prefixWord ++ tailWord_986373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986410 : List Nat := [3, 1, 4, 2, 1, 1, 1, 4, 6]
def baseStart_986410 : Nat := 118140960795 + 986410 * 2 ^ 59
def prefixEnd_986410 : Nat := 4983230072969 + 3 ^ 40 * 986410 * 2
def baseEnd_986410 : Nat := 56278050266843433337621

theorem tailTrace_986410 : CollatzResearch.WordTrace tailWord_986410 prefixEnd_986410 56278050266843433337621 := by
  unfold tailWord_986410
  simp only [CollatzResearch.WordTrace]
  refine ⟨8994332089103127565223171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23984885570941673507261789 8994332089103127565223171)
  ·
    refine ⟨13491498133654691347834757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8994332089103127565223171 13491498133654691347834757)
    ·
      refine ⟨2529655900060254627719017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13491498133654691347834757 2529655900060254627719017)
      ·
        refine ⟨1897241925045190970789263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2529655900060254627719017 1897241925045190970789263)
        ·
          refine ⟨2845862887567786456183895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1897241925045190970789263 2845862887567786456183895)
          ·
            refine ⟨4268794331351679684275843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2845862887567786456183895 4268794331351679684275843)
            ·
              refine ⟨6403191497027519526413765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4268794331351679684275843 6403191497027519526413765)
              ·
                refine ⟨1200598405692659911202581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6403191497027519526413765 1200598405692659911202581)
                ·
                  refine ⟨56278050266843433337621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1200598405692659911202581 56278050266843433337621)
                  ·
                    rfl

theorem cell23_986410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 4, 6].length) (baseStart_986410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_986410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_986410 prefixEnd_986410 := by exact prefixLift 986410
  have htrace : WordTrace (prefixWord ++ tailWord_986410) baseStart_986410 baseEnd_986410 := by
    simpa [prefixWord, tailWord_986410, baseEnd_986410] using wordTrace_append hprefix tailTrace_986410
  have hstable : (prefixWord ++ tailWord_986410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986410).length < 2 ^ (prefixWord ++ tailWord_986410).sum := by decide
  have hdescent : baseEnd_986410 < baseStart_986410 := by decide
  rcases family_descends (prefixWord ++ tailWord_986410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986438 : List Nat := [6, 1, 1, 3, 2, 1, 1, 1, 2, 1, 4]
def baseStart_986438 : Nat := 118140960795 + 986438 * 2 ^ 59
def prefixEnd_986438 : Nat := 4983230072969 + 3 ^ 40 * 986438 * 2
def baseEnd_986438 : Nat := 506516829859916790488461

theorem tailTrace_986438 : CollatzResearch.WordTrace tailWord_986438 prefixEnd_986438 506516829859916790488461 := by
  unfold tailWord_986438
  simp only [CollatzResearch.WordTrace]
  refine ⟨1124323425009720970090999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 23985566400207380695274645 1124323425009720970090999)
  ·
    refine ⟨1686485137514581455136499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1124323425009720970090999 1686485137514581455136499)
    ·
      refine ⟨2529727706271872182704749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1686485137514581455136499 2529727706271872182704749)
      ·
        refine ⟨948647889851952068514281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2529727706271872182704749 948647889851952068514281)
        ·
          refine ⟨711485917388964051385711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 948647889851952068514281 711485917388964051385711)
          ·
            refine ⟨1067228876083446077078567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 711485917388964051385711 1067228876083446077078567)
            ·
              refine ⟨1600843314125169115617851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1067228876083446077078567 1600843314125169115617851)
              ·
                refine ⟨2401264971187753673426777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1600843314125169115617851 2401264971187753673426777)
                ·
                  refine ⟨1800948728390815255070083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2401264971187753673426777 1800948728390815255070083)
                  ·
                    refine ⟨2701423092586222882605125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1800948728390815255070083 2701423092586222882605125)
                    ·
                      refine ⟨506516829859916790488461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2701423092586222882605125 506516829859916790488461)
                      ·
                        rfl

theorem cell23_986438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_986438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_986438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_986438 prefixEnd_986438 := by exact prefixLift 986438
  have htrace : WordTrace (prefixWord ++ tailWord_986438) baseStart_986438 baseEnd_986438 := by
    simpa [prefixWord, tailWord_986438, baseEnd_986438] using wordTrace_append hprefix tailTrace_986438
  have hstable : (prefixWord ++ tailWord_986438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986438).length < 2 ^ (prefixWord ++ tailWord_986438).sum := by decide
  have hdescent : baseEnd_986438 < baseStart_986438 := by decide
  rcases family_descends (prefixWord ++ tailWord_986438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986461 : List Nat := [1, 4, 5, 1, 1, 2, 1, 2, 6]
def baseStart_986461 : Nat := 118140960795 + 986461 * 2 ^ 59
def prefixEnd_986461 : Nat := 4983230072969 + 3 ^ 40 * 986461 * 2
def baseEnd_986461 : Nat := 56280959990552244500095

theorem tailTrace_986461 : CollatzResearch.WordTrace tailWord_986461 prefixEnd_986461 56280959990552244500095 := by
  unfold tailWord_986461
  simp only [CollatzResearch.WordTrace]
  refine ⟨35979188479227745970999237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23986125652818497313999491 35979188479227745970999237)
  ·
    refine ⟨6746097839855202369562357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35979188479227745970999237 6746097839855202369562357)
    ·
      refine ⟨632446672486425222146471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6746097839855202369562357 632446672486425222146471)
      ·
        refine ⟨948670008729637833219707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 632446672486425222146471 948670008729637833219707)
        ·
          refine ⟨1423005013094456749829561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 948670008729637833219707 1423005013094456749829561)
          ·
            refine ⟨1067253759820842562372171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1423005013094456749829561 1067253759820842562372171)
            ·
              refine ⟨1600880639731263843558257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1067253759820842562372171 1600880639731263843558257)
              ·
                refine ⟨1200660479798447882668693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1600880639731263843558257 1200660479798447882668693)
                ·
                  refine ⟨56280959990552244500095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1200660479798447882668693 56280959990552244500095)
                  ·
                    rfl

theorem cell23_986461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 2, 6].length) (baseStart_986461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_986461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_986461 prefixEnd_986461 := by exact prefixLift 986461
  have htrace : WordTrace (prefixWord ++ tailWord_986461) baseStart_986461 baseEnd_986461 := by
    simpa [prefixWord, tailWord_986461, baseEnd_986461] using wordTrace_append hprefix tailTrace_986461
  have hstable : (prefixWord ++ tailWord_986461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986461).length < 2 ^ (prefixWord ++ tailWord_986461).sum := by decide
  have hdescent : baseEnd_986461 < baseStart_986461 := by decide
  rcases family_descends (prefixWord ++ tailWord_986461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986463 : List Nat := [1, 1, 2, 3, 1, 2, 1, 5, 1, 1, 5]
def baseStart_986463 : Nat := 118140960795 + 986463 * 2 ^ 59
def prefixEnd_986463 : Nat := 4983230072969 + 3 ^ 40 * 986463 * 2
def baseEnd_986463 : Nat := 506529666876279192675845

theorem tailTrace_986463 : CollatzResearch.WordTrace tailWord_986463 prefixEnd_986463 506529666876279192675845 := by
  unfold tailWord_986463
  simp only [CollatzResearch.WordTrace]
  refine ⟨35979261425220500312572043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23986174283480333541714695 35979261425220500312572043)
  ·
    refine ⟨53968892137830750468858065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35979261425220500312572043 53968892137830750468858065)
    ·
      refine ⟨40476669103373062851643549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53968892137830750468858065 40476669103373062851643549)
      ·
        refine ⟨15178750913764898569366331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40476669103373062851643549 15178750913764898569366331)
        ·
          refine ⟨22768126370647347854049497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15178750913764898569366331 22768126370647347854049497)
          ·
            refine ⟨17076094777985510890537123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22768126370647347854049497 17076094777985510890537123)
            ·
              refine ⟨25614142166978266335805685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17076094777985510890537123 25614142166978266335805685)
              ·
                refine ⟨2401325828154212468981783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25614142166978266335805685 2401325828154212468981783)
                ·
                  refine ⟨3601988742231318703472675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2401325828154212468981783 3601988742231318703472675)
                  ·
                    refine ⟨5402983113346978055209013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3601988742231318703472675 5402983113346978055209013)
                    ·
                      refine ⟨506529666876279192675845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5402983113346978055209013 506529666876279192675845)
                      ·
                        rfl

theorem cell23_986463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 5, 1, 1, 5].length) (baseStart_986463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_986463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_986463 prefixEnd_986463 := by exact prefixLift 986463
  have htrace : WordTrace (prefixWord ++ tailWord_986463) baseStart_986463 baseEnd_986463 := by
    simpa [prefixWord, tailWord_986463, baseEnd_986463] using wordTrace_append hprefix tailTrace_986463
  have hstable : (prefixWord ++ tailWord_986463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986463).length < 2 ^ (prefixWord ++ tailWord_986463).sum := by decide
  have hdescent : baseEnd_986463 < baseStart_986463 := by decide
  rcases family_descends (prefixWord ++ tailWord_986463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986487 : List Nat := [1, 1, 3, 1, 1, 2, 7, 1, 2, 4]
def baseStart_986487 : Nat := 118140960795 + 986487 * 2 ^ 59
def prefixEnd_986487 : Nat := 4983230072969 + 3 ^ 40 * 986487 * 2
def baseEnd_986487 : Nat := 168847330137329032925245

theorem tailTrace_986487 : CollatzResearch.WordTrace tailWord_986487 prefixEnd_986487 168847330137329032925245 := by
  unfold tailWord_986487
  simp only [CollatzResearch.WordTrace]
  refine ⟨35980136777133552411445715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23986757851422368274297143 35980136777133552411445715)
  ·
    refine ⟨53970205165700328617168573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35980136777133552411445715 53970205165700328617168573)
    ·
      refine ⟨20238826937137623231438215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53970205165700328617168573 20238826937137623231438215)
      ·
        refine ⟨30358240405706434847157323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20238826937137623231438215 30358240405706434847157323)
        ·
          refine ⟨45537360608559652270735985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30358240405706434847157323 45537360608559652270735985)
          ·
            refine ⟨34153020456419739203051989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45537360608559652270735985 34153020456419739203051989)
            ·
              refine ⟨800461416947337637571531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 34153020456419739203051989 800461416947337637571531)
              ·
                refine ⟨1200692125421006456357297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 800461416947337637571531 1200692125421006456357297)
                ·
                  refine ⟨900519094065754842267973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1200692125421006456357297 900519094065754842267973)
                  ·
                    refine ⟨168847330137329032925245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 900519094065754842267973 168847330137329032925245)
                    ·
                      rfl

theorem cell23_986487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 7, 1, 2, 4].length) (baseStart_986487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_986487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_986487 prefixEnd_986487 := by exact prefixLift 986487
  have htrace : WordTrace (prefixWord ++ tailWord_986487) baseStart_986487 baseEnd_986487 := by
    simpa [prefixWord, tailWord_986487, baseEnd_986487] using wordTrace_append hprefix tailTrace_986487
  have hstable : (prefixWord ++ tailWord_986487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986487).length < 2 ^ (prefixWord ++ tailWord_986487).sum := by decide
  have hdescent : baseEnd_986487 < baseStart_986487 := by decide
  rcases family_descends (prefixWord ++ tailWord_986487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986500 : List Nat := [2, 3, 2, 1, 1, 3, 4, 7]
def baseStart_986500 : Nat := 118140960795 + 986500 * 2 ^ 59
def prefixEnd_986500 : Nat := 4983230072969 + 3 ^ 40 * 986500 * 2
def baseEnd_986500 : Nat := 18761061691129464737525

theorem tailTrace_986500 : CollatzResearch.WordTrace tailWord_986500 prefixEnd_986500 18761061691129464737525 := by
  unfold tailWord_986500
  simp only [CollatzResearch.WordTrace]
  refine ⟨17990305463043227815834477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23987073950724303754445969 17990305463043227815834477)
  ·
    refine ⟨6746364548641210430937929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17990305463043227815834477 6746364548641210430937929)
    ·
      refine ⟨5059773411480907823203447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6746364548641210430937929 5059773411480907823203447)
      ·
        refine ⟨7589660117221361734805171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5059773411480907823203447 7589660117221361734805171)
        ·
          refine ⟨11384490175832042602207757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7589660117221361734805171 11384490175832042602207757)
          ·
            refine ⟨4269183815937015975827909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11384490175832042602207757 4269183815937015975827909)
            ·
              refine ⟨800471965488190495467733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4269183815937015975827909 800471965488190495467733)
              ·
                refine ⟨18761061691129464737525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 800471965488190495467733 18761061691129464737525)
                ·
                  rfl

theorem cell23_986500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 4, 7].length) (baseStart_986500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_986500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_986500 prefixEnd_986500 := by exact prefixLift 986500
  have htrace : WordTrace (prefixWord ++ tailWord_986500) baseStart_986500 baseEnd_986500 := by
    simpa [prefixWord, tailWord_986500, baseEnd_986500] using wordTrace_append hprefix tailTrace_986500
  have hstable : (prefixWord ++ tailWord_986500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986500).length < 2 ^ (prefixWord ++ tailWord_986500).sum := by decide
  have hdescent : baseEnd_986500 < baseStart_986500 := by decide
  rcases family_descends (prefixWord ++ tailWord_986500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986514 : List Nat := [3, 2, 3, 3, 1, 1, 2, 1, 1, 1, 5]
def baseStart_986514 : Nat := 118140960795 + 986514 * 2 ^ 59
def prefixEnd_986514 : Nat := 4983230072969 + 3 ^ 40 * 986514 * 2
def baseEnd_986514 : Nat := 506555854389658493138111

theorem tailTrace_986514 : CollatzResearch.WordTrace tailWord_986514 prefixEnd_986514 506555854389658493138111 := by
  unfold tailWord_986514
  simp only [CollatzResearch.WordTrace]
  refine ⟨8995280387008934005669649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23987414365357157348452397 8995280387008934005669649)
  ·
    refine ⟨6746460290256700504252237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8995280387008934005669649 6746460290256700504252237)
    ·
      refine ⟨2529922608846262689094589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6746460290256700504252237 2529922608846262689094589)
      ·
        refine ⟨948720978317348508410471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2529922608846262689094589 948720978317348508410471)
        ·
          refine ⟨1423081467476022762615707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 948720978317348508410471 1423081467476022762615707)
          ·
            refine ⟨2134622201214034143923561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1423081467476022762615707 2134622201214034143923561)
            ·
              refine ⟨1600966650910525607942671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2134622201214034143923561 1600966650910525607942671)
              ·
                refine ⟨2401449976365788411914007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1600966650910525607942671 2401449976365788411914007)
                ·
                  refine ⟨3602174964548682617871011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2401449976365788411914007 3602174964548682617871011)
                  ·
                    refine ⟨5403262446823023926806517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3602174964548682617871011 5403262446823023926806517)
                    ·
                      refine ⟨506555854389658493138111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5403262446823023926806517 506555854389658493138111)
                      ·
                        rfl

theorem cell23_986514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_986514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_986514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_986514 prefixEnd_986514 := by exact prefixLift 986514
  have htrace : WordTrace (prefixWord ++ tailWord_986514) baseStart_986514 baseEnd_986514 := by
    simpa [prefixWord, tailWord_986514, baseEnd_986514] using wordTrace_append hprefix tailTrace_986514
  have hstable : (prefixWord ++ tailWord_986514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986514).length < 2 ^ (prefixWord ++ tailWord_986514).sum := by decide
  have hdescent : baseEnd_986514 < baseStart_986514 := by decide
  rcases family_descends (prefixWord ++ tailWord_986514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986527 : List Nat := [1, 1, 2, 5, 1, 2, 2, 1, 4, 1, 3]
def baseStart_986527 : Nat := 118140960795 + 986527 * 2 ^ 59
def prefixEnd_986527 : Nat := 4983230072969 + 3 ^ 40 * 986527 * 2
def baseEnd_986527 : Nat := 506562529638166942275551

theorem tailTrace_986527 : CollatzResearch.WordTrace tailWord_986527 prefixEnd_986527 506562529638166942275551 := by
  unfold tailWord_986527
  simp only [CollatzResearch.WordTrace]
  refine ⟨35981595696988639242901835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23987730464659092828601223 35981595696988639242901835)
  ·
    refine ⟨53972393545482958864352753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35981595696988639242901835 53972393545482958864352753)
    ·
      refine ⟨40479295159112219148264565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53972393545482958864352753 40479295159112219148264565)
      ·
        refine ⟨3794933921166770545149803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40479295159112219148264565 3794933921166770545149803)
        ·
          refine ⟨5692400881750155817724705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3794933921166770545149803 5692400881750155817724705)
          ·
            refine ⟨4269300661312616863293529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5692400881750155817724705 4269300661312616863293529)
            ·
              refine ⟨3201975495984462647470147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4269300661312616863293529 3201975495984462647470147)
              ·
                refine ⟨4802963243976693971205221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3201975495984462647470147 4802963243976693971205221)
                ·
                  refine ⟨900555608245630119600979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4802963243976693971205221 900555608245630119600979)
                  ·
                    refine ⟨1350833412368445179401469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 900555608245630119600979 1350833412368445179401469)
                    ·
                      refine ⟨506562529638166942275551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1350833412368445179401469 506562529638166942275551)
                      ·
                        rfl

theorem cell23_986527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_986527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_986527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_986527 prefixEnd_986527 := by exact prefixLift 986527
  have htrace : WordTrace (prefixWord ++ tailWord_986527) baseStart_986527 baseEnd_986527 := by
    simpa [prefixWord, tailWord_986527, baseEnd_986527] using wordTrace_append hprefix tailTrace_986527
  have hstable : (prefixWord ++ tailWord_986527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986527).length < 2 ^ (prefixWord ++ tailWord_986527).sum := by decide
  have hdescent : baseEnd_986527 < baseStart_986527 := by decide
  rcases family_descends (prefixWord ++ tailWord_986527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986543 : List Nat := [1, 1, 2, 1, 2, 2, 1, 5, 2, 6]
def baseStart_986543 : Nat := 118140960795 + 986543 * 2 ^ 59
def prefixEnd_986543 : Nat := 4983230072969 + 3 ^ 40 * 986543 * 2
def baseEnd_986543 : Nat := 168856915109546293225159

theorem tailTrace_986543 : CollatzResearch.WordTrace tailWord_986543 prefixEnd_986543 168856915109546293225159 := by
  unfold tailWord_986543
  simp only [CollatzResearch.WordTrace]
  refine ⟨35982179264930673975484283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23988119509953782650322855 35982179264930673975484283)
  ·
    refine ⟨53973268897396010963226425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35982179264930673975484283 53973268897396010963226425)
    ·
      refine ⟨40479951673047008222419819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53973268897396010963226425 40479951673047008222419819)
      ·
        refine ⟨60719927509570512333629729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40479951673047008222419819 60719927509570512333629729)
        ·
          refine ⟨45539945632177884250222297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60719927509570512333629729 45539945632177884250222297)
          ·
            refine ⟨34154959224133413187666723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45539945632177884250222297 34154959224133413187666723)
            ·
              refine ⟨51232438836200119781500085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34154959224133413187666723 51232438836200119781500085)
              ·
                refine ⟨4803041140893761229515633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51232438836200119781500085 4803041140893761229515633)
                ·
                  refine ⟨3602280855670320922136725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4803041140893761229515633 3602280855670320922136725)
                  ·
                    refine ⟨168856915109546293225159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3602280855670320922136725 168856915109546293225159)
                    ·
                      rfl

theorem cell23_986543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 5, 2, 6].length) (baseStart_986543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_986543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_986543 prefixEnd_986543 := by exact prefixLift 986543
  have htrace : WordTrace (prefixWord ++ tailWord_986543) baseStart_986543 baseEnd_986543 := by
    simpa [prefixWord, tailWord_986543, baseEnd_986543] using wordTrace_append hprefix tailTrace_986543
  have hstable : (prefixWord ++ tailWord_986543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986543).length < 2 ^ (prefixWord ++ tailWord_986543).sum := by decide
  have hdescent : baseEnd_986543 < baseStart_986543 := by decide
  rcases family_descends (prefixWord ++ tailWord_986543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986567 : List Nat := [1, 1, 4, 1, 1, 3, 3, 2, 1, 4, 2]
def baseStart_986567 : Nat := 118140960795 + 986567 * 2 ^ 59
def prefixEnd_986567 : Nat := 4983230072969 + 3 ^ 40 * 986567 * 2
def baseEnd_986567 : Nat := 506583068864346785775367

theorem tailTrace_986567 : CollatzResearch.WordTrace tailWord_986567 prefixEnd_986567 506583068864346785775367 := by
  unfold tailWord_986567
  simp only [CollatzResearch.WordTrace]
  refine ⟨35983054616843726074357955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23988703077895817382905303 35983054616843726074357955)
  ·
    refine ⟨53974581925265589111536933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35983054616843726074357955 53974581925265589111536933)
    ·
      refine ⟨10120234110987297958413175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53974581925265589111536933 10120234110987297958413175)
      ·
        refine ⟨15180351166480946937619763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10120234110987297958413175 15180351166480946937619763)
        ·
          refine ⟨22770526749721420406429645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15180351166480946937619763 22770526749721420406429645)
          ·
            refine ⟨8538947531145532652411117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22770526749721420406429645 8538947531145532652411117)
            ·
              refine ⟨3202105324179574744654169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8538947531145532652411117 3202105324179574744654169)
              ·
                refine ⟨2401578993134681058490627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3202105324179574744654169 2401578993134681058490627)
                ·
                  refine ⟨3602368489702021587735941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2401578993134681058490627 3602368489702021587735941)
                  ·
                    refine ⟨675444091819129047700489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3602368489702021587735941 675444091819129047700489)
                    ·
                      refine ⟨506583068864346785775367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 675444091819129047700489 506583068864346785775367)
                      ·
                        rfl

theorem cell23_986567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 2, 1, 4, 2].length) (baseStart_986567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_986567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_986567 prefixEnd_986567 := by exact prefixLift 986567
  have htrace : WordTrace (prefixWord ++ tailWord_986567) baseStart_986567 baseEnd_986567 := by
    simpa [prefixWord, tailWord_986567, baseEnd_986567] using wordTrace_append hprefix tailTrace_986567
  have hstable : (prefixWord ++ tailWord_986567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986567).length < 2 ^ (prefixWord ++ tailWord_986567).sum := by decide
  have hdescent : baseEnd_986567 < baseStart_986567 := by decide
  rcases family_descends (prefixWord ++ tailWord_986567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986570 : List Nat := [3, 1, 2, 1, 2, 3, 2, 1, 2, 1, 5]
def baseStart_986570 : Nat := 118140960795 + 986570 * 2 ^ 59
def prefixEnd_986570 : Nat := 4983230072969 + 3 ^ 40 * 986570 * 2
def baseEnd_986570 : Nat := 506584609306310274037853

theorem tailTrace_986570 : CollatzResearch.WordTrace tailWord_986570 prefixEnd_986570 506584609306310274037853 := by
  unfold tailWord_986570
  simp only [CollatzResearch.WordTrace]
  refine ⟨8995791008958214396679291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23988776023888571724478109 8995791008958214396679291)
  ·
    refine ⟨13493686513437321595018937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8995791008958214396679291 13493686513437321595018937)
    ·
      refine ⟨10120264885077991196264203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13493686513437321595018937 10120264885077991196264203)
      ·
        refine ⟨15180397327616986794396305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10120264885077991196264203 15180397327616986794396305)
        ·
          refine ⟨11385297995712740095797229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15180397327616986794396305 11385297995712740095797229)
          ·
            refine ⟨4269486748392277535923961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11385297995712740095797229 4269486748392277535923961)
            ·
              refine ⟨3202115061294208151942971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4269486748392277535923961 3202115061294208151942971)
              ·
                refine ⟨4803172591941312227914457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3202115061294208151942971 4803172591941312227914457)
                ·
                  refine ⟨3602379443955984170935843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4803172591941312227914457 3602379443955984170935843)
                  ·
                    refine ⟨5403569165933976256403765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3602379443955984170935843 5403569165933976256403765)
                    ·
                      refine ⟨506584609306310274037853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5403569165933976256403765 506584609306310274037853)
                      ·
                        rfl

theorem cell23_986570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 1, 2, 1, 5].length) (baseStart_986570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_986570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_986570 prefixEnd_986570 := by exact prefixLift 986570
  have htrace : WordTrace (prefixWord ++ tailWord_986570) baseStart_986570 baseEnd_986570 := by
    simpa [prefixWord, tailWord_986570, baseEnd_986570] using wordTrace_append hprefix tailTrace_986570
  have hstable : (prefixWord ++ tailWord_986570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986570).length < 2 ^ (prefixWord ++ tailWord_986570).sum := by decide
  have hdescent : baseEnd_986570 < baseStart_986570 := by decide
  rcases family_descends (prefixWord ++ tailWord_986570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986583 : List Nat := [1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 7]
def baseStart_986583 : Nat := 118140960795 + 986583 * 2 ^ 59
def prefixEnd_986583 : Nat := 4983230072969 + 3 ^ 40 * 986583 * 2
def baseEnd_986583 : Nat := 506591284554818723175293

theorem tailTrace_986583 : CollatzResearch.WordTrace tailWord_986583 prefixEnd_986583 506591284554818723175293 := by
  unfold tailWord_986583
  simp only [CollatzResearch.WordTrace]
  refine ⟨35983638184785760806940403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23989092123190507204626935 35983638184785760806940403)
  ·
    refine ⟨53975457277178641210410605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35983638184785760806940403 53975457277178641210410605)
    ·
      refine ⟨20240796478941990453903977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53975457277178641210410605 20240796478941990453903977)
      ·
        refine ⟨15180597359206492840427983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20240796478941990453903977 15180597359206492840427983)
        ·
          refine ⟨22770896038809739260641975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15180597359206492840427983 22770896038809739260641975)
          ·
            refine ⟨34156344058214608890962963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22770896038809739260641975 34156344058214608890962963)
            ·
              refine ⟨51234516087321913336444445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34156344058214608890962963 51234516087321913336444445)
              ·
                refine ⟨19212943532745717501166667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51234516087321913336444445 19212943532745717501166667)
                ·
                  refine ⟨28819415299118576251750001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19212943532745717501166667 28819415299118576251750001)
                  ·
                    refine ⟨21614561474338932188812501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28819415299118576251750001 21614561474338932188812501)
                    ·
                      refine ⟨506591284554818723175293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 21614561474338932188812501 506591284554818723175293)
                      ·
                        rfl

theorem cell23_986583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 7].length) (baseStart_986583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_986583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_986583 prefixEnd_986583 := by exact prefixLift 986583
  have htrace : WordTrace (prefixWord ++ tailWord_986583) baseStart_986583 baseEnd_986583 := by
    simpa [prefixWord, tailWord_986583, baseEnd_986583] using wordTrace_append hprefix tailTrace_986583
  have hstable : (prefixWord ++ tailWord_986583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986583).length < 2 ^ (prefixWord ++ tailWord_986583).sum := by decide
  have hdescent : baseEnd_986583 < baseStart_986583 := by decide
  rcases family_descends (prefixWord ++ tailWord_986583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986584 : List Nat := [2, 1, 2, 2, 2, 1, 3, 4, 2, 2, 2]
def baseStart_986584 : Nat := 118140960795 + 986584 * 2 ^ 59
def prefixEnd_986584 : Nat := 4983230072969 + 3 ^ 40 * 986584 * 2
def baseEnd_986584 : Nat := 506591798035473219262789

theorem tailTrace_986584 : CollatzResearch.WordTrace tailWord_986584 prefixEnd_986584 506591798035473219262789 := by
  unfold tailWord_986584
  simp only [CollatzResearch.WordTrace]
  refine ⟨17991837328891068988863403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23989116438521425318484537 17991837328891068988863403)
  ·
    refine ⟨26987755993336603483295105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17991837328891068988863403 26987755993336603483295105)
    ·
      refine ⟨20240816995002452612471329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26987755993336603483295105 20240816995002452612471329)
      ·
        refine ⟨15180612746251839459353497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20240816995002452612471329 15180612746251839459353497)
        ·
          refine ⟨11385459559688879594515123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15180612746251839459353497 11385459559688879594515123)
          ·
            refine ⟨17078189339533319391772685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11385459559688879594515123 17078189339533319391772685)
            ·
              refine ⟨6404321002324994771914757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17078189339533319391772685 6404321002324994771914757)
              ·
                refine ⟨1200810187935936519734017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6404321002324994771914757 1200810187935936519734017)
                ·
                  refine ⟨900607640951952389800513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1200810187935936519734017 900607640951952389800513)
                  ·
                    refine ⟨675455730713964292350385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 900607640951952389800513 675455730713964292350385)
                    ·
                      refine ⟨506591798035473219262789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 675455730713964292350385 506591798035473219262789)
                      ·
                        rfl

theorem cell23_986584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 4, 2, 2, 2].length) (baseStart_986584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_986584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_986584 prefixEnd_986584 := by exact prefixLift 986584
  have htrace : WordTrace (prefixWord ++ tailWord_986584) baseStart_986584 baseEnd_986584 := by
    simpa [prefixWord, tailWord_986584, baseEnd_986584] using wordTrace_append hprefix tailTrace_986584
  have hstable : (prefixWord ++ tailWord_986584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986584).length < 2 ^ (prefixWord ++ tailWord_986584).sum := by decide
  have hdescent : baseEnd_986584 < baseStart_986584 := by decide
  rcases family_descends (prefixWord ++ tailWord_986584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986597 : List Nat := [1, 3, 1, 5, 1, 2, 1, 1, 2, 2, 4]
def baseStart_986597 : Nat := 118140960795 + 986597 * 2 ^ 59
def prefixEnd_986597 : Nat := 4983230072969 + 3 ^ 40 * 986597 * 2
def baseEnd_986597 : Nat := 506598473283981668400229

theorem tailTrace_986597 : CollatzResearch.WordTrace tailWord_986597 prefixEnd_986597 506598473283981668400229 := by
  unfold tailWord_986597
  simp only [CollatzResearch.WordTrace]
  refine ⟨35984148806735041197950045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23989432537823360798633363 35984148806735041197950045)
  ·
    refine ⟨13494055802525640449231267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35984148806735041197950045 13494055802525640449231267)
    ·
      refine ⟨20241083703788460673846901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13494055802525640449231267 20241083703788460673846901)
      ·
        refine ⟨1897601597230168188173147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20241083703788460673846901 1897601597230168188173147)
        ·
          refine ⟨2846402395845252282259721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1897601597230168188173147 2846402395845252282259721)
          ·
            refine ⟨2134801796883939211694791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2846402395845252282259721 2134801796883939211694791)
            ·
              refine ⟨3202202695325908817542187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2134801796883939211694791 3202202695325908817542187)
              ·
                refine ⟨4803304042988863226313281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3202202695325908817542187 4803304042988863226313281)
                ·
                  refine ⟨3602478032241647419734961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4803304042988863226313281 3602478032241647419734961)
                  ·
                    refine ⟨2701858524181235564801221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3602478032241647419734961 2701858524181235564801221)
                    ·
                      refine ⟨506598473283981668400229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2701858524181235564801221 506598473283981668400229)
                      ·
                        rfl

theorem cell23_986597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_986597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_986597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_986597 prefixEnd_986597 := by exact prefixLift 986597
  have htrace : WordTrace (prefixWord ++ tailWord_986597) baseStart_986597 baseEnd_986597 := by
    simpa [prefixWord, tailWord_986597, baseEnd_986597] using wordTrace_append hprefix tailTrace_986597
  have hstable : (prefixWord ++ tailWord_986597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986597).length < 2 ^ (prefixWord ++ tailWord_986597).sum := by decide
  have hdescent : baseEnd_986597 < baseStart_986597 := by decide
  rcases family_descends (prefixWord ++ tailWord_986597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986622 : List Nat := [4, 2, 2, 3, 2, 1, 2, 1, 1, 3, 2]
def baseStart_986622 : Nat := 118140960795 + 986622 * 2 ^ 59
def prefixEnd_986622 : Nat := 4983230072969 + 3 ^ 40 * 986622 * 2
def baseEnd_986622 : Nat := 506611310300344070587615

theorem tailTrace_986622 : CollatzResearch.WordTrace tailWord_986622 prefixEnd_986622 506611310300344070587615 := by
  unfold tailWord_986622
  simp only [CollatzResearch.WordTrace]
  refine ⟨4498132578955558808451265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23990040421096313645073413 4498132578955558808451265)
  ·
    refine ⟨3373599434216669106338449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4498132578955558808451265 3373599434216669106338449)
    ·
      refine ⟨2530199575662501829753837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3373599434216669106338449 2530199575662501829753837)
      ·
        refine ⟨948824840873438186157689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2530199575662501829753837 948824840873438186157689)
        ·
          refine ⟨711618630655078639618267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 948824840873438186157689 711618630655078639618267)
          ·
            refine ⟨1067427945982617959427401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 711618630655078639618267 1067427945982617959427401)
            ·
              refine ⟨800570959486963469570551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1067427945982617959427401 800570959486963469570551)
              ·
                refine ⟨1200856439230445204355827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 800570959486963469570551 1200856439230445204355827)
                ·
                  refine ⟨1801284658845667806533741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1200856439230445204355827 1801284658845667806533741)
                  ·
                    refine ⟨675481747067125427450153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1801284658845667806533741 675481747067125427450153)
                    ·
                      refine ⟨506611310300344070587615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 675481747067125427450153 506611310300344070587615)
                      ·
                        rfl

theorem cell23_986622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_986622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_986622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_986622 prefixEnd_986622 := by exact prefixLift 986622
  have htrace : WordTrace (prefixWord ++ tailWord_986622) baseStart_986622 baseEnd_986622 := by
    simpa [prefixWord, tailWord_986622, baseEnd_986622] using wordTrace_append hprefix tailTrace_986622
  have hstable : (prefixWord ++ tailWord_986622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986622).length < 2 ^ (prefixWord ++ tailWord_986622).sum := by decide
  have hdescent : baseEnd_986622 < baseStart_986622 := by decide
  rcases family_descends (prefixWord ++ tailWord_986622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986677 : List Nat := [1, 3, 3, 1, 1, 3, 2, 1, 1, 4, 3]
def baseStart_986677 : Nat := 118140960795 + 986677 * 2 ^ 59
def prefixEnd_986677 : Nat := 4983230072969 + 3 ^ 40 * 986677 * 2
def baseEnd_986677 : Nat := 506639551736341355399861

theorem tailTrace_986677 : CollatzResearch.WordTrace tailWord_986677 prefixEnd_986677 506639551736341355399861 := by
  unfold tailWord_986677
  simp only [CollatzResearch.WordTrace]
  refine ⟨35987066646445214860862285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23991377764296809907241523 35987066646445214860862285)
  ·
    refine ⟨13495149992416955572823357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35987066646445214860862285 13495149992416955572823357)
    ·
      refine ⟨5060681247156358339808759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13495149992416955572823357 5060681247156358339808759)
      ·
        refine ⟨7591021870734537509713139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5060681247156358339808759 7591021870734537509713139)
        ·
          refine ⟨11386532806101806264569709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7591021870734537509713139 11386532806101806264569709)
          ·
            refine ⟨4269949802288177349213641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11386532806101806264569709 4269949802288177349213641)
            ·
              refine ⟨3202462351716133011910231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4269949802288177349213641 3202462351716133011910231)
              ·
                refine ⟨4803693527574199517865347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3202462351716133011910231 4803693527574199517865347)
                ·
                  refine ⟨7205540291361299276798021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4803693527574199517865347 7205540291361299276798021)
                  ·
                    refine ⟨1351038804630243614399629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7205540291361299276798021 1351038804630243614399629)
                    ·
                      refine ⟨506639551736341355399861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1351038804630243614399629 506639551736341355399861)
                      ·
                        rfl

theorem cell23_986677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 1, 1, 4, 3].length) (baseStart_986677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_986677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_986677 prefixEnd_986677 := by exact prefixLift 986677
  have htrace : WordTrace (prefixWord ++ tailWord_986677) baseStart_986677 baseEnd_986677 := by
    simpa [prefixWord, tailWord_986677, baseEnd_986677] using wordTrace_append hprefix tailTrace_986677
  have hstable : (prefixWord ++ tailWord_986677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986677).length < 2 ^ (prefixWord ++ tailWord_986677).sum := by decide
  have hdescent : baseEnd_986677 < baseStart_986677 := by decide
  rcases family_descends (prefixWord ++ tailWord_986677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986680 : List Nat := [2, 1, 2, 1, 4, 2, 1, 2, 8]
def baseStart_986680 : Nat := 118140960795 + 986680 * 2 ^ 59
def prefixEnd_986680 : Nat := 4983230072969 + 3 ^ 40 * 986680 * 2
def baseEnd_986680 : Nat := 56293454686478315962483

theorem tailTrace_986680 : CollatzResearch.WordTrace tailWord_986680 prefixEnd_986680 56293454686478315962483 := by
  unfold tailWord_986680
  simp only [CollatzResearch.WordTrace]
  refine ⟨17993588032717173186610747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23991450710289564248814329 17993588032717173186610747)
  ·
    refine ⟨26990382049075759779916121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17993588032717173186610747 26990382049075759779916121)
    ·
      refine ⟨20242786536806819834937091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26990382049075759779916121 20242786536806819834937091)
      ·
        refine ⟨30364179805210229752405637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20242786536806819834937091 30364179805210229752405637)
        ·
          refine ⟨5693283713476918078576057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30364179805210229752405637 5693283713476918078576057)
          ·
            refine ⟨4269962785107688558932043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5693283713476918078576057 4269962785107688558932043)
            ·
              refine ⟨6404944177661532838398065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4269962785107688558932043 6404944177661532838398065)
              ·
                refine ⟨4803708133246149628798549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6404944177661532838398065 4803708133246149628798549)
                ·
                  refine ⟨56293454686478315962483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4803708133246149628798549 56293454686478315962483)
                  ·
                    rfl

theorem cell23_986680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 2, 8].length) (baseStart_986680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_986680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_986680 prefixEnd_986680 := by exact prefixLift 986680
  have htrace : WordTrace (prefixWord ++ tailWord_986680) baseStart_986680 baseEnd_986680 := by
    simpa [prefixWord, tailWord_986680, baseEnd_986680] using wordTrace_append hprefix tailTrace_986680
  have hstable : (prefixWord ++ tailWord_986680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986680).length < 2 ^ (prefixWord ++ tailWord_986680).sum := by decide
  have hdescent : baseEnd_986680 < baseStart_986680 := by decide
  rcases family_descends (prefixWord ++ tailWord_986680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986707 : List Nat := [1, 1, 1, 2, 1, 1, 2, 1, 9, 1, 3]
def baseStart_986707 : Nat := 118140960795 + 986707 * 2 ^ 59
def prefixEnd_986707 : Nat := 4983230072969 + 3 ^ 40 * 986707 * 2
def baseEnd_986707 : Nat := 506654956155976238024723

theorem tailTrace_986707 : CollatzResearch.WordTrace tailWord_986707 prefixEnd_986707 506654956155976238024723 := by
  unfold tailWord_986707
  simp only [CollatzResearch.WordTrace]
  refine ⟨35988160836336529984454375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23992107224224353322969583 35988160836336529984454375)
  ·
    refine ⟨53982241254504794976681563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35988160836336529984454375 53982241254504794976681563)
    ·
      refine ⟨80973361881757192465022345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53982241254504794976681563 80973361881757192465022345)
      ·
        refine ⟨60730021411317894348766759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80973361881757192465022345 60730021411317894348766759)
        ·
          refine ⟨91095032116976841523150139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60730021411317894348766759 91095032116976841523150139)
          ·
            refine ⟨136642548175465262284725209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91095032116976841523150139 136642548175465262284725209)
            ·
              refine ⟨102481911131598946713543907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136642548175465262284725209 102481911131598946713543907)
              ·
                refine ⟨153722866697398420070315861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102481911131598946713543907 153722866697398420070315861)
                ·
                  refine ⟨900719922055068867599507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 153722866697398420070315861 900719922055068867599507)
                  ·
                    refine ⟨1351079883082603301399261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 900719922055068867599507 1351079883082603301399261)
                    ·
                      refine ⟨506654956155976238024723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1351079883082603301399261 506654956155976238024723)
                      ·
                        rfl

theorem cell23_986707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 9, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 9, 1, 3].length) (baseStart_986707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_986707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_986707 prefixEnd_986707 := by exact prefixLift 986707
  have htrace : WordTrace (prefixWord ++ tailWord_986707) baseStart_986707 baseEnd_986707 := by
    simpa [prefixWord, tailWord_986707, baseEnd_986707] using wordTrace_append hprefix tailTrace_986707
  have hstable : (prefixWord ++ tailWord_986707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986707).length < 2 ^ (prefixWord ++ tailWord_986707).sum := by decide
  have hdescent : baseEnd_986707 < baseStart_986707 := by decide
  rcases family_descends (prefixWord ++ tailWord_986707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986784 : List Nat := [2, 1, 1, 4, 3, 1, 2, 1, 3, 2, 3]
def baseStart_986784 : Nat := 118140960795 + 986784 * 2 ^ 59
def prefixEnd_986784 : Nat := 4983230072969 + 3 ^ 40 * 986784 * 2
def baseEnd_986784 : Nat := 506694494166372436761869

theorem tailTrace_986784 : CollatzResearch.WordTrace tailWord_986784 prefixEnd_986784 506694494166372436761869 := by
  unfold tailWord_986784
  simp only [CollatzResearch.WordTrace]
  refine ⟨17995484628528786067503703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23993979504705048090004937 17995484628528786067503703)
  ·
    refine ⟨26993226942793179101255555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17995484628528786067503703 26993226942793179101255555)
    ·
      refine ⟨40489840414189768651883333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26993226942793179101255555 40489840414189768651883333)
      ·
        refine ⟨7591845077660581622228125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40489840414189768651883333 7591845077660581622228125)
        ·
          refine ⟨2846941904122718108335547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7591845077660581622228125 2846941904122718108335547)
          ·
            refine ⟨4270412856184077162503321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2846941904122718108335547 4270412856184077162503321)
            ·
              refine ⟨3202809642138057871877491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4270412856184077162503321 3202809642138057871877491)
              ·
                refine ⟨4804214463207086807816237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3202809642138057871877491 4804214463207086807816237)
                ·
                  refine ⟨1801580423702657552931089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4804214463207086807816237 1801580423702657552931089)
                  ·
                    refine ⟨1351185317776993164698317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1801580423702657552931089 1351185317776993164698317)
                    ·
                      refine ⟨506694494166372436761869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1351185317776993164698317 506694494166372436761869)
                      ·
                        rfl

theorem cell23_986784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 1, 3, 2, 3].length) (baseStart_986784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_986784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_986784 prefixEnd_986784 := by exact prefixLift 986784
  have htrace : WordTrace (prefixWord ++ tailWord_986784) baseStart_986784 baseEnd_986784 := by
    simpa [prefixWord, tailWord_986784, baseEnd_986784] using wordTrace_append hprefix tailTrace_986784
  have hstable : (prefixWord ++ tailWord_986784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986784).length < 2 ^ (prefixWord ++ tailWord_986784).sum := by decide
  have hdescent : baseEnd_986784 < baseStart_986784 := by decide
  rcases family_descends (prefixWord ++ tailWord_986784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986787 : List Nat := [1, 1, 1, 4, 1, 1, 7, 7]
def baseStart_986787 : Nat := 118140960795 + 986787 * 2 ^ 59
def prefixEnd_986787 : Nat := 4983230072969 + 3 ^ 40 * 986787 * 2
def baseEnd_986787 : Nat := 18766519800308737963865

theorem tailTrace_986787 : CollatzResearch.WordTrace tailWord_986787 prefixEnd_986787 18766519800308737963865 := by
  unfold tailWord_986787
  simp only [CollatzResearch.WordTrace]
  refine ⟨35991078676046703647366615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23994052450697802431577743 35991078676046703647366615)
  ·
    refine ⟨53986618014070055471049923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35991078676046703647366615 53986618014070055471049923)
    ·
      refine ⟨80979927021105083206574885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53986618014070055471049923 80979927021105083206574885)
      ·
        refine ⟨15183736316457203101232791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80979927021105083206574885 15183736316457203101232791)
        ·
          refine ⟨22775604474685804651849187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15183736316457203101232791 22775604474685804651849187)
          ·
            refine ⟨34163406712028706977773781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22775604474685804651849187 34163406712028706977773781)
            ·
              refine ⟨800704844813172819791573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 34163406712028706977773781 800704844813172819791573)
              ·
                refine ⟨18766519800308737963865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 800704844813172819791573 18766519800308737963865)
                ·
                  rfl

theorem cell23_986787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 7, 7].length) (baseStart_986787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_986787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_986787 prefixEnd_986787 := by exact prefixLift 986787
  have htrace : WordTrace (prefixWord ++ tailWord_986787) baseStart_986787 baseEnd_986787 := by
    simpa [prefixWord, tailWord_986787, baseEnd_986787] using wordTrace_append hprefix tailTrace_986787
  have hstable : (prefixWord ++ tailWord_986787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986787).length < 2 ^ (prefixWord ++ tailWord_986787).sum := by decide
  have hdescent : baseEnd_986787 < baseStart_986787 := by decide
  rcases family_descends (prefixWord ++ tailWord_986787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986798 : List Nat := [4, 1, 4, 1, 2, 1, 1, 3, 1, 1, 4]
def baseStart_986798 : Nat := 118140960795 + 986798 * 2 ^ 59
def prefixEnd_986798 : Nat := 4983230072969 + 3 ^ 40 * 986798 * 2
def baseEnd_986798 : Nat := 506701682895535381986805

theorem tailTrace_986798 : CollatzResearch.WordTrace tailWord_986798 prefixEnd_986798 506701682895535381986805 := by
  unfold tailWord_986798
  simp only [CollatzResearch.WordTrace]
  refine ⟨4498934984875856565752131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23994319919337901684011365 4498934984875856565752131)
  ·
    refine ⟨6748402477313784848628197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4498934984875856565752131 6748402477313784848628197)
    ·
      refine ⟨1265325464496334659117787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6748402477313784848628197 1265325464496334659117787)
      ·
        refine ⟨1897988196744501988676681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1265325464496334659117787 1897988196744501988676681)
        ·
          refine ⟨1423491147558376491507511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1897988196744501988676681 1423491147558376491507511)
          ·
            refine ⟨2135236721337564737261267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1423491147558376491507511 2135236721337564737261267)
            ·
              refine ⟨3202855082006347105891901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2135236721337564737261267 3202855082006347105891901)
              ·
                refine ⟨1201070655752380164709463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3202855082006347105891901 1201070655752380164709463)
                ·
                  refine ⟨1801605983628570247064195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1201070655752380164709463 1801605983628570247064195)
                  ·
                    refine ⟨2702408975442855370596293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1801605983628570247064195 2702408975442855370596293)
                    ·
                      refine ⟨506701682895535381986805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2702408975442855370596293 506701682895535381986805)
                      ·
                        rfl

theorem cell23_986798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_986798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_986798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_986798 prefixEnd_986798 := by exact prefixLift 986798
  have htrace : WordTrace (prefixWord ++ tailWord_986798) baseStart_986798 baseEnd_986798 := by
    simpa [prefixWord, tailWord_986798, baseEnd_986798] using wordTrace_append hprefix tailTrace_986798
  have hstable : (prefixWord ++ tailWord_986798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986798).length < 2 ^ (prefixWord ++ tailWord_986798).sum := by decide
  have hdescent : baseEnd_986798 < baseStart_986798 := by decide
  rcases family_descends (prefixWord ++ tailWord_986798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986828 : List Nat := [2, 2, 1, 5, 3, 1, 1, 1, 1, 2, 4]
def baseStart_986828 : Nat := 118140960795 + 986828 * 2 ^ 59
def prefixEnd_986828 : Nat := 4983230072969 + 3 ^ 40 * 986828 * 2
def baseEnd_986828 : Nat := 506717087315170264611667

theorem tailTrace_986828 : CollatzResearch.WordTrace tailWord_986828 prefixEnd_986828 506717087315170264611667 := by
  unfold tailWord_986828
  simp only [CollatzResearch.WordTrace]
  refine ⟨17996287034449083824804569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23995049379265445099739425 17996287034449083824804569)
  ·
    refine ⟨13497215275836812868603427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17996287034449083824804569 13497215275836812868603427)
    ·
      refine ⟨20245822913755219302905141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13497215275836812868603427 20245822913755219302905141)
      ·
        refine ⟨1898045898164551809647357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20245822913755219302905141 1898045898164551809647357)
        ·
          refine ⟨711767211811706928617759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1898045898164551809647357 711767211811706928617759)
          ·
            refine ⟨1067650817717560392926639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 711767211811706928617759 1067650817717560392926639)
            ·
              refine ⟨1601476226576340589389959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1067650817717560392926639 1601476226576340589389959)
              ·
                refine ⟨2402214339864510884084939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1601476226576340589389959 2402214339864510884084939)
                ·
                  refine ⟨3603321509796766326127409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2402214339864510884084939 3603321509796766326127409)
                  ·
                    refine ⟨2702491132347574744595557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3603321509796766326127409 2702491132347574744595557)
                    ·
                      refine ⟨506717087315170264611667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2702491132347574744595557 506717087315170264611667)
                      ·
                        rfl

theorem cell23_986828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_986828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_986828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_986828 prefixEnd_986828 := by exact prefixLift 986828
  have htrace : WordTrace (prefixWord ++ tailWord_986828) baseStart_986828 baseEnd_986828 := by
    simpa [prefixWord, tailWord_986828, baseEnd_986828] using wordTrace_append hprefix tailTrace_986828
  have hstable : (prefixWord ++ tailWord_986828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986828).length < 2 ^ (prefixWord ++ tailWord_986828).sum := by decide
  have hdescent : baseEnd_986828 < baseStart_986828 := by decide
  rcases family_descends (prefixWord ++ tailWord_986828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986841 : List Nat := [1, 2, 1, 2, 3, 3, 1, 4, 1, 3, 2]
def baseStart_986841 : Nat := 118140960795 + 986841 * 2 ^ 59
def prefixEnd_986841 : Nat := 4983230072969 + 3 ^ 40 * 986841 * 2
def baseEnd_986841 : Nat := 506723762563678713749107

theorem tailTrace_986841 : CollatzResearch.WordTrace tailWord_986841 prefixEnd_986841 506723762563678713749107 := by
  unfold tailWord_986841
  simp only [CollatzResearch.WordTrace]
  refine ⟨35993048217851070869832377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23995365478567380579888251 35993048217851070869832377)
  ·
    refine ⟨26994786163388303152374283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35993048217851070869832377 26994786163388303152374283)
    ·
      refine ⟨40492179245082454728561425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26994786163388303152374283 40492179245082454728561425)
      ·
        refine ⟨30369134433811841046421069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40492179245082454728561425 30369134433811841046421069)
        ·
          refine ⟨11388425412679440392407901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30369134433811841046421069 11388425412679440392407901)
          ·
            refine ⟨4270659529754790147152963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11388425412679440392407901 4270659529754790147152963)
            ·
              refine ⟨6405989294632185220729445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4270659529754790147152963 6405989294632185220729445)
              ·
                refine ⟨1201122992743534728886771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6405989294632185220729445 1201122992743534728886771)
                ·
                  refine ⟨1801684489115302093330157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1201122992743534728886771 1801684489115302093330157)
                  ·
                    refine ⟨675631683418238284998809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1801684489115302093330157 675631683418238284998809)
                    ·
                      refine ⟨506723762563678713749107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 675631683418238284998809 506723762563678713749107)
                      ·
                        rfl

theorem cell23_986841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 4, 1, 3, 2].length) (baseStart_986841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_986841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_986841 prefixEnd_986841 := by exact prefixLift 986841
  have htrace : WordTrace (prefixWord ++ tailWord_986841) baseStart_986841 baseEnd_986841 := by
    simpa [prefixWord, tailWord_986841, baseEnd_986841] using wordTrace_append hprefix tailTrace_986841
  have hstable : (prefixWord ++ tailWord_986841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986841).length < 2 ^ (prefixWord ++ tailWord_986841).sum := by decide
  have hdescent : baseEnd_986841 < baseStart_986841 := by decide
  rcases family_descends (prefixWord ++ tailWord_986841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986857 : List Nat := [1, 2, 1, 1, 1, 2, 3, 2, 1, 6, 3]
def baseStart_986857 : Nat := 118140960795 + 986857 * 2 ^ 59
def prefixEnd_986857 : Nat := 4983230072969 + 3 ^ 40 * 986857 * 2
def baseEnd_986857 : Nat := 506731978254150651149033

theorem tailTrace_986857 : CollatzResearch.WordTrace tailWord_986857 prefixEnd_986857 506731978254150651149033 := by
  unfold tailWord_986857
  simp only [CollatzResearch.WordTrace]
  refine ⟨35993631785793105602414825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23995754523862070401609883 35993631785793105602414825)
  ·
    refine ⟨26995223839344829201811119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35993631785793105602414825 26995223839344829201811119)
    ·
      refine ⟨40492835759017243802716679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26995223839344829201811119 40492835759017243802716679)
      ·
        refine ⟨60739253638525865704075019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40492835759017243802716679 60739253638525865704075019)
        ·
          refine ⟨91108880457788798556112529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60739253638525865704075019 91108880457788798556112529)
          ·
            refine ⟨68331660343341598917084397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91108880457788798556112529 68331660343341598917084397)
            ·
              refine ⟨25624372628753099593906649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68331660343341598917084397 25624372628753099593906649)
              ·
                refine ⟨19218279471564824695429987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25624372628753099593906649 19218279471564824695429987)
                ·
                  refine ⟨28827419207347237043144981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19218279471564824695429987 28827419207347237043144981)
                  ·
                    refine ⟨1351285275344401736397421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28827419207347237043144981 1351285275344401736397421)
                    ·
                      refine ⟨506731978254150651149033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1351285275344401736397421 506731978254150651149033)
                      ·
                        rfl

theorem cell23_986857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 6, 3].length) (baseStart_986857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_986857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_986857 prefixEnd_986857 := by exact prefixLift 986857
  have htrace : WordTrace (prefixWord ++ tailWord_986857) baseStart_986857 baseEnd_986857 := by
    simpa [prefixWord, tailWord_986857, baseEnd_986857] using wordTrace_append hprefix tailTrace_986857
  have hstable : (prefixWord ++ tailWord_986857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986857).length < 2 ^ (prefixWord ++ tailWord_986857).sum := by decide
  have hdescent : baseEnd_986857 < baseStart_986857 := by decide
  rcases family_descends (prefixWord ++ tailWord_986857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986867 : List Nat := [1, 1, 1, 2, 2, 3, 2, 1, 4, 2, 4]
def baseStart_986867 : Nat := 118140960795 + 986867 * 2 ^ 59
def prefixEnd_986867 : Nat := 4983230072969 + 3 ^ 40 * 986867 * 2
def baseEnd_986867 : Nat := 506737113060695612023987

theorem tailTrace_986867 : CollatzResearch.WordTrace tailWord_986867 prefixEnd_986867 506737113060695612023987 := by
  unfold tailWord_986867
  simp only [CollatzResearch.WordTrace]
  refine ⟨35993996515756877310278855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23995997677171251540185903 35993996515756877310278855)
  ·
    refine ⟨53990994773635315965418283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35993996515756877310278855 53990994773635315965418283)
    ·
      refine ⟨80986492160452973948127425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53990994773635315965418283 80986492160452973948127425)
      ·
        refine ⟨60739869120339730461095569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80986492160452973948127425 60739869120339730461095569)
        ·
          refine ⟨45554901840254797845821677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60739869120339730461095569 45554901840254797845821677)
          ·
            refine ⟨17083088190095549192183129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45554901840254797845821677 17083088190095549192183129)
            ·
              refine ⟨12812316142571661894137347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17083088190095549192183129 12812316142571661894137347)
              ·
                refine ⟨19218474213857492841206021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12812316142571661894137347 19218474213857492841206021)
                ·
                  refine ⟨3603463915098279907726129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19218474213857492841206021 3603463915098279907726129)
                  ·
                    refine ⟨2702597936323709930794597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3603463915098279907726129 2702597936323709930794597)
                    ·
                      refine ⟨506737113060695612023987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2702597936323709930794597 506737113060695612023987)
                      ·
                        rfl

theorem cell23_986867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 4, 2, 4].length) (baseStart_986867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_986867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_986867 prefixEnd_986867 := by exact prefixLift 986867
  have htrace : WordTrace (prefixWord ++ tailWord_986867) baseStart_986867 baseEnd_986867 := by
    simpa [prefixWord, tailWord_986867, baseEnd_986867] using wordTrace_append hprefix tailTrace_986867
  have hstable : (prefixWord ++ tailWord_986867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986867).length < 2 ^ (prefixWord ++ tailWord_986867).sum := by decide
  have hdescent : baseEnd_986867 < baseStart_986867 := by decide
  rcases family_descends (prefixWord ++ tailWord_986867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986871 : List Nat := [1, 1, 3, 1, 1, 1, 6, 1, 4, 2, 2]
def baseStart_986871 : Nat := 118140960795 + 986871 * 2 ^ 59
def prefixEnd_986871 : Nat := 4983230072969 + 3 ^ 40 * 986871 * 2
def baseEnd_986871 : Nat := 506739166983313596373969

theorem tailTrace_986871 : CollatzResearch.WordTrace tailWord_986871 prefixEnd_986871 506739166983313596373969 := by
  unfold tailWord_986871
  simp only [CollatzResearch.WordTrace]
  refine ⟨35994142407742385993424467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23996094938494923995616311 35994142407742385993424467)
  ·
    refine ⟨53991213611613578990136701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35994142407742385993424467 53991213611613578990136701)
    ·
      refine ⟨20246705104355092121301263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53991213611613578990136701 20246705104355092121301263)
      ·
        refine ⟨30370057656532638181951895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20246705104355092121301263 30370057656532638181951895)
        ·
          refine ⟨45555086484798957272927843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30370057656532638181951895 45555086484798957272927843)
          ·
            refine ⟨68332629727198435909391765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45555086484798957272927843 68332629727198435909391765)
            ·
              refine ⟨3203092018462426683252739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 68332629727198435909391765 3203092018462426683252739)
              ·
                refine ⟨4804638027693640024879109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3203092018462426683252739 4804638027693640024879109)
                ·
                  refine ⟨900869630192557504664833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4804638027693640024879109 900869630192557504664833)
                  ·
                    refine ⟨675652222644418128498625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 900869630192557504664833 675652222644418128498625)
                    ·
                      refine ⟨506739166983313596373969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 675652222644418128498625 506739166983313596373969)
                      ·
                        rfl

theorem cell23_986871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 1, 4, 2, 2].length) (baseStart_986871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_986871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_986871 prefixEnd_986871 := by exact prefixLift 986871
  have htrace : WordTrace (prefixWord ++ tailWord_986871) baseStart_986871 baseEnd_986871 := by
    simpa [prefixWord, tailWord_986871, baseEnd_986871] using wordTrace_append hprefix tailTrace_986871
  have hstable : (prefixWord ++ tailWord_986871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986871).length < 2 ^ (prefixWord ++ tailWord_986871).sum := by decide
  have hdescent : baseEnd_986871 < baseStart_986871 := by decide
  rcases family_descends (prefixWord ++ tailWord_986871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986877 : List Nat := [1, 4, 1, 1, 1, 1, 2, 5, 7]
def baseStart_986877 : Nat := 118140960795 + 986877 * 2 ^ 59
def prefixEnd_986877 : Nat := 4983230072969 + 3 ^ 40 * 986877 * 2
def baseEnd_986877 : Nat := 56304694207471174766549

theorem tailTrace_986877 : CollatzResearch.WordTrace tailWord_986877 prefixEnd_986877 56304694207471174766549 := by
  unfold tailWord_986877
  simp only [CollatzResearch.WordTrace]
  refine ⟨35994361245720649018142885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23996240830480432678761923 35994361245720649018142885)
  ·
    refine ⟨6748942733572621690901791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35994361245720649018142885 6748942733572621690901791)
    ·
      refine ⟨10123414100358932536352687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6748942733572621690901791 10123414100358932536352687)
      ·
        refine ⟨15185121150538398804529031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10123414100358932536352687 15185121150538398804529031)
        ·
          refine ⟨22777681725807598206793547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15185121150538398804529031 22777681725807598206793547)
          ·
            refine ⟨34166522588711397310190321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22777681725807598206793547 34166522588711397310190321)
            ·
              refine ⟨25624891941533547982642741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34166522588711397310190321 25624891941533547982642741)
              ·
                refine ⟨2402333619518770123372757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25624891941533547982642741 2402333619518770123372757)
                ·
                  refine ⟨56304694207471174766549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2402333619518770123372757 56304694207471174766549)
                  ·
                    rfl

theorem cell23_986877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 5, 7].length) (baseStart_986877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_986877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_986877 prefixEnd_986877 := by exact prefixLift 986877
  have htrace : WordTrace (prefixWord ++ tailWord_986877) baseStart_986877 baseEnd_986877 := by
    simpa [prefixWord, tailWord_986877, baseEnd_986877] using wordTrace_append hprefix tailTrace_986877
  have hstable : (prefixWord ++ tailWord_986877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986877).length < 2 ^ (prefixWord ++ tailWord_986877).sum := by decide
  have hdescent : baseEnd_986877 < baseStart_986877 := by decide
  rcases family_descends (prefixWord ++ tailWord_986877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986886 : List Nat := [6, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3]
def baseStart_986886 : Nat := 118140960795 + 986886 * 2 ^ 59
def prefixEnd_986886 : Nat := 4983230072969 + 3 ^ 40 * 986886 * 2
def baseEnd_986886 : Nat := 506746869193131037686401

theorem tailTrace_986886 : CollatzResearch.WordTrace tailWord_986886 prefixEnd_986886 506746869193131037686401 := by
  unfold tailWord_986886
  simp only [CollatzResearch.WordTrace]
  refine ⟨1124834046959001361100641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 23996459668458695703480341 1124834046959001361100641)
  ·
    refine ⟨843625535219251020825481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1124834046959001361100641 843625535219251020825481)
    ·
      refine ⟨632719151414438265619111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 843625535219251020825481 632719151414438265619111)
      ·
        refine ⟨949078727121657398428667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 632719151414438265619111 949078727121657398428667)
        ·
          refine ⟨1423618090682486097643001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 949078727121657398428667 1423618090682486097643001)
          ·
            refine ⟨1067713568011864573232251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1423618090682486097643001 1067713568011864573232251)
            ·
              refine ⟨1601570352017796859848377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1067713568011864573232251 1601570352017796859848377)
              ·
                refine ⟨1201177764013347644886283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1601570352017796859848377 1201177764013347644886283)
                ·
                  refine ⟨1801766646020021467329425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1201177764013347644886283 1801766646020021467329425)
                  ·
                    refine ⟨1351324984515016100497069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1801766646020021467329425 1351324984515016100497069)
                    ·
                      refine ⟨506746869193131037686401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1351324984515016100497069 506746869193131037686401)
                      ·
                        rfl

theorem cell23_986886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_986886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_986886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_986886 prefixEnd_986886 := by exact prefixLift 986886
  have htrace : WordTrace (prefixWord ++ tailWord_986886) baseStart_986886 baseEnd_986886 := by
    simpa [prefixWord, tailWord_986886, baseEnd_986886] using wordTrace_append hprefix tailTrace_986886
  have hstable : (prefixWord ++ tailWord_986886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986886).length < 2 ^ (prefixWord ++ tailWord_986886).sum := by decide
  have hdescent : baseEnd_986886 < baseStart_986886 := by decide
  rcases family_descends (prefixWord ++ tailWord_986886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986888 : List Nat := [2, 1, 3, 2, 2, 1, 3, 3, 2, 2, 2]
def baseStart_986888 : Nat := 118140960795 + 986888 * 2 ^ 59
def prefixEnd_986888 : Nat := 4983230072969 + 3 ^ 40 * 986888 * 2
def baseEnd_986888 : Nat := 506747896154440029861391

theorem tailTrace_986888 : CollatzResearch.WordTrace tailWord_986888 prefixEnd_986888 506747896154440029861391 := by
  unfold tailWord_986888
  simp only [CollatzResearch.WordTrace]
  refine ⟨17997381224340398948396659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23996508299120531931195545 17997381224340398948396659)
  ·
    refine ⟨26996071836510598422594989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17997381224340398948396659 26996071836510598422594989)
    ·
      refine ⟨10123526938691474408473121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26996071836510598422594989 10123526938691474408473121)
      ·
        refine ⟨7592645204018605806354841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10123526938691474408473121 7592645204018605806354841)
        ·
          refine ⟨5694483903013954354766131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7592645204018605806354841 5694483903013954354766131)
          ·
            refine ⟨8541725854520931532149197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5694483903013954354766131 8541725854520931532149197)
            ·
              refine ⟨3203147195445349324555949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8541725854520931532149197 3203147195445349324555949)
              ·
                refine ⟨1201180198292005996708481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3203147195445349324555949 1201180198292005996708481)
                ·
                  refine ⟨900885148719004497531361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1201180198292005996708481 900885148719004497531361)
                  ·
                    refine ⟨675663861539253373148521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 900885148719004497531361 675663861539253373148521)
                    ·
                      refine ⟨506747896154440029861391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 675663861539253373148521 506747896154440029861391)
                      ·
                        rfl

theorem cell23_986888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 3, 2, 2, 2].length) (baseStart_986888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_986888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_986888 prefixEnd_986888 := by exact prefixLift 986888
  have htrace : WordTrace (prefixWord ++ tailWord_986888) baseStart_986888 baseEnd_986888 := by
    simpa [prefixWord, tailWord_986888, baseEnd_986888] using wordTrace_append hprefix tailTrace_986888
  have hstable : (prefixWord ++ tailWord_986888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986888).length < 2 ^ (prefixWord ++ tailWord_986888).sum := by decide
  have hdescent : baseEnd_986888 < baseStart_986888 := by decide
  rcases family_descends (prefixWord ++ tailWord_986888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986907 : List Nat := [1, 1, 1, 1, 1, 1, 4, 2, 6, 5]
def baseStart_986907 : Nat := 118140960795 + 986907 * 2 ^ 59
def prefixEnd_986907 : Nat := 4983230072969 + 3 ^ 40 * 986907 * 2
def baseEnd_986907 : Nat := 168919217428958485174601

theorem tailTrace_986907 : CollatzResearch.WordTrace tailWord_986907 prefixEnd_986907 168919217428958485174601 := by
  unfold tailWord_986907
  simp only [CollatzResearch.WordTrace]
  refine ⟨35995455435611964141734975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23996970290407976094489983 35995455435611964141734975)
  ·
    refine ⟨53993183153417946212602463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35995455435611964141734975 53993183153417946212602463)
    ·
      refine ⟨80989774730126919318903695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53993183153417946212602463 80989774730126919318903695)
      ·
        refine ⟨121484662095190378978355543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80989774730126919318903695 121484662095190378978355543)
        ·
          refine ⟨182226993142785568467533315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121484662095190378978355543 182226993142785568467533315)
          ·
            refine ⟨273340489714178352701299973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182226993142785568467533315 273340489714178352701299973)
            ·
              refine ⟨51251341821408441131493745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 273340489714178352701299973 51251341821408441131493745)
              ·
                refine ⟨38438506366056330848620309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51251341821408441131493745 38438506366056330848620309)
                ·
                  refine ⟨1801804985908890508529077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 38438506366056330848620309 1801804985908890508529077)
                  ·
                    refine ⟨168919217428958485174601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1801804985908890508529077 168919217428958485174601)
                    ·
                      rfl

theorem cell23_986907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 6, 5].length) (baseStart_986907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_986907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_986907 prefixEnd_986907 := by exact prefixLift 986907
  have htrace : WordTrace (prefixWord ++ tailWord_986907) baseStart_986907 baseEnd_986907 := by
    simpa [prefixWord, tailWord_986907, baseEnd_986907] using wordTrace_append hprefix tailTrace_986907
  have hstable : (prefixWord ++ tailWord_986907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986907).length < 2 ^ (prefixWord ++ tailWord_986907).sum := by decide
  have hdescent : baseEnd_986907 < baseStart_986907 := by decide
  rcases family_descends (prefixWord ++ tailWord_986907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986924 : List Nat := [2, 2, 1, 1, 1, 5, 2, 2, 2, 5]
def baseStart_986924 : Nat := 118140960795 + 986924 * 2 ^ 59
def prefixEnd_986924 : Nat := 4983230072969 + 3 ^ 40 * 986924 * 2
def baseEnd_986924 : Nat := 168922127152667296337075

theorem tailTrace_986924 : CollatzResearch.WordTrace tailWord_986924 prefixEnd_986924 168922127152667296337075 := by
  unfold tailWord_986924
  simp only [CollatzResearch.WordTrace]
  refine ⟨17998037738275188022551913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23997383651033584030069217 17998037738275188022551913)
  ·
    refine ⟨13498528303706391016913935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17998037738275188022551913 13498528303706391016913935)
    ·
      refine ⟨20247792455559586525370903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13498528303706391016913935 20247792455559586525370903)
      ·
        refine ⟨30371688683339379788056355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20247792455559586525370903 30371688683339379788056355)
        ·
          refine ⟨45557533025009069682084533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30371688683339379788056355 45557533025009069682084533)
          ·
            refine ⟨4271018721094600282695425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45557533025009069682084533 4271018721094600282695425)
            ·
              refine ⟨3203264040820950212021569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4271018721094600282695425 3203264040820950212021569)
              ·
                refine ⟨2402448030615712659016177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3203264040820950212021569 2402448030615712659016177)
                ·
                  refine ⟨1801836022961784494262133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2402448030615712659016177 1801836022961784494262133)
                  ·
                    refine ⟨168922127152667296337075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1801836022961784494262133 168922127152667296337075)
                    ·
                      rfl

theorem cell23_986924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 5].length) (baseStart_986924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_986924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_986924 prefixEnd_986924 := by exact prefixLift 986924
  have htrace : WordTrace (prefixWord ++ tailWord_986924) baseStart_986924 baseEnd_986924 := by
    simpa [prefixWord, tailWord_986924, baseEnd_986924] using wordTrace_append hprefix tailTrace_986924
  have hstable : (prefixWord ++ tailWord_986924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986924).length < 2 ^ (prefixWord ++ tailWord_986924).sum := by decide
  have hdescent : baseEnd_986924 < baseStart_986924 := by decide
  rcases family_descends (prefixWord ++ tailWord_986924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986961 : List Nat := [1, 2, 2, 1, 5, 1, 3, 1, 2, 1, 4]
def baseStart_986961 : Nat := 118140960795 + 986961 * 2 ^ 59
def prefixEnd_986961 : Nat := 4983230072969 + 3 ^ 40 * 986961 * 2
def baseEnd_986961 : Nat := 506785380242218244248555

theorem tailTrace_986961 : CollatzResearch.WordTrace tailWord_986961 prefixEnd_986961 506785380242218244248555 := by
  unfold tailWord_986961
  simp only [CollatzResearch.WordTrace]
  refine ⟨35997424977416331364200737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23998283318277554242800491 35997424977416331364200737)
  ·
    refine ⟨26998068733062248523150553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35997424977416331364200737 26998068733062248523150553)
    ·
      refine ⟨20248551549796686392362915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26998068733062248523150553 20248551549796686392362915)
      ·
        refine ⟨30372827324695029588544373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20248551549796686392362915 30372827324695029588544373)
        ·
          refine ⟨2847452561690159023926035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30372827324695029588544373 2847452561690159023926035)
          ·
            refine ⟨4271178842535238535889053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2847452561690159023926035 4271178842535238535889053)
            ·
              refine ⟨1601692065950714450958395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4271178842535238535889053 1601692065950714450958395)
              ·
                refine ⟨2402538098926071676437593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1601692065950714450958395 2402538098926071676437593)
                ·
                  refine ⟨1801903574194553757328195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2402538098926071676437593 1801903574194553757328195)
                  ·
                    refine ⟨2702855361291830635992293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1801903574194553757328195 2702855361291830635992293)
                    ·
                      refine ⟨506785380242218244248555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2702855361291830635992293 506785380242218244248555)
                      ·
                        rfl

theorem cell23_986961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 1, 2, 1, 4].length) (baseStart_986961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_986961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_986961 prefixEnd_986961 := by exact prefixLift 986961
  have htrace : WordTrace (prefixWord ++ tailWord_986961) baseStart_986961 baseEnd_986961 := by
    simpa [prefixWord, tailWord_986961, baseEnd_986961] using wordTrace_append hprefix tailTrace_986961
  have hstable : (prefixWord ++ tailWord_986961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986961).length < 2 ^ (prefixWord ++ tailWord_986961).sum := by decide
  have hdescent : baseEnd_986961 < baseStart_986961 := by decide
  rcases family_descends (prefixWord ++ tailWord_986961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986978 : List Nat := [3, 3, 2, 1, 2, 1, 1, 2, 2, 4, 2]
def baseStart_986978 : Nat := 118140960795 + 986978 * 2 ^ 59
def prefixEnd_986978 : Nat := 4983230072969 + 3 ^ 40 * 986978 * 2
def baseEnd_986978 : Nat := 506794109413344677735977

theorem tailTrace_986978 : CollatzResearch.WordTrace tailWord_986978 prefixEnd_986978 506794109413344677735977 := by
  unfold tailWord_986978
  simp only [CollatzResearch.WordTrace]
  refine ⟨8999511254588685816892397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23998696678903162178379725 8999511254588685816892397)
  ·
    refine ⟨3374816720470757181334649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8999511254588685816892397 3374816720470757181334649)
    ·
      refine ⟨2531112540353067886000987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3374816720470757181334649 2531112540353067886000987)
      ·
        refine ⟨3796668810529601829001481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2531112540353067886000987 3796668810529601829001481)
        ·
          refine ⟨2847501607897201371751111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3796668810529601829001481 2847501607897201371751111)
          ·
            refine ⟨4271252411845802057626667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2847501607897201371751111 4271252411845802057626667)
            ·
              refine ⟨6406878617768703086440001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4271252411845802057626667 6406878617768703086440001)
              ·
                refine ⟨4805158963326527314830001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6406878617768703086440001 4805158963326527314830001)
                ·
                  refine ⟨3603869222494895486122501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4805158963326527314830001 3603869222494895486122501)
                  ·
                    refine ⟨675725479217792903647969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3603869222494895486122501 675725479217792903647969)
                    ·
                      refine ⟨506794109413344677735977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 675725479217792903647969 506794109413344677735977)
                      ·
                        rfl

theorem cell23_986978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 2, 2, 4, 2].length) (baseStart_986978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_986978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_986978 prefixEnd_986978 := by exact prefixLift 986978
  have htrace : WordTrace (prefixWord ++ tailWord_986978) baseStart_986978 baseEnd_986978 := by
    simpa [prefixWord, tailWord_986978, baseEnd_986978] using wordTrace_append hprefix tailTrace_986978
  have hstable : (prefixWord ++ tailWord_986978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986978).length < 2 ^ (prefixWord ++ tailWord_986978).sum := by decide
  have hdescent : baseEnd_986978 < baseStart_986978 := by decide
  rcases family_descends (prefixWord ++ tailWord_986978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986984 : List Nat := [2, 1, 4, 2, 1, 1, 3, 1, 8]
def baseStart_986984 : Nat := 118140960795 + 986984 * 2 ^ 59
def prefixEnd_986984 : Nat := 4983230072969 + 3 ^ 40 * 986984 * 2
def baseEnd_986984 : Nat := 56310798921919072695661

theorem tailTrace_986984 : CollatzResearch.WordTrace tailWord_986984 prefixEnd_986984 56310798921919072695661 := by
  unfold tailWord_986984
  simp only [CollatzResearch.WordTrace]
  refine ⟨17999131928166503146144003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23998842570888670861525337 17999131928166503146144003)
  ·
    refine ⟨26998697892249754719216005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17999131928166503146144003 26998697892249754719216005)
    ·
      refine ⟨5062255854796829009853001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26998697892249754719216005 5062255854796829009853001)
      ·
        refine ⟨3796691891097621757389751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5062255854796829009853001 3796691891097621757389751)
        ·
          refine ⟨5695037836646432636084627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3796691891097621757389751 5695037836646432636084627)
          ·
            refine ⟨8542556754969648954126941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5695037836646432636084627 8542556754969648954126941)
            ·
              refine ⟨3203458783113618357797603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8542556754969648954126941 3203458783113618357797603)
              ·
                refine ⟨4805188174670427536696405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3203458783113618357797603 4805188174670427536696405)
                ·
                  refine ⟨56310798921919072695661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4805188174670427536696405 56310798921919072695661)
                  ·
                    rfl

theorem cell23_986984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 1, 8].length) (baseStart_986984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_986984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_986984 prefixEnd_986984 := by exact prefixLift 986984
  have htrace : WordTrace (prefixWord ++ tailWord_986984) baseStart_986984 baseEnd_986984 := by
    simpa [prefixWord, tailWord_986984, baseEnd_986984] using wordTrace_append hprefix tailTrace_986984
  have hstable : (prefixWord ++ tailWord_986984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986984).length < 2 ^ (prefixWord ++ tailWord_986984).sum := by decide
  have hdescent : baseEnd_986984 < baseStart_986984 := by decide
  rcases family_descends (prefixWord ++ tailWord_986984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986988 : List Nat := [2, 2, 1, 1, 4, 2, 2, 4, 1, 4]
def baseStart_986988 : Nat := 118140960795 + 986988 * 2 ^ 59
def prefixEnd_986988 : Nat := 4983230072969 + 3 ^ 40 * 986988 * 2
def baseEnd_986988 : Nat := 168933081406629879536977

theorem tailTrace_986988 : CollatzResearch.WordTrace tailWord_986988 prefixEnd_986988 168933081406629879536977 := by
  unfold tailWord_986988
  simp only [CollatzResearch.WordTrace]
  refine ⟨17999204874159257487716809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23998939832212343316955745 17999204874159257487716809)
  ·
    refine ⟨13499403655619443115787607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17999204874159257487716809 13499403655619443115787607)
    ·
      refine ⟨20249105483429164673681411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13499403655619443115787607 20249105483429164673681411)
      ·
        refine ⟨30373658225143747010522117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20249105483429164673681411 30373658225143747010522117)
        ·
          refine ⟨5695060917214452564472897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30373658225143747010522117 5695060917214452564472897)
          ·
            refine ⟨4271295687910839423354673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5695060917214452564472897 4271295687910839423354673)
            ·
              refine ⟨3203471765933129567516005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4271295687910839423354673 3203471765933129567516005)
              ·
                refine ⟨600650956112461793909251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3203471765933129567516005 600650956112461793909251)
                ·
                  refine ⟨900976434168692690863877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 600650956112461793909251 900976434168692690863877)
                  ·
                    refine ⟨168933081406629879536977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 900976434168692690863877 168933081406629879536977)
                    ·
                      rfl

theorem cell23_986988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 4, 1, 4].length) (baseStart_986988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_986988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_986988 prefixEnd_986988 := by exact prefixLift 986988
  have htrace : WordTrace (prefixWord ++ tailWord_986988) baseStart_986988 baseEnd_986988 := by
    simpa [prefixWord, tailWord_986988, baseEnd_986988] using wordTrace_append hprefix tailTrace_986988
  have hstable : (prefixWord ++ tailWord_986988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986988).length < 2 ^ (prefixWord ++ tailWord_986988).sum := by decide
  have hdescent : baseEnd_986988 < baseStart_986988 := by decide
  rcases family_descends (prefixWord ++ tailWord_986988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987001 : List Nat := [1, 2, 1, 3, 2, 2, 5, 1, 6]
def baseStart_987001 : Nat := 118140960795 + 987001 * 2 ^ 59
def prefixEnd_987001 : Nat := 4983230072969 + 3 ^ 40 * 987001 * 2
def baseEnd_987001 : Nat := 56311768829822009749819

theorem tailTrace_987001 : CollatzResearch.WordTrace tailWord_987001 prefixEnd_987001 56311768829822009749819 := by
  unfold tailWord_987001
  simp only [CollatzResearch.WordTrace]
  refine ⟨35998883897271418195656857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23999255931514278797104571 35998883897271418195656857)
  ·
    refine ⟨26999162922953563646742643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35998883897271418195656857 26999162922953563646742643)
    ·
      refine ⟨40498744384430345470113965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26999162922953563646742643 40498744384430345470113965)
      ·
        refine ⟨15187029144161379551292737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40498744384430345470113965 15187029144161379551292737)
        ·
          refine ⟨11390271858121034663469553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15187029144161379551292737 11390271858121034663469553)
          ·
            refine ⟨8542703893590775997602165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11390271858121034663469553 8542703893590775997602165)
            ·
              refine ⟨800878490024135249775203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8542703893590775997602165 800878490024135249775203)
              ·
                refine ⟨1201317735036202874662805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 800878490024135249775203 1201317735036202874662805)
                ·
                  refine ⟨56311768829822009749819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1201317735036202874662805 56311768829822009749819)
                  ·
                    rfl

theorem cell23_987001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 5, 1, 6].length) (baseStart_987001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_987001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_987001 prefixEnd_987001 := by exact prefixLift 987001
  have htrace : WordTrace (prefixWord ++ tailWord_987001) baseStart_987001 baseEnd_987001 := by
    simpa [prefixWord, tailWord_987001, baseEnd_987001] using wordTrace_append hprefix tailTrace_987001
  have hstable : (prefixWord ++ tailWord_987001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987001).length < 2 ^ (prefixWord ++ tailWord_987001).sum := by decide
  have hdescent : baseEnd_987001 < baseStart_987001 := by decide
  rcases family_descends (prefixWord ++ tailWord_987001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987031 : List Nat := [1, 1, 3, 3, 1, 3, 2, 3, 1, 5]
def baseStart_987031 : Nat := 118140960795 + 987031 * 2 ^ 59
def prefixEnd_987031 : Nat := 4983230072969 + 3 ^ 40 * 987031 * 2
def baseEnd_987031 : Nat := 168940441296010990124411

theorem tailTrace_987031 : CollatzResearch.WordTrace tailWord_987031 prefixEnd_987031 168940441296010990124411 := by
  unfold tailWord_987031
  simp only [CollatzResearch.WordTrace]
  refine ⟨35999978087162733319248947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23999985391441822212832631 35999978087162733319248947)
  ·
    refine ⟨53999967130744099978873421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35999978087162733319248947 53999967130744099978873421)
    ·
      refine ⟨20249987674029037492077533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53999967130744099978873421 20249987674029037492077533)
      ·
        refine ⟨7593745377760889059529075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20249987674029037492077533 7593745377760889059529075)
        ·
          refine ⟨11390618066641333589293613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7593745377760889059529075 11390618066641333589293613)
          ·
            refine ⟨4271481774990500095985105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11390618066641333589293613 4271481774990500095985105)
            ·
              refine ⟨3203611331242875071988829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4271481774990500095985105 3203611331242875071988829)
              ·
                refine ⟨1201354249216078151995811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3203611331242875071988829 1201354249216078151995811)
                ·
                  refine ⟨1802031373824117227993717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1201354249216078151995811 1802031373824117227993717)
                  ·
                    refine ⟨168940441296010990124411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1802031373824117227993717 168940441296010990124411)
                    ·
                      rfl

theorem cell23_987031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 3, 1, 5].length) (baseStart_987031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_987031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_987031 prefixEnd_987031 := by exact prefixLift 987031
  have htrace : WordTrace (prefixWord ++ tailWord_987031) baseStart_987031 baseEnd_987031 := by
    simpa [prefixWord, tailWord_987031, baseEnd_987031] using wordTrace_append hprefix tailTrace_987031
  have hstable : (prefixWord ++ tailWord_987031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987031).length < 2 ^ (prefixWord ++ tailWord_987031).sum := by decide
  have hdescent : baseEnd_987031 < baseStart_987031 := by decide
  rcases family_descends (prefixWord ++ tailWord_987031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987064 : List Nat := [2, 1, 2, 1, 2, 3, 1, 3, 1, 1, 6]
def baseStart_987064 : Nat := 118140960795 + 987064 * 2 ^ 59
def prefixEnd_987064 : Nat := 4983230072969 + 3 ^ 40 * 987064 * 2
def baseEnd_987064 : Nat := 506838268749631341260581

theorem tailTrace_987064 : CollatzResearch.WordTrace tailWord_987064 prefixEnd_987064 506838268749631341260581 := by
  unfold tailWord_987064
  simp only [CollatzResearch.WordTrace]
  refine ⟨18000590848021589977600123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24000787797362119970133497 18000590848021589977600123)
  ·
    refine ⟨27000886272032384966400185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18000590848021589977600123 27000886272032384966400185)
    ·
      refine ⟨20250664704024288724800139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27000886272032384966400185 20250664704024288724800139)
      ·
        refine ⟨30375997056036433087200209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20250664704024288724800139 30375997056036433087200209)
        ·
          refine ⟨22781997792027324815400157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30375997056036433087200209 22781997792027324815400157)
          ·
            refine ⟨8543249172010246805775059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22781997792027324815400157 8543249172010246805775059)
            ·
              refine ⟨12814873758015370208662589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8543249172010246805775059 12814873758015370208662589)
              ·
                refine ⟨4805577659255763828248471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12814873758015370208662589 4805577659255763828248471)
                ·
                  refine ⟨7208366488883645742372707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4805577659255763828248471 7208366488883645742372707)
                  ·
                    refine ⟨10812549733325468613559061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7208366488883645742372707 10812549733325468613559061)
                    ·
                      refine ⟨506838268749631341260581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10812549733325468613559061 506838268749631341260581)
                      ·
                        rfl

theorem cell23_987064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 3, 1, 1, 6].length) (baseStart_987064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_987064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_987064 prefixEnd_987064 := by exact prefixLift 987064
  have htrace : WordTrace (prefixWord ++ tailWord_987064) baseStart_987064 baseEnd_987064 := by
    simpa [prefixWord, tailWord_987064, baseEnd_987064] using wordTrace_append hprefix tailTrace_987064
  have hstable : (prefixWord ++ tailWord_987064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987064).length < 2 ^ (prefixWord ++ tailWord_987064).sum := by decide
  have hdescent : baseEnd_987064 < baseStart_987064 := by decide
  rcases family_descends (prefixWord ++ tailWord_987064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987071 : List Nat := [1, 1, 2, 2, 2, 1, 5, 1, 3, 2, 3]
def baseStart_987071 : Nat := 118140960795 + 987071 * 2 ^ 59
def prefixEnd_987071 : Nat := 4983230072969 + 3 ^ 40 * 987071 * 2
def baseEnd_987071 : Nat := 506841863114212813873049

theorem tailTrace_987071 : CollatzResearch.WordTrace tailWord_987071 prefixEnd_987071 506841863114212813873049 := by
  unfold tailWord_987071
  simp only [CollatzResearch.WordTrace]
  refine ⟨36001437007017820150705067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24000958004678546767136711 36001437007017820150705067)
  ·
    refine ⟨54002155510526730226057601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36001437007017820150705067 54002155510526730226057601)
    ·
      refine ⟨40501616632895047669543201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54002155510526730226057601 40501616632895047669543201)
      ·
        refine ⟨30376212474671285752157401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40501616632895047669543201 30376212474671285752157401)
        ·
          refine ⟨22782159356003464314118051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30376212474671285752157401 22782159356003464314118051)
          ·
            refine ⟨34173239034005196471177077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22782159356003464314118051 34173239034005196471177077)
            ·
              refine ⟨3203741159437987169172851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34173239034005196471177077 3203741159437987169172851)
              ·
                refine ⟨4805611739156980753759277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3203741159437987169172851 4805611739156980753759277)
                ·
                  refine ⟨1802104402183867782659729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4805611739156980753759277 1802104402183867782659729)
                  ·
                    refine ⟨1351578301637900836994797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1802104402183867782659729 1351578301637900836994797)
                    ·
                      refine ⟨506841863114212813873049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1351578301637900836994797 506841863114212813873049)
                      ·
                        rfl

theorem cell23_987071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 1, 3, 2, 3].length) (baseStart_987071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_987071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_987071 prefixEnd_987071 := by exact prefixLift 987071
  have htrace : WordTrace (prefixWord ++ tailWord_987071) baseStart_987071 baseEnd_987071 := by
    simpa [prefixWord, tailWord_987071, baseEnd_987071] using wordTrace_append hprefix tailTrace_987071
  have hstable : (prefixWord ++ tailWord_987071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987071).length < 2 ^ (prefixWord ++ tailWord_987071).sum := by decide
  have hdescent : baseEnd_987071 < baseStart_987071 := by decide
  rcases family_descends (prefixWord ++ tailWord_987071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987118 : List Nat := [4, 1, 2, 1, 3, 1, 1, 3, 1, 3, 3]
def baseStart_987118 : Nat := 118140960795 + 987118 * 2 ^ 59
def prefixEnd_987118 : Nat := 4983230072969 + 3 ^ 40 * 987118 * 2
def baseEnd_987118 : Nat := 506865996704974129985333

theorem tailTrace_987118 : CollatzResearch.WordTrace tailWord_987118 prefixEnd_987118 506865996704974129985333 := by
  unfold tailWord_987118
  simp only [CollatzResearch.WordTrace]
  refine ⟨4500393904730943397208251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24002100825231698118444005 4500393904730943397208251)
  ·
    refine ⟨6750590857096415095812377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4500393904730943397208251 6750590857096415095812377)
    ·
      refine ⟨5062943142822311321859283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6750590857096415095812377 5062943142822311321859283)
      ·
        refine ⟨7594414714233466982788925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5062943142822311321859283 7594414714233466982788925)
        ·
          refine ⟨2847905517837550118545847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7594414714233466982788925 2847905517837550118545847)
          ·
            refine ⟨4271858276756325177818771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2847905517837550118545847 4271858276756325177818771)
            ·
              refine ⟨6407787415134487766728157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4271858276756325177818771 6407787415134487766728157)
              ·
                refine ⟨2402920280675432912523059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6407787415134487766728157 2402920280675432912523059)
                ·
                  refine ⟨3604380421013149368784589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2402920280675432912523059 3604380421013149368784589)
                  ·
                    refine ⟨1351642657879931013294221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3604380421013149368784589 1351642657879931013294221)
                    ·
                      refine ⟨506865996704974129985333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1351642657879931013294221 506865996704974129985333)
                      ·
                        rfl

theorem cell23_987118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 3, 1, 3, 3].length) (baseStart_987118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_987118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_987118 prefixEnd_987118 := by exact prefixLift 987118
  have htrace : WordTrace (prefixWord ++ tailWord_987118) baseStart_987118 baseEnd_987118 := by
    simpa [prefixWord, tailWord_987118, baseEnd_987118] using wordTrace_append hprefix tailTrace_987118
  have hstable : (prefixWord ++ tailWord_987118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987118).length < 2 ^ (prefixWord ++ tailWord_987118).sum := by decide
  have hdescent : baseEnd_987118 < baseStart_987118 := by decide
  rcases family_descends (prefixWord ++ tailWord_987118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987128 : List Nat := [2, 1, 2, 1, 1, 3, 4, 1, 3, 3, 2]
def baseStart_987128 : Nat := 118140960795 + 987128 * 2 ^ 59
def prefixEnd_987128 : Nat := 4983230072969 + 3 ^ 40 * 987128 * 2
def baseEnd_987128 : Nat := 506871131511519090860287

theorem tailTrace_987128 : CollatzResearch.WordTrace tailWord_987128 prefixEnd_987128 506871131511519090860287 := by
  unfold tailWord_987128
  simp only [CollatzResearch.WordTrace]
  refine ⟨18001757983905659442765019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24002343978540879257020025 18001757983905659442765019)
  ·
    refine ⟨27002636975858489164147529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18001757983905659442765019 27002636975858489164147529)
    ·
      refine ⟨20251977731893866873110647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27002636975858489164147529 20251977731893866873110647)
      ·
        refine ⟨30377966597840800309665971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20251977731893866873110647 30377966597840800309665971)
        ·
          refine ⟨45566949896761200464498957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30377966597840800309665971 45566949896761200464498957)
          ·
            refine ⟨17087606211285450174187109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45566949896761200464498957 17087606211285450174187109)
            ·
              refine ⟨3203926164616021907660083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17087606211285450174187109 3203926164616021907660083)
              ·
                refine ⟨4805889246924032861490125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3203926164616021907660083 4805889246924032861490125)
                ·
                  refine ⟨1802208467596512323058797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4805889246924032861490125 1802208467596512323058797)
                  ·
                    refine ⟨675828175348692121147049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1802208467596512323058797 675828175348692121147049)
                    ·
                      refine ⟨506871131511519090860287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 675828175348692121147049 506871131511519090860287)
                      ·
                        rfl

theorem cell23_987128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 1, 3, 3, 2].length) (baseStart_987128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_987128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_987128 prefixEnd_987128 := by exact prefixLift 987128
  have htrace : WordTrace (prefixWord ++ tailWord_987128) baseStart_987128 baseEnd_987128 := by
    simpa [prefixWord, tailWord_987128, baseEnd_987128] using wordTrace_append hprefix tailTrace_987128
  have hstable : (prefixWord ++ tailWord_987128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987128).length < 2 ^ (prefixWord ++ tailWord_987128).sum := by decide
  have hdescent : baseEnd_987128 < baseStart_987128 := by decide
  rcases family_descends (prefixWord ++ tailWord_987128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987142 : List Nat := [6, 2, 1, 2, 1, 1, 10]
def baseStart_987142 : Nat := 118140960795 + 987142 * 2 ^ 59
def prefixEnd_987142 : Nat := 4983230072969 + 3 ^ 40 * 987142 * 2
def baseEnd_987142 : Nat := 6257757040008420198583

theorem tailTrace_987142 : CollatzResearch.WordTrace tailWord_987142 prefixEnd_987142 6257757040008420198583 := by
  unfold tailWord_987142
  simp only [CollatzResearch.WordTrace]
  refine ⟨1125125830930018727391865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 24002684393173732851026453 1125125830930018727391865)
  ·
    refine ⟨843844373197514045543899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1125125830930018727391865 843844373197514045543899)
    ·
      refine ⟨1265766559796271068315849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 843844373197514045543899 1265766559796271068315849)
      ·
        refine ⟨949324919847203301236887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1265766559796271068315849 949324919847203301236887)
        ·
          refine ⟨1423987379770804951855331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 949324919847203301236887 1423987379770804951855331)
          ·
            refine ⟨2135981069656207427782997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1423987379770804951855331 2135981069656207427782997)
            ·
              refine ⟨6257757040008420198583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2135981069656207427782997 6257757040008420198583)
              ·
                rfl

theorem cell23_987142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 10].length) (baseStart_987142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_987142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_987142 prefixEnd_987142 := by exact prefixLift 987142
  have htrace : WordTrace (prefixWord ++ tailWord_987142) baseStart_987142 baseEnd_987142 := by
    simpa [prefixWord, tailWord_987142, baseEnd_987142] using wordTrace_append hprefix tailTrace_987142
  have hstable : (prefixWord ++ tailWord_987142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987142).length < 2 ^ (prefixWord ++ tailWord_987142).sum := by decide
  have hdescent : baseEnd_987142 < baseStart_987142 := by decide
  rcases family_descends (prefixWord ++ tailWord_987142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987171 : List Nat := [1, 1, 1, 4, 3, 1, 1, 3, 2, 2, 4]
def baseStart_987171 : Nat := 118140960795 + 987171 * 2 ^ 59
def prefixEnd_987171 : Nat := 4983230072969 + 3 ^ 40 * 987171 * 2
def baseEnd_987171 : Nat := 506893211179662422622589

theorem tailTrace_987171 : CollatzResearch.WordTrace tailWord_987171 prefixEnd_987171 506893211179662422622589 := by
  unfold tailWord_987171
  simp only [CollatzResearch.WordTrace]
  refine ⟨36005084306655537229345367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24003389537770358152896911 36005084306655537229345367)
  ·
    refine ⟨54007626459983305844018051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36005084306655537229345367 54007626459983305844018051)
    ·
      refine ⟨81011439689974958766027077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54007626459983305844018051 81011439689974958766027077)
      ·
        refine ⟨15189644941870304768630077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81011439689974958766027077 15189644941870304768630077)
        ·
          refine ⟨5696116853201364288236279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15189644941870304768630077 5696116853201364288236279)
          ·
            refine ⟨8544175279802046432354419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5696116853201364288236279 8544175279802046432354419)
            ·
              refine ⟨12816262919703069648531629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8544175279802046432354419 12816262919703069648531629)
              ·
                refine ⟨4806098594888651118199361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12816262919703069648531629 4806098594888651118199361)
                ·
                  refine ⟨3604573946166488338649521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4806098594888651118199361 3604573946166488338649521)
                  ·
                    refine ⟨2703430459624866253987141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3604573946166488338649521 2703430459624866253987141)
                    ·
                      refine ⟨506893211179662422622589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2703430459624866253987141 506893211179662422622589)
                      ·
                        rfl

theorem cell23_987171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 3, 2, 2, 4].length) (baseStart_987171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_987171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_987171 prefixEnd_987171 := by exact prefixLift 987171
  have htrace : WordTrace (prefixWord ++ tailWord_987171) baseStart_987171 baseEnd_987171 := by
    simpa [prefixWord, tailWord_987171, baseEnd_987171] using wordTrace_append hprefix tailTrace_987171
  have hstable : (prefixWord ++ tailWord_987171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987171).length < 2 ^ (prefixWord ++ tailWord_987171).sum := by decide
  have hdescent : baseEnd_987171 < baseStart_987171 := by decide
  rcases family_descends (prefixWord ++ tailWord_987171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987191 : List Nat := [1, 1, 3, 1, 2, 2, 2, 2, 1, 5, 3]
def baseStart_987191 : Nat := 118140960795 + 987191 * 2 ^ 59
def prefixEnd_987191 : Nat := 4983230072969 + 3 ^ 40 * 987191 * 2
def baseEnd_987191 : Nat := 506903480792752344372497

theorem tailTrace_987191 : CollatzResearch.WordTrace tailWord_987191 prefixEnd_987191 506903480792752344372497 := by
  unfold tailWord_987191
  simp only [CollatzResearch.WordTrace]
  refine ⟨36005813766583080645073427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24003875844388720430048951 36005813766583080645073427)
  ·
    refine ⟨54008720649874620967610141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36005813766583080645073427 54008720649874620967610141)
    ·
      refine ⟨20253270243702982862853803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54008720649874620967610141 20253270243702982862853803)
      ·
        refine ⟨30379905365554474294280705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20253270243702982862853803 30379905365554474294280705)
        ·
          refine ⟨22784929024165855720710529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30379905365554474294280705 22784929024165855720710529)
          ·
            refine ⟨17088696768124391790532897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22784929024165855720710529 17088696768124391790532897)
            ·
              refine ⟨12816522576093293842899673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17088696768124391790532897 12816522576093293842899673)
              ·
                refine ⟨9612391932069970382174755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12816522576093293842899673 9612391932069970382174755)
                ·
                  refine ⟨14418587898104955573262133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9612391932069970382174755 14418587898104955573262133)
                  ·
                    refine ⟨1351742615447339584993325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14418587898104955573262133 1351742615447339584993325)
                    ·
                      refine ⟨506903480792752344372497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1351742615447339584993325 506903480792752344372497)
                      ·
                        rfl

theorem cell23_987191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 5, 3].length) (baseStart_987191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_987191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_987191 prefixEnd_987191 := by exact prefixLift 987191
  have htrace : WordTrace (prefixWord ++ tailWord_987191) baseStart_987191 baseEnd_987191 := by
    simpa [prefixWord, tailWord_987191, baseEnd_987191] using wordTrace_append hprefix tailTrace_987191
  have hstable : (prefixWord ++ tailWord_987191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987191).length < 2 ^ (prefixWord ++ tailWord_987191).sum := by decide
  have hdescent : baseEnd_987191 < baseStart_987191 := by decide
  rcases family_descends (prefixWord ++ tailWord_987191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987211 : List Nat := [1, 1, 1, 1, 3, 1, 2, 6, 2, 5]
def baseStart_987211 : Nat := 118140960795 + 987211 * 2 ^ 59
def prefixEnd_987211 : Nat := 4983230072969 + 3 ^ 40 * 987211 * 2
def baseEnd_987211 : Nat := 168971250135280755374135

theorem tailTrace_987211 : CollatzResearch.WordTrace tailWord_987211 prefixEnd_987211 168971250135280755374135 := by
  unfold tailWord_987211
  simp only [CollatzResearch.WordTrace]
  refine ⟨36006543226510624060801487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24004362151007082707200991 36006543226510624060801487)
  ·
    refine ⟨54009814839765936091202231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36006543226510624060801487 54009814839765936091202231)
    ·
      refine ⟨81014722259648904136803347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54009814839765936091202231 81014722259648904136803347)
      ·
        refine ⟨121522083389473356205205021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81014722259648904136803347 121522083389473356205205021)
        ·
          refine ⟨45570781271052508576951883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121522083389473356205205021 45570781271052508576951883)
          ·
            refine ⟨68356171906578762865427825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45570781271052508576951883 68356171906578762865427825)
            ·
              refine ⟨51267128929934072149070869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68356171906578762865427825 51267128929934072149070869)
              ·
                refine ⟨2403146668590659631987697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 51267128929934072149070869 2403146668590659631987697)
                ·
                  refine ⟨1802360001442994723990773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2403146668590659631987697 1802360001442994723990773)
                  ·
                    refine ⟨168971250135280755374135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1802360001442994723990773 168971250135280755374135)
                    ·
                      rfl

theorem cell23_987211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 6, 2, 5].length) (baseStart_987211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_987211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_987211 prefixEnd_987211 := by exact prefixLift 987211
  have htrace : WordTrace (prefixWord ++ tailWord_987211) baseStart_987211 baseEnd_987211 := by
    simpa [prefixWord, tailWord_987211, baseEnd_987211] using wordTrace_append hprefix tailTrace_987211
  have hstable : (prefixWord ++ tailWord_987211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987211).length < 2 ^ (prefixWord ++ tailWord_987211).sum := by decide
  have hdescent : baseEnd_987211 < baseStart_987211 := by decide
  rcases family_descends (prefixWord ++ tailWord_987211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987221 : List Nat := [1, 3, 2, 2, 1, 3, 1, 1, 1, 1, 7]
def baseStart_987221 : Nat := 118140960795 + 987221 * 2 ^ 59
def prefixEnd_987221 : Nat := 4983230072969 + 3 ^ 40 * 987221 * 2
def baseEnd_987221 : Nat := 506918885212387226997359

theorem tailTrace_987221 : CollatzResearch.WordTrace tailWord_987221 prefixEnd_987221 506918885212387226997359 := by
  unfold tailWord_987221
  simp only [CollatzResearch.WordTrace]
  refine ⟨36006907956474395768665517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24004605304316263845777011 36006907956474395768665517)
  ·
    refine ⟨13502590483677898413249569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36006907956474395768665517 13502590483677898413249569)
    ·
      refine ⟨10126942862758423809937177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13502590483677898413249569 10126942862758423809937177)
      ·
        refine ⟨7595207147068817857452883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10126942862758423809937177 7595207147068817857452883)
        ·
          refine ⟨11392810720603226786179325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7595207147068817857452883 11392810720603226786179325)
          ·
            refine ⟨4272304020226210044817247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11392810720603226786179325 4272304020226210044817247)
            ·
              refine ⟨6408456030339315067225871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4272304020226210044817247 6408456030339315067225871)
              ·
                refine ⟨9612684045508972600838807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6408456030339315067225871 9612684045508972600838807)
                ·
                  refine ⟨14419026068263458901258211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9612684045508972600838807 14419026068263458901258211)
                  ·
                    refine ⟨21628539102395188351887317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14419026068263458901258211 21628539102395188351887317)
                    ·
                      refine ⟨506918885212387226997359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 21628539102395188351887317 506918885212387226997359)
                      ·
                        rfl

theorem cell23_987221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_987221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_987221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_987221 prefixEnd_987221 := by exact prefixLift 987221
  have htrace : WordTrace (prefixWord ++ tailWord_987221) baseStart_987221 baseEnd_987221 := by
    simpa [prefixWord, tailWord_987221, baseEnd_987221] using wordTrace_append hprefix tailTrace_987221
  have hstable : (prefixWord ++ tailWord_987221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987221).length < 2 ^ (prefixWord ++ tailWord_987221).sum := by decide
  have hdescent : baseEnd_987221 < baseStart_987221 := by decide
  rcases family_descends (prefixWord ++ tailWord_987221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987231 : List Nat := [1, 1, 2, 3, 1, 1, 2, 4, 1, 3, 4]
def baseStart_987231 : Nat := 118140960795 + 987231 * 2 ^ 59
def prefixEnd_987231 : Nat := 4983230072969 + 3 ^ 40 * 987231 * 2
def baseEnd_987231 : Nat := 506924020018932187872313

theorem tailTrace_987231 : CollatzResearch.WordTrace tailWord_987231 prefixEnd_987231 506924020018932187872313 := by
  unfold tailWord_987231
  simp only [CollatzResearch.WordTrace]
  refine ⟨36007272686438167476529547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24004848457625444984353031 36007272686438167476529547)
  ·
    refine ⟨54010909029657251214794321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36007272686438167476529547 54010909029657251214794321)
    ·
      refine ⟨40508181772242938411095741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54010909029657251214794321 40508181772242938411095741)
      ·
        refine ⟨15190568164591101904160903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40508181772242938411095741 15190568164591101904160903)
        ·
          refine ⟨22785852246886652856241355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15190568164591101904160903 22785852246886652856241355)
          ·
            refine ⟨34178778370329979284362033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22785852246886652856241355 34178778370329979284362033)
            ·
              refine ⟨25634083777747484463271525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34178778370329979284362033 25634083777747484463271525)
              ·
                refine ⟨4806390708327653336863411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25634083777747484463271525 4806390708327653336863411)
                ·
                  refine ⟨7209586062491480005295117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4806390708327653336863411 7209586062491480005295117)
                  ·
                    refine ⟨2703594773434305001985669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7209586062491480005295117 2703594773434305001985669)
                    ·
                      refine ⟨506924020018932187872313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2703594773434305001985669 506924020018932187872313)
                      ·
                        rfl

theorem cell23_987231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 4, 1, 3, 4].length) (baseStart_987231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_987231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_987231 prefixEnd_987231 := by exact prefixLift 987231
  have htrace : WordTrace (prefixWord ++ tailWord_987231) baseStart_987231 baseEnd_987231 := by
    simpa [prefixWord, tailWord_987231, baseEnd_987231] using wordTrace_append hprefix tailTrace_987231
  have hstable : (prefixWord ++ tailWord_987231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987231).length < 2 ^ (prefixWord ++ tailWord_987231).sum := by decide
  have hdescent : baseEnd_987231 < baseStart_987231 := by decide
  rcases family_descends (prefixWord ++ tailWord_987231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987248 : List Nat := [2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 4]
def baseStart_987248 : Nat := 118140960795 + 987248 * 2 ^ 59
def prefixEnd_987248 : Nat := 4983230072969 + 3 ^ 40 * 987248 * 2
def baseEnd_987248 : Nat := 506932749190058621359735

theorem tailTrace_987248 : CollatzResearch.WordTrace tailWord_987248 prefixEnd_987248 506932749190058621359735 := by
  unfold tailWord_987248
  simp only [CollatzResearch.WordTrace]
  refine ⟨18003946363688289689949199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24005261818251052919932265 18003946363688289689949199)
  ·
    refine ⟨27005919545532434534923799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18003946363688289689949199 27005919545532434534923799)
    ·
      refine ⟨40508879318298651802385699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27005919545532434534923799 40508879318298651802385699)
      ·
        refine ⟨60763318977447977703578549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40508879318298651802385699 60763318977447977703578549)
        ·
          refine ⟨5696561154135747909710489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60763318977447977703578549 5696561154135747909710489)
          ·
            refine ⟨4272420865601810932282867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5696561154135747909710489 4272420865601810932282867)
            ·
              refine ⟨6408631298402716398424301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4272420865601810932282867 6408631298402716398424301)
              ·
                refine ⟨2403236736901018649409113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6408631298402716398424301 2403236736901018649409113)
                ·
                  refine ⟨1802427552675763987056835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2403236736901018649409113 1802427552675763987056835)
                  ·
                    refine ⟨2703641329013645980585253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1802427552675763987056835 2703641329013645980585253)
                    ·
                      refine ⟨506932749190058621359735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2703641329013645980585253 506932749190058621359735)
                      ·
                        rfl

theorem cell23_987248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 4].length) (baseStart_987248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_987248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_987248 prefixEnd_987248 := by exact prefixLift 987248
  have htrace : WordTrace (prefixWord ++ tailWord_987248) baseStart_987248 baseEnd_987248 := by
    simpa [prefixWord, tailWord_987248, baseEnd_987248] using wordTrace_append hprefix tailTrace_987248
  have hstable : (prefixWord ++ tailWord_987248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987248).length < 2 ^ (prefixWord ++ tailWord_987248).sum := by decide
  have hdescent : baseEnd_987248 < baseStart_987248 := by decide
  rcases family_descends (prefixWord ++ tailWord_987248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987271 : List Nat := [1, 1, 4, 2, 1, 1, 2, 3, 8]
def baseStart_987271 : Nat := 118140960795 + 987271 * 2 ^ 59
def prefixEnd_987271 : Nat := 4983230072969 + 3 ^ 40 * 987271 * 2
def baseEnd_987271 : Nat := 56327173249456892374681

theorem tailTrace_987271 : CollatzResearch.WordTrace tailWord_987271 prefixEnd_987271 56327173249456892374681 := by
  unfold tailWord_987271
  simp only [CollatzResearch.WordTrace]
  refine ⟨36008731606293254307985667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24005821070862169538657111 36008731606293254307985667)
  ·
    refine ⟨54013097409439881461978501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36008731606293254307985667 54013097409439881461978501)
    ·
      refine ⟨10127455764269977774120969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54013097409439881461978501 10127455764269977774120969)
      ·
        refine ⟨7595591823202483330590727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10127455764269977774120969 7595591823202483330590727)
        ·
          refine ⟨11393387734803724995886091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7595591823202483330590727 11393387734803724995886091)
          ·
            refine ⟨17090081602205587493829137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11393387734803724995886091 17090081602205587493829137)
            ·
              refine ⟨12817561201654190620371853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17090081602205587493829137 12817561201654190620371853)
              ·
                refine ⟨4806585450620321482639445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12817561201654190620371853 4806585450620321482639445)
                ·
                  refine ⟨56327173249456892374681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4806585450620321482639445 56327173249456892374681)
                  ·
                    rfl

theorem cell23_987271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 3, 8].length) (baseStart_987271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_987271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_987271 prefixEnd_987271 := by exact prefixLift 987271
  have htrace : WordTrace (prefixWord ++ tailWord_987271) baseStart_987271 baseEnd_987271 := by
    simpa [prefixWord, tailWord_987271, baseEnd_987271] using wordTrace_append hprefix tailTrace_987271
  have hstable : (prefixWord ++ tailWord_987271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987271).length < 2 ^ (prefixWord ++ tailWord_987271).sum := by decide
  have hdescent : baseEnd_987271 < baseStart_987271 := by decide
  rcases family_descends (prefixWord ++ tailWord_987271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987309 : List Nat := [1, 5, 2, 1, 2, 2, 2, 3, 1, 4]
def baseStart_987309 : Nat := 118140960795 + 987309 * 2 ^ 59
def prefixEnd_987309 : Nat := 4983230072969 + 3 ^ 40 * 987309 * 2
def baseEnd_987309 : Nat := 168988023836660960898985

theorem tailTrace_987309 : CollatzResearch.WordTrace tailWord_987309 prefixEnd_987309 168988023836660960898985 := by
  unfold tailWord_987309
  simp only [CollatzResearch.WordTrace]
  refine ⟨36010117580155586797868981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24006745053437057865245987 36010117580155586797868981)
  ·
    refine ⟨3375948523139586262300217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36010117580155586797868981 3375948523139586262300217)
    ·
      refine ⟨2531961392354689696725163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3375948523139586262300217 2531961392354689696725163)
      ·
        refine ⟨3797942088532034545087745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2531961392354689696725163 3797942088532034545087745)
        ·
          refine ⟨2848456566399025908815809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3797942088532034545087745 2848456566399025908815809)
          ·
            refine ⟨2136342424799269431611857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2848456566399025908815809 2136342424799269431611857)
            ·
              refine ⟨1602256818599452073708893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2136342424799269431611857 1602256818599452073708893)
              ·
                refine ⟨600846306974794527640835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1602256818599452073708893 600846306974794527640835)
                ·
                  refine ⟨901269460462191791461253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 600846306974794527640835 901269460462191791461253)
                  ·
                    refine ⟨168988023836660960898985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 901269460462191791461253 168988023836660960898985)
                    ·
                      rfl

theorem cell23_987309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_987309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_987309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_987309 prefixEnd_987309 := by exact prefixLift 987309
  have htrace : WordTrace (prefixWord ++ tailWord_987309) baseStart_987309 baseEnd_987309 := by
    simpa [prefixWord, tailWord_987309, baseEnd_987309] using wordTrace_append hprefix tailTrace_987309
  have hstable : (prefixWord ++ tailWord_987309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987309).length < 2 ^ (prefixWord ++ tailWord_987309).sum := by decide
  have hdescent : baseEnd_987309 < baseStart_987309 := by decide
  rcases family_descends (prefixWord ++ tailWord_987309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987311 : List Nat := [1, 1, 2, 1, 2, 3, 1, 1, 2, 4, 5]
def baseStart_987311 : Nat := 118140960795 + 987311 * 2 ^ 59
def prefixEnd_987311 : Nat := 4983230072969 + 3 ^ 40 * 987311 * 2
def baseEnd_987311 : Nat := 506965098471291874871945

theorem tailTrace_987311 : CollatzResearch.WordTrace tailWord_987311 prefixEnd_987311 506965098471291874871945 := by
  unfold tailWord_987311
  simp only [CollatzResearch.WordTrace]
  refine ⟨36010190526148341139441787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24006793684098894092961191 36010190526148341139441787)
  ·
    refine ⟨54015285789222511709162681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36010190526148341139441787 54015285789222511709162681)
    ·
      refine ⟨40511464341916883781872011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54015285789222511709162681 40511464341916883781872011)
      ·
        refine ⟨60767196512875325672808017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40511464341916883781872011 60767196512875325672808017)
        ·
          refine ⟨45575397384656494254606013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60767196512875325672808017 45575397384656494254606013)
          ·
            refine ⟨17090774019246185345477255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45575397384656494254606013 17090774019246185345477255)
            ·
              refine ⟨25636161028869278018215883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17090774019246185345477255 25636161028869278018215883)
              ·
                refine ⟨38454241543303917027323825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25636161028869278018215883 38454241543303917027323825)
                ·
                  refine ⟨28840681157477937770492869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38454241543303917027323825 28840681157477937770492869)
                  ·
                    refine ⟨5407627717027113331967413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28840681157477937770492869 5407627717027113331967413)
                    ·
                      refine ⟨506965098471291874871945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5407627717027113331967413 506965098471291874871945)
                      ·
                        rfl

theorem cell23_987311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 4, 5].length) (baseStart_987311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_987311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_987311 prefixEnd_987311 := by exact prefixLift 987311
  have htrace : WordTrace (prefixWord ++ tailWord_987311) baseStart_987311 baseEnd_987311 := by
    simpa [prefixWord, tailWord_987311, baseEnd_987311] using wordTrace_append hprefix tailTrace_987311
  have hstable : (prefixWord ++ tailWord_987311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987311).length < 2 ^ (prefixWord ++ tailWord_987311).sum := by decide
  have hdescent : baseEnd_987311 < baseStart_987311 := by decide
  rcases family_descends (prefixWord ++ tailWord_987311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987325 : List Nat := [1, 4, 1, 2, 1, 1, 1, 3, 4, 3, 2]
def baseStart_987325 : Nat := 118140960795 + 987325 * 2 ^ 59
def prefixEnd_987325 : Nat := 4983230072969 + 3 ^ 40 * 987325 * 2
def baseEnd_987325 : Nat := 506972287200454820096881

theorem tailTrace_987325 : CollatzResearch.WordTrace tailWord_987325 prefixEnd_987325 506972287200454820096881 := by
  unfold tailWord_987325
  simp only [CollatzResearch.WordTrace]
  refine ⟨36010701148097621530451429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24007134098731747686967619 36010701148097621530451429)
  ·
    refine ⟨6752006465268304036959643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36010701148097621530451429 6752006465268304036959643)
    ·
      refine ⟨10128009697902456055439465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6752006465268304036959643 10128009697902456055439465)
      ·
        refine ⟨7596007273426842041579599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10128009697902456055439465 7596007273426842041579599)
        ·
          refine ⟨11394010910140263062369399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7596007273426842041579599 11394010910140263062369399)
          ·
            refine ⟨17091016365210394593554099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11394010910140263062369399 17091016365210394593554099)
            ·
              refine ⟨25636524547815591890331149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17091016365210394593554099 25636524547815591890331149)
              ·
                refine ⟨9613696705430846958874181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25636524547815591890331149 9613696705430846958874181)
                ·
                  refine ⟨1802568132268283804788909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9613696705430846958874181 1802568132268283804788909)
                  ·
                    refine ⟨675963049600606426795841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1802568132268283804788909 675963049600606426795841)
                    ·
                      refine ⟨506972287200454820096881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 675963049600606426795841 506972287200454820096881)
                      ·
                        rfl

theorem cell23_987325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 4, 3, 2].length) (baseStart_987325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_987325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_987325 prefixEnd_987325 := by exact prefixLift 987325
  have htrace : WordTrace (prefixWord ++ tailWord_987325) baseStart_987325 baseEnd_987325 := by
    simpa [prefixWord, tailWord_987325, baseEnd_987325] using wordTrace_append hprefix tailTrace_987325
  have hstable : (prefixWord ++ tailWord_987325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987325).length < 2 ^ (prefixWord ++ tailWord_987325).sum := by decide
  have hdescent : baseEnd_987325 < baseStart_987325 := by decide
  rcases family_descends (prefixWord ++ tailWord_987325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987332 : List Nat := [2, 3, 3, 1, 2, 1, 1, 3, 3, 1, 3]
def baseStart_987332 : Nat := 118140960795 + 987332 * 2 ^ 59
def prefixEnd_987332 : Nat := 4983230072969 + 3 ^ 40 * 987332 * 2
def baseEnd_987332 : Nat := 506975881565036292709349

theorem tailTrace_987332 : CollatzResearch.WordTrace tailWord_987332 prefixEnd_987332 506975881565036292709349 := by
  unfold tailWord_987332
  simp only [CollatzResearch.WordTrace]
  refine ⟨18005478229536130862978125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24007304306048174483970833 18005478229536130862978125)
  ·
    refine ⟨6752054336076049073616797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18005478229536130862978125 6752054336076049073616797)
    ·
      refine ⟨2532020376028518402606299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6752054336076049073616797 2532020376028518402606299)
      ·
        refine ⟨3798030564042777603909449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2532020376028518402606299 3798030564042777603909449)
        ·
          refine ⟨2848522923032083202932087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3798030564042777603909449 2848522923032083202932087)
          ·
            refine ⟨4272784384548124804398131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2848522923032083202932087 4272784384548124804398131)
            ·
              refine ⟨6409176576822187206597197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4272784384548124804398131 6409176576822187206597197)
              ·
                refine ⟨2403441216308320202473949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6409176576822187206597197 2403441216308320202473949)
                ·
                  refine ⟨901290456115620075927731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2403441216308320202473949 901290456115620075927731)
                  ·
                    refine ⟨1351935684173430113891597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 901290456115620075927731 1351935684173430113891597)
                    ·
                      refine ⟨506975881565036292709349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1351935684173430113891597 506975881565036292709349)
                      ·
                        rfl

theorem cell23_987332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_987332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_987332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_987332 prefixEnd_987332 := by exact prefixLift 987332
  have htrace : WordTrace (prefixWord ++ tailWord_987332) baseStart_987332 baseEnd_987332 := by
    simpa [prefixWord, tailWord_987332, baseEnd_987332] using wordTrace_append hprefix tailTrace_987332
  have hstable : (prefixWord ++ tailWord_987332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987332).length < 2 ^ (prefixWord ++ tailWord_987332).sum := by decide
  have hdescent : baseEnd_987332 < baseStart_987332 := by decide
  rcases family_descends (prefixWord ++ tailWord_987332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987365 : List Nat := [1, 3, 1, 4, 2, 1, 1, 2, 4, 4]
def baseStart_987365 : Nat := 118140960795 + 987365 * 2 ^ 59
def prefixEnd_987365 : Nat := 4983230072969 + 3 ^ 40 * 987365 * 2
def baseEnd_987365 : Nat := 168997608808878221198899

theorem tailTrace_987365 : CollatzResearch.WordTrace tailWord_987365 prefixEnd_987365 168997608808878221198899 := by
  unfold tailWord_987365
  simp only [CollatzResearch.WordTrace]
  refine ⟨36012160067952708361907549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24008106711968472241271699 36012160067952708361907549)
  ·
    refine ⟨13504560025482265635715331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36012160067952708361907549 13504560025482265635715331)
    ·
      refine ⟨20256840038223398453572997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13504560025482265635715331 20256840038223398453572997)
      ·
        refine ⟨3798157507166887210044937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20256840038223398453572997 3798157507166887210044937)
        ·
          refine ⟨2848618130375165407533703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3798157507166887210044937 2848618130375165407533703)
          ·
            refine ⟨4272927195562748111300555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2848618130375165407533703 4272927195562748111300555)
            ·
              refine ⟨6409390793344122166950833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4272927195562748111300555 6409390793344122166950833)
              ·
                refine ⟨4807043095008091625213125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6409390793344122166950833 4807043095008091625213125)
                ·
                  refine ⟨901320580314017179727461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4807043095008091625213125 901320580314017179727461)
                  ·
                    refine ⟨168997608808878221198899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 901320580314017179727461 168997608808878221198899)
                    ·
                      rfl

theorem cell23_987365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 2, 4, 4].length) (baseStart_987365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_987365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_987365 prefixEnd_987365 := by exact prefixLift 987365
  have htrace : WordTrace (prefixWord ++ tailWord_987365) baseStart_987365 baseEnd_987365 := by
    simpa [prefixWord, tailWord_987365, baseEnd_987365] using wordTrace_append hprefix tailTrace_987365
  have hstable : (prefixWord ++ tailWord_987365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987365).length < 2 ^ (prefixWord ++ tailWord_987365).sum := by decide
  have hdescent : baseEnd_987365 < baseStart_987365 := by decide
  rcases family_descends (prefixWord ++ tailWord_987365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987375 : List Nat := [1, 1, 2, 1, 6, 2, 2, 1, 1, 1, 5]
def baseStart_987375 : Nat := 118140960795 + 987375 * 2 ^ 59
def prefixEnd_987375 : Nat := 4983230072969 + 3 ^ 40 * 987375 * 2
def baseEnd_987375 : Nat := 506997961233179624471651

theorem tailTrace_987375 : CollatzResearch.WordTrace tailWord_987375 prefixEnd_987375 506997961233179624471651 := by
  unfold tailWord_987375
  simp only [CollatzResearch.WordTrace]
  refine ⟨36012524797916480069771579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24008349865277653379847719 36012524797916480069771579)
  ·
    refine ⟨54018787196874720104657369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36012524797916480069771579 54018787196874720104657369)
    ·
      refine ⟨40514090397656040078493027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54018787196874720104657369 40514090397656040078493027)
      ·
        refine ⟨60771135596484060117739541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40514090397656040078493027 60771135596484060117739541)
        ·
          refine ⟨2848646981085190318019041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 60771135596484060117739541 2848646981085190318019041)
          ·
            refine ⟨2136485235813892738514281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2848646981085190318019041 2136485235813892738514281)
            ·
              refine ⟨1602363926860419553885711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2136485235813892738514281 1602363926860419553885711)
              ·
                refine ⟨2403545890290629330828567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1602363926860419553885711 2403545890290629330828567)
                ·
                  refine ⟨3605318835435943996242851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2403545890290629330828567 3605318835435943996242851)
                  ·
                    refine ⟨5407978253153915994364277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3605318835435943996242851 5407978253153915994364277)
                    ·
                      refine ⟨506997961233179624471651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5407978253153915994364277 506997961233179624471651)
                      ·
                        rfl

theorem cell23_987375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 1, 1, 1, 5].length) (baseStart_987375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_987375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_987375 prefixEnd_987375 := by exact prefixLift 987375
  have htrace : WordTrace (prefixWord ++ tailWord_987375) baseStart_987375 baseEnd_987375 := by
    simpa [prefixWord, tailWord_987375, baseEnd_987375] using wordTrace_append hprefix tailTrace_987375
  have hstable : (prefixWord ++ tailWord_987375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987375).length < 2 ^ (prefixWord ++ tailWord_987375).sum := by decide
  have hdescent : baseEnd_987375 < baseStart_987375 := by decide
  rcases family_descends (prefixWord ++ tailWord_987375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987378 : List Nat := [3, 2, 1, 3, 2, 1, 11]
def baseStart_987378 : Nat := 118140960795 + 987378 * 2 ^ 59
def prefixEnd_987378 : Nat := 4983230072969 + 3 ^ 40 * 987378 * 2
def baseEnd_987378 : Nat := 6259253107100532255977

theorem tailTrace_987378 : CollatzResearch.WordTrace tailWord_987378 prefixEnd_987378 6259253107100532255977 := by
  unfold tailWord_987378
  simp only [CollatzResearch.WordTrace]
  refine ⟨9003158554226402895532697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24008422811270407721420525 9003158554226402895532697)
  ·
    refine ⟨6752368915669802171649523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9003158554226402895532697 6752368915669802171649523)
    ·
      refine ⟨10128553373504703257474285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6752368915669802171649523 10128553373504703257474285)
      ·
        refine ⟨3798207515064263721552857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10128553373504703257474285 3798207515064263721552857)
        ·
          refine ⟨2848655636298197791164643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3798207515064263721552857 2848655636298197791164643)
          ·
            refine ⟨4272983454447296686746965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2848655636298197791164643 4272983454447296686746965)
            ·
              refine ⟨6259253107100532255977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 4272983454447296686746965 6259253107100532255977)
              ·
                rfl

theorem cell23_987378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 11].length) (baseStart_987378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_987378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_987378 prefixEnd_987378 := by exact prefixLift 987378
  have htrace : WordTrace (prefixWord ++ tailWord_987378) baseStart_987378 baseEnd_987378 := by
    simpa [prefixWord, tailWord_987378, baseEnd_987378] using wordTrace_append hprefix tailTrace_987378
  have hstable : (prefixWord ++ tailWord_987378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987378).length < 2 ^ (prefixWord ++ tailWord_987378).sum := by decide
  have hdescent : baseEnd_987378 < baseStart_987378 := by decide
  rcases family_descends (prefixWord ++ tailWord_987378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987389 : List Nat := [1, 4, 1, 1, 1, 1, 1, 8, 1, 2, 2]
def baseStart_987389 : Nat := 118140960795 + 987389 * 2 ^ 59
def prefixEnd_987389 : Nat := 4983230072969 + 3 ^ 40 * 987389 * 2
def baseEnd_987389 : Nat := 507005149962342569696587

theorem tailTrace_987389 : CollatzResearch.WordTrace tailWord_987389 prefixEnd_987389 507005149962342569696587 := by
  unfold tailWord_987389
  simp only [CollatzResearch.WordTrace]
  refine ⟨36013035419865760460781221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24008690279910506973854147 36013035419865760460781221)
  ·
    refine ⟨6752444141224830086396479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36013035419865760460781221 6752444141224830086396479)
    ·
      refine ⟨10128666211837245129594719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6752444141224830086396479 10128666211837245129594719)
      ·
        refine ⟨15192999317755867694392079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10128666211837245129594719 15192999317755867694392079)
        ·
          refine ⟨22789498976633801541588119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15192999317755867694392079 22789498976633801541588119)
          ·
            refine ⟨34184248464950702312382179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22789498976633801541588119 34184248464950702312382179)
            ·
              refine ⟨51276372697426053468573269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34184248464950702312382179 51276372697426053468573269)
              ·
                refine ⟨600894992547961564084843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 51276372697426053468573269 600894992547961564084843)
                ·
                  refine ⟨901342488821942346127265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 600894992547961564084843 901342488821942346127265)
                  ·
                    refine ⟨676006866616456759595449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 901342488821942346127265 676006866616456759595449)
                    ·
                      refine ⟨507005149962342569696587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 676006866616456759595449 507005149962342569696587)
                      ·
                        rfl

theorem cell23_987389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 8, 1, 2, 2].length) (baseStart_987389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_987389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_987389 prefixEnd_987389 := by exact prefixLift 987389
  have htrace : WordTrace (prefixWord ++ tailWord_987389) baseStart_987389 baseEnd_987389 := by
    simpa [prefixWord, tailWord_987389, baseEnd_987389] using wordTrace_append hprefix tailTrace_987389
  have hstable : (prefixWord ++ tailWord_987389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987389).length < 2 ^ (prefixWord ++ tailWord_987389).sum := by decide
  have hdescent : baseEnd_987389 < baseStart_987389 := by decide
  rcases family_descends (prefixWord ++ tailWord_987389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987399 : List Nat := [1, 1, 4, 5, 1, 1, 1, 3, 2, 4]
def baseStart_987399 : Nat := 118140960795 + 987399 * 2 ^ 59
def prefixEnd_987399 : Nat := 4983230072969 + 3 ^ 40 * 987399 * 2
def baseEnd_987399 : Nat := 169003428256295843523847

theorem tailTrace_987399 : CollatzResearch.WordTrace tailWord_987399 prefixEnd_987399 169003428256295843523847 := by
  unfold tailWord_987399
  simp only [CollatzResearch.WordTrace]
  refine ⟨36013400149829532168645251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24008933433219688112430167 36013400149829532168645251)
  ·
    refine ⟨54020100224744298252967877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36013400149829532168645251 54020100224744298252967877)
    ·
      refine ⟨10128768792139555922431477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54020100224744298252967877 10128768792139555922431477)
      ·
        refine ⟨949572074263083367727951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10128768792139555922431477 949572074263083367727951)
        ·
          refine ⟨1424358111394625051591927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 949572074263083367727951 1424358111394625051591927)
          ·
            refine ⟨2136537167091937577387891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1424358111394625051591927 2136537167091937577387891)
            ·
              refine ⟨3204805750637906366081837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2136537167091937577387891 3204805750637906366081837)
              ·
                refine ⟨1201802156489214887280689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3204805750637906366081837 1201802156489214887280689)
                ·
                  refine ⟨901351617366911165460517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1201802156489214887280689 901351617366911165460517)
                  ·
                    refine ⟨169003428256295843523847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 901351617366911165460517 169003428256295843523847)
                    ·
                      rfl

theorem cell23_987399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 3, 2, 4].length) (baseStart_987399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_987399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_987399 prefixEnd_987399 := by exact prefixLift 987399
  have htrace : WordTrace (prefixWord ++ tailWord_987399) baseStart_987399 baseEnd_987399 := by
    simpa [prefixWord, tailWord_987399, baseEnd_987399] using wordTrace_append hprefix tailTrace_987399
  have hstable : (prefixWord ++ tailWord_987399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987399).length < 2 ^ (prefixWord ++ tailWord_987399).sum := by decide
  have hdescent : baseEnd_987399 < baseStart_987399 := by decide
  rcases family_descends (prefixWord ++ tailWord_987399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
