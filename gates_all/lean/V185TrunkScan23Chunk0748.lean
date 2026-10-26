import V185TrunkScan23Chunk0747

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4423401 : List Nat := [1, 2, 1, 1, 1, 2, 3, 3, 5, 1, 3]
def baseStart_4423401 : Nat := 118140960795 + 4423401 * 2 ^ 59
def prefixEnd_4423401 : Nat := 4983230072969 + 3 ^ 40 * 4423401 * 2
def baseEnd_4423401 : Nat := 2271330840578753156944655

theorem tailTrace_4423401 : CollatzResearch.WordTrace tailWord_4423401 prefixEnd_4423401 2271330840578753156944655 := by
  unfold tailWord_4423401
  simp only [CollatzResearch.WordTrace]
  refine ⟨161334688647781108590926057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107556459098520739060617371 161334688647781108590926057)
  ·
    refine ⟨121001016485835831443194543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161334688647781108590926057 121001016485835831443194543)
    ·
      refine ⟨181501524728753747164791815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121001016485835831443194543 181501524728753747164791815)
      ·
        refine ⟨272252287093130620747187723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181501524728753747164791815 272252287093130620747187723)
        ·
          refine ⟨408378430639695931120781585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 272252287093130620747187723 408378430639695931120781585)
          ·
            refine ⟨306283822979771948340586189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 408378430639695931120781585 306283822979771948340586189)
            ·
              refine ⟨114856433617414480627719821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 306283822979771948340586189 114856433617414480627719821)
              ·
                refine ⟨43071162606530430235394933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 114856433617414480627719821 43071162606530430235394933)
                ·
                  refine ⟨4037921494362227834568275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43071162606530430235394933 4037921494362227834568275)
                  ·
                    refine ⟨6056882241543341751852413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4037921494362227834568275 6056882241543341751852413)
                    ·
                      refine ⟨2271330840578753156944655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6056882241543341751852413 2271330840578753156944655)
                      ·
                        rfl

theorem cell23_4423401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 5, 1, 3].length) (baseStart_4423401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4423401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4423401 prefixEnd_4423401 := by exact prefixLift 4423401
  have htrace : WordTrace (prefixWord ++ tailWord_4423401) baseStart_4423401 baseEnd_4423401 := by
    simpa [prefixWord, tailWord_4423401, baseEnd_4423401] using wordTrace_append hprefix tailTrace_4423401
  have hstable : (prefixWord ++ tailWord_4423401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4423401).length < 2 ^ (prefixWord ++ tailWord_4423401).sum := by decide
  have hdescent : baseEnd_4423401 < baseStart_4423401 := by decide
  rcases family_descends (prefixWord ++ tailWord_4423401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4423411 : List Nat := [1, 1, 1, 2, 2, 3, 2, 3, 1, 5, 2]
def baseStart_4423411 : Nat := 118140960795 + 4423411 * 2 ^ 59
def prefixEnd_4423411 : Nat := 4983230072969 + 3 ^ 40 * 4423411 * 2
def baseEnd_4423411 : Nat := 2271335975385298117819609

theorem tailTrace_4423411 : CollatzResearch.WordTrace tailWord_4423411 prefixEnd_4423411 2271335975385298117819609 := by
  unfold tailWord_4423411
  simp only [CollatzResearch.WordTrace]
  refine ⟨161335053377744880298790087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107556702251829920199193391 161335053377744880298790087)
  ·
    refine ⟨242002580066617320448185131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161335053377744880298790087 242002580066617320448185131)
    ·
      refine ⟨363003870099925980672277697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242002580066617320448185131 363003870099925980672277697)
      ·
        refine ⟨272252902574944485504208273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 363003870099925980672277697 272252902574944485504208273)
        ·
          refine ⟨204189676931208364128156205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 272252902574944485504208273 204189676931208364128156205)
          ·
            refine ⟨76571128849203136548058577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 204189676931208364128156205 76571128849203136548058577)
            ·
              refine ⟨57428346636902352411043933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76571128849203136548058577 57428346636902352411043933)
              ·
                refine ⟨21535629988838382154141475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57428346636902352411043933 21535629988838382154141475)
                ·
                  refine ⟨32303444983257573231212213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21535629988838382154141475 32303444983257573231212213)
                  ·
                    refine ⟨3028447967180397490426145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32303444983257573231212213 3028447967180397490426145)
                    ·
                      refine ⟨2271335975385298117819609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3028447967180397490426145 2271335975385298117819609)
                      ·
                        rfl

theorem cell23_4423411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 3, 1, 5, 2].length) (baseStart_4423411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4423411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4423411 prefixEnd_4423411 := by exact prefixLift 4423411
  have htrace : WordTrace (prefixWord ++ tailWord_4423411) baseStart_4423411 baseEnd_4423411 := by
    simpa [prefixWord, tailWord_4423411, baseEnd_4423411] using wordTrace_append hprefix tailTrace_4423411
  have hstable : (prefixWord ++ tailWord_4423411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4423411).length < 2 ^ (prefixWord ++ tailWord_4423411).sum := by decide
  have hdescent : baseEnd_4423411 < baseStart_4423411 := by decide
  rcases family_descends (prefixWord ++ tailWord_4423411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4423441 : List Nat := [1, 2, 2, 1, 1, 3, 1, 2, 2, 6, 2]
def baseStart_4423441 : Nat := 118140960795 + 4423441 * 2 ^ 59
def prefixEnd_4423441 : Nat := 4983230072969 + 3 ^ 40 * 4423441 * 2
def baseEnd_4423441 : Nat := 2271351379804933000444471

theorem tailTrace_4423441 : CollatzResearch.WordTrace tailWord_4423441 prefixEnd_4423441 2271351379804933000444471 := by
  unfold tailWord_4423441
  simp only [CollatzResearch.WordTrace]
  refine ⟨161336147567636195422382177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107557431711757463614921451 161336147567636195422382177)
  ·
    refine ⟨121002110675727146566786633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161336147567636195422382177 121002110675727146566786633)
    ·
      refine ⟨90751583006795359925089975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121002110675727146566786633 90751583006795359925089975)
      ·
        refine ⟨136127374510193039887634963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90751583006795359925089975 136127374510193039887634963)
        ·
          refine ⟨204191061765289559831452445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136127374510193039887634963 204191061765289559831452445)
          ·
            refine ⟨76571648161983584936794667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 204191061765289559831452445 76571648161983584936794667)
            ·
              refine ⟨114857472242975377405192001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76571648161983584936794667 114857472242975377405192001)
              ·
                refine ⟨86143104182231533053894001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 114857472242975377405192001 86143104182231533053894001)
                ·
                  refine ⟨64607328136673649790420501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 86143104182231533053894001 64607328136673649790420501)
                  ·
                    refine ⟨3028468506406577333925961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 64607328136673649790420501 3028468506406577333925961)
                    ·
                      refine ⟨2271351379804933000444471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3028468506406577333925961 2271351379804933000444471)
                      ·
                        rfl

theorem cell23_4423441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 6, 2].length) (baseStart_4423441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4423441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4423441 prefixEnd_4423441 := by exact prefixLift 4423441
  have htrace : WordTrace (prefixWord ++ tailWord_4423441) baseStart_4423441 baseEnd_4423441 := by
    simpa [prefixWord, tailWord_4423441, baseEnd_4423441] using wordTrace_append hprefix tailTrace_4423441
  have hstable : (prefixWord ++ tailWord_4423441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4423441).length < 2 ^ (prefixWord ++ tailWord_4423441).sum := by decide
  have hdescent : baseEnd_4423441 < baseStart_4423441 := by decide
  rcases family_descends (prefixWord ++ tailWord_4423441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4423458 : List Nat := [3, 3, 1, 1, 2, 1, 2, 4, 1, 1, 4]
def baseStart_4423458 : Nat := 118140960795 + 4423458 * 2 ^ 59
def prefixEnd_4423458 : Nat := 4983230072969 + 3 ^ 40 * 4423458 * 2
def baseEnd_4423458 : Nat := 2271360108976059433931893

theorem tailTrace_4423458 : CollatzResearch.WordTrace tailWord_4423458 prefixEnd_4423458 2271360108976059433931893 := by
  unfold tailWord_4423458
  simp only [CollatzResearch.WordTrace]
  refine ⟨40334191902143651831437757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107557845072383071550500685 40334191902143651831437757)
  ·
    refine ⟨15125321963303869436789159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40334191902143651831437757 15125321963303869436789159)
    ·
      refine ⟨22687982944955804155183739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15125321963303869436789159 22687982944955804155183739)
      ·
        refine ⟨34031974417433706232775609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22687982944955804155183739 34031974417433706232775609)
        ·
          refine ⟨25523980813075279674581707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34031974417433706232775609 25523980813075279674581707)
          ·
            refine ⟨38285971219612919511872561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25523980813075279674581707 38285971219612919511872561)
            ·
              refine ⟨28714478414709689633904421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38285971219612919511872561 28714478414709689633904421)
              ·
                refine ⟨5383964702758066806357079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28714478414709689633904421 5383964702758066806357079)
                ·
                  refine ⟨8075947054137100209535619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5383964702758066806357079 8075947054137100209535619)
                  ·
                    refine ⟨12113920581205650314303429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8075947054137100209535619 12113920581205650314303429)
                    ·
                      refine ⟨2271360108976059433931893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12113920581205650314303429 2271360108976059433931893)
                      ·
                        rfl

theorem cell23_4423458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 4, 1, 1, 4].length) (baseStart_4423458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4423458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4423458 prefixEnd_4423458 := by exact prefixLift 4423458
  have htrace : WordTrace (prefixWord ++ tailWord_4423458) baseStart_4423458 baseEnd_4423458 := by
    simpa [prefixWord, tailWord_4423458, baseEnd_4423458] using wordTrace_append hprefix tailTrace_4423458
  have hstable : (prefixWord ++ tailWord_4423458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4423458).length < 2 ^ (prefixWord ++ tailWord_4423458).sum := by decide
  have hdescent : baseEnd_4423458 < baseStart_4423458 := by decide
  rcases family_descends (prefixWord ++ tailWord_4423458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4423485 : List Nat := [1, 4, 1, 4, 1, 1, 3, 2, 2, 4]
def baseStart_4423485 : Nat := 118140960795 + 4423485 * 2 ^ 59
def prefixEnd_4423485 : Nat := 4983230072969 + 3 ^ 40 * 4423485 * 2
def baseEnd_4423485 : Nat := 757124657651243609431423

theorem tailTrace_4423485 : CollatzResearch.WordTrace tailWord_4423485 prefixEnd_4423485 757124657651243609431423 := by
  unfold tailWord_4423485
  simp only [CollatzResearch.WordTrace]
  refine ⟨161337752379476790936983909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107558501586317860624655939 161337752379476790936983909)
  ·
    refine ⟨30250828571151898300684483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 161337752379476790936983909 30250828571151898300684483)
    ·
      refine ⟨45376242856727847451026725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30250828571151898300684483 45376242856727847451026725)
      ·
        refine ⟨8508045535636471397067511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45376242856727847451026725 8508045535636471397067511)
        ·
          refine ⟨12762068303454707095601267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8508045535636471397067511 12762068303454707095601267)
          ·
            refine ⟨19143102455182060643401901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12762068303454707095601267 19143102455182060643401901)
            ·
              refine ⟨7178663420693272741275713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19143102455182060643401901 7178663420693272741275713)
              ·
                refine ⟨5383997565519954555956785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7178663420693272741275713 5383997565519954555956785)
                ·
                  refine ⟨4037998174139965916967589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5383997565519954555956785 4037998174139965916967589)
                  ·
                    refine ⟨757124657651243609431423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4037998174139965916967589 757124657651243609431423)
                    ·
                      rfl

theorem cell23_4423485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 2, 2, 4].length) (baseStart_4423485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4423485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4423485 prefixEnd_4423485 := by exact prefixLift 4423485
  have htrace : WordTrace (prefixWord ++ tailWord_4423485) baseStart_4423485 baseEnd_4423485 := by
    simpa [prefixWord, tailWord_4423485, baseEnd_4423485] using wordTrace_append hprefix tailTrace_4423485
  have hstable : (prefixWord ++ tailWord_4423485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4423485).length < 2 ^ (prefixWord ++ tailWord_4423485).sum := by decide
  have hdescent : baseEnd_4423485 < baseStart_4423485 := by decide
  rcases family_descends (prefixWord ++ tailWord_4423485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4423551 : List Nat := [1, 1, 2, 2, 1, 1, 3, 3, 2, 4, 3]
def baseStart_4423551 : Nat := 118140960795 + 4423551 * 2 ^ 59
def prefixEnd_4423551 : Nat := 4983230072969 + 3 ^ 40 * 4423551 * 2
def baseEnd_4423551 : Nat := 2271407862676927570068965

theorem tailTrace_4423551 : CollatzResearch.WordTrace tailWord_4423551 prefixEnd_4423551 2271407862676927570068965 := by
  unfold tailWord_4423551
  simp only [CollatzResearch.WordTrace]
  refine ⟨161340159597237684208886507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107560106398158456139257671 161340159597237684208886507)
  ·
    refine ⟨242010239395856526313329761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161340159597237684208886507 242010239395856526313329761)
    ·
      refine ⟨181507679546892394734997321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 242010239395856526313329761 181507679546892394734997321)
      ·
        refine ⟨136130759660169296051247991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 181507679546892394734997321 136130759660169296051247991)
        ·
          refine ⟨204196139490253944076871987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136130759660169296051247991 204196139490253944076871987)
          ·
            refine ⟨306294209235380916115307981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 204196139490253944076871987 306294209235380916115307981)
            ·
              refine ⟨114860328463267843543240493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 306294209235380916115307981 114860328463267843543240493)
              ·
                refine ⟨43072623173725441328715185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 114860328463267843543240493 43072623173725441328715185)
                ·
                  refine ⟨32304467380294080996536389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43072623173725441328715185 32304467380294080996536389)
                  ·
                    refine ⟨6057087633805140186850573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32304467380294080996536389 6057087633805140186850573)
                    ·
                      refine ⟨2271407862676927570068965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6057087633805140186850573 2271407862676927570068965)
                      ·
                        rfl

theorem cell23_4423551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 2, 4, 3].length) (baseStart_4423551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4423551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4423551 prefixEnd_4423551 := by exact prefixLift 4423551
  have htrace : WordTrace (prefixWord ++ tailWord_4423551) baseStart_4423551 baseEnd_4423551 := by
    simpa [prefixWord, tailWord_4423551, baseEnd_4423551] using wordTrace_append hprefix tailTrace_4423551
  have hstable : (prefixWord ++ tailWord_4423551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4423551).length < 2 ^ (prefixWord ++ tailWord_4423551).sum := by decide
  have hdescent : baseEnd_4423551 < baseStart_4423551 := by decide
  rcases family_descends (prefixWord ++ tailWord_4423551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4423559 : List Nat := [1, 1, 4, 2, 4, 2, 2, 1, 2, 1, 3]
def baseStart_4423559 : Nat := 118140960795 + 4423559 * 2 ^ 59
def prefixEnd_4423559 : Nat := 4983230072969 + 3 ^ 40 * 4423559 * 2
def baseEnd_4423559 : Nat := 2271411970522163538768929

theorem tailTrace_4423559 : CollatzResearch.WordTrace tailWord_4423559 prefixEnd_4423559 2271411970522163538768929 := by
  unfold tailWord_4423559
  simp only [CollatzResearch.WordTrace]
  refine ⟨161340451381208701575177731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107560300920805801050118487 161340451381208701575177731)
  ·
    refine ⟨242010677071813052362766597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161340451381208701575177731 242010677071813052362766597)
    ·
      refine ⟨45377001950964947318018737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 242010677071813052362766597 45377001950964947318018737)
      ·
        refine ⟨34032751463223710488514053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45377001950964947318018737 34032751463223710488514053)
        ·
          refine ⟨6381140899354445716596385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34032751463223710488514053 6381140899354445716596385)
          ·
            refine ⟨4785855674515834287447289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6381140899354445716596385 4785855674515834287447289)
            ·
              refine ⟨3589391755886875715585467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4785855674515834287447289 3589391755886875715585467)
              ·
                refine ⟨5384087633830313573378201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3589391755886875715585467 5384087633830313573378201)
                ·
                  refine ⟨4038065725372735180033651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5384087633830313573378201 4038065725372735180033651)
                  ·
                    refine ⟨6057098588059102770050477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4038065725372735180033651 6057098588059102770050477)
                    ·
                      refine ⟨2271411970522163538768929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6057098588059102770050477 2271411970522163538768929)
                      ·
                        rfl

theorem cell23_4423559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 2, 1, 2, 1, 3].length) (baseStart_4423559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4423559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4423559 prefixEnd_4423559 := by exact prefixLift 4423559
  have htrace : WordTrace (prefixWord ++ tailWord_4423559) baseStart_4423559 baseEnd_4423559 := by
    simpa [prefixWord, tailWord_4423559, baseEnd_4423559] using wordTrace_append hprefix tailTrace_4423559
  have hstable : (prefixWord ++ tailWord_4423559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4423559).length < 2 ^ (prefixWord ++ tailWord_4423559).sum := by decide
  have hdescent : baseEnd_4423559 < baseStart_4423559 := by decide
  rcases family_descends (prefixWord ++ tailWord_4423559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4423561 : List Nat := [1, 2, 1, 1, 5, 1, 2, 1, 1, 4, 4]
def baseStart_4423561 : Nat := 118140960795 + 4423561 * 2 ^ 59
def prefixEnd_4423561 : Nat := 4983230072969 + 3 ^ 40 * 4423561 * 2
def baseEnd_4423561 : Nat := 2271412997483472530943919

theorem tailTrace_4423561 : CollatzResearch.WordTrace tailWord_4423561 prefixEnd_4423561 2271412997483472530943919 := by
  unfold tailWord_4423561
  simp only [CollatzResearch.WordTrace]
  refine ⟨161340524327201455916750537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107560349551467637277833691 161340524327201455916750537)
  ·
    refine ⟨121005393245401091937562903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161340524327201455916750537 121005393245401091937562903)
    ·
      refine ⟨181508089868101637906344355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121005393245401091937562903 181508089868101637906344355)
      ·
        refine ⟨272262134802152456859516533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181508089868101637906344355 272262134802152456859516533)
        ·
          refine ⟨25524575137701792830579675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 272262134802152456859516533 25524575137701792830579675)
          ·
            refine ⟨38286862706552689245869513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25524575137701792830579675 38286862706552689245869513)
            ·
              refine ⟨28715147029914516934402135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38286862706552689245869513 28715147029914516934402135)
              ·
                refine ⟨43072720544871775401603203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28715147029914516934402135 43072720544871775401603203)
                ·
                  refine ⟨64609080817307663102404805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43072720544871775401603203 64609080817307663102404805)
                  ·
                    refine ⟨12114202653245186831700901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 64609080817307663102404805 12114202653245186831700901)
                    ·
                      refine ⟨2271412997483472530943919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12114202653245186831700901 2271412997483472530943919)
                      ·
                        rfl

theorem cell23_4423561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 4, 4].length) (baseStart_4423561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4423561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4423561 prefixEnd_4423561 := by exact prefixLift 4423561
  have htrace : WordTrace (prefixWord ++ tailWord_4423561) baseStart_4423561 baseEnd_4423561 := by
    simpa [prefixWord, tailWord_4423561, baseEnd_4423561] using wordTrace_append hprefix tailTrace_4423561
  have hstable : (prefixWord ++ tailWord_4423561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4423561).length < 2 ^ (prefixWord ++ tailWord_4423561).sum := by decide
  have hdescent : baseEnd_4423561 < baseStart_4423561 := by decide
  rcases family_descends (prefixWord ++ tailWord_4423561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4423605 : List Nat := [1, 3, 3, 2, 1, 3, 1, 4, 5]
def baseStart_4423605 : Nat := 118140960795 + 4423605 * 2 ^ 59
def prefixEnd_4423605 : Nat := 4983230072969 + 3 ^ 40 * 4423605 * 2
def baseEnd_4423605 : Nat := 252381732292474484310413

theorem tailTrace_4423605 : CollatzResearch.WordTrace tailWord_4423605 prefixEnd_4423605 252381732292474484310413 := by
  unfold tailWord_4423605
  simp only [CollatzResearch.WordTrace]
  refine ⟨161342129139042051431352269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107561419426028034287568179 161342129139042051431352269)
  ·
    refine ⟨60503298427140769286757101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 161342129139042051431352269 60503298427140769286757101)
    ·
      refine ⟨22688736910177788482533913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60503298427140769286757101 22688736910177788482533913)
      ·
        refine ⟨17016552682633341361900435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22688736910177788482533913 17016552682633341361900435)
        ·
          refine ⟨25524829023950012042850653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17016552682633341361900435 25524829023950012042850653)
          ·
            refine ⟨9571810883981254516068995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25524829023950012042850653 9571810883981254516068995)
            ·
              refine ⟨14357716325971881774103493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9571810883981254516068995 14357716325971881774103493)
              ·
                refine ⟨2692071811119727832644405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14357716325971881774103493 2692071811119727832644405)
                ·
                  refine ⟨252381732292474484310413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2692071811119727832644405 252381732292474484310413)
                  ·
                    rfl

theorem cell23_4423605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 4, 5].length) (baseStart_4423605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4423605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4423605 prefixEnd_4423605 := by exact prefixLift 4423605
  have htrace : WordTrace (prefixWord ++ tailWord_4423605) baseStart_4423605 baseEnd_4423605 := by
    simpa [prefixWord, tailWord_4423605, baseEnd_4423605] using wordTrace_append hprefix tailTrace_4423605
  have hstable : (prefixWord ++ tailWord_4423605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4423605).length < 2 ^ (prefixWord ++ tailWord_4423605).sum := by decide
  have hdescent : baseEnd_4423605 < baseStart_4423605 := by decide
  rcases family_descends (prefixWord ++ tailWord_4423605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4423608 : List Nat := [2, 1, 2, 1, 2, 3, 1, 1, 1, 7, 2]
def baseStart_4423608 : Nat := 118140960795 + 4423608 * 2 ^ 59
def prefixEnd_4423608 : Nat := 4983230072969 + 3 ^ 40 * 4423608 * 2
def baseEnd_4423608 : Nat := 2271437131074233847056203

theorem tailTrace_4423608 : CollatzResearch.WordTrace tailWord_4423608 prefixEnd_4423608 2271437131074233847056203 := by
  unfold tailWord_4423608
  simp only [CollatzResearch.WordTrace]
  refine ⟨80671119279015591471855739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107561492372020788629140985 80671119279015591471855739)
  ·
    refine ⟨121006678918523387207783609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80671119279015591471855739 121006678918523387207783609)
    ·
      refine ⟨90755009188892540405837707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121006678918523387207783609 90755009188892540405837707)
      ·
        refine ⟨136132513783338810608756561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90755009188892540405837707 136132513783338810608756561)
        ·
          refine ⟨102099385337504107956567421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136132513783338810608756561 102099385337504107956567421)
          ·
            refine ⟨38287269501564040483712783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102099385337504107956567421 38287269501564040483712783)
            ·
              refine ⟨57430904252346060725569175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38287269501564040483712783 57430904252346060725569175)
              ·
                refine ⟨86146356378519091088353763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57430904252346060725569175 86146356378519091088353763)
                ·
                  refine ⟨129219534567778636632530645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 86146356378519091088353763 129219534567778636632530645)
                  ·
                    refine ⟨3028582841432311796074937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 129219534567778636632530645 3028582841432311796074937)
                    ·
                      refine ⟨2271437131074233847056203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3028582841432311796074937 2271437131074233847056203)
                      ·
                        rfl

theorem cell23_4423608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 1, 7, 2].length) (baseStart_4423608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4423608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4423608 prefixEnd_4423608 := by exact prefixLift 4423608
  have htrace : WordTrace (prefixWord ++ tailWord_4423608) baseStart_4423608 baseEnd_4423608 := by
    simpa [prefixWord, tailWord_4423608, baseEnd_4423608] using wordTrace_append hprefix tailTrace_4423608
  have hstable : (prefixWord ++ tailWord_4423608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4423608).length < 2 ^ (prefixWord ++ tailWord_4423608).sum := by decide
  have hdescent : baseEnd_4423608 < baseStart_4423608 := by decide
  rcases family_descends (prefixWord ++ tailWord_4423608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4423688 : List Nat := [2, 1, 3, 2, 1, 2, 1, 1, 2, 5, 3]
def baseStart_4423688 : Nat := 118140960795 + 4423688 * 2 ^ 59
def prefixEnd_4423688 : Nat := 4983230072969 + 3 ^ 40 * 4423688 * 2
def baseEnd_4423688 : Nat := 2271478209526593534055835

theorem tailTrace_4423688 : CollatzResearch.WordTrace tailWord_4423688 prefixEnd_4423688 2271478209526593534055835 := by
  unfold tailWord_4423688
  simp only [CollatzResearch.WordTrace]
  refine ⟨80672578198870678303311859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107563437598494237737749145 80672578198870678303311859)
  ·
    refine ⟨121008867298306017454967789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80672578198870678303311859 121008867298306017454967789)
    ·
      refine ⟨45378325236864756545612921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121008867298306017454967789 45378325236864756545612921)
      ·
        refine ⟨34033743927648567409209691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45378325236864756545612921 34033743927648567409209691)
        ·
          refine ⟨51050615891472851113814537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34033743927648567409209691 51050615891472851113814537)
          ·
            refine ⟨38287961918604638335360903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51050615891472851113814537 38287961918604638335360903)
            ·
              refine ⟨57431942877906957503041355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38287961918604638335360903 57431942877906957503041355)
              ·
                refine ⟨86147914316860436254562033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57431942877906957503041355 86147914316860436254562033)
                ·
                  refine ⟨64610935737645327190921525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 86147914316860436254562033 64610935737645327190921525)
                  ·
                    refine ⟨6057275225404249424148893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 64610935737645327190921525 6057275225404249424148893)
                    ·
                      refine ⟨2271478209526593534055835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6057275225404249424148893 2271478209526593534055835)
                      ·
                        rfl

theorem cell23_4423688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 2, 5, 3].length) (baseStart_4423688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4423688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4423688 prefixEnd_4423688 := by exact prefixLift 4423688
  have htrace : WordTrace (prefixWord ++ tailWord_4423688) baseStart_4423688 baseEnd_4423688 := by
    simpa [prefixWord, tailWord_4423688, baseEnd_4423688] using wordTrace_append hprefix tailTrace_4423688
  have hstable : (prefixWord ++ tailWord_4423688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4423688).length < 2 ^ (prefixWord ++ tailWord_4423688).sum := by decide
  have hdescent : baseEnd_4423688 < baseStart_4423688 := by decide
  rcases family_descends (prefixWord ++ tailWord_4423688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4423716 : List Nat := [2, 3, 1, 4, 2, 1, 3, 2, 1, 4]
def baseStart_4423716 : Nat := 118140960795 + 4423716 * 2 ^ 59
def prefixEnd_4423716 : Nat := 4983230072969 + 3 ^ 40 * 4423716 * 2
def baseEnd_4423716 : Nat := 757164195661639808168569

theorem tailTrace_4423716 : CollatzResearch.WordTrace tailWord_4423716 prefixEnd_4423716 757164195661639808168569 := by
  unfold tailWord_4423716
  simp only [CollatzResearch.WordTrace]
  refine ⟨80673088820819958694321501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107564118427759944925762001 80673088820819958694321501)
  ·
    refine ⟨30252408307807484510370563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80673088820819958694321501 30252408307807484510370563)
    ·
      refine ⟨45378612461711226765555845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30252408307807484510370563 45378612461711226765555845)
      ·
        refine ⟨8508489836570855018541721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45378612461711226765555845 8508489836570855018541721)
        ·
          refine ⟨6381367377428141263906291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8508489836570855018541721 6381367377428141263906291)
          ·
            refine ⟨9572051066142211895859437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6381367377428141263906291 9572051066142211895859437)
            ·
              refine ⟨3589519149803329460947289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9572051066142211895859437 3589519149803329460947289)
              ·
                refine ⟨2692139362352497095710467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3589519149803329460947289 2692139362352497095710467)
                ·
                  refine ⟨4038209043528745643565701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2692139362352497095710467 4038209043528745643565701)
                  ·
                    refine ⟨757164195661639808168569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4038209043528745643565701 757164195661639808168569)
                    ·
                      rfl

theorem cell23_4423716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 3, 2, 1, 4].length) (baseStart_4423716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4423716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4423716 prefixEnd_4423716 := by exact prefixLift 4423716
  have htrace : WordTrace (prefixWord ++ tailWord_4423716) baseStart_4423716 baseEnd_4423716 := by
    simpa [prefixWord, tailWord_4423716, baseEnd_4423716] using wordTrace_append hprefix tailTrace_4423716
  have hstable : (prefixWord ++ tailWord_4423716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4423716).length < 2 ^ (prefixWord ++ tailWord_4423716).sum := by decide
  have hdescent : baseEnd_4423716 < baseStart_4423716 := by decide
  rcases family_descends (prefixWord ++ tailWord_4423716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4423738 : List Nat := [3, 1, 1, 1, 3, 1, 1, 5, 1, 6]
def baseStart_4423738 : Nat := 118140960795 + 4423738 * 2 ^ 59
def prefixEnd_4423738 : Nat := 4983230072969 + 3 ^ 40 * 4423738 * 2
def baseEnd_4423738 : Nat := 757167961186439446143535

theorem tailTrace_4423738 : CollatzResearch.WordTrace tailWord_4423738 prefixEnd_4423738 757167961186439446143535 := by
  unfold tailWord_4423738
  simp only [CollatzResearch.WordTrace]
  refine ⟨40336745011890053786485967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107564653365040143430629245 40336745011890053786485967)
  ·
    refine ⟨60505117517835080679728951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40336745011890053786485967 60505117517835080679728951)
    ·
      refine ⟨90757676276752621019593427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60505117517835080679728951 90757676276752621019593427)
      ·
        refine ⟨136136514415128931529390141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90757676276752621019593427 136136514415128931529390141)
        ·
          refine ⟨51051192905673349323521303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 136136514415128931529390141 51051192905673349323521303)
          ·
            refine ⟨76576789358510023985281955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51051192905673349323521303 76576789358510023985281955)
            ·
              refine ⟨114865184037765035977922933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76576789358510023985281955 114865184037765035977922933)
              ·
                refine ⟨10768611003540472122930275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 114865184037765035977922933 10768611003540472122930275)
                ·
                  refine ⟨16152916505310708184395413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10768611003540472122930275 16152916505310708184395413)
                  ·
                    refine ⟨757167961186439446143535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16152916505310708184395413 757167961186439446143535)
                    ·
                      rfl

theorem cell23_4423738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 5, 1, 6].length) (baseStart_4423738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4423738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4423738 prefixEnd_4423738 := by exact prefixLift 4423738
  have htrace : WordTrace (prefixWord ++ tailWord_4423738) baseStart_4423738 baseEnd_4423738 := by
    simpa [prefixWord, tailWord_4423738, baseEnd_4423738] using wordTrace_append hprefix tailTrace_4423738
  have hstable : (prefixWord ++ tailWord_4423738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4423738).length < 2 ^ (prefixWord ++ tailWord_4423738).sum := by decide
  have hdescent : baseEnd_4423738 < baseStart_4423738 := by decide
  rcases family_descends (prefixWord ++ tailWord_4423738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4423742 : List Nat := [4, 2, 1, 3, 2, 1, 1, 1, 3, 5]
def baseStart_4423742 : Nat := 118140960795 + 4423742 * 2 ^ 59
def prefixEnd_4423742 : Nat := 4983230072969 + 3 ^ 40 * 4423742 * 2
def baseEnd_4423742 : Nat := 757168645827312107593529

theorem tailTrace_4423742 : CollatzResearch.WordTrace tailWord_4423742 prefixEnd_4423742 757168645827312107593529 := by
  unfold tailWord_4423742
  simp only [CollatzResearch.WordTrace]
  refine ⟨20168390742443215478636185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107564750626363815886059653 20168390742443215478636185)
  ·
    refine ⟨15126293056832411608977139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20168390742443215478636185 15126293056832411608977139)
    ·
      refine ⟨22689439585248617413465709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15126293056832411608977139 22689439585248617413465709)
      ·
        refine ⟨8508539844468231530049641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22689439585248617413465709 8508539844468231530049641)
        ·
          refine ⟨6381404883351173647537231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8508539844468231530049641 6381404883351173647537231)
          ·
            refine ⟨9572107325026760471305847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6381404883351173647537231 9572107325026760471305847)
            ·
              refine ⟨14358160987540140706958771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9572107325026760471305847 14358160987540140706958771)
              ·
                refine ⟨21537241481310211060438157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14358160987540140706958771 21537241481310211060438157)
                ·
                  refine ⟨8076465555491329147664309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21537241481310211060438157 8076465555491329147664309)
                  ·
                    refine ⟨757168645827312107593529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8076465555491329147664309 757168645827312107593529)
                    ·
                      rfl

theorem cell23_4423742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 1, 3, 5].length) (baseStart_4423742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4423742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4423742 prefixEnd_4423742 := by exact prefixLift 4423742
  have htrace : WordTrace (prefixWord ++ tailWord_4423742) baseStart_4423742 baseEnd_4423742 := by
    simpa [prefixWord, tailWord_4423742, baseEnd_4423742] using wordTrace_append hprefix tailTrace_4423742
  have hstable : (prefixWord ++ tailWord_4423742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4423742).length < 2 ^ (prefixWord ++ tailWord_4423742).sum := by decide
  have hdescent : baseEnd_4423742 < baseStart_4423742 := by decide
  rcases family_descends (prefixWord ++ tailWord_4423742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4423765 : List Nat := [1, 3, 2, 2, 1, 3, 3, 1, 1, 1, 5]
def baseStart_4423765 : Nat := 118140960795 + 4423765 * 2 ^ 59
def prefixEnd_4423765 : Nat := 4983230072969 + 3 ^ 40 * 4423765 * 2
def baseEnd_4423765 : Nat := 2271517747536989732792981

theorem tailTrace_4423765 : CollatzResearch.WordTrace tailWord_4423765 prefixEnd_4423765 2271517747536989732792981 := by
  unfold tailWord_4423765
  simp only [CollatzResearch.WordTrace]
  refine ⟨161347964818462398757176749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107565309878974932504784499 161347964818462398757176749)
  ·
    refine ⟨60505486806923399533941281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 161347964818462398757176749 60505486806923399533941281)
    ·
      refine ⟨45379115105192549650455961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60505486806923399533941281 45379115105192549650455961)
      ·
        refine ⟨34034336328894412237841971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45379115105192549650455961 34034336328894412237841971)
        ·
          refine ⟨51051504493341618356762957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34034336328894412237841971 51051504493341618356762957)
          ·
            refine ⟨19144314185003106883786109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51051504493341618356762957 19144314185003106883786109)
            ·
              refine ⟨7179117819376165081419791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19144314185003106883786109 7179117819376165081419791)
              ·
                refine ⟨10768676729064247622129687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7179117819376165081419791 10768676729064247622129687)
                ·
                  refine ⟨16153015093596371433194531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10768676729064247622129687 16153015093596371433194531)
                  ·
                    refine ⟨24229522640394557149791797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16153015093596371433194531 24229522640394557149791797)
                    ·
                      refine ⟨2271517747536989732792981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24229522640394557149791797 2271517747536989732792981)
                      ·
                        rfl

theorem cell23_4423765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 1, 1, 1, 5].length) (baseStart_4423765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4423765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4423765 prefixEnd_4423765 := by exact prefixLift 4423765
  have htrace : WordTrace (prefixWord ++ tailWord_4423765) baseStart_4423765 baseEnd_4423765 := by
    simpa [prefixWord, tailWord_4423765, baseEnd_4423765] using wordTrace_append hprefix tailTrace_4423765
  have hstable : (prefixWord ++ tailWord_4423765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4423765).length < 2 ^ (prefixWord ++ tailWord_4423765).sum := by decide
  have hdescent : baseEnd_4423765 < baseStart_4423765 := by decide
  rcases family_descends (prefixWord ++ tailWord_4423765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4423766 : List Nat := [5, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2]
def baseStart_4423766 : Nat := 118140960795 + 4423766 * 2 ^ 59
def prefixEnd_4423766 : Nat := 4983230072969 + 3 ^ 40 * 4423766 * 2
def baseEnd_4423766 : Nat := 2271518261017644228880477

theorem tailTrace_4423766 : CollatzResearch.WordTrace tailWord_4423766 prefixEnd_4423766 2271518261017644228880477 := by
  unfold tailWord_4423766
  simp only [CollatzResearch.WordTrace]
  refine ⟨10084250080716173495497697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 107565334194305850618642101 10084250080716173495497697)
  ·
    refine ⟨7563187560537130121623273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10084250080716173495497697 7563187560537130121623273)
    ·
      refine ⟨5672390670402847591217455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7563187560537130121623273 5672390670402847591217455)
      ·
        refine ⟨8508586005604271386826183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5672390670402847591217455 8508586005604271386826183)
        ·
          refine ⟨12762879008406407080239275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8508586005604271386826183 12762879008406407080239275)
          ·
            refine ⟨19144318512609610620358913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12762879008406407080239275 19144318512609610620358913)
            ·
              refine ⟨14358238884457207965269185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19144318512609610620358913 14358238884457207965269185)
              ·
                refine ⟨10768679163342905973951889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14358238884457207965269185 10768679163342905973951889)
                ·
                  refine ⟨8076509372507179480463917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10768679163342905973951889 8076509372507179480463917)
                  ·
                    refine ⟨3028691014690192305173969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8076509372507179480463917 3028691014690192305173969)
                    ·
                      refine ⟨2271518261017644228880477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3028691014690192305173969 2271518261017644228880477)
                      ·
                        rfl

theorem cell23_4423766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_4423766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4423766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4423766 prefixEnd_4423766 := by exact prefixLift 4423766
  have htrace : WordTrace (prefixWord ++ tailWord_4423766) baseStart_4423766 baseEnd_4423766 := by
    simpa [prefixWord, tailWord_4423766, baseEnd_4423766] using wordTrace_append hprefix tailTrace_4423766
  have hstable : (prefixWord ++ tailWord_4423766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4423766).length < 2 ^ (prefixWord ++ tailWord_4423766).sum := by decide
  have hdescent : baseEnd_4423766 < baseStart_4423766 := by decide
  rcases family_descends (prefixWord ++ tailWord_4423766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4423772 : List Nat := [2, 2, 4, 1, 1, 2, 1, 4, 2, 4]
def baseStart_4423772 : Nat := 118140960795 + 4423772 * 2 ^ 59
def prefixEnd_4423772 : Nat := 4983230072969 + 3 ^ 40 * 4423772 * 2
def baseEnd_4423772 : Nat := 757173780633857068468483

theorem tailTrace_4423772 : CollatzResearch.WordTrace tailWord_4423772 prefixEnd_4423772 757173780633857068468483 := by
  unfold tailWord_4423772
  simp only [CollatzResearch.WordTrace]
  refine ⟨80674110064718519476340785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107565480086291359301787713 80674110064718519476340785)
  ·
    refine ⟨60505582548538889607255589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80674110064718519476340785 60505582548538889607255589)
    ·
      refine ⟨11344796727851041801360423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60505582548538889607255589 11344796727851041801360423)
      ·
        refine ⟨17017195091776562702040635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11344796727851041801360423 17017195091776562702040635)
        ·
          refine ⟨25525792637664844053060953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17017195091776562702040635 25525792637664844053060953)
          ·
            refine ⟨19144344478248633039795715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25525792637664844053060953 19144344478248633039795715)
            ·
              refine ⟨28716516717372949559693573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19144344478248633039795715 28716516717372949559693573)
              ·
                refine ⟨5384346884507428042442545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28716516717372949559693573 5384346884507428042442545)
                ·
                  refine ⟨4038260163380571031831909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5384346884507428042442545 4038260163380571031831909)
                  ·
                    refine ⟨757173780633857068468483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4038260163380571031831909 757173780633857068468483)
                    ·
                      rfl

theorem cell23_4423772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_4423772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4423772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4423772 prefixEnd_4423772 := by exact prefixLift 4423772
  have htrace : WordTrace (prefixWord ++ tailWord_4423772) baseStart_4423772 baseEnd_4423772 := by
    simpa [prefixWord, tailWord_4423772, baseEnd_4423772] using wordTrace_append hprefix tailTrace_4423772
  have hstable : (prefixWord ++ tailWord_4423772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4423772).length < 2 ^ (prefixWord ++ tailWord_4423772).sum := by decide
  have hdescent : baseEnd_4423772 < baseStart_4423772 := by decide
  rcases family_descends (prefixWord ++ tailWord_4423772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4423773 : List Nat := [1, 4, 4, 1, 1, 1, 4, 2, 1, 1, 3]
def baseStart_4423773 : Nat := 118140960795 + 4423773 * 2 ^ 59
def prefixEnd_4423773 : Nat := 4983230072969 + 3 ^ 40 * 4423773 * 2
def baseEnd_4423773 : Nat := 2271521855382225701492945

theorem tailTrace_4423773 : CollatzResearch.WordTrace tailWord_4423773 prefixEnd_4423773 2271521855382225701492945 := by
  unfold tailWord_4423773
  simp only [CollatzResearch.WordTrace]
  refine ⟨161348256602433416123467973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107565504401622277415645315 161348256602433416123467973)
  ·
    refine ⟨30252798112956265523150245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 161348256602433416123467973 30252798112956265523150245)
    ·
      refine ⟨5672399646179299785590671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30252798112956265523150245 5672399646179299785590671)
      ·
        refine ⟨8508599469268949678386007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5672399646179299785590671 8508599469268949678386007)
        ·
          refine ⟨12762899203903424517579011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8508599469268949678386007 12762899203903424517579011)
          ·
            refine ⟨19144348805855136776368517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12762899203903424517579011 19144348805855136776368517)
            ·
              refine ⟨3589565401097838145569097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19144348805855136776368517 3589565401097838145569097)
              ·
                refine ⟨2692174050823378609176823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3589565401097838145569097 2692174050823378609176823)
                ·
                  refine ⟨4038261076235067913765235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2692174050823378609176823 4038261076235067913765235)
                  ·
                    refine ⟨6057391614352601870647853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4038261076235067913765235 6057391614352601870647853)
                    ·
                      refine ⟨2271521855382225701492945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6057391614352601870647853 2271521855382225701492945)
                      ·
                        rfl

theorem cell23_4423773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_4423773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4423773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4423773 prefixEnd_4423773 := by exact prefixLift 4423773
  have htrace : WordTrace (prefixWord ++ tailWord_4423773) baseStart_4423773 baseEnd_4423773 := by
    simpa [prefixWord, tailWord_4423773, baseEnd_4423773] using wordTrace_append hprefix tailTrace_4423773
  have hstable : (prefixWord ++ tailWord_4423773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4423773).length < 2 ^ (prefixWord ++ tailWord_4423773).sum := by decide
  have hdescent : baseEnd_4423773 < baseStart_4423773 := by decide
  rcases family_descends (prefixWord ++ tailWord_4423773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4423808 : List Nat := [2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 5]
def baseStart_4423808 : Nat := 118140960795 + 4423808 * 2 ^ 59
def prefixEnd_4423808 : Nat := 4983230072969 + 3 ^ 40 * 4423808 * 2
def baseEnd_4423808 : Nat := 2271539827205133064555283

theorem tailTrace_4423808 : CollatzResearch.WordTrace tailWord_4423808 prefixEnd_4423808 2271539827205133064555283 := by
  unfold tailWord_4423808
  simp only [CollatzResearch.WordTrace]
  refine ⟨80674766578653308550496039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107566355438204411400661385 80674766578653308550496039)
  ·
    refine ⟨121012149867979962825744059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80674766578653308550496039 121012149867979962825744059)
    ·
      refine ⟨181518224801969944238616089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121012149867979962825744059 181518224801969944238616089)
      ·
        refine ⟨136138668601477458178962067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 181518224801969944238616089 136138668601477458178962067)
        ·
          refine ⟨204208002902216187268443101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136138668601477458178962067 204208002902216187268443101)
          ·
            refine ⟨76578001088331070225666163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 204208002902216187268443101 76578001088331070225666163)
            ·
              refine ⟨114867001632496605338499245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76578001088331070225666163 114867001632496605338499245)
              ·
                refine ⟨43075125612186227001937217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 114867001632496605338499245 43075125612186227001937217)
                ·
                  refine ⟨32306344209139670251452913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43075125612186227001937217 32306344209139670251452913)
                  ·
                    refine ⟨24229758156854752688589685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32306344209139670251452913 24229758156854752688589685)
                    ·
                      refine ⟨2271539827205133064555283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24229758156854752688589685 2271539827205133064555283)
                      ·
                        rfl

theorem cell23_4423808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 5].length) (baseStart_4423808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4423808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4423808 prefixEnd_4423808 := by exact prefixLift 4423808
  have htrace : WordTrace (prefixWord ++ tailWord_4423808) baseStart_4423808 baseEnd_4423808 := by
    simpa [prefixWord, tailWord_4423808, baseEnd_4423808] using wordTrace_append hprefix tailTrace_4423808
  have hstable : (prefixWord ++ tailWord_4423808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4423808).length < 2 ^ (prefixWord ++ tailWord_4423808).sum := by decide
  have hdescent : baseEnd_4423808 < baseStart_4423808 := by decide
  rcases family_descends (prefixWord ++ tailWord_4423808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4423812 : List Nat := [2, 3, 2, 1, 2, 1, 2, 2, 4, 1, 3]
def baseStart_4423812 : Nat := 118140960795 + 4423812 * 2 ^ 59
def prefixEnd_4423812 : Nat := 4983230072969 + 3 ^ 40 * 4423812 * 2
def baseEnd_4423812 : Nat := 2271541881127751048905265

theorem tailTrace_4423812 : CollatzResearch.WordTrace tailWord_4423812 prefixEnd_4423812 2271541881127751048905265 := by
  unfold tailWord_4423812
  simp only [CollatzResearch.WordTrace]
  refine ⟨80674839524646062892068845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107566452699528083856091793 80674839524646062892068845)
  ·
    refine ⟨30253064821742273584525817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80674839524646062892068845 30253064821742273584525817)
    ·
      refine ⟨22689798616306705188394363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30253064821742273584525817 22689798616306705188394363)
      ·
        refine ⟨34034697924460057782591545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22689798616306705188394363 34034697924460057782591545)
        ·
          refine ⟨25526023443345043336943659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34034697924460057782591545 25526023443345043336943659)
          ·
            refine ⟨38289035165017565005415489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25526023443345043336943659 38289035165017565005415489)
            ·
              refine ⟨28716776373763173754061617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38289035165017565005415489 28716776373763173754061617)
              ·
                refine ⟨21537582280322380315546213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28716776373763173754061617 21537582280322380315546213)
                ·
                  refine ⟨4038296677560446309164915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21537582280322380315546213 4038296677560446309164915)
                  ·
                    refine ⟨6057445016340669463747373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4038296677560446309164915 6057445016340669463747373)
                    ·
                      refine ⟨2271541881127751048905265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6057445016340669463747373 2271541881127751048905265)
                      ·
                        rfl

theorem cell23_4423812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 2, 4, 1, 3].length) (baseStart_4423812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4423812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4423812 prefixEnd_4423812 := by exact prefixLift 4423812
  have htrace : WordTrace (prefixWord ++ tailWord_4423812) baseStart_4423812 baseEnd_4423812 := by
    simpa [prefixWord, tailWord_4423812, baseEnd_4423812] using wordTrace_append hprefix tailTrace_4423812
  have hstable : (prefixWord ++ tailWord_4423812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4423812).length < 2 ^ (prefixWord ++ tailWord_4423812).sum := by decide
  have hdescent : baseEnd_4423812 < baseStart_4423812 := by decide
  rcases family_descends (prefixWord ++ tailWord_4423812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4423816 : List Nat := [2, 1, 3, 4, 1, 3, 2, 1, 1, 2, 3]
def baseStart_4423816 : Nat := 118140960795 + 4423816 * 2 ^ 59
def prefixEnd_4423816 : Nat := 4983230072969 + 3 ^ 40 * 4423816 * 2
def baseEnd_4423816 : Nat := 2271543935050369033255247

theorem tailTrace_4423816 : CollatzResearch.WordTrace tailWord_4423816 prefixEnd_4423816 2271543935050369033255247 := by
  unfold tailWord_4423816
  simp only [CollatzResearch.WordTrace]
  refine ⟨80674912470638817233641651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107566549960851756311522201 80674912470638817233641651)
  ·
    refine ⟨121012368705958225850462477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80674912470638817233641651 121012368705958225850462477)
    ·
      refine ⟨45379638264734334693923429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121012368705958225850462477 45379638264734334693923429)
      ·
        refine ⟨8508682174637687755110643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45379638264734334693923429 8508682174637687755110643)
        ·
          refine ⟨12763023261956531632665965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8508682174637687755110643 12763023261956531632665965)
          ·
            refine ⟨4786133723233699362249737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12763023261956531632665965 4786133723233699362249737)
            ·
              refine ⟨3589600292425274521687303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4786133723233699362249737 3589600292425274521687303)
              ·
                refine ⟨5384400438637911782530955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3589600292425274521687303 5384400438637911782530955)
                ·
                  refine ⟨8076600657956867673796433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5384400438637911782530955 8076600657956867673796433)
                  ·
                    refine ⟨6057450493467650755347325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8076600657956867673796433 6057450493467650755347325)
                    ·
                      refine ⟨2271543935050369033255247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6057450493467650755347325 2271543935050369033255247)
                      ·
                        rfl

theorem cell23_4423816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_4423816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4423816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4423816 prefixEnd_4423816 := by exact prefixLift 4423816
  have htrace : WordTrace (prefixWord ++ tailWord_4423816) baseStart_4423816 baseEnd_4423816 := by
    simpa [prefixWord, tailWord_4423816, baseEnd_4423816] using wordTrace_append hprefix tailTrace_4423816
  have hstable : (prefixWord ++ tailWord_4423816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4423816).length < 2 ^ (prefixWord ++ tailWord_4423816).sum := by decide
  have hdescent : baseEnd_4423816 < baseStart_4423816 := by decide
  rcases family_descends (prefixWord ++ tailWord_4423816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4423888 : List Nat := [2, 1, 1, 1, 1, 2, 1, 1, 2, 11]
def baseStart_4423888 : Nat := 118140960795 + 4423888 * 2 ^ 59
def prefixEnd_4423888 : Nat := 4983230072969 + 3 ^ 40 * 4423888 * 2
def baseEnd_4423888 : Nat := 757193635219164250518305

theorem tailTrace_4423888 : CollatzResearch.WordTrace tailWord_4423888 prefixEnd_4423888 757193635219164250518305 := by
  unfold tailWord_4423888
  simp only [CollatzResearch.WordTrace]
  refine ⟨80676225498508395381952159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107568300664677860509269545 80676225498508395381952159)
  ·
    refine ⟨121014338247762593072928239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80676225498508395381952159 121014338247762593072928239)
    ·
      refine ⟨181521507371643889609392359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121014338247762593072928239 181521507371643889609392359)
      ·
        refine ⟨272282261057465834414088539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181521507371643889609392359 272282261057465834414088539)
        ·
          refine ⟨408423391586198751621132809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 272282261057465834414088539 408423391586198751621132809)
          ·
            refine ⟨306317543689649063715849607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 408423391586198751621132809 306317543689649063715849607)
            ·
              refine ⟨459476315534473595573774411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 306317543689649063715849607 459476315534473595573774411)
              ·
                refine ⟨689214473301710393360661617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 459476315534473595573774411 689214473301710393360661617)
                ·
                  refine ⟨516910854976282795020496213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 689214473301710393360661617 516910854976282795020496213)
                  ·
                    refine ⟨757193635219164250518305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 516910854976282795020496213 757193635219164250518305)
                    ·
                      rfl

theorem cell23_4423888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 2, 11].length) (baseStart_4423888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4423888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4423888 prefixEnd_4423888 := by exact prefixLift 4423888
  have htrace : WordTrace (prefixWord ++ tailWord_4423888) baseStart_4423888 baseEnd_4423888 := by
    simpa [prefixWord, tailWord_4423888, baseEnd_4423888] using wordTrace_append hprefix tailTrace_4423888
  have hstable : (prefixWord ++ tailWord_4423888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4423888).length < 2 ^ (prefixWord ++ tailWord_4423888).sum := by decide
  have hdescent : baseEnd_4423888 < baseStart_4423888 := by decide
  rcases family_descends (prefixWord ++ tailWord_4423888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4423905 : List Nat := [1, 2, 3, 1, 3, 1, 1, 2, 4, 5]
def baseStart_4423905 : Nat := 118140960795 + 4423905 * 2 ^ 59
def prefixEnd_4423905 : Nat := 4983230072969 + 3 ^ 40 * 4423905 * 2
def baseEnd_4423905 : Nat := 757196544942873061680779

theorem tailTrace_4423905 : CollatzResearch.WordTrace tailWord_4423905 prefixEnd_4423905 757196544942873061680779 := by
  unfold tailWord_4423905
  simp only [CollatzResearch.WordTrace]
  refine ⟨161353071037955202667273169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107568714025303468444848779 161353071037955202667273169)
  ·
    refine ⟨121014803278466402000454877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161353071037955202667273169 121014803278466402000454877)
    ·
      refine ⟨45380551229424900750170579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121014803278466402000454877 45380551229424900750170579)
      ·
        refine ⟨68070826844137351125255869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45380551229424900750170579 68070826844137351125255869)
        ·
          refine ⟨25526560066551506671970951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68070826844137351125255869 25526560066551506671970951)
          ·
            refine ⟨38289840099827260007956427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25526560066551506671970951 38289840099827260007956427)
            ·
              refine ⟨57434760149740890011934641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38289840099827260007956427 57434760149740890011934641)
              ·
                refine ⟨43076070112305667508950981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57434760149740890011934641 43076070112305667508950981)
                ·
                  refine ⟨8076763146057312657928309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43076070112305667508950981 8076763146057312657928309)
                  ·
                    refine ⟨757196544942873061680779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8076763146057312657928309 757196544942873061680779)
                    ·
                      rfl

theorem cell23_4423905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 4, 5].length) (baseStart_4423905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4423905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4423905 prefixEnd_4423905 := by exact prefixLift 4423905
  have htrace : WordTrace (prefixWord ++ tailWord_4423905) baseStart_4423905 baseEnd_4423905 := by
    simpa [prefixWord, tailWord_4423905, baseEnd_4423905] using wordTrace_append hprefix tailTrace_4423905
  have hstable : (prefixWord ++ tailWord_4423905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4423905).length < 2 ^ (prefixWord ++ tailWord_4423905).sum := by decide
  have hdescent : baseEnd_4423905 < baseStart_4423905 := by decide
  rcases family_descends (prefixWord ++ tailWord_4423905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4423922 : List Nat := [3, 2, 1, 3, 2, 1, 1, 3, 2, 5]
def baseStart_4423922 : Nat := 118140960795 + 4423922 * 2 ^ 59
def prefixEnd_4423922 : Nat := 4983230072969 + 3 ^ 40 * 4423922 * 2
def baseEnd_4423922 : Nat := 757199454666581872843253

theorem tailTrace_4423922 : CollatzResearch.WordTrace tailWord_4423922 prefixEnd_4423922 757199454666581872843253 := by
  unfold tailWord_4423922
  simp only [CollatzResearch.WordTrace]
  refine ⟨40338422769723403642660505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107569127385929076380428013 40338422769723403642660505)
  ·
    refine ⟨30253817077292552731995379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40338422769723403642660505 30253817077292552731995379)
    ·
      refine ⟨45380725615938829097993069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30253817077292552731995379 45380725615938829097993069)
      ·
        refine ⟨17017772105977060911747401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45380725615938829097993069 17017772105977060911747401)
        ·
          refine ⟨12763329079482795683810551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17017772105977060911747401 12763329079482795683810551)
          ·
            refine ⟨19144993619224193525715827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12763329079482795683810551 19144993619224193525715827)
            ·
              refine ⟨28717490428836290288573741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19144993619224193525715827 28717490428836290288573741)
              ·
                refine ⟨10769058910813608858215153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28717490428836290288573741 10769058910813608858215153)
                ·
                  refine ⟨8076794183110206643661365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10769058910813608858215153 8076794183110206643661365)
                  ·
                    refine ⟨757199454666581872843253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8076794183110206643661365 757199454666581872843253)
                    ·
                      rfl

theorem cell23_4423922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 3, 2, 5].length) (baseStart_4423922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4423922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4423922 prefixEnd_4423922 := by exact prefixLift 4423922
  have htrace : WordTrace (prefixWord ++ tailWord_4423922) baseStart_4423922 baseEnd_4423922 := by
    simpa [prefixWord, tailWord_4423922, baseEnd_4423922] using wordTrace_append hprefix tailTrace_4423922
  have hstable : (prefixWord ++ tailWord_4423922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4423922).length < 2 ^ (prefixWord ++ tailWord_4423922).sum := by decide
  have hdescent : baseEnd_4423922 < baseStart_4423922 := by decide
  rcases family_descends (prefixWord ++ tailWord_4423922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4423943 : List Nat := [1, 1, 4, 5, 1, 2, 2, 2, 5]
def baseStart_4423943 : Nat := 118140960795 + 4423943 * 2 ^ 59
def prefixEnd_4423943 : Nat := 4983230072969 + 3 ^ 40 * 4423943 * 2
def baseEnd_4423943 : Nat := 252401016343721115151907

theorem tailTrace_4423943 : CollatzResearch.WordTrace tailWord_4423943 prefixEnd_4423943 252401016343721115151907 := by
  unfold tailWord_4423943
  simp only [CollatzResearch.WordTrace]
  refine ⟨161354457011817535157156483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107569638007878356771437655 161354457011817535157156483)
  ·
    refine ⟨242031685517726302735734725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161354457011817535157156483 242031685517726302735734725)
    ·
      refine ⟨45380941034573681762950261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 242031685517726302735734725 45380941034573681762950261)
      ·
        refine ⟨4254463221991282665276587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45380941034573681762950261 4254463221991282665276587)
        ·
          refine ⟨6381694832986923997914881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4254463221991282665276587 6381694832986923997914881)
          ·
            refine ⟨4786271124740192998436161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6381694832986923997914881 4786271124740192998436161)
            ·
              refine ⟨3589703343555144748827121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4786271124740192998436161 3589703343555144748827121)
              ·
                refine ⟨2692277507666358561620341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3589703343555144748827121 2692277507666358561620341)
                ·
                  refine ⟨252401016343721115151907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2692277507666358561620341 252401016343721115151907)
                  ·
                    rfl

theorem cell23_4423943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 2, 2, 5].length) (baseStart_4423943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4423943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4423943 prefixEnd_4423943 := by exact prefixLift 4423943
  have htrace : WordTrace (prefixWord ++ tailWord_4423943) baseStart_4423943 baseEnd_4423943 := by
    simpa [prefixWord, tailWord_4423943, baseEnd_4423943] using wordTrace_append hprefix tailTrace_4423943
  have hstable : (prefixWord ++ tailWord_4423943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4423943).length < 2 ^ (prefixWord ++ tailWord_4423943).sum := by decide
  have hdescent : baseEnd_4423943 < baseStart_4423943 := by decide
  rcases family_descends (prefixWord ++ tailWord_4423943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4423959 : List Nat := [1, 1, 3, 4, 1, 3, 1, 1, 2, 4, 2]
def baseStart_4423959 : Nat := 118140960795 + 4423959 * 2 ^ 59
def prefixEnd_4423959 : Nat := 4983230072969 + 3 ^ 40 * 4423959 * 2
def baseEnd_4423959 : Nat := 2271617362783961973767089

theorem tailTrace_4423959 : CollatzResearch.WordTrace tailWord_4423959 prefixEnd_4423959 2271617362783961973767089 := by
  unfold tailWord_4423959
  simp only [CollatzResearch.WordTrace]
  refine ⟨161355040579759569889738931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107570027053173046593159287 161355040579759569889738931)
  ·
    refine ⟨242032560869639354834608397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161355040579759569889738931 242032560869639354834608397)
    ·
      refine ⟨90762210326114758062978149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 242032560869639354834608397 90762210326114758062978149)
      ·
        refine ⟨17017914436146517136808403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 90762210326114758062978149 17017914436146517136808403)
        ·
          refine ⟨25526871654219775705212605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17017914436146517136808403 25526871654219775705212605)
          ·
            refine ⟨9572576870332415889454727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25526871654219775705212605 9572576870332415889454727)
            ·
              refine ⟨14358865305498623834182091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9572576870332415889454727 14358865305498623834182091)
              ·
                refine ⟨21538297958247935751273137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14358865305498623834182091 21538297958247935751273137)
                ·
                  refine ⟨16153723468685951813454853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21538297958247935751273137 16153723468685951813454853)
                  ·
                    refine ⟨3028823150378615965022785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16153723468685951813454853 3028823150378615965022785)
                    ·
                      refine ⟨2271617362783961973767089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3028823150378615965022785 2271617362783961973767089)
                      ·
                        rfl

theorem cell23_4423959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 1, 2, 4, 2].length) (baseStart_4423959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4423959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4423959 prefixEnd_4423959 := by exact prefixLift 4423959
  have htrace : WordTrace (prefixWord ++ tailWord_4423959) baseStart_4423959 baseEnd_4423959 := by
    simpa [prefixWord, tailWord_4423959, baseEnd_4423959] using wordTrace_append hprefix tailTrace_4423959
  have hstable : (prefixWord ++ tailWord_4423959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4423959).length < 2 ^ (prefixWord ++ tailWord_4423959).sum := by decide
  have hdescent : baseEnd_4423959 < baseStart_4423959 := by decide
  rcases family_descends (prefixWord ++ tailWord_4423959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4423976 : List Nat := [2, 1, 5, 1, 3, 2, 1, 1, 2, 1, 4]
def baseStart_4423976 : Nat := 118140960795 + 4423976 * 2 ^ 59
def prefixEnd_4423976 : Nat := 4983230072969 + 3 ^ 40 * 4423976 * 2
def baseEnd_4423976 : Nat := 2271626091955088407254511

theorem tailTrace_4423976 : CollatzResearch.WordTrace tailWord_4423976 prefixEnd_4423976 2271626091955088407254511 := by
  unfold tailWord_4423976
  simp only [CollatzResearch.WordTrace]
  refine ⟨80677830310348990896553891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107570440413798654528738521 80677830310348990896553891)
  ·
    refine ⟨121016745465523486344830837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80677830310348990896553891 121016745465523486344830837)
    ·
      refine ⟨11345319887392826844827891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 121016745465523486344830837 11345319887392826844827891)
      ·
        refine ⟨17017979831089240267241837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11345319887392826844827891 17017979831089240267241837)
        ·
          refine ⟨6381742436658465100215689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17017979831089240267241837 6381742436658465100215689)
          ·
            refine ⟨4786306827493848825161767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6381742436658465100215689 4786306827493848825161767)
            ·
              refine ⟨7179460241240773237742651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4786306827493848825161767 7179460241240773237742651)
              ·
                refine ⟨10769190361861159856613977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7179460241240773237742651 10769190361861159856613977)
                ·
                  refine ⟨8076892771395869892460483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10769190361861159856613977 8076892771395869892460483)
                  ·
                    refine ⟨12115339157093804838690725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8076892771395869892460483 12115339157093804838690725)
                    ·
                      refine ⟨2271626091955088407254511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12115339157093804838690725 2271626091955088407254511)
                      ·
                        rfl

theorem cell23_4423976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_4423976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4423976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4423976 prefixEnd_4423976 := by exact prefixLift 4423976
  have htrace : WordTrace (prefixWord ++ tailWord_4423976) baseStart_4423976 baseEnd_4423976 := by
    simpa [prefixWord, tailWord_4423976, baseEnd_4423976] using wordTrace_append hprefix tailTrace_4423976
  have hstable : (prefixWord ++ tailWord_4423976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4423976).length < 2 ^ (prefixWord ++ tailWord_4423976).sum := by decide
  have hdescent : baseEnd_4423976 < baseStart_4423976 := by decide
  rcases family_descends (prefixWord ++ tailWord_4423976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4424015 : List Nat := [1, 1, 2, 1, 1, 2, 1, 3, 2, 5, 4]
def baseStart_4424015 : Nat := 118140960795 + 4424015 * 2 ^ 59
def prefixEnd_4424015 : Nat := 4983230072969 + 3 ^ 40 * 4424015 * 2
def baseEnd_4424015 : Nat := 2271646117700613754666831

theorem tailTrace_4424015 : CollatzResearch.WordTrace tailWord_4424015 prefixEnd_4424015 2271646117700613754666831 := by
  unfold tailWord_4424015
  simp only [CollatzResearch.WordTrace]
  refine ⟨161357083067556691453777499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107571388711704460969184999 161357083067556691453777499)
  ·
    refine ⟨242035624601335037180666249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161357083067556691453777499 242035624601335037180666249)
    ·
      refine ⟨181526718451001277885499687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 242035624601335037180666249 181526718451001277885499687)
      ·
        refine ⟨272290077676501916828249531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181526718451001277885499687 272290077676501916828249531)
        ·
          refine ⟨408435116514752875242374297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 272290077676501916828249531 408435116514752875242374297)
          ·
            refine ⟨306326337386064656431780723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 408435116514752875242374297 306326337386064656431780723)
            ·
              refine ⟨459489506079096984647671085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 306326337386064656431780723 459489506079096984647671085)
              ·
                refine ⟨172308564779661369242876657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 459489506079096984647671085 172308564779661369242876657)
                ·
                  refine ⟨129231423584746026932157493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 172308564779661369242876657 129231423584746026932157493)
                  ·
                    refine ⟨12115445961069940024889765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 129231423584746026932157493 12115445961069940024889765)
                    ·
                      refine ⟨2271646117700613754666831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12115445961069940024889765 2271646117700613754666831)
                      ·
                        rfl

theorem cell23_4424015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 5, 4].length) (baseStart_4424015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4424015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4424015 prefixEnd_4424015 := by exact prefixLift 4424015
  have htrace : WordTrace (prefixWord ++ tailWord_4424015) baseStart_4424015 baseEnd_4424015 := by
    simpa [prefixWord, tailWord_4424015, baseEnd_4424015] using wordTrace_append hprefix tailTrace_4424015
  have hstable : (prefixWord ++ tailWord_4424015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4424015).length < 2 ^ (prefixWord ++ tailWord_4424015).sum := by decide
  have hdescent : baseEnd_4424015 < baseStart_4424015 := by decide
  rcases family_descends (prefixWord ++ tailWord_4424015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4424072 : List Nat := [2, 1, 3, 3, 1, 1, 4, 8]
def baseStart_4424072 : Nat := 118140960795 + 4424072 * 2 ^ 59
def prefixEnd_4424072 : Nat := 4983230072969 + 3 ^ 40 * 4424072 * 2
def baseEnd_4424072 : Nat := 84136125411034075246447

theorem tailTrace_4424072 : CollatzResearch.WordTrace tailWord_4424072 prefixEnd_4424072 84136125411034075246447 := by
  unfold tailWord_4424072
  simp only [CollatzResearch.WordTrace]
  refine ⟨80679581014175095094301235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107572774685566793459068313 80679581014175095094301235)
  ·
    refine ⟨121019371521262642641451853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80679581014175095094301235 121019371521262642641451853)
    ·
      refine ⟨45382264320473490990544445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121019371521262642641451853 45382264320473490990544445)
      ·
        refine ⟨17018349120177559121454167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45382264320473490990544445 17018349120177559121454167)
        ·
          refine ⟨25527523680266338682181251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17018349120177559121454167 25527523680266338682181251)
          ·
            refine ⟨38291285520399508023271877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25527523680266338682181251 38291285520399508023271877)
            ·
              refine ⟨7179616035074907754363477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38291285520399508023271877 7179616035074907754363477)
              ·
                refine ⟨84136125411034075246447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7179616035074907754363477 84136125411034075246447)
                ·
                  rfl

theorem cell23_4424072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 8].length) (baseStart_4424072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4424072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4424072 prefixEnd_4424072 := by exact prefixLift 4424072
  have htrace : WordTrace (prefixWord ++ tailWord_4424072) baseStart_4424072 baseEnd_4424072 := by
    simpa [prefixWord, tailWord_4424072, baseEnd_4424072] using wordTrace_append hprefix tailTrace_4424072
  have hstable : (prefixWord ++ tailWord_4424072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4424072).length < 2 ^ (prefixWord ++ tailWord_4424072).sum := by decide
  have hdescent : baseEnd_4424072 < baseStart_4424072 := by decide
  rcases family_descends (prefixWord ++ tailWord_4424072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4424076 : List Nat := [2, 2, 1, 2, 1, 4, 4, 1, 2, 4]
def baseStart_4424076 : Nat := 118140960795 + 4424076 * 2 ^ 59
def prefixEnd_4424076 : Nat := 4983230072969 + 3 ^ 40 * 4424076 * 2
def baseEnd_4424076 : Nat := 757225813340179338668017

theorem tailTrace_4424076 : CollatzResearch.WordTrace tailWord_4424076 prefixEnd_4424076 757225813340179338668017 := by
  unfold tailWord_4424076
  simp only [CollatzResearch.WordTrace]
  refine ⟨80679653960167849435874041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107572871946890465914498721 80679653960167849435874041)
  ·
    refine ⟨60509740470125887076905531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80679653960167849435874041 60509740470125887076905531)
    ·
      refine ⟨90764610705188830615358297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60509740470125887076905531 90764610705188830615358297)
      ·
        refine ⟨68073458028891622961518723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90764610705188830615358297 68073458028891622961518723)
        ·
          refine ⟨102110187043337434442278085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68073458028891622961518723 102110187043337434442278085)
          ·
            refine ⟨19145660070625768957927141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 102110187043337434442278085 19145660070625768957927141)
            ·
              refine ⟨3589811263242331679611339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19145660070625768957927141 3589811263242331679611339)
              ·
                refine ⟨5384716894863497519417009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3589811263242331679611339 5384716894863497519417009)
                ·
                  refine ⟨4038537671147623139562757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5384716894863497519417009 4038537671147623139562757)
                  ·
                    refine ⟨757225813340179338668017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4038537671147623139562757 757225813340179338668017)
                    ·
                      rfl

theorem cell23_4424076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 4, 1, 2, 4].length) (baseStart_4424076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4424076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4424076 prefixEnd_4424076 := by exact prefixLift 4424076
  have htrace : WordTrace (prefixWord ++ tailWord_4424076) baseStart_4424076 baseEnd_4424076 := by
    simpa [prefixWord, tailWord_4424076, baseEnd_4424076] using wordTrace_append hprefix tailTrace_4424076
  have hstable : (prefixWord ++ tailWord_4424076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4424076).length < 2 ^ (prefixWord ++ tailWord_4424076).sum := by decide
  have hdescent : baseEnd_4424076 < baseStart_4424076 := by decide
  rcases family_descends (prefixWord ++ tailWord_4424076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4424099 : List Nat := [1, 1, 1, 4, 1, 5, 1, 2, 1, 3, 3]
def baseStart_4424099 : Nat := 118140960795 + 4424099 * 2 ^ 59
def prefixEnd_4424099 : Nat := 4983230072969 + 3 ^ 40 * 4424099 * 2
def baseEnd_4424099 : Nat := 2271689250075591426016445

theorem tailTrace_4424099 : CollatzResearch.WordTrace tailWord_4424099 prefixEnd_4424099 2271689250075591426016445 := by
  unfold tailWord_4424099
  simp only [CollatzResearch.WordTrace]
  refine ⟨161360146799252373799835351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107573431199501582533223567 161360146799252373799835351)
  ·
    refine ⟨242040220198878560699753027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161360146799252373799835351 242040220198878560699753027)
    ·
      refine ⟨363060330298317841049629541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242040220198878560699753027 363060330298317841049629541)
      ·
        refine ⟨68073811930934595196805539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 363060330298317841049629541 68073811930934595196805539)
        ·
          refine ⟨102110717896401892795208309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68073811930934595196805539 102110717896401892795208309)
          ·
            refine ⟨9572879802787677449550779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 102110717896401892795208309 9572879802787677449550779)
            ·
              refine ⟨14359319704181516174326169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9572879802787677449550779 14359319704181516174326169)
              ·
                refine ⟨10769489778136137130744627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14359319704181516174326169 10769489778136137130744627)
                ·
                  refine ⟨16154234667204205696116941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10769489778136137130744627 16154234667204205696116941)
                  ·
                    refine ⟨6057838000201577136043853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16154234667204205696116941 6057838000201577136043853)
                    ·
                      refine ⟨2271689250075591426016445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6057838000201577136043853 2271689250075591426016445)
                      ·
                        rfl

theorem cell23_4424099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 2, 1, 3, 3].length) (baseStart_4424099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4424099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4424099 prefixEnd_4424099 := by exact prefixLift 4424099
  have htrace : WordTrace (prefixWord ++ tailWord_4424099) baseStart_4424099 baseEnd_4424099 := by
    simpa [prefixWord, tailWord_4424099, baseEnd_4424099] using wordTrace_append hprefix tailTrace_4424099
  have hstable : (prefixWord ++ tailWord_4424099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4424099).length < 2 ^ (prefixWord ++ tailWord_4424099).sum := by decide
  have hdescent : baseEnd_4424099 < baseStart_4424099 := by decide
  rcases family_descends (prefixWord ++ tailWord_4424099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4424103 : List Nat := [1, 1, 6, 1, 1, 3, 3, 1, 1, 2, 3]
def baseStart_4424103 : Nat := 118140960795 + 4424103 * 2 ^ 59
def prefixEnd_4424103 : Nat := 4983230072969 + 3 ^ 40 * 4424103 * 2
def baseEnd_4424103 : Nat := 2271691303998209410366427

theorem tailTrace_4424103 : CollatzResearch.WordTrace tailWord_4424103 prefixEnd_4424103 2271691303998209410366427 := by
  unfold tailWord_4424103
  simp only [CollatzResearch.WordTrace]
  refine ⟨161360292691237882482980963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107573528460825254988653975 161360292691237882482980963)
  ·
    refine ⟨242040439036856823724471445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161360292691237882482980963 242040439036856823724471445)
    ·
      refine ⟨11345645579852663612084599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 242040439036856823724471445 11345645579852663612084599)
      ·
        refine ⟨17018468369778995418126899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11345645579852663612084599 17018468369778995418126899)
        ·
          refine ⟨25527702554668493127190349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17018468369778995418126899 25527702554668493127190349)
          ·
            refine ⟨9572888458000684922696381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25527702554668493127190349 9572888458000684922696381)
            ·
              refine ⟨3589833171750256846011143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9572888458000684922696381 3589833171750256846011143)
              ·
                refine ⟨5384749757625385269016715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3589833171750256846011143 5384749757625385269016715)
                ·
                  refine ⟨8077124636438077903525073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5384749757625385269016715 8077124636438077903525073)
                  ·
                    refine ⟨6057843477328558427643805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8077124636438077903525073 6057843477328558427643805)
                    ·
                      refine ⟨2271691303998209410366427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6057843477328558427643805 2271691303998209410366427)
                      ·
                        rfl

theorem cell23_4424103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 3, 1, 1, 2, 3].length) (baseStart_4424103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4424103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4424103 prefixEnd_4424103 := by exact prefixLift 4424103
  have htrace : WordTrace (prefixWord ++ tailWord_4424103) baseStart_4424103 baseEnd_4424103 := by
    simpa [prefixWord, tailWord_4424103, baseEnd_4424103] using wordTrace_append hprefix tailTrace_4424103
  have hstable : (prefixWord ++ tailWord_4424103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4424103).length < 2 ^ (prefixWord ++ tailWord_4424103).sum := by decide
  have hdescent : baseEnd_4424103 < baseStart_4424103 := by decide
  rcases family_descends (prefixWord ++ tailWord_4424103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4424106 : List Nat := [3, 1, 6, 1, 1, 11]
def baseStart_4424106 : Nat := 118140960795 + 4424106 * 2 ^ 59
def prefixEnd_4424106 : Nat := 4983230072969 + 3 ^ 40 * 4424106 * 2
def baseEnd_4424106 : Nat := 9348530224033633327691

theorem tailTrace_4424106 : CollatzResearch.WordTrace tailWord_4424106 prefixEnd_4424106 9348530224033633327691 := by
  unfold tailWord_4424106
  simp only [CollatzResearch.WordTrace]
  refine ⟨40340100527556753498835043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107573601406818009330226781 40340100527556753498835043)
  ·
    refine ⟨60510150791335130248252565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40340100527556753498835043 60510150791335130248252565)
    ·
      refine ⟨2836413318343834230386839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 60510150791335130248252565 2836413318343834230386839)
      ·
        refine ⟨4254619977515751345580259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2836413318343834230386839 4254619977515751345580259)
        ·
          refine ⟨6381929966273627018370389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4254619977515751345580259 6381929966273627018370389)
          ·
            refine ⟨9348530224033633327691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 6381929966273627018370389 9348530224033633327691)
            ·
              rfl

theorem cell23_4424106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 11].length) (baseStart_4424106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4424106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4424106 prefixEnd_4424106 := by exact prefixLift 4424106
  have htrace : WordTrace (prefixWord ++ tailWord_4424106) baseStart_4424106 baseEnd_4424106 := by
    simpa [prefixWord, tailWord_4424106, baseEnd_4424106] using wordTrace_append hprefix tailTrace_4424106
  have hstable : (prefixWord ++ tailWord_4424106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4424106).length < 2 ^ (prefixWord ++ tailWord_4424106).sum := by decide
  have hdescent : baseEnd_4424106 < baseStart_4424106 := by decide
  rcases family_descends (prefixWord ++ tailWord_4424106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4424126 : List Nat := [4, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2]
def baseStart_4424126 : Nat := 118140960795 + 4424126 * 2 ^ 59
def prefixEnd_4424126 : Nat := 4983230072969 + 3 ^ 40 * 4424126 * 2
def baseEnd_4424126 : Nat := 2271703114053262820378821

theorem tailTrace_4424126 : CollatzResearch.WordTrace tailWord_4424126 prefixEnd_4424126 2271703114053262820378821 := by
  unfold tailWord_4424126
  simp only [CollatzResearch.WordTrace]
  refine ⟨20170141446269319676383529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107574087713436371607378821 20170141446269319676383529)
  ·
    refine ⟨15127606084701989757287647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20170141446269319676383529 15127606084701989757287647)
    ·
      refine ⟨22691409127052984635931471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15127606084701989757287647 22691409127052984635931471)
      ·
        refine ⟨34037113690579476953897207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22691409127052984635931471 34037113690579476953897207)
        ·
          refine ⟨51055670535869215430845811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34037113690579476953897207 51055670535869215430845811)
          ·
            refine ⟨76583505803803823146268717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51055670535869215430845811 76583505803803823146268717)
            ·
              refine ⟨28718814676426433679850769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76583505803803823146268717 28718814676426433679850769)
              ·
                refine ⟨21539111007319825259888077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28718814676426433679850769 21539111007319825259888077)
                ·
                  refine ⟨8077166627744934472458029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21539111007319825259888077 8077166627744934472458029)
                  ·
                    refine ⟨3028937485404350427171761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8077166627744934472458029 3028937485404350427171761)
                    ·
                      refine ⟨2271703114053262820378821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3028937485404350427171761 2271703114053262820378821)
                      ·
                        rfl

theorem cell23_4424126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2].length) (baseStart_4424126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4424126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4424126 prefixEnd_4424126 := by exact prefixLift 4424126
  have htrace : WordTrace (prefixWord ++ tailWord_4424126) baseStart_4424126 baseEnd_4424126 := by
    simpa [prefixWord, tailWord_4424126, baseEnd_4424126] using wordTrace_append hprefix tailTrace_4424126
  have hstable : (prefixWord ++ tailWord_4424126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4424126).length < 2 ^ (prefixWord ++ tailWord_4424126).sum := by decide
  have hdescent : baseEnd_4424126 < baseStart_4424126 := by decide
  rcases family_descends (prefixWord ++ tailWord_4424126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4424152 : List Nat := [2, 1, 2, 2, 2, 1, 1, 1, 3, 4, 4]
def baseStart_4424152 : Nat := 118140960795 + 4424152 * 2 ^ 59
def prefixEnd_4424152 : Nat := 4983230072969 + 3 ^ 40 * 4424152 * 2
def baseEnd_4424152 : Nat := 2271716464550279718653701

theorem tailTrace_4424152 : CollatzResearch.WordTrace tailWord_4424152 prefixEnd_4424152 2271716464550279718653701 := by
  unfold tailWord_4424152
  simp only [CollatzResearch.WordTrace]
  refine ⟨80681039934030181925757355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107574719912040242567676473 80681039934030181925757355)
  ·
    refine ⟨121021559901045272888636033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80681039934030181925757355 121021559901045272888636033)
    ·
      refine ⟨90766169925783954666477025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121021559901045272888636033 90766169925783954666477025)
      ·
        refine ⟨68074627444337965999857769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90766169925783954666477025 68074627444337965999857769)
        ·
          refine ⟨51055970583253474499893327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68074627444337965999857769 51055970583253474499893327)
          ·
            refine ⟨76583955874880211749839991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51055970583253474499893327 76583955874880211749839991)
            ·
              refine ⟨114875933812320317624759987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76583955874880211749839991 114875933812320317624759987)
              ·
                refine ⟨172313900718480476437139981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114875933812320317624759987 172313900718480476437139981)
                ·
                  refine ⟨64617712769430178663927493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 172313900718480476437139981 64617712769430178663927493)
                  ·
                    refine ⟨12115821144268158499486405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 64617712769430178663927493 12115821144268158499486405)
                    ·
                      refine ⟨2271716464550279718653701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12115821144268158499486405 2271716464550279718653701)
                      ·
                        rfl

theorem cell23_4424152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 3, 4, 4].length) (baseStart_4424152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4424152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4424152 prefixEnd_4424152 := by exact prefixLift 4424152
  have htrace : WordTrace (prefixWord ++ tailWord_4424152) baseStart_4424152 baseEnd_4424152 := by
    simpa [prefixWord, tailWord_4424152, baseEnd_4424152] using wordTrace_append hprefix tailTrace_4424152
  have hstable : (prefixWord ++ tailWord_4424152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4424152).length < 2 ^ (prefixWord ++ tailWord_4424152).sum := by decide
  have hdescent : baseEnd_4424152 < baseStart_4424152 := by decide
  rcases family_descends (prefixWord ++ tailWord_4424152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4424179 : List Nat := [1, 1, 1, 2, 2, 2, 3, 6, 5]
def baseStart_4424179 : Nat := 118140960795 + 4424179 * 2 ^ 59
def prefixEnd_4424179 : Nat := 4983230072969 + 3 ^ 40 * 4424179 * 2
def baseEnd_4424179 : Nat := 252414480947550123668453

theorem tailTrace_4424179 : CollatzResearch.WordTrace tailWord_4424179 prefixEnd_4424179 252414480947550123668453 := by
  unfold tailWord_4424179
  simp only [CollatzResearch.WordTrace]
  refine ⟨161363064638962547462747591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107575376425975031641831727 161363064638962547462747591)
  ·
    refine ⟨242044596958443821194121387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161363064638962547462747591 242044596958443821194121387)
    ·
      refine ⟨363066895437665731791182081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242044596958443821194121387 363066895437665731791182081)
      ·
        refine ⟨272300171578249298843386561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 363066895437665731791182081 272300171578249298843386561)
        ·
          refine ⟨204225128683686974132539921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 272300171578249298843386561 204225128683686974132539921)
          ·
            refine ⟨153168846512765230599404941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 204225128683686974132539921 153168846512765230599404941)
            ·
              refine ⟨57438317442286961474776853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 153168846512765230599404941 57438317442286961474776853)
              ·
                refine ⟨2692421130107201319130165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 57438317442286961474776853 2692421130107201319130165)
                ·
                  refine ⟨252414480947550123668453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2692421130107201319130165 252414480947550123668453)
                  ·
                    rfl

theorem cell23_4424179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 6, 5].length) (baseStart_4424179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4424179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4424179 prefixEnd_4424179 := by exact prefixLift 4424179
  have htrace : WordTrace (prefixWord ++ tailWord_4424179) baseStart_4424179 baseEnd_4424179 := by
    simpa [prefixWord, tailWord_4424179, baseEnd_4424179] using wordTrace_append hprefix tailTrace_4424179
  have hstable : (prefixWord ++ tailWord_4424179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4424179).length < 2 ^ (prefixWord ++ tailWord_4424179).sum := by decide
  have hdescent : baseEnd_4424179 < baseStart_4424179 := by decide
  rcases family_descends (prefixWord ++ tailWord_4424179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4424189 : List Nat := [1, 4, 1, 1, 1, 3, 1, 3, 2, 3, 3]
def baseStart_4424189 : Nat := 118140960795 + 4424189 * 2 ^ 59
def prefixEnd_4424189 : Nat := 4983230072969 + 3 ^ 40 * 4424189 * 2
def baseEnd_4424189 : Nat := 2271735463334496073891031

theorem tailTrace_4424189 : CollatzResearch.WordTrace tailWord_4424189 prefixEnd_4424189 2271735463334496073891031 := by
  unfold tailWord_4424189
  simp only [CollatzResearch.WordTrace]
  refine ⟨161363429368926319170611621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107575619579284212780407747 161363429368926319170611621)
  ·
    refine ⟨30255643006673684844489679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 161363429368926319170611621 30255643006673684844489679)
    ·
      refine ⟨45383464510010527266734519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30255643006673684844489679 45383464510010527266734519)
      ·
        refine ⟨68075196765015790900101779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45383464510010527266734519 68075196765015790900101779)
        ·
          refine ⟨102112795147523686350152669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68075196765015790900101779 102112795147523686350152669)
          ·
            refine ⟨38292298180321382381307251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102112795147523686350152669 38292298180321382381307251)
            ·
              refine ⟨57438447270482073571960877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38292298180321382381307251 57438447270482073571960877)
              ·
                refine ⟨21539417726430777589485329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57438447270482073571960877 21539417726430777589485329)
                ·
                  refine ⟨16154563294823083192113997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21539417726430777589485329 16154563294823083192113997)
                  ·
                    refine ⟨6057961235558656197042749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16154563294823083192113997 6057961235558656197042749)
                    ·
                      refine ⟨2271735463334496073891031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6057961235558656197042749 2271735463334496073891031)
                      ·
                        rfl

theorem cell23_4424189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 3, 2, 3, 3].length) (baseStart_4424189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4424189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4424189 prefixEnd_4424189 := by exact prefixLift 4424189
  have htrace : WordTrace (prefixWord ++ tailWord_4424189) baseStart_4424189 baseEnd_4424189 := by
    simpa [prefixWord, tailWord_4424189, baseEnd_4424189] using wordTrace_append hprefix tailTrace_4424189
  have hstable : (prefixWord ++ tailWord_4424189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4424189).length < 2 ^ (prefixWord ++ tailWord_4424189).sum := by decide
  have hdescent : baseEnd_4424189 < baseStart_4424189 := by decide
  rcases family_descends (prefixWord ++ tailWord_4424189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4424229 : List Nat := [1, 3, 1, 2, 2, 1, 3, 1, 4, 1, 4]
def baseStart_4424229 : Nat := 118140960795 + 4424229 * 2 ^ 59
def prefixEnd_4424229 : Nat := 4983230072969 + 3 ^ 40 * 4424229 * 2
def baseEnd_4424229 : Nat := 2271756002560675917390847

theorem tailTrace_4424229 : CollatzResearch.WordTrace tailWord_4424229 prefixEnd_4424229 2271756002560675917390847 := by
  unfold tailWord_4424229
  simp only [CollatzResearch.WordTrace]
  refine ⟨161364888288781406002067741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107576592192520937334711827 161364888288781406002067741)
  ·
    refine ⟨60511833108293027250775403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 161364888288781406002067741 60511833108293027250775403)
    ·
      refine ⟨90767749662439540876163105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60511833108293027250775403 90767749662439540876163105)
      ·
        refine ⟨68075812246829655657122329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90767749662439540876163105 68075812246829655657122329)
        ·
          refine ⟨51056859185122241742841747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68075812246829655657122329 51056859185122241742841747)
          ·
            refine ⟨76585288777683362614262621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51056859185122241742841747 76585288777683362614262621)
            ·
              refine ⟨28719483291631260980348483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76585288777683362614262621 28719483291631260980348483)
              ·
                refine ⟨43079224937446891470522725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28719483291631260980348483 43079224937446891470522725)
                ·
                  refine ⟨8077354675771292150723011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43079224937446891470522725 8077354675771292150723011)
                  ·
                    refine ⟨12116032013656938226084517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8077354675771292150723011 12116032013656938226084517)
                    ·
                      refine ⟨2271756002560675917390847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12116032013656938226084517 2271756002560675917390847)
                      ·
                        rfl

theorem cell23_4424229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 4, 1, 4].length) (baseStart_4424229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4424229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4424229 prefixEnd_4424229 := by exact prefixLift 4424229
  have htrace : WordTrace (prefixWord ++ tailWord_4424229) baseStart_4424229 baseEnd_4424229 := by
    simpa [prefixWord, tailWord_4424229, baseEnd_4424229] using wordTrace_append hprefix tailTrace_4424229
  have hstable : (prefixWord ++ tailWord_4424229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4424229).length < 2 ^ (prefixWord ++ tailWord_4424229).sum := by decide
  have hdescent : baseEnd_4424229 < baseStart_4424229 := by decide
  rcases family_descends (prefixWord ++ tailWord_4424229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4424266 : List Nat := [3, 1, 2, 1, 1, 4, 1, 3, 2, 2, 3]
def baseStart_4424266 : Nat := 118140960795 + 4424266 * 2 ^ 59
def prefixEnd_4424266 : Nat := 4983230072969 + 3 ^ 40 * 4424266 * 2
def baseEnd_4424266 : Nat := 2271775001344892272628177

theorem tailTrace_4424266 : CollatzResearch.WordTrace tailWord_4424266 prefixEnd_4424266 2271775001344892272628177 := by
  unfold tailWord_4424266
  simp only [CollatzResearch.WordTrace]
  refine ⟨40341559447411840330291163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107577491859764907547443101 40341559447411840330291163)
  ·
    refine ⟨60512339171117760495436745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40341559447411840330291163 60512339171117760495436745)
    ·
      refine ⟨45384254378338320371577559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60512339171117760495436745 45384254378338320371577559)
      ·
        refine ⟨68076381567507480557366339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45384254378338320371577559 68076381567507480557366339)
        ·
          refine ⟨102114572351261220836049509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68076381567507480557366339 102114572351261220836049509)
          ·
            refine ⟨19146482315861478906759283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 102114572351261220836049509 19146482315861478906759283)
            ·
              refine ⟨28719723473792218360138925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19146482315861478906759283 28719723473792218360138925)
              ·
                refine ⟨10769896302672081885052097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28719723473792218360138925 10769896302672081885052097)
                ·
                  refine ⟨8077422227004061413789073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10769896302672081885052097 8077422227004061413789073)
                  ·
                    refine ⟨6058066670253046060341805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8077422227004061413789073 6058066670253046060341805)
                    ·
                      refine ⟨2271775001344892272628177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6058066670253046060341805 2271775001344892272628177)
                      ·
                        rfl

theorem cell23_4424266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 3, 2, 2, 3].length) (baseStart_4424266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4424266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4424266 prefixEnd_4424266 := by exact prefixLift 4424266
  have htrace : WordTrace (prefixWord ++ tailWord_4424266) baseStart_4424266 baseEnd_4424266 := by
    simpa [prefixWord, tailWord_4424266, baseEnd_4424266] using wordTrace_append hprefix tailTrace_4424266
  have hstable : (prefixWord ++ tailWord_4424266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4424266).length < 2 ^ (prefixWord ++ tailWord_4424266).sum := by decide
  have hdescent : baseEnd_4424266 < baseStart_4424266 := by decide
  rcases family_descends (prefixWord ++ tailWord_4424266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4424313 : List Nat := [1, 2, 1, 3, 3, 3, 1, 2, 3, 1, 3]
def baseStart_4424313 : Nat := 118140960795 + 4424313 * 2 ^ 59
def prefixEnd_4424313 : Nat := 4983230072969 + 3 ^ 40 * 4424313 * 2
def baseEnd_4424313 : Nat := 2271799134935653588740461

theorem tailTrace_4424313 : CollatzResearch.WordTrace tailWord_4424313 prefixEnd_4424313 2271799134935653588740461 := by
  unfold tailWord_4424313
  simp only [CollatzResearch.WordTrace]
  refine ⟨161367952020477088348125593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107578634680318058898750395 161367952020477088348125593)
  ·
    refine ⟨121025964015357816261094195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161367952020477088348125593 121025964015357816261094195)
    ·
      refine ⟨181538946023036724391641293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121025964015357816261094195 181538946023036724391641293)
      ·
        refine ⟨68077104758638771646865485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 181538946023036724391641293 68077104758638771646865485)
        ·
          refine ⟨25528914284489539367574557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68077104758638771646865485 25528914284489539367574557)
          ·
            refine ⟨9573342856683577262840459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25528914284489539367574557 9573342856683577262840459)
            ·
              refine ⟨14360014285025365894260689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9573342856683577262840459 14360014285025365894260689)
              ·
                refine ⟨10770010713769024420695517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14360014285025365894260689 10770010713769024420695517)
                ·
                  refine ⟨4038754017663384157760819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10770010713769024420695517 4038754017663384157760819)
                  ·
                    refine ⟨6058131026495076236641229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4038754017663384157760819 6058131026495076236641229)
                    ·
                      refine ⟨2271799134935653588740461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6058131026495076236641229 2271799134935653588740461)
                      ·
                        rfl

theorem cell23_4424313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 2, 3, 1, 3].length) (baseStart_4424313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4424313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4424313 prefixEnd_4424313 := by exact prefixLift 4424313
  have htrace : WordTrace (prefixWord ++ tailWord_4424313) baseStart_4424313 baseEnd_4424313 := by
    simpa [prefixWord, tailWord_4424313, baseEnd_4424313] using wordTrace_append hprefix tailTrace_4424313
  have hstable : (prefixWord ++ tailWord_4424313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4424313).length < 2 ^ (prefixWord ++ tailWord_4424313).sum := by decide
  have hdescent : baseEnd_4424313 < baseStart_4424313 := by decide
  rcases family_descends (prefixWord ++ tailWord_4424313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4424323 : List Nat := [1, 1, 1, 3, 3, 1, 5, 1, 2, 3, 2]
def baseStart_4424323 : Nat := 118140960795 + 4424323 * 2 ^ 59
def prefixEnd_4424323 : Nat := 4983230072969 + 3 ^ 40 * 4424323 * 2
def baseEnd_4424323 : Nat := 2271804269742198549615415

theorem tailTrace_4424323 : CollatzResearch.WordTrace tailWord_4424323 prefixEnd_4424323 2271804269742198549615415 := by
  unfold tailWord_4424323
  simp only [CollatzResearch.WordTrace]
  refine ⟨161368316750440860055989623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107578877833627240037326415 161368316750440860055989623)
  ·
    refine ⟨242052475125661290083984435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161368316750440860055989623 242052475125661290083984435)
    ·
      refine ⟨363078712688491935125976653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242052475125661290083984435 363078712688491935125976653)
      ·
        refine ⟨136154517258184475672241245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 363078712688491935125976653 136154517258184475672241245)
        ·
          refine ⟨51057943971819178377090467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 136154517258184475672241245 51057943971819178377090467)
          ·
            refine ⟨76586915957728767565635701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51057943971819178377090467 76586915957728767565635701)
            ·
              refine ⟨7180023371037071959278347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 76586915957728767565635701 7180023371037071959278347)
              ·
                refine ⟨10770035056555607938917521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7180023371037071959278347 10770035056555607938917521)
                ·
                  refine ⟨8077526292416705954188141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10770035056555607938917521 8077526292416705954188141)
                  ·
                    refine ⟨3029072359656264732820553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8077526292416705954188141 3029072359656264732820553)
                    ·
                      refine ⟨2271804269742198549615415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3029072359656264732820553 2271804269742198549615415)
                      ·
                        rfl

theorem cell23_4424323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 1, 2, 3, 2].length) (baseStart_4424323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4424323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4424323 prefixEnd_4424323 := by exact prefixLift 4424323
  have htrace : WordTrace (prefixWord ++ tailWord_4424323) baseStart_4424323 baseEnd_4424323 := by
    simpa [prefixWord, tailWord_4424323, baseEnd_4424323] using wordTrace_append hprefix tailTrace_4424323
  have hstable : (prefixWord ++ tailWord_4424323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4424323).length < 2 ^ (prefixWord ++ tailWord_4424323).sum := by decide
  have hdescent : baseEnd_4424323 < baseStart_4424323 := by decide
  rcases family_descends (prefixWord ++ tailWord_4424323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4424356 : List Nat := [2, 3, 1, 2, 2, 1, 3, 2, 1, 1, 5]
def baseStart_4424356 : Nat := 118140960795 + 4424356 * 2 ^ 59
def prefixEnd_4424356 : Nat := 4983230072969 + 3 ^ 40 * 4424356 * 2
def baseEnd_4424356 : Nat := 2271821214603796920502763

theorem tailTrace_4424356 : CollatzResearch.WordTrace tailWord_4424356 prefixEnd_4424356 2271821214603796920502763 := by
  unfold tailWord_4424356
  simp only [CollatzResearch.WordTrace]
  refine ⟨80684760179660653345970461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107579680239547537794627281 80684760179660653345970461)
  ·
    refine ⟨30256785067372745004738923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80684760179660653345970461 30256785067372745004738923)
    ·
      refine ⟨45385177601059117507108385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30256785067372745004738923 45385177601059117507108385)
      ·
        refine ⟨34038883200794338130331289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45385177601059117507108385 34038883200794338130331289)
        ·
          refine ⟨25529162400595753597748467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34038883200794338130331289 25529162400595753597748467)
          ·
            refine ⟨38293743600893630396622701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25529162400595753597748467 38293743600893630396622701)
            ·
              refine ⟨14360153850335111398733513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38293743600893630396622701 14360153850335111398733513)
              ·
                refine ⟨10770115387751333549050135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14360153850335111398733513 10770115387751333549050135)
                ·
                  refine ⟨16155173081627000323575203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10770115387751333549050135 16155173081627000323575203)
                  ·
                    refine ⟨24232759622440500485362805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16155173081627000323575203 24232759622440500485362805)
                    ·
                      refine ⟨2271821214603796920502763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24232759622440500485362805 2271821214603796920502763)
                      ·
                        rfl

theorem cell23_4424356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_4424356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4424356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4424356 prefixEnd_4424356 := by exact prefixLift 4424356
  have htrace : WordTrace (prefixWord ++ tailWord_4424356) baseStart_4424356 baseEnd_4424356 := by
    simpa [prefixWord, tailWord_4424356, baseEnd_4424356] using wordTrace_append hprefix tailTrace_4424356
  have hstable : (prefixWord ++ tailWord_4424356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4424356).length < 2 ^ (prefixWord ++ tailWord_4424356).sum := by decide
  have hdescent : baseEnd_4424356 < baseStart_4424356 := by decide
  rcases family_descends (prefixWord ++ tailWord_4424356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4424404 : List Nat := [2, 4, 1, 3, 2, 2, 1, 1, 3, 2, 2]
def baseStart_4424404 : Nat := 118140960795 + 4424404 * 2 ^ 59
def prefixEnd_4424404 : Nat := 4983230072969 + 3 ^ 40 * 4424404 * 2
def baseEnd_4424404 : Nat := 2271845861675212732702543

theorem tailTrace_4424404 : CollatzResearch.WordTrace tailWord_4424404 prefixEnd_4424404 2271845861675212732702543 := by
  unfold tailWord_4424404
  simp only [CollatzResearch.WordTrace]
  refine ⟨80685635531573705444844133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107580847375431607259792177 80685635531573705444844133)
  ·
    refine ⟨15128556662170069770908275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80685635531573705444844133 15128556662170069770908275)
    ·
      refine ⟨22692834993255104656362413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15128556662170069770908275 22692834993255104656362413)
      ·
        refine ⟨8509813122470664246135905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22692834993255104656362413 8509813122470664246135905)
        ·
          refine ⟨6382359841852998184601929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8509813122470664246135905 6382359841852998184601929)
          ·
            refine ⟨4786769881389748638451447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6382359841852998184601929 4786769881389748638451447)
            ·
              refine ⟨7180154822084622957677171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4786769881389748638451447 7180154822084622957677171)
              ·
                refine ⟨10770232233126934436515757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7180154822084622957677171 10770232233126934436515757)
                ·
                  refine ⟨4038837087422600413693409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10770232233126934436515757 4038837087422600413693409)
                  ·
                    refine ⟨3029127815566950310270057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4038837087422600413693409 3029127815566950310270057)
                    ·
                      refine ⟨2271845861675212732702543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3029127815566950310270057 2271845861675212732702543)
                      ·
                        rfl

theorem cell23_4424404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_4424404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4424404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4424404 prefixEnd_4424404 := by exact prefixLift 4424404
  have htrace : WordTrace (prefixWord ++ tailWord_4424404) baseStart_4424404 baseEnd_4424404 := by
    simpa [prefixWord, tailWord_4424404, baseEnd_4424404] using wordTrace_append hprefix tailTrace_4424404
  have hstable : (prefixWord ++ tailWord_4424404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4424404).length < 2 ^ (prefixWord ++ tailWord_4424404).sum := by decide
  have hdescent : baseEnd_4424404 < baseStart_4424404 := by decide
  rcases family_descends (prefixWord ++ tailWord_4424404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4424420 : List Nat := [2, 3, 1, 1, 1, 5, 1, 3, 2, 1, 3]
def baseStart_4424420 : Nat := 118140960795 + 4424420 * 2 ^ 59
def prefixEnd_4424420 : Nat := 4983230072969 + 3 ^ 40 * 4424420 * 2
def baseEnd_4424420 : Nat := 2271854077365684670102469

theorem tailTrace_4424420 : CollatzResearch.WordTrace tailWord_4424420 prefixEnd_4424420 2271854077365684670102469 := by
  unfold tailWord_4424420
  simp only [CollatzResearch.WordTrace]
  refine ⟨80685927315544722811135357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107581236420726297081513809 80685927315544722811135357)
  ·
    refine ⟨30257222743329271054175759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80685927315544722811135357 30257222743329271054175759)
    ·
      refine ⟨45385834114993906581263639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30257222743329271054175759 45385834114993906581263639)
      ·
        refine ⟨68078751172490859871895459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45385834114993906581263639 68078751172490859871895459)
        ·
          refine ⟨102118126758736289807843189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68078751172490859871895459 102118126758736289807843189)
          ·
            refine ⟨9573574383631527169485299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 102118126758736289807843189 9573574383631527169485299)
            ·
              refine ⟨14360361575447290754227949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9573574383631527169485299 14360361575447290754227949)
              ·
                refine ⟨5385135590792734032835481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14360361575447290754227949 5385135590792734032835481)
                ·
                  refine ⟨4038851693094550524626611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5385135590792734032835481 4038851693094550524626611)
                  ·
                    refine ⟨6058277539641825786939917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4038851693094550524626611 6058277539641825786939917)
                    ·
                      refine ⟨2271854077365684670102469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6058277539641825786939917 2271854077365684670102469)
                      ·
                        rfl

theorem cell23_4424420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 3, 2, 1, 3].length) (baseStart_4424420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4424420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4424420 prefixEnd_4424420 := by exact prefixLift 4424420
  have htrace : WordTrace (prefixWord ++ tailWord_4424420) baseStart_4424420 baseEnd_4424420 := by
    simpa [prefixWord, tailWord_4424420, baseEnd_4424420] using wordTrace_append hprefix tailTrace_4424420
  have hstable : (prefixWord ++ tailWord_4424420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4424420).length < 2 ^ (prefixWord ++ tailWord_4424420).sum := by decide
  have hdescent : baseEnd_4424420 < baseStart_4424420 := by decide
  rcases family_descends (prefixWord ++ tailWord_4424420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4424430 : List Nat := [4, 1, 2, 1, 1, 4, 1, 1, 3, 3, 2]
def baseStart_4424430 : Nat := 118140960795 + 4424430 * 2 ^ 59
def prefixEnd_4424430 : Nat := 4983230072969 + 3 ^ 40 * 4424430 * 2
def baseEnd_4424430 : Nat := 2271859212172229630977423

theorem tailTrace_4424430 : CollatzResearch.WordTrace tailWord_4424430 prefixEnd_4424430 2271859212172229630977423 := by
  unfold tailWord_4424430
  simp only [CollatzResearch.WordTrace]
  refine ⟨20171527420131652166266843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107581479574035478220089829 20171527420131652166266843)
  ·
    refine ⟨30257291130197478249400265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20171527420131652166266843 30257291130197478249400265)
    ·
      refine ⟨22692968347648108687050199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30257291130197478249400265 22692968347648108687050199)
      ·
        refine ⟨34039452521472163030575299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22692968347648108687050199 34039452521472163030575299)
        ·
          refine ⟨51059178782208244545862949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34039452521472163030575299 51059178782208244545862949)
          ·
            refine ⟨9573596021664045852349303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51059178782208244545862949 9573596021664045852349303)
            ·
              refine ⟨14360394032496068778523955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9573596021664045852349303 14360394032496068778523955)
              ·
                refine ⟨21540591048744103167785933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14360394032496068778523955 21540591048744103167785933)
                ·
                  refine ⟨8077721643279038687919725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21540591048744103167785933 8077721643279038687919725)
                  ·
                    refine ⟨3029145616229639507969897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8077721643279038687919725 3029145616229639507969897)
                    ·
                      refine ⟨2271859212172229630977423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3029145616229639507969897 2271859212172229630977423)
                      ·
                        rfl

theorem cell23_4424430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 1, 3, 3, 2].length) (baseStart_4424430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4424430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4424430 prefixEnd_4424430 := by exact prefixLift 4424430
  have htrace : WordTrace (prefixWord ++ tailWord_4424430) baseStart_4424430 baseEnd_4424430 := by
    simpa [prefixWord, tailWord_4424430, baseEnd_4424430] using wordTrace_append hprefix tailTrace_4424430
  have hstable : (prefixWord ++ tailWord_4424430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4424430).length < 2 ^ (prefixWord ++ tailWord_4424430).sum := by decide
  have hdescent : baseEnd_4424430 < baseStart_4424430 := by decide
  rcases family_descends (prefixWord ++ tailWord_4424430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4424543 : List Nat := [1, 1, 2, 3, 1, 3, 1, 4, 3, 4]
def baseStart_4424543 : Nat := 118140960795 + 4424543 * 2 ^ 59
def prefixEnd_4424543 : Nat := 4983230072969 + 3 ^ 40 * 4424543 * 2
def baseEnd_4424543 : Nat := 757305745162062562954801

theorem tailTrace_4424543 : CollatzResearch.WordTrace tailWord_4424543 prefixEnd_4424543 757305745162062562954801 := by
  unfold tailWord_4424543
  simp only [CollatzResearch.WordTrace]
  refine ⟨161376340809643837628998283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107584227206429225085998855 161376340809643837628998283)
  ·
    refine ⟨242064511214465756443497425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161376340809643837628998283 242064511214465756443497425)
    ·
      refine ⟨181548383410849317332623069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 242064511214465756443497425 181548383410849317332623069)
      ·
        refine ⟨68080643779068493999733651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 181548383410849317332623069 68080643779068493999733651)
        ·
          refine ⟨102120965668602740999600477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68080643779068493999733651 102120965668602740999600477)
          ·
            refine ⟨38295362125726027874850179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102120965668602740999600477 38295362125726027874850179)
            ·
              refine ⟨57443043188589041812275269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38295362125726027874850179 57443043188589041812275269)
              ·
                refine ⟨10770570597860445339801613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57443043188589041812275269 10770570597860445339801613)
                ·
                  refine ⟨4038963974197667002425605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10770570597860445339801613 4038963974197667002425605)
                  ·
                    refine ⟨757305745162062562954801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4038963974197667002425605 757305745162062562954801)
                    ·
                      rfl

theorem cell23_4424543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 4, 3, 4].length) (baseStart_4424543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4424543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4424543 prefixEnd_4424543 := by exact prefixLift 4424543
  have htrace : WordTrace (prefixWord ++ tailWord_4424543) baseStart_4424543 baseEnd_4424543 := by
    simpa [prefixWord, tailWord_4424543, baseEnd_4424543] using wordTrace_append hprefix tailTrace_4424543
  have hstable : (prefixWord ++ tailWord_4424543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4424543).length < 2 ^ (prefixWord ++ tailWord_4424543).sum := by decide
  have hdescent : baseEnd_4424543 < baseStart_4424543 := by decide
  rcases family_descends (prefixWord ++ tailWord_4424543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4424556 : List Nat := [2, 2, 1, 1, 4, 1, 1, 1, 10]
def baseStart_4424556 : Nat := 118140960795 + 4424556 * 2 ^ 59
def prefixEnd_4424556 : Nat := 4983230072969 + 3 ^ 40 * 4424556 * 2
def baseEnd_4424556 : Nat := 252435990081632904222427

theorem tailTrace_4424556 : CollatzResearch.WordTrace tailWord_4424556 prefixEnd_4424556 252435990081632904222427 := by
  unfold tailWord_4424556
  simp only [CollatzResearch.WordTrace]
  refine ⟨80688407479298370424610761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107584543305731160566147681 80688407479298370424610761)
  ·
    refine ⟨60516305609473777818458071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80688407479298370424610761 60516305609473777818458071)
    ·
      refine ⟨90774458414210666727687107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60516305609473777818458071 90774458414210666727687107)
      ·
        refine ⟨136161687621316000091530661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90774458414210666727687107 136161687621316000091530661)
        ·
          refine ⟨25530316428996750017161999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 136161687621316000091530661 25530316428996750017161999)
          ·
            refine ⟨38295474643495125025742999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25530316428996750017161999 38295474643495125025742999)
            ·
              refine ⟨57443211965242687538614499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38295474643495125025742999 57443211965242687538614499)
              ·
                refine ⟨86164817947864031307921749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57443211965242687538614499 86164817947864031307921749)
                ·
                  refine ⟨252435990081632904222427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 86164817947864031307921749 252435990081632904222427)
                  ·
                    rfl

theorem cell23_4424556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 10].length) (baseStart_4424556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4424556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4424556 prefixEnd_4424556 := by exact prefixLift 4424556
  have htrace : WordTrace (prefixWord ++ tailWord_4424556) baseStart_4424556 baseEnd_4424556 := by
    simpa [prefixWord, tailWord_4424556, baseEnd_4424556] using wordTrace_append hprefix tailTrace_4424556
  have hstable : (prefixWord ++ tailWord_4424556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4424556).length < 2 ^ (prefixWord ++ tailWord_4424556).sum := by decide
  have hdescent : baseEnd_4424556 < baseStart_4424556 := by decide
  rcases family_descends (prefixWord ++ tailWord_4424556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4424576 : List Nat := [2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 6]
def baseStart_4424576 : Nat := 118140960795 + 4424576 * 2 ^ 59
def prefixEnd_4424576 : Nat := 4983230072969 + 3 ^ 40 * 4424576 * 2
def baseEnd_4424576 : Nat := 2271934180347786059751751

theorem tailTrace_4424576 : CollatzResearch.WordTrace tailWord_4424576 prefixEnd_4424576 2271934180347786059751751 := by
  unfold tailWord_4424576
  simp only [CollatzResearch.WordTrace]
  refine ⟨80688772209262142132474791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107585029612349522843299721 80688772209262142132474791)
  ·
    refine ⟨121033158313893213198712187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80688772209262142132474791 121033158313893213198712187)
    ·
      refine ⟨181549737470839819798068281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121033158313893213198712187 181549737470839819798068281)
      ·
        refine ⟨136162303103129864848551211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 181549737470839819798068281 136162303103129864848551211)
        ·
          refine ⟨204243454654694797272826817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136162303103129864848551211 204243454654694797272826817)
          ·
            refine ⟨153182590991021097954620113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 204243454654694797272826817 153182590991021097954620113)
            ·
              refine ⟨114886943243265823465965085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 153182590991021097954620113 114886943243265823465965085)
              ·
                refine ⟨43082603716224683799736907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 114886943243265823465965085 43082603716224683799736907)
                ·
                  refine ⟨64623905574337025699605361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43082603716224683799736907 64623905574337025699605361)
                  ·
                    refine ⟨48467929180752769274704021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 64623905574337025699605361 48467929180752769274704021)
                    ·
                      refine ⟨2271934180347786059751751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48467929180752769274704021 2271934180347786059751751)
                      ·
                        rfl

theorem cell23_4424576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 6].length) (baseStart_4424576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4424576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4424576 prefixEnd_4424576 := by exact prefixLift 4424576
  have htrace : WordTrace (prefixWord ++ tailWord_4424576) baseStart_4424576 baseEnd_4424576 := by
    simpa [prefixWord, tailWord_4424576, baseEnd_4424576] using wordTrace_append hprefix tailTrace_4424576
  have hstable : (prefixWord ++ tailWord_4424576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4424576).length < 2 ^ (prefixWord ++ tailWord_4424576).sum := by decide
  have hdescent : baseEnd_4424576 < baseStart_4424576 := by decide
  rcases family_descends (prefixWord ++ tailWord_4424576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4424617 : List Nat := [1, 2, 1, 1, 1, 1, 6, 5, 1, 1, 3]
def baseStart_4424617 : Nat := 118140960795 + 4424617 * 2 ^ 59
def prefixEnd_4424617 : Nat := 4983230072969 + 3 ^ 40 * 4424617 * 2
def baseEnd_4424617 : Nat := 2271955233054620399339063

theorem tailTrace_4424617 : CollatzResearch.WordTrace tailWord_4424617 prefixEnd_4424617 2271955233054620399339063 := by
  unfold tailWord_4424617
  simp only [CollatzResearch.WordTrace]
  refine ⟨161379039811375748267192105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107586026540917165511461403 161379039811375748267192105)
  ·
    refine ⟨121034279858531811200394079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161379039811375748267192105 121034279858531811200394079)
    ·
      refine ⟨181551419787797716800591119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121034279858531811200394079 181551419787797716800591119)
      ·
        refine ⟨272327129681696575200886679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181551419787797716800591119 272327129681696575200886679)
        ·
          refine ⟨408490694522544862801330019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 272327129681696575200886679 408490694522544862801330019)
          ·
            refine ⟨612736041783817294201995029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 408490694522544862801330019 612736041783817294201995029)
            ·
              refine ⟨28722001958616435665718517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 612736041783817294201995029 28722001958616435665718517)
              ·
                refine ⟨2692687683620290843661111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28722001958616435665718517 2692687683620290843661111)
                ·
                  refine ⟨4039031525430436265491667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2692687683620290843661111 4039031525430436265491667)
                  ·
                    refine ⟨6058547288145654398237501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4039031525430436265491667 6058547288145654398237501)
                    ·
                      refine ⟨2271955233054620399339063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6058547288145654398237501 2271955233054620399339063)
                      ·
                        rfl

theorem cell23_4424617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 5, 1, 1, 3].length) (baseStart_4424617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4424617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4424617 prefixEnd_4424617 := by exact prefixLift 4424617
  have htrace : WordTrace (prefixWord ++ tailWord_4424617) baseStart_4424617 baseEnd_4424617 := by
    simpa [prefixWord, tailWord_4424617, baseEnd_4424617] using wordTrace_append hprefix tailTrace_4424617
  have hstable : (prefixWord ++ tailWord_4424617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4424617).length < 2 ^ (prefixWord ++ tailWord_4424617).sum := by decide
  have hdescent : baseEnd_4424617 < baseStart_4424617 := by decide
  rcases family_descends (prefixWord ++ tailWord_4424617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4424628 : List Nat := [2, 5, 2, 1, 1, 3, 2, 2, 1, 4]
def baseStart_4424628 : Nat := 118140960795 + 4424628 * 2 ^ 59
def prefixEnd_4424628 : Nat := 4983230072969 + 3 ^ 40 * 4424628 * 2
def baseEnd_4424628 : Nat := 757320293780606618767171

theorem tailTrace_4424628 : CollatzResearch.WordTrace tailWord_4424628 prefixEnd_4424628 757320293780606618767171 := by
  unfold tailWord_4424628
  simp only [CollatzResearch.WordTrace]
  refine ⟨80689720507167948572921269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107586294009557264763895025 80689720507167948572921269)
  ·
    refine ⟨7564661297546995178711369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 80689720507167948572921269 7564661297546995178711369)
    ·
      refine ⟨5673495973160246384033527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7564661297546995178711369 5673495973160246384033527)
      ·
        refine ⟨8510243959740369576050291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5673495973160246384033527 8510243959740369576050291)
        ·
          refine ⟨12765365939610554364075437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8510243959740369576050291 12765365939610554364075437)
          ·
            refine ⟨4787012227353957886528289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12765365939610554364075437 4787012227353957886528289)
            ·
              refine ⟨3590259170515468414896217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4787012227353957886528289 3590259170515468414896217)
              ·
                refine ⟨2692694377886601311172163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3590259170515468414896217 2692694377886601311172163)
                ·
                  refine ⟨4039041566829901966758245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2692694377886601311172163 4039041566829901966758245)
                  ·
                    refine ⟨757320293780606618767171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4039041566829901966758245 757320293780606618767171)
                    ·
                      rfl

theorem cell23_4424628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_4424628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4424628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4424628 prefixEnd_4424628 := by exact prefixLift 4424628
  have htrace : WordTrace (prefixWord ++ tailWord_4424628) baseStart_4424628 baseEnd_4424628 := by
    simpa [prefixWord, tailWord_4424628, baseEnd_4424628] using wordTrace_append hprefix tailTrace_4424628
  have hstable : (prefixWord ++ tailWord_4424628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4424628).length < 2 ^ (prefixWord ++ tailWord_4424628).sum := by decide
  have hdescent : baseEnd_4424628 < baseStart_4424628 := by decide
  rcases family_descends (prefixWord ++ tailWord_4424628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4424657 : List Nat := [1, 2, 2, 1, 2, 1, 5, 2, 3, 2, 2]
def baseStart_4424657 : Nat := 118140960795 + 4424657 * 2 ^ 59
def prefixEnd_4424657 : Nat := 4983230072969 + 3 ^ 40 * 4424657 * 2
def baseEnd_4424657 : Nat := 2271975772280800242838879

theorem tailTrace_4424657 : CollatzResearch.WordTrace tailWord_4424657 prefixEnd_4424657 2271975772280800242838879 := by
  unfold tailWord_4424657
  simp only [CollatzResearch.WordTrace]
  refine ⟨161380498731230835098648225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107586999154153890065765483 161380498731230835098648225)
  ·
    refine ⟨121035374048423126323986169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161380498731230835098648225 121035374048423126323986169)
    ·
      refine ⟨90776530536317344742989627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121035374048423126323986169 90776530536317344742989627)
      ·
        refine ⟨136164795804476017114484441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90776530536317344742989627 136164795804476017114484441)
        ·
          refine ⟨102123596853357012835863331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136164795804476017114484441 102123596853357012835863331)
          ·
            refine ⟨153185395280035519253794997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102123596853357012835863331 153185395280035519253794997)
            ·
              refine ⟨14361130807503329930043281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 153185395280035519253794997 14361130807503329930043281)
              ·
                refine ⟨10770848105627497447532461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14361130807503329930043281 10770848105627497447532461)
                ·
                  refine ⟨4039068039610311542824673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10770848105627497447532461 4039068039610311542824673)
                  ·
                    refine ⟨3029301029707733657118505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4039068039610311542824673 3029301029707733657118505)
                    ·
                      refine ⟨2271975772280800242838879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3029301029707733657118505 2271975772280800242838879)
                      ·
                        rfl

theorem cell23_4424657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 2, 3, 2, 2].length) (baseStart_4424657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4424657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4424657 prefixEnd_4424657 := by exact prefixLift 4424657
  have htrace : WordTrace (prefixWord ++ tailWord_4424657) baseStart_4424657 baseEnd_4424657 := by
    simpa [prefixWord, tailWord_4424657, baseEnd_4424657] using wordTrace_append hprefix tailTrace_4424657
  have hstable : (prefixWord ++ tailWord_4424657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4424657).length < 2 ^ (prefixWord ++ tailWord_4424657).sum := by decide
  have hdescent : baseEnd_4424657 < baseStart_4424657 := by decide
  rcases family_descends (prefixWord ++ tailWord_4424657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4424661 : List Nat := [1, 3, 2, 3, 4, 1, 1, 1, 2, 3, 2]
def baseStart_4424661 : Nat := 118140960795 + 4424661 * 2 ^ 59
def prefixEnd_4424661 : Nat := 4983230072969 + 3 ^ 40 * 4424661 * 2
def baseEnd_4424661 : Nat := 2271977826203418227188861

theorem tailTrace_4424661 : CollatzResearch.WordTrace tailWord_4424661 prefixEnd_4424661 2271977826203418227188861 := by
  unfold tailWord_4424661
  simp only [CollatzResearch.WordTrace]
  refine ⟨161380644623216343781793837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107587096415477562521195891 161380644623216343781793837)
  ·
    refine ⟨60517741733706128918172689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 161380644623216343781793837 60517741733706128918172689)
    ·
      refine ⟨45388306300279596688629517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60517741733706128918172689 45388306300279596688629517)
      ·
        refine ⟨17020614862604848758236069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45388306300279596688629517 17020614862604848758236069)
        ·
          refine ⟨3191365286738409142169263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17020614862604848758236069 3191365286738409142169263)
          ·
            refine ⟨4787047930107613713253895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3191365286738409142169263 4787047930107613713253895)
            ·
              refine ⟨7180571895161420569880843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4787047930107613713253895 7180571895161420569880843)
              ·
                refine ⟨10770857842742130854821265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7180571895161420569880843 10770857842742130854821265)
                ·
                  refine ⟨8078143382056598141115949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10770857842742130854821265 8078143382056598141115949)
                  ·
                    refine ⟨3029303768271224302918481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8078143382056598141115949 3029303768271224302918481)
                    ·
                      refine ⟨2271977826203418227188861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3029303768271224302918481 2271977826203418227188861)
                      ·
                        rfl

theorem cell23_4424661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 1, 2, 3, 2].length) (baseStart_4424661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4424661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4424661 prefixEnd_4424661 := by exact prefixLift 4424661
  have htrace : WordTrace (prefixWord ++ tailWord_4424661) baseStart_4424661 baseEnd_4424661 := by
    simpa [prefixWord, tailWord_4424661, baseEnd_4424661] using wordTrace_append hprefix tailTrace_4424661
  have hstable : (prefixWord ++ tailWord_4424661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4424661).length < 2 ^ (prefixWord ++ tailWord_4424661).sum := by decide
  have hdescent : baseEnd_4424661 < baseStart_4424661 := by decide
  rcases family_descends (prefixWord ++ tailWord_4424661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4424674 : List Nat := [3, 3, 3, 1, 1, 2, 1, 3, 1, 1, 4]
def baseStart_4424674 : Nat := 118140960795 + 4424674 * 2 ^ 59
def prefixEnd_4424674 : Nat := 4983230072969 + 3 ^ 40 * 4424674 * 2
def baseEnd_4424674 : Nat := 2271984501451926676326301

theorem tailTrace_4424674 : CollatzResearch.WordTrace tailWord_4424674 prefixEnd_4424674 2271984501451926676326301 := by
  unfold tailWord_4424674
  simp only [CollatzResearch.WordTrace]
  refine ⟨40345279693042311750504269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107587412514779498001344717 40345279693042311750504269)
  ·
    refine ⟨15129479884890866906439101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40345279693042311750504269 15129479884890866906439101)
    ·
      refine ⟨5673554956834075089914663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15129479884890866906439101 5673554956834075089914663)
      ·
        refine ⟨8510332435251112634871995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5673554956834075089914663 8510332435251112634871995)
        ·
          refine ⟨12765498652876668952307993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8510332435251112634871995 12765498652876668952307993)
          ·
            refine ⟨9574123989657501714230995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12765498652876668952307993 9574123989657501714230995)
            ·
              refine ⟨14361185984486252571346493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9574123989657501714230995 14361185984486252571346493)
              ·
                refine ⟨5385444744182344714254935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14361185984486252571346493 5385444744182344714254935)
                ·
                  refine ⟨8078167116273517071382403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5385444744182344714254935 8078167116273517071382403)
                  ·
                    refine ⟨12117250674410275607073605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8078167116273517071382403 12117250674410275607073605)
                    ·
                      refine ⟨2271984501451926676326301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12117250674410275607073605 2271984501451926676326301)
                      ·
                        rfl

theorem cell23_4424674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_4424674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4424674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4424674 prefixEnd_4424674 := by exact prefixLift 4424674
  have htrace : WordTrace (prefixWord ++ tailWord_4424674) baseStart_4424674 baseEnd_4424674 := by
    simpa [prefixWord, tailWord_4424674, baseEnd_4424674] using wordTrace_append hprefix tailTrace_4424674
  have hstable : (prefixWord ++ tailWord_4424674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4424674).length < 2 ^ (prefixWord ++ tailWord_4424674).sum := by decide
  have hdescent : baseEnd_4424674 < baseStart_4424674 := by decide
  rcases family_descends (prefixWord ++ tailWord_4424674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4424713 : List Nat := [1, 2, 1, 1, 3, 1, 1, 4, 2, 3, 4]
def baseStart_4424713 : Nat := 118140960795 + 4424713 * 2 ^ 59
def prefixEnd_4424713 : Nat := 4983230072969 + 3 ^ 40 * 4424713 * 2
def baseEnd_4424713 : Nat := 2272004527197452023738621

theorem tailTrace_4424713 : CollatzResearch.WordTrace tailWord_4424713 prefixEnd_4424713 2272004527197452023738621 := by
  unfold tailWord_4424713
  simp only [CollatzResearch.WordTrace]
  refine ⟨161382541219027956662686793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107588360812685304441791195 161382541219027956662686793)
  ·
    refine ⟨121036905914270967497015095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161382541219027956662686793 121036905914270967497015095)
    ·
      refine ⟨181555358871406451245522643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121036905914270967497015095 181555358871406451245522643)
      ·
        refine ⟨272333038307109676868283965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181555358871406451245522643 272333038307109676868283965)
        ·
          refine ⟨102124889365166128825606487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 272333038307109676868283965 102124889365166128825606487)
          ·
            refine ⟨153187334047749193238409731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102124889365166128825606487 153187334047749193238409731)
            ·
              refine ⟨229781001071623789857614597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 153187334047749193238409731 229781001071623789857614597)
              ·
                refine ⟨43083937700929460598302737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 229781001071623789857614597 43083937700929460598302737)
                ·
                  refine ⟨32312953275697095448727053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43083937700929460598302737 32312953275697095448727053)
                  ·
                    refine ⟨12117357478386410793272645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32312953275697095448727053 12117357478386410793272645)
                    ·
                      refine ⟨2272004527197452023738621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12117357478386410793272645 2272004527197452023738621)
                      ·
                        rfl

theorem cell23_4424713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 2, 3, 4].length) (baseStart_4424713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4424713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4424713 prefixEnd_4424713 := by exact prefixLift 4424713
  have htrace : WordTrace (prefixWord ++ tailWord_4424713) baseStart_4424713 baseEnd_4424713 := by
    simpa [prefixWord, tailWord_4424713, baseEnd_4424713] using wordTrace_append hprefix tailTrace_4424713
  have hstable : (prefixWord ++ tailWord_4424713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4424713).length < 2 ^ (prefixWord ++ tailWord_4424713).sum := by decide
  have hdescent : baseEnd_4424713 < baseStart_4424713 := by decide
  rcases family_descends (prefixWord ++ tailWord_4424713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4424747 : List Nat := [1, 1, 1, 1, 2, 1, 5, 3, 4, 2, 2]
def baseStart_4424747 : Nat := 118140960795 + 4424747 * 2 ^ 59
def prefixEnd_4424747 : Nat := 4983230072969 + 3 ^ 40 * 4424747 * 2
def baseEnd_4424747 : Nat := 2272021985539704890713465

theorem tailTrace_4424747 : CollatzResearch.WordTrace tailWord_4424747 prefixEnd_4424747 2272021985539704890713465 := by
  unfold tailWord_4424747
  simp only [CollatzResearch.WordTrace]
  refine ⟨161383781300904780469424495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107589187533936520312949663 161383781300904780469424495)
  ·
    refine ⟨242075671951357170704136743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161383781300904780469424495 242075671951357170704136743)
    ·
      refine ⟨363113507927035756056205115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242075671951357170704136743 363113507927035756056205115)
      ·
        refine ⟨544670261890553634084307673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 363113507927035756056205115 544670261890553634084307673)
        ·
          refine ⟨408502696417915225563230755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 544670261890553634084307673 408502696417915225563230755)
          ·
            refine ⟨612754044626872838344846133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 408502696417915225563230755 612754044626872838344846133)
            ·
              refine ⟨57445691683769328594829325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 612754044626872838344846133 57445691683769328594829325)
              ·
                refine ⟨21542134381413498223060997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57445691683769328594829325 21542134381413498223060997)
                ·
                  refine ⟨4039150196515030916823937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21542134381413498223060997 4039150196515030916823937)
                  ·
                    refine ⟨3029362647386273187617953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4039150196515030916823937 3029362647386273187617953)
                    ·
                      refine ⟨2272021985539704890713465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3029362647386273187617953 2272021985539704890713465)
                      ·
                        rfl

theorem cell23_4424747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 3, 4, 2, 2].length) (baseStart_4424747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4424747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4424747 prefixEnd_4424747 := by exact prefixLift 4424747
  have htrace : WordTrace (prefixWord ++ tailWord_4424747) baseStart_4424747 baseEnd_4424747 := by
    simpa [prefixWord, tailWord_4424747, baseEnd_4424747] using wordTrace_append hprefix tailTrace_4424747
  have hstable : (prefixWord ++ tailWord_4424747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4424747).length < 2 ^ (prefixWord ++ tailWord_4424747).sum := by decide
  have hdescent : baseEnd_4424747 < baseStart_4424747 := by decide
  rcases family_descends (prefixWord ++ tailWord_4424747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4424750 : List Nat := [4, 1, 3, 1, 1, 1, 1, 2, 1, 3, 5]
def baseStart_4424750 : Nat := 118140960795 + 4424750 * 2 ^ 59
def prefixEnd_4424750 : Nat := 4983230072969 + 3 ^ 40 * 4424750 * 2
def baseEnd_4424750 : Nat := 2272023525981668378975951

theorem tailTrace_4424750 : CollatzResearch.WordTrace tailWord_4424750 prefixEnd_4424750 2272023525981668378975951 := by
  unfold tailWord_4424750
  simp only [CollatzResearch.WordTrace]
  refine ⟨20172986339986738997722963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107589260479929274654522469 20172986339986738997722963)
  ·
    refine ⟨30259479509980108496584445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20172986339986738997722963 30259479509980108496584445)
    ·
      refine ⟨11347304816242540686219167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30259479509980108496584445 11347304816242540686219167)
      ·
        refine ⟨17020957224363811029328751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11347304816242540686219167 17020957224363811029328751)
        ·
          refine ⟨25531435836545716543993127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17020957224363811029328751 25531435836545716543993127)
          ·
            refine ⟨38297153754818574815989691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25531435836545716543993127 38297153754818574815989691)
            ·
              refine ⟨57445730632227862223984537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38297153754818574815989691 57445730632227862223984537)
              ·
                refine ⟨43084297974170896667988403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57445730632227862223984537 43084297974170896667988403)
                ·
                  refine ⟨64626446961256345001982605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43084297974170896667988403 64626446961256345001982605)
                  ·
                    refine ⟨24234917610471129375743477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 64626446961256345001982605 24234917610471129375743477)
                    ·
                      refine ⟨2272023525981668378975951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24234917610471129375743477 2272023525981668378975951)
                      ·
                        rfl

theorem cell23_4424750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_4424750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4424750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4424750 prefixEnd_4424750 := by exact prefixLift 4424750
  have htrace : WordTrace (prefixWord ++ tailWord_4424750) baseStart_4424750 baseEnd_4424750 := by
    simpa [prefixWord, tailWord_4424750, baseEnd_4424750] using wordTrace_append hprefix tailTrace_4424750
  have hstable : (prefixWord ++ tailWord_4424750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4424750).length < 2 ^ (prefixWord ++ tailWord_4424750).sum := by decide
  have hdescent : baseEnd_4424750 < baseStart_4424750 := by decide
  rcases family_descends (prefixWord ++ tailWord_4424750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4424758 : List Nat := [5, 1, 2, 1, 1, 4, 2, 1, 2, 1, 3]
def baseStart_4424758 : Nat := 118140960795 + 4424758 * 2 ^ 59
def prefixEnd_4424758 : Nat := 4983230072969 + 3 ^ 40 * 4424758 * 2
def baseEnd_4424758 : Nat := 2272027633826904347675915

theorem tailTrace_4424758 : CollatzResearch.WordTrace tailWord_4424758 prefixEnd_4424758 2272027633826904347675915 := by
  unfold tailWord_4424758
  simp only [CollatzResearch.WordTrace]
  refine ⟨10086511406491558084254683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 107589455002576619565383285 10086511406491558084254683)
  ·
    refine ⟨15129767109737337126382025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10086511406491558084254683 15129767109737337126382025)
    ·
      refine ⟨11347325332303002844786519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15129767109737337126382025 11347325332303002844786519)
      ·
        refine ⟨17020987998454504267179779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11347325332303002844786519 17020987998454504267179779)
        ·
          refine ⟨25531481997681756400769669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17020987998454504267179779 25531481997681756400769669)
          ·
            refine ⟨4787152874565329325144313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25531481997681756400769669 4787152874565329325144313)
            ·
              refine ⟨3590364655923996993858235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4787152874565329325144313 3590364655923996993858235)
              ·
                refine ⟨5385546983885995490787353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3590364655923996993858235 5385546983885995490787353)
                ·
                  refine ⟨4039160237914496618090515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5385546983885995490787353 4039160237914496618090515)
                  ·
                    refine ⟨6058740356871744927135773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4039160237914496618090515 6058740356871744927135773)
                    ·
                      refine ⟨2272027633826904347675915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6058740356871744927135773 2272027633826904347675915)
                      ·
                        rfl

theorem cell23_4424758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 2, 1, 2, 1, 3].length) (baseStart_4424758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4424758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4424758 prefixEnd_4424758 := by exact prefixLift 4424758
  have htrace : WordTrace (prefixWord ++ tailWord_4424758) baseStart_4424758 baseEnd_4424758 := by
    simpa [prefixWord, tailWord_4424758, baseEnd_4424758] using wordTrace_append hprefix tailTrace_4424758
  have hstable : (prefixWord ++ tailWord_4424758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4424758).length < 2 ^ (prefixWord ++ tailWord_4424758).sum := by decide
  have hdescent : baseEnd_4424758 < baseStart_4424758 := by decide
  rcases family_descends (prefixWord ++ tailWord_4424758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4424780 : List Nat := [2, 2, 1, 3, 1, 1, 1, 2, 4, 3, 3]
def baseStart_4424780 : Nat := 118140960795 + 4424780 * 2 ^ 59
def prefixEnd_4424780 : Nat := 4983230072969 + 3 ^ 40 * 4424780 * 2
def baseEnd_4424780 : Nat := 2272038930401303261600813

theorem tailTrace_4424780 : CollatzResearch.WordTrace tailWord_4424780 prefixEnd_4424780 2272038930401303261600813 := by
  unfold tailWord_4424780
  simp only [CollatzResearch.WordTrace]
  refine ⟨80692492454892613552687897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107589989939856818070250529 80692492454892613552687897)
  ·
    refine ⟨60519369341169460164515923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80692492454892613552687897 60519369341169460164515923)
    ·
      refine ⟨90779054011754190246773885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60519369341169460164515923 90779054011754190246773885)
      ·
        refine ⟨34042145254407821342540207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90779054011754190246773885 34042145254407821342540207)
        ·
          refine ⟨51063217881611732013810311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34042145254407821342540207 51063217881611732013810311)
          ·
            refine ⟨76594826822417598020715467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51063217881611732013810311 76594826822417598020715467)
            ·
              refine ⟨114892240233626397031073201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76594826822417598020715467 114892240233626397031073201)
              ·
                refine ⟨86169180175219797773304901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 114892240233626397031073201 86169180175219797773304901)
                ·
                  refine ⟨16156721282853712082494669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 86169180175219797773304901 16156721282853712082494669)
                  ·
                    refine ⟨6058770481070142030935501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16156721282853712082494669 6058770481070142030935501)
                    ·
                      refine ⟨2272038930401303261600813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6058770481070142030935501 2272038930401303261600813)
                      ·
                        rfl

theorem cell23_4424780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 4, 3, 3].length) (baseStart_4424780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4424780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4424780 prefixEnd_4424780 := by exact prefixLift 4424780
  have htrace : WordTrace (prefixWord ++ tailWord_4424780) baseStart_4424780 baseEnd_4424780 := by
    simpa [prefixWord, tailWord_4424780, baseEnd_4424780] using wordTrace_append hprefix tailTrace_4424780
  have hstable : (prefixWord ++ tailWord_4424780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4424780).length < 2 ^ (prefixWord ++ tailWord_4424780).sum := by decide
  have hdescent : baseEnd_4424780 < baseStart_4424780 := by decide
  rcases family_descends (prefixWord ++ tailWord_4424780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4424800 : List Nat := [2, 1, 1, 3, 2, 2, 1, 4, 2, 5]
def baseStart_4424800 : Nat := 118140960795 + 4424800 * 2 ^ 59
def prefixEnd_4424800 : Nat := 4983230072969 + 3 ^ 40 * 4424800 * 2
def baseEnd_4424800 : Nat := 757349733338131061116907

theorem tailTrace_4424800 : CollatzResearch.WordTrace tailWord_4424800 prefixEnd_4424800 757349733338131061116907 := by
  unfold tailWord_4424800
  simp only [CollatzResearch.WordTrace]
  refine ⟨80692857184856385260551927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107590476246475180347402569 80692857184856385260551927)
  ·
    refine ⟨121039285777284577890827891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80692857184856385260551927 121039285777284577890827891)
    ·
      refine ⟨181558928665926866836241837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121039285777284577890827891 181558928665926866836241837)
      ·
        refine ⟨68084598249722575063590689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 181558928665926866836241837 68084598249722575063590689)
        ·
          refine ⟨51063448687291931297693017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68084598249722575063590689 51063448687291931297693017)
          ·
            refine ⟨38297586515468948473269763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51063448687291931297693017 38297586515468948473269763)
            ·
              refine ⟨57446379773203422709904645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38297586515468948473269763 57446379773203422709904645)
              ·
                refine ⟨10771196207475641758107121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57446379773203422709904645 10771196207475641758107121)
                ·
                  refine ⟨8078397155606731318580341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10771196207475641758107121 8078397155606731318580341)
                  ·
                    refine ⟨757349733338131061116907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8078397155606731318580341 757349733338131061116907)
                    ·
                      rfl

theorem cell23_4424800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 4, 2, 5].length) (baseStart_4424800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4424800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4424800 prefixEnd_4424800 := by exact prefixLift 4424800
  have htrace : WordTrace (prefixWord ++ tailWord_4424800) baseStart_4424800 baseEnd_4424800 := by
    simpa [prefixWord, tailWord_4424800, baseEnd_4424800] using wordTrace_append hprefix tailTrace_4424800
  have hstable : (prefixWord ++ tailWord_4424800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4424800).length < 2 ^ (prefixWord ++ tailWord_4424800).sum := by decide
  have hdescent : baseEnd_4424800 < baseStart_4424800 := by decide
  rcases family_descends (prefixWord ++ tailWord_4424800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4424807 : List Nat := [1, 1, 5, 1, 1, 3, 1, 1, 2, 5, 2]
def baseStart_4424807 : Nat := 118140960795 + 4424807 * 2 ^ 59
def prefixEnd_4424807 : Nat := 4983230072969 + 3 ^ 40 * 4424807 * 2
def baseEnd_4424807 : Nat := 2272052794378974655963189

theorem tailTrace_4424807 : CollatzResearch.WordTrace tailWord_4424807 prefixEnd_4424807 2272052794378974655963189 := by
  unfold tailWord_4424807
  simp only [CollatzResearch.WordTrace]
  refine ⟨161385969680687410716608675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107590646453791607144405783 161385969680687410716608675)
  ·
    refine ⟨242078954521031116074913013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161385969680687410716608675 242078954521031116074913013)
    ·
      refine ⟨22694901986346667132023095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 242078954521031116074913013 22694901986346667132023095)
      ·
        refine ⟨34042352979520000698034643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22694901986346667132023095 34042352979520000698034643)
        ·
          refine ⟨51063529469280001047051965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34042352979520000698034643 51063529469280001047051965)
          ·
            refine ⟨19148823550980000392644487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51063529469280001047051965 19148823550980000392644487)
            ·
              refine ⟨28723235326470000588966731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19148823550980000392644487 28723235326470000588966731)
              ·
                refine ⟨43084852989705000883450097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28723235326470000588966731 43084852989705000883450097)
                ·
                  refine ⟨32313639742278750662587573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43084852989705000883450097 32313639742278750662587573)
                  ·
                    refine ⟨3029403725838632874617585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32313639742278750662587573 3029403725838632874617585)
                    ·
                      refine ⟨2272052794378974655963189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3029403725838632874617585 2272052794378974655963189)
                      ·
                        rfl

theorem cell23_4424807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 2, 5, 2].length) (baseStart_4424807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4424807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4424807 prefixEnd_4424807 := by exact prefixLift 4424807
  have htrace : WordTrace (prefixWord ++ tailWord_4424807) baseStart_4424807 baseEnd_4424807 := by
    simpa [prefixWord, tailWord_4424807, baseEnd_4424807] using wordTrace_append hprefix tailTrace_4424807
  have hstable : (prefixWord ++ tailWord_4424807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4424807).length < 2 ^ (prefixWord ++ tailWord_4424807).sum := by decide
  have hdescent : baseEnd_4424807 < baseStart_4424807 := by decide
  rcases family_descends (prefixWord ++ tailWord_4424807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4424837 : List Nat := [1, 3, 1, 1, 6, 1, 1, 1, 1, 3, 4]
def baseStart_4424837 : Nat := 118140960795 + 4424837 * 2 ^ 59
def prefixEnd_4424837 : Nat := 4983230072969 + 3 ^ 40 * 4424837 * 2
def baseEnd_4424837 : Nat := 2272068198798609538588051

theorem tailTrace_4424837 : CollatzResearch.WordTrace tailWord_4424837 prefixEnd_4424837 2272068198798609538588051 := by
  unfold tailWord_4424837
  simp only [CollatzResearch.WordTrace]
  refine ⟨161387063870578725840200765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107591375913719150560133843 161387063870578725840200765)
  ·
    refine ⟨60520148951467022190075287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 161387063870578725840200765 60520148951467022190075287)
    ·
      refine ⟨90780223427200533285112931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60520148951467022190075287 90780223427200533285112931)
      ·
        refine ⟨136170335140800799927669397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90780223427200533285112931 136170335140800799927669397)
        ·
          refine ⟨6382984459725037496609503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 136170335140800799927669397 6382984459725037496609503)
          ·
            refine ⟨9574476689587556244914255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6382984459725037496609503 9574476689587556244914255)
            ·
              refine ⟨14361715034381334367371383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9574476689587556244914255 14361715034381334367371383)
              ·
                refine ⟨21542572551572001551057075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14361715034381334367371383 21542572551572001551057075)
                ·
                  refine ⟨32313858827358002326585613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21542572551572001551057075 32313858827358002326585613)
                  ·
                    refine ⟨12117697060259250872469605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32313858827358002326585613 12117697060259250872469605)
                    ·
                      refine ⟨2272068198798609538588051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12117697060259250872469605 2272068198798609538588051)
                      ·
                        rfl

theorem cell23_4424837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 1, 1, 3, 4].length) (baseStart_4424837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4424837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4424837 prefixEnd_4424837 := by exact prefixLift 4424837
  have htrace : WordTrace (prefixWord ++ tailWord_4424837) baseStart_4424837 baseEnd_4424837 := by
    simpa [prefixWord, tailWord_4424837, baseEnd_4424837] using wordTrace_append hprefix tailTrace_4424837
  have hstable : (prefixWord ++ tailWord_4424837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4424837).length < 2 ^ (prefixWord ++ tailWord_4424837).sum := by decide
  have hdescent : baseEnd_4424837 < baseStart_4424837 := by decide
  rcases family_descends (prefixWord ++ tailWord_4424837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4424864 : List Nat := [2, 1, 1, 4, 2, 1, 1, 6, 1, 4]
def baseStart_4424864 : Nat := 118140960795 + 4424864 * 2 ^ 59
def prefixEnd_4424864 : Nat := 4983230072969 + 3 ^ 40 * 4424864 * 2
def baseEnd_4424864 : Nat := 757360687592093644316809

theorem tailTrace_4424864 : CollatzResearch.WordTrace tailWord_4424864 prefixEnd_4424864 757360687592093644316809 := by
  unfold tailWord_4424864
  simp only [CollatzResearch.WordTrace]
  refine ⟨80694024320740454725716823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107592032427653939634289097 80694024320740454725716823)
  ·
    refine ⟨121041036481110682088575235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80694024320740454725716823 121041036481110682088575235)
    ·
      refine ⟨181561554721666023132862853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121041036481110682088575235 181561554721666023132862853)
      ·
        refine ⟨34042791510312379337411785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 181561554721666023132862853 34042791510312379337411785)
        ·
          refine ⟨25532093632734284503058839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34042791510312379337411785 25532093632734284503058839)
          ·
            refine ⟨38298140449101426754588259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25532093632734284503058839 38298140449101426754588259)
            ·
              refine ⟨57447210673652140131882389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38298140449101426754588259 57447210673652140131882389)
              ·
                refine ⟨2692838000327444068681987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 57447210673652140131882389 2692838000327444068681987)
                ·
                  refine ⟨4039257000491166103022981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2692838000327444068681987 4039257000491166103022981)
                  ·
                    refine ⟨757360687592093644316809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4039257000491166103022981 757360687592093644316809)
                    ·
                      rfl

theorem cell23_4424864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 6, 1, 4].length) (baseStart_4424864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4424864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4424864 prefixEnd_4424864 := by exact prefixLift 4424864
  have htrace : WordTrace (prefixWord ++ tailWord_4424864) baseStart_4424864 baseEnd_4424864 := by
    simpa [prefixWord, tailWord_4424864, baseEnd_4424864] using wordTrace_append hprefix tailTrace_4424864
  have hstable : (prefixWord ++ tailWord_4424864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4424864).length < 2 ^ (prefixWord ++ tailWord_4424864).sum := by decide
  have hdescent : baseEnd_4424864 < baseStart_4424864 := by decide
  rcases family_descends (prefixWord ++ tailWord_4424864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4424874 : List Nat := [3, 1, 5, 1, 1, 1, 1, 2, 1, 4, 3]
def baseStart_4424874 : Nat := 118140960795 + 4424874 * 2 ^ 59
def prefixEnd_4424874 : Nat := 4983230072969 + 3 ^ 40 * 4424874 * 2
def baseEnd_4424874 : Nat := 2272087197582825893825381

theorem tailTrace_4424874 : CollatzResearch.WordTrace tailWord_4424874 prefixEnd_4424874 2272087197582825893825381 := by
  unfold tailWord_4424874
  simp only [CollatzResearch.WordTrace]
  refine ⟨40347103342861170289824419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107592275580963120772865117 40347103342861170289824419)
  ·
    refine ⟨60520655014291755434736629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40347103342861170289824419 60520655014291755434736629)
    ·
      refine ⟨5673811407589852072006559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 60520655014291755434736629 5673811407589852072006559)
      ·
        refine ⟨8510717111384778108009839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5673811407589852072006559 8510717111384778108009839)
        ·
          refine ⟨12766075667077167162014759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8510717111384778108009839 12766075667077167162014759)
          ·
            refine ⟨19149113500615750743022139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12766075667077167162014759 19149113500615750743022139)
            ·
              refine ⟨28723670250923626114533209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19149113500615750743022139 28723670250923626114533209)
              ·
                refine ⟨21542752688192719585899907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28723670250923626114533209 21542752688192719585899907)
                ·
                  refine ⟨32314129032289079378849861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21542752688192719585899907 32314129032289079378849861)
                  ·
                    refine ⟨6058899193554202383534349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32314129032289079378849861 6058899193554202383534349)
                    ·
                      refine ⟨2272087197582825893825381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6058899193554202383534349 2272087197582825893825381)
                      ·
                        rfl

theorem cell23_4424874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_4424874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4424874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4424874 prefixEnd_4424874 := by exact prefixLift 4424874
  have htrace : WordTrace (prefixWord ++ tailWord_4424874) baseStart_4424874 baseEnd_4424874 := by
    simpa [prefixWord, tailWord_4424874, baseEnd_4424874] using wordTrace_append hprefix tailTrace_4424874
  have hstable : (prefixWord ++ tailWord_4424874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4424874).length < 2 ^ (prefixWord ++ tailWord_4424874).sum := by decide
  have hdescent : baseEnd_4424874 < baseStart_4424874 := by decide
  rcases family_descends (prefixWord ++ tailWord_4424874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4424941 : List Nat := [1, 5, 1, 2, 2, 3, 1, 2, 1, 5]
def baseStart_4424941 : Nat := 118140960795 + 4424941 * 2 ^ 59
def prefixEnd_4424941 : Nat := 4983230072969 + 3 ^ 40 * 4424941 * 2
def baseEnd_4424941 : Nat := 757373866928892377229191

theorem tailTrace_4424941 : CollatzResearch.WordTrace tailWord_4424941 prefixEnd_4424941 757373866928892377229191 := by
  unfold tailWord_4424941
  simp only [CollatzResearch.WordTrace]
  refine ⟨161390857062201951601986677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107593904708134634401324451 161390857062201951601986677)
  ·
    refine ⟨15130392849581432962686251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 161390857062201951601986677 15130392849581432962686251)
    ·
      refine ⟨22695589274372149444029377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15130392849581432962686251 22695589274372149444029377)
      ·
        refine ⟨17021691955779112083022033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22695589274372149444029377 17021691955779112083022033)
        ·
          refine ⟨12766268966834334062266525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17021691955779112083022033 12766268966834334062266525)
          ·
            refine ⟨4787350862562875273349947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12766268966834334062266525 4787350862562875273349947)
            ·
              refine ⟨7181026293844312910024921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4787350862562875273349947 7181026293844312910024921)
              ·
                refine ⟨5385769720383234682518691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7181026293844312910024921 5385769720383234682518691)
                ·
                  refine ⟨8078654580574852023778037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5385769720383234682518691 8078654580574852023778037)
                  ·
                    refine ⟨757373866928892377229191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8078654580574852023778037 757373866928892377229191)
                    ·
                      rfl

theorem cell23_4424941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 2, 1, 5].length) (baseStart_4424941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4424941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4424941 prefixEnd_4424941 := by exact prefixLift 4424941
  have htrace : WordTrace (prefixWord ++ tailWord_4424941) baseStart_4424941 baseEnd_4424941 := by
    simpa [prefixWord, tailWord_4424941, baseEnd_4424941] using wordTrace_append hprefix tailTrace_4424941
  have hstable : (prefixWord ++ tailWord_4424941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4424941).length < 2 ^ (prefixWord ++ tailWord_4424941).sum := by decide
  have hdescent : baseEnd_4424941 < baseStart_4424941 := by decide
  rcases family_descends (prefixWord ++ tailWord_4424941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4424961 : List Nat := [1, 2, 4, 1, 1, 4, 3, 1, 1, 1, 4]
def baseStart_4424961 : Nat := 118140960795 + 4424961 * 2 ^ 59
def prefixEnd_4424961 : Nat := 4983230072969 + 3 ^ 40 * 4424961 * 2
def baseEnd_4424961 : Nat := 2272131870399767053437481

theorem tailTrace_4424961 : CollatzResearch.WordTrace tailWord_4424961 prefixEnd_4424961 2272131870399767053437481 := by
  unfold tailWord_4424961
  simp only [CollatzResearch.WordTrace]
  refine ⟨161391586522129495017714737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107594391014752996678476491 161391586522129495017714737)
  ·
    refine ⟨121043689891597121263286053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161391586522129495017714737 121043689891597121263286053)
    ·
      refine ⟨22695691854674460236866135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 121043689891597121263286053 22695691854674460236866135)
      ·
        refine ⟨34043537782011690355299203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22695691854674460236866135 34043537782011690355299203)
        ·
          refine ⟨51065306673017535532948805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34043537782011690355299203 51065306673017535532948805)
          ·
            refine ⟨9574745001190787912427901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51065306673017535532948805 9574745001190787912427901)
            ·
              refine ⟨3590529375446545467160463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9574745001190787912427901 3590529375446545467160463)
              ·
                refine ⟨5385794063169818200740695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3590529375446545467160463 5385794063169818200740695)
                ·
                  refine ⟨8078691094754727301111043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5385794063169818200740695 8078691094754727301111043)
                  ·
                    refine ⟨12118036642132090951666565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8078691094754727301111043 12118036642132090951666565)
                    ·
                      refine ⟨2272131870399767053437481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12118036642132090951666565 2272131870399767053437481)
                      ·
                        rfl

theorem cell23_4424961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 3, 1, 1, 1, 4].length) (baseStart_4424961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4424961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4424961 prefixEnd_4424961 := by exact prefixLift 4424961
  have htrace : WordTrace (prefixWord ++ tailWord_4424961) baseStart_4424961 baseEnd_4424961 := by
    simpa [prefixWord, tailWord_4424961, baseEnd_4424961] using wordTrace_append hprefix tailTrace_4424961
  have hstable : (prefixWord ++ tailWord_4424961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4424961).length < 2 ^ (prefixWord ++ tailWord_4424961).sum := by decide
  have hdescent : baseEnd_4424961 < baseStart_4424961 := by decide
  rcases family_descends (prefixWord ++ tailWord_4424961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4424964 : List Nat := [2, 3, 2, 2, 2, 1, 3, 1, 1, 1, 5]
def baseStart_4424964 : Nat := 118140960795 + 4424964 * 2 ^ 59
def prefixEnd_4424964 : Nat := 4983230072969 + 3 ^ 40 * 4424964 * 2
def baseEnd_4424964 : Nat := 2272133410841730541699967

theorem tailTrace_4424964 : CollatzResearch.WordTrace tailWord_4424964 prefixEnd_4424964 2272133410841730541699967 := by
  unfold tailWord_4424964
  simp only [CollatzResearch.WordTrace]
  refine ⟨80695847970559313265036973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107594463960745751020049297 80695847970559313265036973)
  ·
    refine ⟨30260942988959742474388865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80695847970559313265036973 30260942988959742474388865)
    ·
      refine ⟨22695707241719806855791649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30260942988959742474388865 22695707241719806855791649)
      ·
        refine ⟨17021780431289855141843737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22695707241719806855791649 17021780431289855141843737)
        ·
          refine ⟨12766335323467391356382803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17021780431289855141843737 12766335323467391356382803)
          ·
            refine ⟨19149502985201087034574205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12766335323467391356382803 19149502985201087034574205)
            ·
              refine ⟨7181063619450407637965327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19149502985201087034574205 7181063619450407637965327)
              ·
                refine ⟨10771595429175611456947991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7181063619450407637965327 10771595429175611456947991)
                ·
                  refine ⟨16157393143763417185421987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10771595429175611456947991 16157393143763417185421987)
                  ·
                    refine ⟨24236089715645125778132981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16157393143763417185421987 24236089715645125778132981)
                    ·
                      refine ⟨2272133410841730541699967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24236089715645125778132981 2272133410841730541699967)
                      ·
                        rfl

theorem cell23_4424964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_4424964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4424964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4424964 prefixEnd_4424964 := by exact prefixLift 4424964
  have htrace : WordTrace (prefixWord ++ tailWord_4424964) baseStart_4424964 baseEnd_4424964 := by
    simpa [prefixWord, tailWord_4424964, baseEnd_4424964] using wordTrace_append hprefix tailTrace_4424964
  have hstable : (prefixWord ++ tailWord_4424964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4424964).length < 2 ^ (prefixWord ++ tailWord_4424964).sum := by decide
  have hdescent : baseEnd_4424964 < baseStart_4424964 := by decide
  rcases family_descends (prefixWord ++ tailWord_4424964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4424977 : List Nat := [1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 3]
def baseStart_4424977 : Nat := 118140960795 + 4424977 * 2 ^ 59
def prefixEnd_4424977 : Nat := 4983230072969 + 3 ^ 40 * 4424977 * 2
def baseEnd_4424977 : Nat := 2272140086090238990837407

theorem tailTrace_4424977 : CollatzResearch.WordTrace tailWord_4424977 prefixEnd_4424977 2272140086090238990837407 := by
  unfold tailWord_4424977
  simp only [CollatzResearch.WordTrace]
  refine ⟨161392170090071529750297185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107594780060047686500198123 161392170090071529750297185)
  ·
    refine ⟨121044127567553647312722889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161392170090071529750297185 121044127567553647312722889)
    ·
      refine ⟨90783095675665235484542167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121044127567553647312722889 90783095675665235484542167)
      ·
        refine ⟨136174643513497853226813251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90783095675665235484542167 136174643513497853226813251)
        ·
          refine ⟨204261965270246779840219877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136174643513497853226813251 204261965270246779840219877)
          ·
            refine ⟨38299118488171271220041227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 204261965270246779840219877 38299118488171271220041227)
            ·
              refine ⟨57448677732256906830061841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38299118488171271220041227 57448677732256906830061841)
              ·
                refine ⟨43086508299192680122546381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57448677732256906830061841 43086508299192680122546381)
                ·
                  refine ⟨16157440612197255045954893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43086508299192680122546381 16157440612197255045954893)
                  ·
                    refine ⟨6059040229573970642233085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16157440612197255045954893 6059040229573970642233085)
                    ·
                      refine ⟨2272140086090238990837407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6059040229573970642233085 2272140086090238990837407)
                      ·
                        rfl

theorem cell23_4424977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 3].length) (baseStart_4424977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4424977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4424977 prefixEnd_4424977 := by exact prefixLift 4424977
  have htrace : WordTrace (prefixWord ++ tailWord_4424977) baseStart_4424977 baseEnd_4424977 := by
    simpa [prefixWord, tailWord_4424977, baseEnd_4424977] using wordTrace_append hprefix tailTrace_4424977
  have hstable : (prefixWord ++ tailWord_4424977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4424977).length < 2 ^ (prefixWord ++ tailWord_4424977).sum := by decide
  have hdescent : baseEnd_4424977 < baseStart_4424977 := by decide
  rcases family_descends (prefixWord ++ tailWord_4424977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4425028 : List Nat := [2, 3, 4, 1, 1, 2, 1, 1, 4, 1, 3]
def baseStart_4425028 : Nat := 118140960795 + 4425028 * 2 ^ 59
def prefixEnd_4425028 : Nat := 4983230072969 + 3 ^ 40 * 4425028 * 2
def baseEnd_4425028 : Nat := 2272166273603618291299673

theorem tailTrace_4425028 : CollatzResearch.WordTrace tailWord_4425028 prefixEnd_4425028 2272166273603618291299673 := by
  unfold tailWord_4425028
  simp only [CollatzResearch.WordTrace]
  refine ⟨80697015106443382730201869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107596020141924510306935825 80697015106443382730201869)
  ·
    refine ⟨30261380664916268523825701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80697015106443382730201869 30261380664916268523825701)
    ·
      refine ⟨5674008874671800348217319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30261380664916268523825701 5674008874671800348217319)
      ·
        refine ⟨8511013312007700522325979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5674008874671800348217319 8511013312007700522325979)
        ·
          refine ⟨12766519968011550783488969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8511013312007700522325979 12766519968011550783488969)
          ·
            refine ⟨9574889976008663087616727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12766519968011550783488969 9574889976008663087616727)
            ·
              refine ⟨14362334964012994631425091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9574889976008663087616727 14362334964012994631425091)
              ·
                refine ⟨21543502446019491947137637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14362334964012994631425091 21543502446019491947137637)
                ·
                  refine ⟨4039406708628654740088307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21543502446019491947137637 4039406708628654740088307)
                  ·
                    refine ⟨6059110062942982110132461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4039406708628654740088307 6059110062942982110132461)
                    ·
                      refine ⟨2272166273603618291299673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6059110062942982110132461 2272166273603618291299673)
                      ·
                        rfl

theorem cell23_4425028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_4425028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4425028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4425028 prefixEnd_4425028 := by exact prefixLift 4425028
  have htrace : WordTrace (prefixWord ++ tailWord_4425028) baseStart_4425028 baseEnd_4425028 := by
    simpa [prefixWord, tailWord_4425028, baseEnd_4425028] using wordTrace_append hprefix tailTrace_4425028
  have hstable : (prefixWord ++ tailWord_4425028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4425028).length < 2 ^ (prefixWord ++ tailWord_4425028).sum := by decide
  have hdescent : baseEnd_4425028 < baseStart_4425028 := by decide
  rcases family_descends (prefixWord ++ tailWord_4425028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4425034 : List Nat := [3, 1, 2, 1, 1, 1, 1, 4, 3, 4, 2]
def baseStart_4425034 : Nat := 118140960795 + 4425034 * 2 ^ 59
def prefixEnd_4425034 : Nat := 4983230072969 + 3 ^ 40 * 4425034 * 2
def baseEnd_4425034 : Nat := 2272169354487545267824645

theorem tailTrace_4425034 : CollatzResearch.WordTrace tailWord_4425034 prefixEnd_4425034 2272169354487545267824645 := by
  unfold tailWord_4425034
  simp only [CollatzResearch.WordTrace]
  refine ⟨40348562262716257121280539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107596166033910018990081437 40348562262716257121280539)
  ·
    refine ⟨60522843394074385681920809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40348562262716257121280539 60522843394074385681920809)
    ·
      refine ⟨45392132545555789261440607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60522843394074385681920809 45392132545555789261440607)
      ·
        refine ⟨68088198818333683892160911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45392132545555789261440607 68088198818333683892160911)
        ·
          refine ⟨102132298227500525838241367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68088198818333683892160911 102132298227500525838241367)
          ·
            refine ⟨153198447341250788757362051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102132298227500525838241367 153198447341250788757362051)
            ·
              refine ⟨229797671011876183136043077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 153198447341250788757362051 229797671011876183136043077)
              ·
                refine ⟨43087063314726784338008077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 229797671011876183136043077 43087063314726784338008077)
                ·
                  refine ⟨16157648743022544126753029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43087063314726784338008077 16157648743022544126753029)
                  ·
                    refine ⟨3029559139316727023766193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16157648743022544126753029 3029559139316727023766193)
                    ·
                      refine ⟨2272169354487545267824645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3029559139316727023766193 2272169354487545267824645)
                      ·
                        rfl

theorem cell23_4425034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 3, 4, 2].length) (baseStart_4425034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4425034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4425034 prefixEnd_4425034 := by exact prefixLift 4425034
  have htrace : WordTrace (prefixWord ++ tailWord_4425034) baseStart_4425034 baseEnd_4425034 := by
    simpa [prefixWord, tailWord_4425034, baseEnd_4425034] using wordTrace_append hprefix tailTrace_4425034
  have hstable : (prefixWord ++ tailWord_4425034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4425034).length < 2 ^ (prefixWord ++ tailWord_4425034).sum := by decide
  have hdescent : baseEnd_4425034 < baseStart_4425034 := by decide
  rcases family_descends (prefixWord ++ tailWord_4425034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4425141 : List Nat := [1, 3, 3, 2, 2, 1, 2, 2, 2, 1, 4]
def baseStart_4425141 : Nat := 118140960795 + 4425141 * 2 ^ 59
def prefixEnd_4425141 : Nat := 4983230072969 + 3 ^ 40 * 4425141 * 2
def baseEnd_4425141 : Nat := 2272224296917576349186653

theorem tailTrace_4425141 : CollatzResearch.WordTrace tailWord_4425141 prefixEnd_4425141 2272224296917576349186653 := by
  unfold tailWord_4425141
  simp only [CollatzResearch.WordTrace]
  refine ⟨161398151661477385759267277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107598767774318257172844851 161398151661477385759267277)
  ·
    refine ⟨60524306873054019659725229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 161398151661477385759267277 60524306873054019659725229)
    ·
      refine ⟨22696615077395257372396961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60524306873054019659725229 22696615077395257372396961)
      ·
        refine ⟨17022461308046443029297721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22696615077395257372396961 17022461308046443029297721)
        ·
          refine ⟨12766845981034832271973291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17022461308046443029297721 12766845981034832271973291)
          ·
            refine ⟨19150268971552248407959937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12766845981034832271973291 19150268971552248407959937)
            ·
              refine ⟨14362701728664186305969953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19150268971552248407959937 14362701728664186305969953)
              ·
                refine ⟨10772026296498139729477465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14362701728664186305969953 10772026296498139729477465)
                ·
                  refine ⟨8079019722373604797108099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10772026296498139729477465 8079019722373604797108099)
                  ·
                    refine ⟨12118529583560407195662149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8079019722373604797108099 12118529583560407195662149)
                    ·
                      refine ⟨2272224296917576349186653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12118529583560407195662149 2272224296917576349186653)
                      ·
                        rfl

theorem cell23_4425141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_4425141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4425141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4425141 prefixEnd_4425141 := by exact prefixLift 4425141
  have htrace : WordTrace (prefixWord ++ tailWord_4425141) baseStart_4425141 baseEnd_4425141 := by
    simpa [prefixWord, tailWord_4425141, baseEnd_4425141] using wordTrace_append hprefix tailTrace_4425141
  have hstable : (prefixWord ++ tailWord_4425141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4425141).length < 2 ^ (prefixWord ++ tailWord_4425141).sum := by decide
  have hdescent : baseEnd_4425141 < baseStart_4425141 := by decide
  rcases family_descends (prefixWord ++ tailWord_4425141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4425178 : List Nat := [3, 1, 1, 2, 3, 4, 1, 1, 2, 2, 3]
def baseStart_4425178 : Nat := 118140960795 + 4425178 * 2 ^ 59
def prefixEnd_4425178 : Nat := 4983230072969 + 3 ^ 40 * 4425178 * 2
def baseEnd_4425178 : Nat := 2272243295701792704423983

theorem tailTrace_4425178 : CollatzResearch.WordTrace tailWord_4425178 prefixEnd_4425178 2272243295701792704423983 := by
  unfold tailWord_4425178
  simp only [CollatzResearch.WordTrace]
  refine ⟨40349875290585835269591047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107599667441562227385576125 40349875290585835269591047)
  ·
    refine ⟨60524812935878752904386571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40349875290585835269591047 60524812935878752904386571)
    ·
      refine ⟨90787219403818129356579857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60524812935878752904386571 90787219403818129356579857)
      ·
        refine ⟨68090414552863597017434893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90787219403818129356579857 68090414552863597017434893)
        ·
          refine ⟨25533905457323848881538085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68090414552863597017434893 25533905457323848881538085)
          ·
            refine ⟨4787607273248221665288391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25533905457323848881538085 4787607273248221665288391)
            ·
              refine ⟨7181410909872332497932587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4787607273248221665288391 7181410909872332497932587)
              ·
                refine ⟨10772116364808498746898881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7181410909872332497932587 10772116364808498746898881)
                ·
                  refine ⟨8079087273606374060174161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10772116364808498746898881 8079087273606374060174161)
                  ·
                    refine ⟨6059315455204780545130621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8079087273606374060174161 6059315455204780545130621)
                    ·
                      refine ⟨2272243295701792704423983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6059315455204780545130621 2272243295701792704423983)
                      ·
                        rfl

theorem cell23_4425178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 1, 2, 2, 3].length) (baseStart_4425178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4425178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4425178 prefixEnd_4425178 := by exact prefixLift 4425178
  have htrace : WordTrace (prefixWord ++ tailWord_4425178) baseStart_4425178 baseEnd_4425178 := by
    simpa [prefixWord, tailWord_4425178, baseEnd_4425178] using wordTrace_append hprefix tailTrace_4425178
  have hstable : (prefixWord ++ tailWord_4425178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4425178).length < 2 ^ (prefixWord ++ tailWord_4425178).sum := by decide
  have hdescent : baseEnd_4425178 < baseStart_4425178 := by decide
  rcases family_descends (prefixWord ++ tailWord_4425178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4425208 : List Nat := [2, 1, 2, 1, 1, 6, 2, 1, 3, 1, 3]
def baseStart_4425208 : Nat := 118140960795 + 4425208 * 2 ^ 59
def prefixEnd_4425208 : Nat := 4983230072969 + 3 ^ 40 * 4425208 * 2
def baseEnd_4425208 : Nat := 2272258700121427587048845

theorem tailTrace_4425208 : CollatzResearch.WordTrace tailWord_4425208 prefixEnd_4425208 2272258700121427587048845 := by
  unfold tailWord_4425208
  simp only [CollatzResearch.WordTrace]
  refine ⟨80700297676117328100978139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107600396901489770801304185 80700297676117328100978139)
  ·
    refine ⟨121050446514175992151467209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80700297676117328100978139 121050446514175992151467209)
    ·
      refine ⟨90787834885631994113600407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121050446514175992151467209 90787834885631994113600407)
      ·
        refine ⟨136181752328447991170400611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90787834885631994113600407 136181752328447991170400611)
        ·
          refine ⟨204272628492671986755600917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136181752328447991170400611 204272628492671986755600917)
          ·
            refine ⟨9575279460593999379168793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 204272628492671986755600917 9575279460593999379168793)
            ·
              refine ⟨7181459595445499534376595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9575279460593999379168793 7181459595445499534376595)
              ·
                refine ⟨10772189393168249301564893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7181459595445499534376595 10772189393168249301564893)
                ·
                  refine ⟨4039571022438093488086835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10772189393168249301564893 4039571022438093488086835)
                  ·
                    refine ⟨6059356533657140232130253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4039571022438093488086835 6059356533657140232130253)
                    ·
                      refine ⟨2272258700121427587048845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6059356533657140232130253 2272258700121427587048845)
                      ·
                        rfl

theorem cell23_4425208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 1, 3, 1, 3].length) (baseStart_4425208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4425208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4425208 prefixEnd_4425208 := by exact prefixLift 4425208
  have htrace : WordTrace (prefixWord ++ tailWord_4425208) baseStart_4425208 baseEnd_4425208 := by
    simpa [prefixWord, tailWord_4425208, baseEnd_4425208] using wordTrace_append hprefix tailTrace_4425208
  have hstable : (prefixWord ++ tailWord_4425208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4425208).length < 2 ^ (prefixWord ++ tailWord_4425208).sum := by decide
  have hdescent : baseEnd_4425208 < baseStart_4425208 := by decide
  rcases family_descends (prefixWord ++ tailWord_4425208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4425228 : List Nat := [2, 2, 1, 2, 5, 1, 2, 2, 1, 5]
def baseStart_4425228 : Nat := 118140960795 + 4425228 * 2 ^ 59
def prefixEnd_4425228 : Nat := 4983230072969 + 3 ^ 40 * 4425228 * 2
def baseEnd_4425228 : Nat := 757422989911505836266251

theorem tailTrace_4425228 : CollatzResearch.WordTrace tailWord_4425228 prefixEnd_4425228 757422989911505836266251 := by
  unfold tailWord_4425228
  simp only [CollatzResearch.WordTrace]
  refine ⟨80700662406081099808842169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107600883208108133078456225 80700662406081099808842169)
  ·
    refine ⟨60525496804560824856631627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80700662406081099808842169 60525496804560824856631627)
    ·
      refine ⟨90788245206841237284947441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60525496804560824856631627 90788245206841237284947441)
      ·
        refine ⟨68091183905130927963710581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90788245206841237284947441 68091183905130927963710581)
        ·
          refine ⟨6383548491106024496597867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 68091183905130927963710581 6383548491106024496597867)
          ·
            refine ⟨9575322736659036744896801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6383548491106024496597867 9575322736659036744896801)
            ·
              refine ⟨7181492052494277558672601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9575322736659036744896801 7181492052494277558672601)
              ·
                refine ⟨5386119039370708169004451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7181492052494277558672601 5386119039370708169004451)
                ·
                  refine ⟨8079178559056062253506677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5386119039370708169004451 8079178559056062253506677)
                  ·
                    refine ⟨757422989911505836266251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8079178559056062253506677 757422989911505836266251)
                    ·
                      rfl

theorem cell23_4425228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 2, 1, 5].length) (baseStart_4425228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4425228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4425228 prefixEnd_4425228 := by exact prefixLift 4425228
  have htrace : WordTrace (prefixWord ++ tailWord_4425228) baseStart_4425228 baseEnd_4425228 := by
    simpa [prefixWord, tailWord_4425228, baseEnd_4425228] using wordTrace_append hprefix tailTrace_4425228
  have hstable : (prefixWord ++ tailWord_4425228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4425228).length < 2 ^ (prefixWord ++ tailWord_4425228).sum := by decide
  have hdescent : baseEnd_4425228 < baseStart_4425228 := by decide
  rcases family_descends (prefixWord ++ tailWord_4425228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4425248 : List Nat := [2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 4]
def baseStart_4425248 : Nat := 118140960795 + 4425248 * 2 ^ 59
def prefixEnd_4425248 : Nat := 4983230072969 + 3 ^ 40 * 4425248 * 2
def baseEnd_4425248 : Nat := 2272279239347607430548661

theorem tailTrace_4425248 : CollatzResearch.WordTrace tailWord_4425248 prefixEnd_4425248 2272279239347607430548661 := by
  unfold tailWord_4425248
  simp only [CollatzResearch.WordTrace]
  refine ⟨80701027136044871516706199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107601369514726495355608265 80701027136044871516706199)
  ·
    refine ⟨121051540704067307275059299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80701027136044871516706199 121051540704067307275059299)
    ·
      refine ⟨181577311056100960912588949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121051540704067307275059299 181577311056100960912588949)
      ·
        refine ⟨8511436455754732542777607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 181577311056100960912588949 8511436455754732542777607)
        ·
          refine ⟨12767154683632098814166411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8511436455754732542777607 12767154683632098814166411)
          ·
            refine ⟨19150732025448148221249617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12767154683632098814166411 19150732025448148221249617)
            ·
              refine ⟨14363049019086111165937213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19150732025448148221249617 14363049019086111165937213)
              ·
                refine ⟨5386143382157291687226455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14363049019086111165937213 5386143382157291687226455)
                ·
                  refine ⟨8079215073235937530839683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5386143382157291687226455 8079215073235937530839683)
                  ·
                    refine ⟨12118822609853906296259525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8079215073235937530839683 12118822609853906296259525)
                    ·
                      refine ⟨2272279239347607430548661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12118822609853906296259525 2272279239347607430548661)
                      ·
                        rfl

theorem cell23_4425248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_4425248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4425248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4425248 prefixEnd_4425248 := by exact prefixLift 4425248
  have htrace : WordTrace (prefixWord ++ tailWord_4425248) baseStart_4425248 baseEnd_4425248 := by
    simpa [prefixWord, tailWord_4425248, baseEnd_4425248] using wordTrace_append hprefix tailTrace_4425248
  have hstable : (prefixWord ++ tailWord_4425248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4425248).length < 2 ^ (prefixWord ++ tailWord_4425248).sum := by decide
  have hdescent : baseEnd_4425248 < baseStart_4425248 := by decide
  rcases family_descends (prefixWord ++ tailWord_4425248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4425258 : List Nat := [3, 1, 4, 1, 1, 1, 2, 4, 2, 4]
def baseStart_4425258 : Nat := 118140960795 + 4425258 * 2 ^ 59
def prefixEnd_4425258 : Nat := 4983230072969 + 3 ^ 40 * 4425258 * 2
def baseEnd_4425258 : Nat := 757428124718050797141205

theorem tailTrace_4425258 : CollatzResearch.WordTrace tailWord_4425258 prefixEnd_4425258 757428124718050797141205 := by
  unfold tailWord_4425258
  simp only [CollatzResearch.WordTrace]
  refine ⟨40350604750513378685319107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107601612668035676494184285 40350604750513378685319107)
  ·
    refine ⟨60525907125770068027978661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40350604750513378685319107 60525907125770068027978661)
    ·
      refine ⟨11348607586081887755245999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60525907125770068027978661 11348607586081887755245999)
      ·
        refine ⟨17022911379122831632868999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11348607586081887755245999 17022911379122831632868999)
        ·
          refine ⟨25534367068684247449303499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17022911379122831632868999 25534367068684247449303499)
          ·
            refine ⟨38301550603026371173955249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25534367068684247449303499 38301550603026371173955249)
            ·
              refine ⟨28726162952269778380466437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38301550603026371173955249 28726162952269778380466437)
              ·
                refine ⟨5386155553550583446337457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28726162952269778380466437 5386155553550583446337457)
                ·
                  refine ⟨4039616665162937584753093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5386155553550583446337457 4039616665162937584753093)
                  ·
                    refine ⟨757428124718050797141205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4039616665162937584753093 757428124718050797141205)
                    ·
                      rfl

theorem cell23_4425258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_4425258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4425258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4425258 prefixEnd_4425258 := by exact prefixLift 4425258
  have htrace : WordTrace (prefixWord ++ tailWord_4425258) baseStart_4425258 baseEnd_4425258 := by
    simpa [prefixWord, tailWord_4425258, baseEnd_4425258] using wordTrace_append hprefix tailTrace_4425258
  have hstable : (prefixWord ++ tailWord_4425258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4425258).length < 2 ^ (prefixWord ++ tailWord_4425258).sum := by decide
  have hdescent : baseEnd_4425258 < baseStart_4425258 := by decide
  rcases family_descends (prefixWord ++ tailWord_4425258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4425274 : List Nat := [3, 1, 1, 1, 3, 2, 1, 1, 2, 2, 6]
def baseStart_4425274 : Nat := 118140960795 + 4425274 * 2 ^ 59
def prefixEnd_4425274 : Nat := 4983230072969 + 3 ^ 40 * 4425274 * 2
def baseEnd_4425274 : Nat := 2272292589844624328823541

theorem tailTrace_4425274 : CollatzResearch.WordTrace tailWord_4425274 prefixEnd_4425274 2272292589844624328823541 := by
  unfold tailWord_4425274
  simp only [CollatzResearch.WordTrace]
  refine ⟨40350750642498887368464719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107602001713330366315905917 40350750642498887368464719)
  ·
    refine ⟨60526125963748331052697079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40350750642498887368464719 60526125963748331052697079)
    ·
      refine ⟨90789188945622496579045619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60526125963748331052697079 90789188945622496579045619)
      ·
        refine ⟨136183783418433744868568429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90789188945622496579045619 136183783418433744868568429)
        ·
          refine ⟨51068918781912654325713161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 136183783418433744868568429 51068918781912654325713161)
          ·
            refine ⟨38301689086434490744284871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51068918781912654325713161 38301689086434490744284871)
            ·
              refine ⟨57452533629651736116427307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38301689086434490744284871 57452533629651736116427307)
              ·
                refine ⟨86178800444477604174640961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57452533629651736116427307 86178800444477604174640961)
                ·
                  refine ⟨64634100333358203130980721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 86178800444477604174640961 64634100333358203130980721)
                  ·
                    refine ⟨48475575250018652348235541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 64634100333358203130980721 48475575250018652348235541)
                    ·
                      refine ⟨2272292589844624328823541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48475575250018652348235541 2272292589844624328823541)
                      ·
                        rfl

theorem cell23_4425274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 2, 2, 6].length) (baseStart_4425274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4425274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4425274 prefixEnd_4425274 := by exact prefixLift 4425274
  have htrace : WordTrace (prefixWord ++ tailWord_4425274) baseStart_4425274 baseEnd_4425274 := by
    simpa [prefixWord, tailWord_4425274, baseEnd_4425274] using wordTrace_append hprefix tailTrace_4425274
  have hstable : (prefixWord ++ tailWord_4425274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4425274).length < 2 ^ (prefixWord ++ tailWord_4425274).sum := by decide
  have hdescent : baseEnd_4425274 < baseStart_4425274 := by decide
  rcases family_descends (prefixWord ++ tailWord_4425274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4425298 : List Nat := [3, 2, 2, 1, 2, 3, 1, 2, 1, 3, 3]
def baseStart_4425298 : Nat := 118140960795 + 4425298 * 2 ^ 59
def prefixEnd_4425298 : Nat := 4983230072969 + 3 ^ 40 * 4425298 * 2
def baseEnd_4425298 : Nat := 2272304913380332234923431

theorem tailTrace_4425298 : CollatzResearch.WordTrace tailWord_4425298 prefixEnd_4425298 2272304913380332234923431 := by
  unfold tailWord_4425298
  simp only [CollatzResearch.WordTrace]
  refine ⟨40350969480477150393183137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107602585281272401048488365 40350969480477150393183137)
  ·
    refine ⟨30263227110357862794887353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40350969480477150393183137 30263227110357862794887353)
    ·
      refine ⟨22697420332768397096165515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30263227110357862794887353 22697420332768397096165515)
      ·
        refine ⟨34046130499152595644248273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22697420332768397096165515 34046130499152595644248273)
        ·
          refine ⟨25534597874364446733186205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34046130499152595644248273 25534597874364446733186205)
          ·
            refine ⟨9575474202886667524944827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25534597874364446733186205 9575474202886667524944827)
            ·
              refine ⟨14363211304330001287417241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9575474202886667524944827 14363211304330001287417241)
              ·
                refine ⟨10772408478247500965562931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14363211304330001287417241 10772408478247500965562931)
                ·
                  refine ⟨16158612717371251448344397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10772408478247500965562931 16158612717371251448344397)
                  ·
                    refine ⟨6059479769014219293129149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16158612717371251448344397 6059479769014219293129149)
                    ·
                      refine ⟨2272304913380332234923431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6059479769014219293129149 2272304913380332234923431)
                      ·
                        rfl

theorem cell23_4425298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 2, 1, 3, 3].length) (baseStart_4425298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4425298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4425298 prefixEnd_4425298 := by exact prefixLift 4425298
  have htrace : WordTrace (prefixWord ++ tailWord_4425298) baseStart_4425298 baseEnd_4425298 := by
    simpa [prefixWord, tailWord_4425298, baseEnd_4425298] using wordTrace_append hprefix tailTrace_4425298
  have hstable : (prefixWord ++ tailWord_4425298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4425298).length < 2 ^ (prefixWord ++ tailWord_4425298).sum := by decide
  have hdescent : baseEnd_4425298 < baseStart_4425298 := by decide
  rcases family_descends (prefixWord ++ tailWord_4425298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4425315 : List Nat := [1, 1, 1, 5, 1, 4, 2, 2, 2, 1, 3]
def baseStart_4425315 : Nat := 118140960795 + 4425315 * 2 ^ 59
def prefixEnd_4425315 : Nat := 4983230072969 + 3 ^ 40 * 4425315 * 2
def baseEnd_4425315 : Nat := 2272313642551458668410853

theorem tailTrace_4425315 : CollatzResearch.WordTrace tailWord_4425315 prefixEnd_4425315 2272313642551458668410853 := by
  unfold tailWord_4425315
  simp only [CollatzResearch.WordTrace]
  refine ⟨161404497962847013476101399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107602998641898008984067599 161404497962847013476101399)
  ·
    refine ⟨242106746944270520214152099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161404497962847013476101399 242106746944270520214152099)
    ·
      refine ⟨363160120416405780321228149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242106746944270520214152099 363160120416405780321228149)
      ·
        refine ⟨34046261289038041905115139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 363160120416405780321228149 34046261289038041905115139)
        ·
          refine ⟨51069391933557062857672709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34046261289038041905115139 51069391933557062857672709)
          ·
            refine ⟨9575510987541949285813633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51069391933557062857672709 9575510987541949285813633)
            ·
              refine ⟨7181633240656461964360225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9575510987541949285813633 7181633240656461964360225)
              ·
                refine ⟨5386224930492346473270169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7181633240656461964360225 5386224930492346473270169)
                ·
                  refine ⟨4039668697869259854952627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5386224930492346473270169 4039668697869259854952627)
                  ·
                    refine ⟨6059503046803889782428941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4039668697869259854952627 6059503046803889782428941)
                    ·
                      refine ⟨2272313642551458668410853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6059503046803889782428941 2272313642551458668410853)
                      ·
                        rfl

theorem cell23_4425315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 2, 2, 1, 3].length) (baseStart_4425315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4425315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4425315 prefixEnd_4425315 := by exact prefixLift 4425315
  have htrace : WordTrace (prefixWord ++ tailWord_4425315) baseStart_4425315 baseEnd_4425315 := by
    simpa [prefixWord, tailWord_4425315, baseEnd_4425315] using wordTrace_append hprefix tailTrace_4425315
  have hstable : (prefixWord ++ tailWord_4425315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4425315).length < 2 ^ (prefixWord ++ tailWord_4425315).sum := by decide
  have hdescent : baseEnd_4425315 < baseStart_4425315 := by decide
  rcases family_descends (prefixWord ++ tailWord_4425315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4425372 : List Nat := [2, 2, 3, 2, 3, 1, 1, 1, 4, 2, 2]
def baseStart_4425372 : Nat := 118140960795 + 4425372 * 2 ^ 59
def prefixEnd_4425372 : Nat := 4983230072969 + 3 ^ 40 * 4425372 * 2
def baseEnd_4425372 : Nat := 2272342910948764945398091

theorem tailTrace_4425372 : CollatzResearch.WordTrace tailWord_4425372 prefixEnd_4425372 2272342910948764945398091 := by
  unfold tailWord_4425372
  simp only [CollatzResearch.WordTrace]
  refine ⟨80703288461820256105463185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107604384615760341473950913 80703288461820256105463185)
  ·
    refine ⟨60527466346365192079097389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80703288461820256105463185 60527466346365192079097389)
    ·
      refine ⟨22697799879886947029661521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60527466346365192079097389 22697799879886947029661521)
      ·
        refine ⟨17023349909915210272246141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22697799879886947029661521 17023349909915210272246141)
        ·
          refine ⟨6383756216218203852092303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17023349909915210272246141 6383756216218203852092303)
          ·
            refine ⟨9575634324327305778138455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6383756216218203852092303 9575634324327305778138455)
            ·
              refine ⟨14363451486490958667207683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9575634324327305778138455 14363451486490958667207683)
              ·
                refine ⟨21545177229736438000811525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14363451486490958667207683 21545177229736438000811525)
                ·
                  refine ⟨4039720730575582125152161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21545177229736438000811525 4039720730575582125152161)
                  ·
                    refine ⟨3029790547931686593864121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4039720730575582125152161 3029790547931686593864121)
                    ·
                      refine ⟨2272342910948764945398091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3029790547931686593864121 2272342910948764945398091)
                      ·
                        rfl

theorem cell23_4425372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 1, 4, 2, 2].length) (baseStart_4425372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4425372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4425372 prefixEnd_4425372 := by exact prefixLift 4425372
  have htrace : WordTrace (prefixWord ++ tailWord_4425372) baseStart_4425372 baseEnd_4425372 := by
    simpa [prefixWord, tailWord_4425372, baseEnd_4425372] using wordTrace_append hprefix tailTrace_4425372
  have hstable : (prefixWord ++ tailWord_4425372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4425372).length < 2 ^ (prefixWord ++ tailWord_4425372).sum := by decide
  have hdescent : baseEnd_4425372 < baseStart_4425372 := by decide
  rcases family_descends (prefixWord ++ tailWord_4425372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4425389 : List Nat := [1, 5, 2, 1, 1, 1, 5, 1, 2, 2, 2]
def baseStart_4425389 : Nat := 118140960795 + 4425389 * 2 ^ 59
def prefixEnd_4425389 : Nat := 4983230072969 + 3 ^ 40 * 4425389 * 2
def baseEnd_4425389 : Nat := 2272351640119891378885513

theorem tailTrace_4425389 : CollatzResearch.WordTrace tailWord_4425389 prefixEnd_4425389 2272351640119891378885513 := by
  unfold tailWord_4425389
  simp only [CollatzResearch.WordTrace]
  refine ⟨161407196964578924114295221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107604797976385949409530147 161407196964578924114295221)
  ·
    refine ⟨15131924715429274135715177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 161407196964578924114295221 15131924715429274135715177)
    ·
      refine ⟨11348943536571955601786383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15131924715429274135715177 11348943536571955601786383)
      ·
        refine ⟨17023415304857933402679575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11348943536571955601786383 17023415304857933402679575)
        ·
          refine ⟨25535122957286900104019363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17023415304857933402679575 25535122957286900104019363)
          ·
            refine ⟨38302684435930350156029045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25535122957286900104019363 38302684435930350156029045)
            ·
              refine ⟨3590876665868470327127723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38302684435930350156029045 3590876665868470327127723)
              ·
                refine ⟨5386314998802705490691585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3590876665868470327127723 5386314998802705490691585)
                ·
                  refine ⟨4039736249102029118018689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5386314998802705490691585 4039736249102029118018689)
                  ·
                    refine ⟨3029802186826521838514017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4039736249102029118018689 3029802186826521838514017)
                    ·
                      refine ⟨2272351640119891378885513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3029802186826521838514017 2272351640119891378885513)
                      ·
                        rfl

theorem cell23_4425389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 5, 1, 2, 2, 2].length) (baseStart_4425389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4425389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4425389 prefixEnd_4425389 := by exact prefixLift 4425389
  have htrace : WordTrace (prefixWord ++ tailWord_4425389) baseStart_4425389 baseEnd_4425389 := by
    simpa [prefixWord, tailWord_4425389, baseEnd_4425389] using wordTrace_append hprefix tailTrace_4425389
  have hstable : (prefixWord ++ tailWord_4425389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4425389).length < 2 ^ (prefixWord ++ tailWord_4425389).sum := by decide
  have hdescent : baseEnd_4425389 < baseStart_4425389 := by decide
  rcases family_descends (prefixWord ++ tailWord_4425389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4425411 : List Nat := [1, 1, 1, 3, 1, 1, 1, 1, 8, 1, 4]
def baseStart_4425411 : Nat := 118140960795 + 4425411 * 2 ^ 59
def prefixEnd_4425411 : Nat := 4983230072969 + 3 ^ 40 * 4425411 * 2
def baseEnd_4425411 : Nat := 2272362936694290292810411

theorem tailTrace_4425411 : CollatzResearch.WordTrace tailWord_4425411 prefixEnd_4425411 2272362936694290292810411 := by
  unfold tailWord_4425411
  simp only [CollatzResearch.WordTrace]
  refine ⟨161407999370499221871596087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107605332913666147914397391 161407999370499221871596087)
  ·
    refine ⟨242111999055748832807394131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161407999370499221871596087 242111999055748832807394131)
    ·
      refine ⟨363167998583623249211091197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242111999055748832807394131 363167998583623249211091197)
      ·
        refine ⟨136187999468858718454159199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 363167998583623249211091197 136187999468858718454159199)
        ·
          refine ⟨204281999203288077681238799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136187999468858718454159199 204281999203288077681238799)
          ·
            refine ⟨306422998804932116521858199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 204281999203288077681238799 306422998804932116521858199)
            ·
              refine ⟨459634498207398174782787299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 306422998804932116521858199 459634498207398174782787299)
              ·
                refine ⟨689451747311097262174180949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 459634498207398174782787299 689451747311097262174180949)
                ·
                  refine ⟨8079512663801921041103683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 689451747311097262174180949 8079512663801921041103683)
                  ·
                    refine ⟨12119268995702881561655525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8079512663801921041103683 12119268995702881561655525)
                    ·
                      refine ⟨2272362936694290292810411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12119268995702881561655525 2272362936694290292810411)
                      ·
                        rfl

theorem cell23_4425411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 8, 1, 4].length) (baseStart_4425411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4425411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4425411 prefixEnd_4425411 := by exact prefixLift 4425411
  have htrace : WordTrace (prefixWord ++ tailWord_4425411) baseStart_4425411 baseEnd_4425411 := by
    simpa [prefixWord, tailWord_4425411, baseEnd_4425411] using wordTrace_append hprefix tailTrace_4425411
  have hstable : (prefixWord ++ tailWord_4425411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4425411).length < 2 ^ (prefixWord ++ tailWord_4425411).sum := by decide
  have hdescent : baseEnd_4425411 < baseStart_4425411 := by decide
  rcases family_descends (prefixWord ++ tailWord_4425411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4425498 : List Nat := [3, 1, 1, 3, 2, 2, 1, 2, 3, 5]
def baseStart_4425498 : Nat := 118140960795 + 4425498 * 2 ^ 59
def prefixEnd_4425498 : Nat := 4983230072969 + 3 ^ 40 * 4425498 * 2
def baseEnd_4425498 : Nat := 757469203170410484140837

theorem tailTrace_4425498 : CollatzResearch.WordTrace tailWord_4425498 prefixEnd_4425498 757469203170410484140837 := by
  unfold tailWord_4425498
  simp only [CollatzResearch.WordTrace]
  refine ⟨40352793130296008932503287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107607448347456023820008765 40352793130296008932503287)
  ·
    refine ⟨60529189695444013398754931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40352793130296008932503287 60529189695444013398754931)
    ·
      refine ⟨90793784543166020098132397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60529189695444013398754931 90793784543166020098132397)
      ·
        refine ⟨34047669203687257536799649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90793784543166020098132397 34047669203687257536799649)
        ·
          refine ⟨25535751902765443152599737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34047669203687257536799649 25535751902765443152599737)
          ·
            refine ⟨19151813927074082364449803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25535751902765443152599737 19151813927074082364449803)
            ·
              refine ⟨28727720890611123546674705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19151813927074082364449803 28727720890611123546674705)
              ·
                refine ⟨21545790667958342660006029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28727720890611123546674705 21545790667958342660006029)
                ·
                  refine ⟨8079671500484378497502261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21545790667958342660006029 8079671500484378497502261)
                  ·
                    refine ⟨757469203170410484140837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8079671500484378497502261 757469203170410484140837)
                    ·
                      rfl

theorem cell23_4425498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 2, 3, 5].length) (baseStart_4425498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4425498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4425498 prefixEnd_4425498 := by exact prefixLift 4425498
  have htrace : WordTrace (prefixWord ++ tailWord_4425498) baseStart_4425498 baseEnd_4425498 := by
    simpa [prefixWord, tailWord_4425498, baseEnd_4425498] using wordTrace_append hprefix tailTrace_4425498
  have hstable : (prefixWord ++ tailWord_4425498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4425498).length < 2 ^ (prefixWord ++ tailWord_4425498).sum := by decide
  have hdescent : baseEnd_4425498 < baseStart_4425498 := by decide
  rcases family_descends (prefixWord ++ tailWord_4425498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4425512 : List Nat := [2, 1, 5, 1, 1, 3, 1, 2, 3, 1, 3]
def baseStart_4425512 : Nat := 118140960795 + 4425512 * 2 ^ 59
def prefixEnd_4425512 : Nat := 4983230072969 + 3 ^ 40 * 4425512 * 2
def baseEnd_4425512 : Nat := 2272414798240394397647447

theorem tailTrace_4425512 : CollatzResearch.WordTrace tailWord_4425512 prefixEnd_4425512 2272414798240394397647447 := by
  unfold tailWord_4425512
  simp only [CollatzResearch.WordTrace]
  refine ⟨80705841571566658060511395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107607788762088877414015193 80705841571566658060511395)
  ·
    refine ⟨121058762357349987090767093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80705841571566658060511395 121058762357349987090767093)
    ·
      refine ⟨11349258971001561289759415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 121058762357349987090767093 11349258971001561289759415)
      ·
        refine ⟨17023888456502341934639123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11349258971001561289759415 17023888456502341934639123)
        ·
          refine ⟨25535832684753512901958685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17023888456502341934639123 25535832684753512901958685)
          ·
            refine ⟨9575937256782567338234507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25535832684753512901958685 9575937256782567338234507)
            ·
              refine ⟨14363905885173851007351761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9575937256782567338234507 14363905885173851007351761)
              ·
                refine ⟨10772929413880388255513821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14363905885173851007351761 10772929413880388255513821)
                ·
                  refine ⟨4039848530205145595817683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10772929413880388255513821 4039848530205145595817683)
                  ·
                    refine ⟨6059772795307718393726525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4039848530205145595817683 6059772795307718393726525)
                    ·
                      refine ⟨2272414798240394397647447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6059772795307718393726525 2272414798240394397647447)
                      ·
                        rfl

theorem cell23_4425512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_4425512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4425512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4425512 prefixEnd_4425512 := by exact prefixLift 4425512
  have htrace : WordTrace (prefixWord ++ tailWord_4425512) baseStart_4425512 baseEnd_4425512 := by
    simpa [prefixWord, tailWord_4425512, baseEnd_4425512] using wordTrace_append hprefix tailTrace_4425512
  have hstable : (prefixWord ++ tailWord_4425512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4425512).length < 2 ^ (prefixWord ++ tailWord_4425512).sum := by decide
  have hdescent : baseEnd_4425512 < baseStart_4425512 := by decide
  rcases family_descends (prefixWord ++ tailWord_4425512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4425522 : List Nat := [3, 2, 1, 1, 3, 2, 3, 1, 2, 3, 2]
def baseStart_4425522 : Nat := 118140960795 + 4425522 * 2 ^ 59
def prefixEnd_4425522 : Nat := 4983230072969 + 3 ^ 40 * 4425522 * 2
def baseEnd_4425522 : Nat := 2272419933046939358522401

theorem tailTrace_4425522 : CollatzResearch.WordTrace tailWord_4425522 prefixEnd_4425522 2272419933046939358522401 := by
  unfold tailWord_4425522
  simp only [CollatzResearch.WordTrace]
  refine ⟨40353011968274271957221705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107608031915398058552591213 40353011968274271957221705)
  ·
    refine ⟨30264758976205703967916279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40353011968274271957221705 30264758976205703967916279)
    ·
      refine ⟨45397138464308555951874419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30264758976205703967916279 45397138464308555951874419)
      ·
        refine ⟨68095707696462833927811629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45397138464308555951874419 68095707696462833927811629)
        ·
          refine ⟨25535890386173562722929361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68095707696462833927811629 25535890386173562722929361)
          ·
            refine ⟨19151917789630172042197021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25535890386173562722929361 19151917789630172042197021)
            ·
              refine ⟨7181969171111314515823883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19151917789630172042197021 7181969171111314515823883)
              ·
                refine ⟨10772953756666971773735825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7181969171111314515823883 10772953756666971773735825)
                ·
                  refine ⟨8079715317500228830301869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10772953756666971773735825 8079715317500228830301869)
                  ·
                    refine ⟨3029893244062585811363201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8079715317500228830301869 3029893244062585811363201)
                    ·
                      refine ⟨2272419933046939358522401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3029893244062585811363201 2272419933046939358522401)
                      ·
                        rfl

theorem cell23_4425522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 1, 2, 3, 2].length) (baseStart_4425522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4425522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4425522 prefixEnd_4425522 := by exact prefixLift 4425522
  have htrace : WordTrace (prefixWord ++ tailWord_4425522) baseStart_4425522 baseEnd_4425522 := by
    simpa [prefixWord, tailWord_4425522, baseEnd_4425522] using wordTrace_append hprefix tailTrace_4425522
  have hstable : (prefixWord ++ tailWord_4425522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4425522).length < 2 ^ (prefixWord ++ tailWord_4425522).sum := by decide
  have hdescent : baseEnd_4425522 < baseStart_4425522 := by decide
  rcases family_descends (prefixWord ++ tailWord_4425522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4425528 : List Nat := [2, 1, 2, 1, 3, 3, 2, 2, 1, 6]
def baseStart_4425528 : Nat := 118140960795 + 4425528 * 2 ^ 59
def prefixEnd_4425528 : Nat := 4983230072969 + 3 ^ 40 * 4425528 * 2
def baseEnd_4425528 : Nat := 757474337976955445015791

theorem tailTrace_4425528 : CollatzResearch.WordTrace tailWord_4425528 prefixEnd_4425528 757474337976955445015791 := by
  unfold tailWord_4425528
  simp only [CollatzResearch.WordTrace]
  refine ⟨80706133355537675426802619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107608177807383567235736825 80706133355537675426802619)
  ·
    refine ⟨121059200033306513140203929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80706133355537675426802619 121059200033306513140203929)
    ·
      refine ⟨90794400024979884855152947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121059200033306513140203929 90794400024979884855152947)
      ·
        refine ⟨136191600037469827282729421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90794400024979884855152947 136191600037469827282729421)
        ·
          refine ⟨51071850014051185231023533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 136191600037469827282729421 51071850014051185231023533)
          ·
            refine ⟨19151943755269194461633825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51071850014051185231023533 19151943755269194461633825)
            ·
              refine ⟨14363957816451895846225369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19151943755269194461633825 14363957816451895846225369)
              ·
                refine ⟨10772968362338921884669027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14363957816451895846225369 10772968362338921884669027)
                ·
                  refine ⟨16159452543508382827003541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10772968362338921884669027 16159452543508382827003541)
                  ·
                    refine ⟨757474337976955445015791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16159452543508382827003541 757474337976955445015791)
                    ·
                      rfl

theorem cell23_4425528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 2, 1, 6].length) (baseStart_4425528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4425528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4425528 prefixEnd_4425528 := by exact prefixLift 4425528
  have htrace : WordTrace (prefixWord ++ tailWord_4425528) baseStart_4425528 baseEnd_4425528 := by
    simpa [prefixWord, tailWord_4425528, baseEnd_4425528] using wordTrace_append hprefix tailTrace_4425528
  have hstable : (prefixWord ++ tailWord_4425528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4425528).length < 2 ^ (prefixWord ++ tailWord_4425528).sum := by decide
  have hdescent : baseEnd_4425528 < baseStart_4425528 := by decide
  rcases family_descends (prefixWord ++ tailWord_4425528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4425541 : List Nat := [1, 3, 1, 1, 1, 2, 14]
def baseStart_4425541 : Nat := 118140960795 + 4425541 * 2 ^ 59
def prefixEnd_4425541 : Nat := 4983230072969 + 3 ^ 40 * 4425541 * 2
def baseEnd_4425541 : Nat := 28054687520733022026973

theorem tailTrace_4425541 : CollatzResearch.WordTrace tailWord_4425541 prefixEnd_4425541 28054687520733022026973 := by
  unfold tailWord_4425541
  simp only [CollatzResearch.WordTrace]
  refine ⟨161412740860028254073828477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107608493906685502715885651 161412740860028254073828477)
  ·
    refine ⟨60529777822510595277685679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 161412740860028254073828477 60529777822510595277685679)
    ·
      refine ⟨90794666733765892916528519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60529777822510595277685679 90794666733765892916528519)
      ·
        refine ⟨136192000100648839374792779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90794666733765892916528519 136192000100648839374792779)
        ·
          refine ⟨204288000150973259062189169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136192000100648839374792779 204288000150973259062189169)
          ·
            refine ⟨153216000113229944296641877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 204288000150973259062189169 153216000113229944296641877)
            ·
              refine ⟨28054687520733022026973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 153216000113229944296641877 28054687520733022026973)
              ·
                rfl

theorem cell23_4425541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 14].length) (baseStart_4425541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4425541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4425541 prefixEnd_4425541 := by exact prefixLift 4425541
  have htrace : WordTrace (prefixWord ++ tailWord_4425541) baseStart_4425541 baseEnd_4425541 := by
    simpa [prefixWord, tailWord_4425541, baseEnd_4425541] using wordTrace_append hprefix tailTrace_4425541
  have hstable : (prefixWord ++ tailWord_4425541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4425541).length < 2 ^ (prefixWord ++ tailWord_4425541).sum := by decide
  have hdescent : baseEnd_4425541 < baseStart_4425541 := by decide
  rcases family_descends (prefixWord ++ tailWord_4425541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4425562 : List Nat := [3, 1, 1, 2, 1, 3, 5, 1, 2, 4]
def baseStart_4425562 : Nat := 118140960795 + 4425562 * 2 ^ 59
def prefixEnd_4425562 : Nat := 4983230072969 + 3 ^ 40 * 4425562 * 2
def baseEnd_4425562 : Nat := 757480157424373067340739

theorem tailTrace_4425562 : CollatzResearch.WordTrace tailWord_4425562 prefixEnd_4425562 757480157424373067340739 := by
  unfold tailWord_4425562
  simp only [CollatzResearch.WordTrace]
  refine ⟨40353376698238043665085735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107609004528634783106895293 40353376698238043665085735)
  ·
    refine ⟨60530065047357065497628603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40353376698238043665085735 60530065047357065497628603)
    ·
      refine ⟨90795097571035598246442905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60530065047357065497628603 90795097571035598246442905)
      ·
        refine ⟨68096323178276698684832179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90795097571035598246442905 68096323178276698684832179)
        ·
          refine ⟨102144484767415048027248269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68096323178276698684832179 102144484767415048027248269)
          ·
            refine ⟨38304181787780643010218101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102144484767415048027248269 38304181787780643010218101)
            ·
              refine ⟨3591017042604435282207947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38304181787780643010218101 3591017042604435282207947)
              ·
                refine ⟨5386525563906652923311921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3591017042604435282207947 5386525563906652923311921)
                ·
                  refine ⟨4039894172929989692483941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5386525563906652923311921 4039894172929989692483941)
                  ·
                    refine ⟨757480157424373067340739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4039894172929989692483941 757480157424373067340739)
                    ·
                      rfl

theorem cell23_4425562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 5, 1, 2, 4].length) (baseStart_4425562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4425562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4425562 prefixEnd_4425562 := by exact prefixLift 4425562
  have htrace : WordTrace (prefixWord ++ tailWord_4425562) baseStart_4425562 baseEnd_4425562 := by
    simpa [prefixWord, tailWord_4425562, baseEnd_4425562] using wordTrace_append hprefix tailTrace_4425562
  have hstable : (prefixWord ++ tailWord_4425562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4425562).length < 2 ^ (prefixWord ++ tailWord_4425562).sum := by decide
  have hdescent : baseEnd_4425562 < baseStart_4425562 := by decide
  rcases family_descends (prefixWord ++ tailWord_4425562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4425585 : List Nat := [1, 2, 2, 2, 1, 3, 1, 1, 6, 1, 3]
def baseStart_4425585 : Nat := 118140960795 + 4425585 * 2 ^ 59
def prefixEnd_4425585 : Nat := 4983230072969 + 3 ^ 40 * 4425585 * 2
def baseEnd_4425585 : Nat := 2272452282328172612034611

theorem tailTrace_4425585 : CollatzResearch.WordTrace tailWord_4425585 prefixEnd_4425585 2272452282328172612034611 := by
  unfold tailWord_4425585
  simp only [CollatzResearch.WordTrace]
  refine ⟨161414345671868849588430209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107609563781245899725620139 161414345671868849588430209)
  ·
    refine ⟨121060759253901637191322657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161414345671868849588430209 121060759253901637191322657)
    ·
      refine ⟨90795569440426227893491993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121060759253901637191322657 90795569440426227893491993)
      ·
        refine ⟨68096677080319670920118995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90795569440426227893491993 68096677080319670920118995)
        ·
          refine ⟨102145015620479506380178493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68096677080319670920118995 102145015620479506380178493)
          ·
            refine ⟨38304380857679814892566935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102145015620479506380178493 38304380857679814892566935)
            ·
              refine ⟨57456571286519722338850403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38304380857679814892566935 57456571286519722338850403)
              ·
                refine ⟨86184856929779583508275605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57456571286519722338850403 86184856929779583508275605)
                ·
                  refine ⟨4039915168583417976950419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 86184856929779583508275605 4039915168583417976950419)
                  ·
                    refine ⟨6059872752875126965425629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4039915168583417976950419 6059872752875126965425629)
                    ·
                      refine ⟨2272452282328172612034611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6059872752875126965425629 2272452282328172612034611)
                      ·
                        rfl

theorem cell23_4425585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 6, 1, 3].length) (baseStart_4425585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4425585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4425585 prefixEnd_4425585 := by exact prefixLift 4425585
  have htrace : WordTrace (prefixWord ++ tailWord_4425585) baseStart_4425585 baseEnd_4425585 := by
    simpa [prefixWord, tailWord_4425585, baseEnd_4425585] using wordTrace_append hprefix tailTrace_4425585
  have hstable : (prefixWord ++ tailWord_4425585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4425585).length < 2 ^ (prefixWord ++ tailWord_4425585).sum := by decide
  have hdescent : baseEnd_4425585 < baseStart_4425585 := by decide
  rcases family_descends (prefixWord ++ tailWord_4425585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4425595 : List Nat := [1, 1, 1, 1, 1, 5, 1, 2, 5, 3, 2]
def baseStart_4425595 : Nat := 118140960795 + 4425595 * 2 ^ 59
def prefixEnd_4425595 : Nat := 4983230072969 + 3 ^ 40 * 4425595 * 2
def baseEnd_4425595 : Nat := 2272457417134717572909565

theorem tailTrace_4425595 : CollatzResearch.WordTrace tailWord_4425595 prefixEnd_4425595 2272457417134717572909565 := by
  unfold tailWord_4425595
  simp only [CollatzResearch.WordTrace]
  refine ⟨161414710401832621296294239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107609806934555080864196159 161414710401832621296294239)
  ·
    refine ⟨242122065602748931944441359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161414710401832621296294239 242122065602748931944441359)
    ·
      refine ⟨363183098404123397916662039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242122065602748931944441359 363183098404123397916662039)
      ·
        refine ⟨544774647606185096874993059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 363183098404123397916662039 544774647606185096874993059)
        ·
          refine ⟨817161971409277645312489589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 544774647606185096874993059 817161971409277645312489589)
          ·
            refine ⟨76608934819619779248045899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 817161971409277645312489589 76608934819619779248045899)
            ·
              refine ⟨114913402229429668872068849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76608934819619779248045899 114913402229429668872068849)
              ·
                refine ⟨86185051672072251654051637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 114913402229429668872068849 86185051672072251654051637)
                ·
                  refine ⟨8079848594256773592567341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 86185051672072251654051637 8079848594256773592567341)
                  ·
                    refine ⟨3029943222846290097212753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8079848594256773592567341 3029943222846290097212753)
                    ·
                      refine ⟨2272457417134717572909565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3029943222846290097212753 2272457417134717572909565)
                      ·
                        rfl

theorem cell23_4425595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 5, 3, 2].length) (baseStart_4425595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4425595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4425595 prefixEnd_4425595 := by exact prefixLift 4425595
  have htrace : WordTrace (prefixWord ++ tailWord_4425595) baseStart_4425595 baseEnd_4425595 := by
    simpa [prefixWord, tailWord_4425595, baseEnd_4425595] using wordTrace_append hprefix tailTrace_4425595
  have hstable : (prefixWord ++ tailWord_4425595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4425595).length < 2 ^ (prefixWord ++ tailWord_4425595).sum := by decide
  have hdescent : baseEnd_4425595 < baseStart_4425595 := by decide
  rcases family_descends (prefixWord ++ tailWord_4425595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4425629 : List Nat := [1, 4, 2, 1, 2, 2, 3, 2, 1, 3, 2]
def baseStart_4425629 : Nat := 118140960795 + 4425629 * 2 ^ 59
def prefixEnd_4425629 : Nat := 4983230072969 + 3 ^ 40 * 4425629 * 2
def baseEnd_4425629 : Nat := 2272474875476970439884409

theorem tailTrace_4425629 : CollatzResearch.WordTrace tailWord_4425629 prefixEnd_4425629 2272474875476970439884409 := by
  unfold tailWord_4425629
  simp only [CollatzResearch.WordTrace]
  refine ⟨161415950483709445103031941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107610633655806296735354627 161415950483709445103031941)
  ·
    refine ⟨30265490715695520956818489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 161415950483709445103031941 30265490715695520956818489)
    ·
      refine ⟨22699118036771640717613867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30265490715695520956818489 22699118036771640717613867)
      ·
        refine ⟨34048677055157461076420801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22699118036771640717613867 34048677055157461076420801)
        ·
          refine ⟨25536507791368095807315601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34048677055157461076420801 25536507791368095807315601)
          ·
            refine ⟨19152380843526071855486701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25536507791368095807315601 19152380843526071855486701)
            ·
              refine ⟨7182142816322276945807513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19152380843526071855486701 7182142816322276945807513)
              ·
                refine ⟨5386607112241707709355635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7182142816322276945807513 5386607112241707709355635)
                ·
                  refine ⟨8079910668362561564033453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5386607112241707709355635 8079910668362561564033453)
                  ·
                    refine ⟨3029966500635960586512545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8079910668362561564033453 3029966500635960586512545)
                    ·
                      refine ⟨2272474875476970439884409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3029966500635960586512545 2272474875476970439884409)
                      ·
                        rfl

theorem cell23_4425629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 2, 1, 3, 2].length) (baseStart_4425629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4425629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4425629 prefixEnd_4425629 := by exact prefixLift 4425629
  have htrace : WordTrace (prefixWord ++ tailWord_4425629) baseStart_4425629 baseEnd_4425629 := by
    simpa [prefixWord, tailWord_4425629, baseEnd_4425629] using wordTrace_append hprefix tailTrace_4425629
  have hstable : (prefixWord ++ tailWord_4425629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4425629).length < 2 ^ (prefixWord ++ tailWord_4425629).sum := by decide
  have hdescent : baseEnd_4425629 < baseStart_4425629 := by decide
  rcases family_descends (prefixWord ++ tailWord_4425629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4425675 : List Nat := [1, 1, 1, 1, 3, 4, 3, 1, 2, 3, 3]
def baseStart_4425675 : Nat := 118140960795 + 4425675 * 2 ^ 59
def prefixEnd_4425675 : Nat := 4983230072969 + 3 ^ 40 * 4425675 * 2
def baseEnd_4425675 : Nat := 2272498495587077259909197

theorem tailTrace_4425675 : CollatzResearch.WordTrace tailWord_4425675 prefixEnd_4425675 2272498495587077259909197 := by
  unfold tailWord_4425675
  simp only [CollatzResearch.WordTrace]
  refine ⟨161417628241542794959206479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107611752161028529972804319 161417628241542794959206479)
  ·
    refine ⟨242126442362314192438809719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161417628241542794959206479 242126442362314192438809719)
    ·
      refine ⟨363189663543471288658214579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242126442362314192438809719 363189663543471288658214579)
      ·
        refine ⟨544784495315206932987321869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 363189663543471288658214579 544784495315206932987321869)
        ·
          refine ⟨204294185743202599870245701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 544784495315206932987321869 204294185743202599870245701)
          ·
            refine ⟨38305159826850487475671069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 204294185743202599870245701 38305159826850487475671069)
            ·
              refine ⟨14364434935068932803376651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38305159826850487475671069 14364434935068932803376651)
              ·
                refine ⟨21546652402603399205064977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14364434935068932803376651 21546652402603399205064977)
                ·
                  refine ⟨16159989301952549403798733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21546652402603399205064977 16159989301952549403798733)
                  ·
                    refine ⟨6059995988232206026424525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16159989301952549403798733 6059995988232206026424525)
                    ·
                      refine ⟨2272498495587077259909197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6059995988232206026424525 2272498495587077259909197)
                      ·
                        rfl

theorem cell23_4425675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 1, 2, 3, 3].length) (baseStart_4425675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4425675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4425675 prefixEnd_4425675 := by exact prefixLift 4425675
  have htrace : WordTrace (prefixWord ++ tailWord_4425675) baseStart_4425675 baseEnd_4425675 := by
    simpa [prefixWord, tailWord_4425675, baseEnd_4425675] using wordTrace_append hprefix tailTrace_4425675
  have hstable : (prefixWord ++ tailWord_4425675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4425675).length < 2 ^ (prefixWord ++ tailWord_4425675).sum := by decide
  have hdescent : baseEnd_4425675 < baseStart_4425675 := by decide
  rcases family_descends (prefixWord ++ tailWord_4425675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4425682 : List Nat := [3, 2, 2, 3, 2, 1, 1, 2, 7]
def baseStart_4425682 : Nat := 118140960795 + 4425682 * 2 ^ 59
def prefixEnd_4425682 : Nat := 4983230072969 + 3 ^ 40 * 4425682 * 2
def baseEnd_4425682 : Nat := 252500232216850970280185

theorem tailTrace_4425682 : CollatzResearch.WordTrace tailWord_4425682 prefixEnd_4425682 252500232216850970280185 := by
  unfold tailWord_4425682
  simp only [CollatzResearch.WordTrace]
  refine ⟨40354470888129358788677825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107611922368344956769807533 40354470888129358788677825)
  ·
    refine ⟨30265853166097019091508369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40354470888129358788677825 30265853166097019091508369)
    ·
      refine ⟨22699389874572764318631277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30265853166097019091508369 22699389874572764318631277)
      ·
        refine ⟨8512271202964786619486729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22699389874572764318631277 8512271202964786619486729)
        ·
          refine ⟨6384203402223589964615047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8512271202964786619486729 6384203402223589964615047)
          ·
            refine ⟨9576305103335384946922571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6384203402223589964615047 9576305103335384946922571)
            ·
              refine ⟨14364457655003077420383857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9576305103335384946922571 14364457655003077420383857)
              ·
                refine ⟨10773343241252308065287893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14364457655003077420383857 10773343241252308065287893)
                ·
                  refine ⟨252500232216850970280185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10773343241252308065287893 252500232216850970280185)
                  ·
                    rfl

theorem cell23_4425682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 2, 7].length) (baseStart_4425682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4425682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4425682 prefixEnd_4425682 := by exact prefixLift 4425682
  have htrace : WordTrace (prefixWord ++ tailWord_4425682) baseStart_4425682 baseEnd_4425682 := by
    simpa [prefixWord, tailWord_4425682, baseEnd_4425682] using wordTrace_append hprefix tailTrace_4425682
  have hstable : (prefixWord ++ tailWord_4425682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4425682).length < 2 ^ (prefixWord ++ tailWord_4425682).sum := by decide
  have hdescent : baseEnd_4425682 < baseStart_4425682 := by decide
  rcases family_descends (prefixWord ++ tailWord_4425682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4425695 : List Nat := [1, 1, 2, 3, 4, 2, 1, 1, 1, 7]
def baseStart_4425695 : Nat := 118140960795 + 4425695 * 2 ^ 59
def prefixEnd_4425695 : Nat := 4983230072969 + 3 ^ 40 * 4425695 * 2
def baseEnd_4425695 : Nat := 757502921733389060553035

theorem tailTrace_4425695 : CollatzResearch.WordTrace tailWord_4425695 prefixEnd_4425695 757502921733389060553035 := by
  unfold tailWord_4425695
  simp only [CollatzResearch.WordTrace]
  refine ⟨161418357701470338374934539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107612238467646892249956359 161418357701470338374934539)
  ·
    refine ⟨242127536552205507562401809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161418357701470338374934539 242127536552205507562401809)
    ·
      refine ⟨181595652414154130671801357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 242127536552205507562401809 181595652414154130671801357)
      ·
        refine ⟨68098369655307799001925509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 181595652414154130671801357 68098369655307799001925509)
        ·
          refine ⟨12768444310370212312861033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68098369655307799001925509 12768444310370212312861033)
          ·
            refine ⟨9576333232777659234645775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12768444310370212312861033 9576333232777659234645775)
            ·
              refine ⟨14364499849166488851968663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9576333232777659234645775 14364499849166488851968663)
              ·
                refine ⟨21546749773749733277952995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14364499849166488851968663 21546749773749733277952995)
                ·
                  refine ⟨32320124660624599916929493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21546749773749733277952995 32320124660624599916929493)
                  ·
                    refine ⟨757502921733389060553035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32320124660624599916929493 757502921733389060553035)
                    ·
                      rfl

theorem cell23_4425695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 1, 1, 7].length) (baseStart_4425695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4425695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4425695 prefixEnd_4425695 := by exact prefixLift 4425695
  have htrace : WordTrace (prefixWord ++ tailWord_4425695) baseStart_4425695 baseEnd_4425695 := by
    simpa [prefixWord, tailWord_4425695, baseEnd_4425695] using wordTrace_append hprefix tailTrace_4425695
  have hstable : (prefixWord ++ tailWord_4425695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4425695).length < 2 ^ (prefixWord ++ tailWord_4425695).sum := by decide
  have hdescent : baseEnd_4425695 < baseStart_4425695 := by decide
  rcases family_descends (prefixWord ++ tailWord_4425695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4425708 : List Nat := [2, 2, 1, 1, 2, 1, 1, 2, 1, 10]
def baseStart_4425708 : Nat := 118140960795 + 4425708 * 2 ^ 59
def prefixEnd_4425708 : Nat := 4983230072969 + 3 ^ 40 * 4425708 * 2
def baseEnd_4425708 : Nat := 757505146816225210265515

theorem tailTrace_4425708 : CollatzResearch.WordTrace tailWord_4425708 prefixEnd_4425708 757505146816225210265515 := by
  unfold tailWord_4425708
  simp only [CollatzResearch.WordTrace]
  refine ⟨80709415925211620797578889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107612554566948827730105185 80709415925211620797578889)
  ·
    refine ⟨60532061943908715598184167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80709415925211620797578889 60532061943908715598184167)
    ·
      refine ⟨90798092915863073397276251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60532061943908715598184167 90798092915863073397276251)
      ·
        refine ⟨136197139373794610095914377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90798092915863073397276251 136197139373794610095914377)
        ·
          refine ⟨102147854530345957571935783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136197139373794610095914377 102147854530345957571935783)
          ·
            refine ⟨153221781795518936357903675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102147854530345957571935783 153221781795518936357903675)
            ·
              refine ⟨229832672693278404536855513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 153221781795518936357903675 229832672693278404536855513)
              ·
                refine ⟨172374504519958803402641635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 229832672693278404536855513 172374504519958803402641635)
                ·
                  refine ⟨258561756779938205103962453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 172374504519958803402641635 258561756779938205103962453)
                  ·
                    refine ⟨757505146816225210265515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 258561756779938205103962453 757505146816225210265515)
                    ·
                      rfl

theorem cell23_4425708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 10].length) (baseStart_4425708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4425708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4425708 prefixEnd_4425708 := by exact prefixLift 4425708
  have htrace : WordTrace (prefixWord ++ tailWord_4425708) baseStart_4425708 baseEnd_4425708 := by
    simpa [prefixWord, tailWord_4425708, baseEnd_4425708] using wordTrace_append hprefix tailTrace_4425708
  have hstable : (prefixWord ++ tailWord_4425708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4425708).length < 2 ^ (prefixWord ++ tailWord_4425708).sum := by decide
  have hdescent : baseEnd_4425708 < baseStart_4425708 := by decide
  rcases family_descends (prefixWord ++ tailWord_4425708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4425715 : List Nat := [1, 1, 1, 2, 2, 2, 1, 6, 2, 1, 4]
def baseStart_4425715 : Nat := 118140960795 + 4425715 * 2 ^ 59
def prefixEnd_4425715 : Nat := 4983230072969 + 3 ^ 40 * 4425715 * 2
def baseEnd_4425715 : Nat := 2272519034813257103409013

theorem tailTrace_4425715 : CollatzResearch.WordTrace tailWord_4425715 prefixEnd_4425715 2272519034813257103409013 := by
  unfold tailWord_4425715
  simp only [CollatzResearch.WordTrace]
  refine ⟨161419087161397881790662599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107612724774265254527108399 161419087161397881790662599)
  ·
    refine ⟨242128630742096822685993899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161419087161397881790662599 242128630742096822685993899)
    ·
      refine ⟨363192946113145234028990849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242128630742096822685993899 363192946113145234028990849)
      ·
        refine ⟨272394709584858925521743137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 363192946113145234028990849 272394709584858925521743137)
        ·
          refine ⟨204296032188644194141307353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 272394709584858925521743137 204296032188644194141307353)
          ·
            refine ⟨153222024141483145605980515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 204296032188644194141307353 153222024141483145605980515)
            ·
              refine ⟨229833036212224718408970773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 153222024141483145605980515 229833036212224718408970773)
              ·
                refine ⟨10773423572448033675420505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 229833036212224718408970773 10773423572448033675420505)
                ·
                  refine ⟨8080067679336025256565379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10773423572448033675420505 8080067679336025256565379)
                  ·
                    refine ⟨12120101519004037884848069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8080067679336025256565379 12120101519004037884848069)
                    ·
                      refine ⟨2272519034813257103409013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12120101519004037884848069 2272519034813257103409013)
                      ·
                        rfl

theorem cell23_4425715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 6, 2, 1, 4].length) (baseStart_4425715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4425715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4425715 prefixEnd_4425715 := by exact prefixLift 4425715
  have htrace : WordTrace (prefixWord ++ tailWord_4425715) baseStart_4425715 baseEnd_4425715 := by
    simpa [prefixWord, tailWord_4425715, baseEnd_4425715] using wordTrace_append hprefix tailTrace_4425715
  have hstable : (prefixWord ++ tailWord_4425715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4425715).length < 2 ^ (prefixWord ++ tailWord_4425715).sum := by decide
  have hdescent : baseEnd_4425715 < baseStart_4425715 := by decide
  rcases family_descends (prefixWord ++ tailWord_4425715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4425742 : List Nat := [4, 1, 1, 2, 2, 1, 1, 4, 3, 4]
def baseStart_4425742 : Nat := 118140960795 + 4425742 * 2 ^ 59
def prefixEnd_4425742 : Nat := 4983230072969 + 3 ^ 40 * 4425742 * 2
def baseEnd_4425742 : Nat := 757510966263642832590463

theorem tailTrace_4425742 : CollatzResearch.WordTrace tailWord_4425742 prefixEnd_4425742 757510966263642832590463 := by
  unfold tailWord_4425742
  simp only [CollatzResearch.WordTrace]
  refine ⟨20177508991537508175236935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107613381288200043601263653 20177508991537508175236935)
  ·
    refine ⟨30266263487306262262855403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20177508991537508175236935 30266263487306262262855403)
    ·
      refine ⟨45399395230959393394283105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30266263487306262262855403 45399395230959393394283105)
      ·
        refine ⟨34049546423219545045712329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45399395230959393394283105 34049546423219545045712329)
        ·
          refine ⟨25537159817414658784284247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34049546423219545045712329 25537159817414658784284247)
          ·
            refine ⟨38305739726121988176426371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25537159817414658784284247 38305739726121988176426371)
            ·
              refine ⟨57458609589182982264639557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38305739726121988176426371 57458609589182982264639557)
              ·
                refine ⟨10773489297971809174619917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57458609589182982264639557 10773489297971809174619917)
                ·
                  refine ⟨4040058486739428440482469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10773489297971809174619917 4040058486739428440482469)
                  ·
                    refine ⟨757510966263642832590463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4040058486739428440482469 757510966263642832590463)
                    ·
                      rfl

theorem cell23_4425742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 4, 3, 4].length) (baseStart_4425742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4425742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4425742 prefixEnd_4425742 := by exact prefixLift 4425742
  have htrace : WordTrace (prefixWord ++ tailWord_4425742) baseStart_4425742 baseEnd_4425742 := by
    simpa [prefixWord, tailWord_4425742, baseEnd_4425742] using wordTrace_append hprefix tailTrace_4425742
  have hstable : (prefixWord ++ tailWord_4425742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4425742).length < 2 ^ (prefixWord ++ tailWord_4425742).sum := by decide
  have hdescent : baseEnd_4425742 < baseStart_4425742 := by decide
  rcases family_descends (prefixWord ++ tailWord_4425742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4425752 : List Nat := [2, 1, 2, 3, 2, 1, 2, 3, 2, 2, 3]
def baseStart_4425752 : Nat := 118140960795 + 4425752 * 2 ^ 59
def prefixEnd_4425752 : Nat := 4983230072969 + 3 ^ 40 * 4425752 * 2
def baseEnd_4425752 : Nat := 2272538033597473458646343

theorem tailTrace_4425752 : CollatzResearch.WordTrace tailWord_4425752 prefixEnd_4425752 2272538033597473458646343 := by
  unfold tailWord_4425752
  simp only [CollatzResearch.WordTrace]
  refine ⟨80710218331131918554879755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107613624441509224739839673 80710218331131918554879755)
  ·
    refine ⟨121065327496697877832319633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80710218331131918554879755 121065327496697877832319633)
    ·
      refine ⟨90798995622523408374239725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121065327496697877832319633 90798995622523408374239725)
      ·
        refine ⟨34049623358446278140339897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90798995622523408374239725 34049623358446278140339897)
        ·
          refine ⟨25537217518834708605254923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34049623358446278140339897 25537217518834708605254923)
          ·
            refine ⟨38305826278252062907882385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25537217518834708605254923 38305826278252062907882385)
            ·
              refine ⟨28729369708689047180911789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38305826278252062907882385 28729369708689047180911789)
              ·
                refine ⟨10773513640758392692841921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28729369708689047180911789 10773513640758392692841921)
                ·
                  refine ⟨8080135230568794519631441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10773513640758392692841921 8080135230568794519631441)
                  ·
                    refine ⟨6060101422926595889723581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8080135230568794519631441 6060101422926595889723581)
                    ·
                      refine ⟨2272538033597473458646343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6060101422926595889723581 2272538033597473458646343)
                      ·
                        rfl

theorem cell23_4425752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 3, 2, 2, 3].length) (baseStart_4425752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4425752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4425752 prefixEnd_4425752 := by exact prefixLift 4425752
  have htrace : WordTrace (prefixWord ++ tailWord_4425752) baseStart_4425752 baseEnd_4425752 := by
    simpa [prefixWord, tailWord_4425752, baseEnd_4425752] using wordTrace_append hprefix tailTrace_4425752
  have hstable : (prefixWord ++ tailWord_4425752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4425752).length < 2 ^ (prefixWord ++ tailWord_4425752).sum := by decide
  have hdescent : baseEnd_4425752 < baseStart_4425752 := by decide
  rcases family_descends (prefixWord ++ tailWord_4425752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4425776 : List Nat := [2, 1, 1, 1, 2, 6, 3, 2, 1, 4]
def baseStart_4425776 : Nat := 118140960795 + 4425776 * 2 ^ 59
def prefixEnd_4425776 : Nat := 4983230072969 + 3 ^ 40 * 4425776 * 2
def baseEnd_4425776 : Nat := 757516785711060454915411

theorem tailTrace_4425776 : CollatzResearch.WordTrace tailWord_4425776 prefixEnd_4425776 757516785711060454915411 := by
  unfold tailWord_4425776
  simp only [CollatzResearch.WordTrace]
  refine ⟨80710656007088444604316591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107614208009451259472422121 80710656007088444604316591)
  ·
    refine ⟨121065984010632666906474887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80710656007088444604316591 121065984010632666906474887)
    ·
      refine ⟨181598976015949000359712331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121065984010632666906474887 181598976015949000359712331)
      ·
        refine ⟨272398464023923500539568497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181598976015949000359712331 272398464023923500539568497)
        ·
          refine ⟨204298848017942625404676373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 272398464023923500539568497 204298848017942625404676373)
          ·
            refine ⟨9576508500841060565844205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 204298848017942625404676373 9576508500841060565844205)
            ·
              refine ⟨3591190687815397712191577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9576508500841060565844205 3591190687815397712191577)
              ·
                refine ⟨2693393015861548284143683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3591190687815397712191577 2693393015861548284143683)
                ·
                  refine ⟨4040089523792322426215525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2693393015861548284143683 4040089523792322426215525)
                  ·
                    refine ⟨757516785711060454915411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4040089523792322426215525 757516785711060454915411)
                    ·
                      rfl

theorem cell23_4425776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 3, 2, 1, 4].length) (baseStart_4425776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4425776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4425776 prefixEnd_4425776 := by exact prefixLift 4425776
  have htrace : WordTrace (prefixWord ++ tailWord_4425776) baseStart_4425776 baseEnd_4425776 := by
    simpa [prefixWord, tailWord_4425776, baseEnd_4425776] using wordTrace_append hprefix tailTrace_4425776
  have hstable : (prefixWord ++ tailWord_4425776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4425776).length < 2 ^ (prefixWord ++ tailWord_4425776).sum := by decide
  have hdescent : baseEnd_4425776 < baseStart_4425776 := by decide
  rcases family_descends (prefixWord ++ tailWord_4425776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4425815 : List Nat := [1, 1, 3, 2, 2, 1, 3, 1, 3, 6]
def baseStart_4425815 : Nat := 118140960795 + 4425815 * 2 ^ 59
def prefixEnd_4425815 : Nat := 4983230072969 + 3 ^ 40 * 4425815 * 2
def baseEnd_4425815 : Nat := 757523460959568904052851

theorem tailTrace_4425815 : CollatzResearch.WordTrace tailWord_4425815 prefixEnd_4425815 757523460959568904052851 := by
  unfold tailWord_4425815
  simp only [CollatzResearch.WordTrace]
  refine ⟨161422734461035598869302899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107615156307357065912868599 161422734461035598869302899)
  ·
    refine ⟨242134101691553398303954349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161422734461035598869302899 242134101691553398303954349)
    ·
      refine ⟨90800288134332524363982881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 242134101691553398303954349 90800288134332524363982881)
      ·
        refine ⟨68100216100749393272987161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90800288134332524363982881 68100216100749393272987161)
        ·
          refine ⟨51075162075562044954740371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68100216100749393272987161 51075162075562044954740371)
          ·
            refine ⟨76612743113343067432110557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51075162075562044954740371 76612743113343067432110557)
            ·
              refine ⟨28729778667503650287041459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76612743113343067432110557 28729778667503650287041459)
              ·
                refine ⟨43094668001255475430562189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28729778667503650287041459 43094668001255475430562189)
                ·
                  refine ⟨16160500500470803286460821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43094668001255475430562189 16160500500470803286460821)
                  ·
                    refine ⟨757523460959568904052851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16160500500470803286460821 757523460959568904052851)
                    ·
                      rfl

theorem cell23_4425815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 3, 6].length) (baseStart_4425815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4425815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4425815 prefixEnd_4425815 := by exact prefixLift 4425815
  have htrace : WordTrace (prefixWord ++ tailWord_4425815) baseStart_4425815 baseEnd_4425815 := by
    simpa [prefixWord, tailWord_4425815, baseEnd_4425815] using wordTrace_append hprefix tailTrace_4425815
  have hstable : (prefixWord ++ tailWord_4425815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4425815).length < 2 ^ (prefixWord ++ tailWord_4425815).sum := by decide
  have hdescent : baseEnd_4425815 < baseStart_4425815 := by decide
  rcases family_descends (prefixWord ++ tailWord_4425815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4425849 : List Nat := [1, 2, 1, 3, 4, 1, 2, 3, 2, 4]
def baseStart_4425849 : Nat := 118140960795 + 4425849 * 2 ^ 59
def prefixEnd_4425849 : Nat := 4983230072969 + 3 ^ 40 * 4425849 * 2
def baseEnd_4425849 : Nat := 757529280406986526377799

theorem tailTrace_4425849 : CollatzResearch.WordTrace tailWord_4425849 prefixEnd_4425849 757529280406986526377799 := by
  unfold tailWord_4425849
  simp only [CollatzResearch.WordTrace]
  refine ⟨161423974542912422676040601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107615983028608281784027067 161423974542912422676040601)
  ·
    refine ⟨121067980907184317007030451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161423974542912422676040601 121067980907184317007030451)
    ·
      refine ⟨181601971360776475510545677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121067980907184317007030451 181601971360776475510545677)
      ·
        refine ⟨68100739260291178316454629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 181601971360776475510545677 68100739260291178316454629)
        ·
          refine ⟨12768888611304595934335243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68100739260291178316454629 12768888611304595934335243)
          ·
            refine ⟨19153332916956893901502865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12768888611304595934335243 19153332916956893901502865)
            ·
              refine ⟨14364999687717670426127149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19153332916956893901502865 14364999687717670426127149)
              ·
                refine ⟨5386874882894126409797681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14364999687717670426127149 5386874882894126409797681)
                ·
                  refine ⟨4040156162170594807348261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5386874882894126409797681 4040156162170594807348261)
                  ·
                    refine ⟨757529280406986526377799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4040156162170594807348261 757529280406986526377799)
                    ·
                      rfl

theorem cell23_4425849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 3, 2, 4].length) (baseStart_4425849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4425849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4425849 prefixEnd_4425849 := by exact prefixLift 4425849
  have htrace : WordTrace (prefixWord ++ tailWord_4425849) baseStart_4425849 baseEnd_4425849 := by
    simpa [prefixWord, tailWord_4425849, baseEnd_4425849] using wordTrace_append hprefix tailTrace_4425849
  have hstable : (prefixWord ++ tailWord_4425849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4425849).length < 2 ^ (prefixWord ++ tailWord_4425849).sum := by decide
  have hdescent : baseEnd_4425849 < baseStart_4425849 := by decide
  rcases family_descends (prefixWord ++ tailWord_4425849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4425852 : List Nat := [2, 2, 2, 1, 1, 4, 1, 3, 1, 2, 4]
def baseStart_4425852 : Nat := 118140960795 + 4425852 * 2 ^ 59
def prefixEnd_4425852 : Nat := 4983230072969 + 3 ^ 40 * 4425852 * 2
def baseEnd_4425852 : Nat := 2272589381662923067395883

theorem tailTrace_4425852 : CollatzResearch.WordTrace tailWord_4425852 prefixEnd_4425852 2272589381662923067395883 := by
  unfold tailWord_4425852
  simp only [CollatzResearch.WordTrace]
  refine ⟨80712041980950777094199905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107616055974601036125599873 80712041980950777094199905)
  ·
    refine ⟨60534031485713082820649929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80712041980950777094199905 60534031485713082820649929)
    ·
      refine ⟨45400523614284812115487447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60534031485713082820649929 45400523614284812115487447)
      ·
        refine ⟨68100785421427218173231171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45400523614284812115487447 68100785421427218173231171)
        ·
          refine ⟨102151178132140827259846757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68100785421427218173231171 102151178132140827259846757)
          ·
            refine ⟨19153345899776405111221267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 102151178132140827259846757 19153345899776405111221267)
            ·
              refine ⟨28730018849664607666831901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19153345899776405111221267 28730018849664607666831901)
              ·
                refine ⟨10773757068624227875061963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28730018849664607666831901 10773757068624227875061963)
                ·
                  refine ⟨16160635602936341812592945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10773757068624227875061963 16160635602936341812592945)
                  ·
                    refine ⟨12120476702202256359444709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16160635602936341812592945 12120476702202256359444709)
                    ·
                      refine ⟨2272589381662923067395883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12120476702202256359444709 2272589381662923067395883)
                      ·
                        rfl

theorem cell23_4425852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 3, 1, 2, 4].length) (baseStart_4425852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4425852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4425852 prefixEnd_4425852 := by exact prefixLift 4425852
  have htrace : WordTrace (prefixWord ++ tailWord_4425852) baseStart_4425852 baseEnd_4425852 := by
    simpa [prefixWord, tailWord_4425852, baseEnd_4425852] using wordTrace_append hprefix tailTrace_4425852
  have hstable : (prefixWord ++ tailWord_4425852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4425852).length < 2 ^ (prefixWord ++ tailWord_4425852).sum := by decide
  have hdescent : baseEnd_4425852 < baseStart_4425852 := by decide
  rcases family_descends (prefixWord ++ tailWord_4425852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4425872 : List Nat := [2, 1, 1, 1, 1, 1, 5, 4, 1, 3, 3]
def baseStart_4425872 : Nat := 118140960795 + 4425872 * 2 ^ 59
def prefixEnd_4425872 : Nat := 4983230072969 + 3 ^ 40 * 4425872 * 2
def baseEnd_4425872 : Nat := 2272599651276012989145791

theorem tailTrace_4425872 : CollatzResearch.WordTrace tailWord_4425872 prefixEnd_4425872 2272599651276012989145791 := by
  unfold tailWord_4425872
  simp only [CollatzResearch.WordTrace]
  refine ⟨80712406710914548802063935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107616542281219398402751913 80712406710914548802063935)
  ·
    refine ⟨121068610066371823203095903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80712406710914548802063935 121068610066371823203095903)
    ·
      refine ⟨181602915099557734804643855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121068610066371823203095903 181602915099557734804643855)
      ·
        refine ⟨272404372649336602206965783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181602915099557734804643855 272404372649336602206965783)
        ·
          refine ⟨408606558974004903310448675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 272404372649336602206965783 408606558974004903310448675)
          ·
            refine ⟨612909838461007354965673013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 408606558974004903310448675 612909838461007354965673013)
            ·
              refine ⟨57460297355719439528031845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 612909838461007354965673013 57460297355719439528031845)
              ·
                refine ⟨10773805754197394911505971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57460297355719439528031845 10773805754197394911505971)
                ·
                  refine ⟨16160708631296092367258957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10773805754197394911505971 16160708631296092367258957)
                  ·
                    refine ⟨6060265736736034637722109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16160708631296092367258957 6060265736736034637722109)
                    ·
                      refine ⟨2272599651276012989145791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6060265736736034637722109 2272599651276012989145791)
                      ·
                        rfl

theorem cell23_4425872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 4, 1, 3, 3].length) (baseStart_4425872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4425872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4425872 prefixEnd_4425872 := by exact prefixLift 4425872
  have htrace : WordTrace (prefixWord ++ tailWord_4425872) baseStart_4425872 baseEnd_4425872 := by
    simpa [prefixWord, tailWord_4425872, baseEnd_4425872] using wordTrace_append hprefix tailTrace_4425872
  have hstable : (prefixWord ++ tailWord_4425872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4425872).length < 2 ^ (prefixWord ++ tailWord_4425872).sum := by decide
  have hdescent : baseEnd_4425872 < baseStart_4425872 := by decide
  rcases family_descends (prefixWord ++ tailWord_4425872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4425890 : List Nat := [3, 3, 1, 3, 1, 1, 2, 4, 1, 2, 2]
def baseStart_4425890 : Nat := 118140960795 + 4425890 * 2 ^ 59
def prefixEnd_4425890 : Nat := 4983230072969 + 3 ^ 40 * 4425890 * 2
def baseEnd_4425890 : Nat := 2272608893927793918720709

theorem tailTrace_4425890 : CollatzResearch.WordTrace tailWord_4425890 prefixEnd_4425890 2272608893927793918720709 := by
  unfold tailWord_4425890
  simp only [CollatzResearch.WordTrace]
  refine ⟨40356367483940971669570781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107616979957175924452188749 40356367483940971669570781)
  ·
    refine ⟨15133637806477864376089043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40356367483940971669570781 15133637806477864376089043)
    ·
      refine ⟨22700456709716796564133565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15133637806477864376089043 22700456709716796564133565)
      ·
        refine ⟨8512671266143798711550087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22700456709716796564133565 8512671266143798711550087)
        ·
          refine ⟨12769006899215698067325131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8512671266143798711550087 12769006899215698067325131)
          ·
            refine ⟨19153510348823547100987697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12769006899215698067325131 19153510348823547100987697)
            ·
              refine ⟨14365132761617660325740773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19153510348823547100987697 14365132761617660325740773)
              ·
                refine ⟨2693462392803311311076395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14365132761617660325740773 2693462392803311311076395)
                ·
                  refine ⟨4040193589204966966614593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2693462392803311311076395 4040193589204966966614593)
                  ·
                    refine ⟨3030145191903725224960945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4040193589204966966614593 3030145191903725224960945)
                    ·
                      refine ⟨2272608893927793918720709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3030145191903725224960945 2272608893927793918720709)
                      ·
                        rfl

theorem cell23_4425890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_4425890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4425890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4425890 prefixEnd_4425890 := by exact prefixLift 4425890
  have htrace : WordTrace (prefixWord ++ tailWord_4425890) baseStart_4425890 baseEnd_4425890 := by
    simpa [prefixWord, tailWord_4425890, baseEnd_4425890] using wordTrace_append hprefix tailTrace_4425890
  have hstable : (prefixWord ++ tailWord_4425890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4425890).length < 2 ^ (prefixWord ++ tailWord_4425890).sum := by decide
  have hdescent : baseEnd_4425890 < baseStart_4425890 := by decide
  rcases family_descends (prefixWord ++ tailWord_4425890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4425946 : List Nat := [3, 1, 1, 2, 2, 1, 4, 1, 4, 2, 2]
def baseStart_4425946 : Nat := 118140960795 + 4425946 * 2 ^ 59
def prefixEnd_4425946 : Nat := 4983230072969 + 3 ^ 40 * 4425946 * 2
def baseEnd_4425946 : Nat := 2272637648844445699620451

theorem tailTrace_4425946 : CollatzResearch.WordTrace tailWord_4425946 prefixEnd_4425946 2272637648844445699620451 := by
  unfold tailWord_4425946
  simp only [CollatzResearch.WordTrace]
  refine ⟨40356878105890252060580423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107618341615707338828214461 40356878105890252060580423)
  ·
    refine ⟨60535317158835378090870635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40356878105890252060580423 60535317158835378090870635)
    ·
      refine ⟨90802975738253067136305953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60535317158835378090870635 90802975738253067136305953)
      ·
        refine ⟨68102231803689800352229465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90802975738253067136305953 68102231803689800352229465)
        ·
          refine ⟨51076673852767350264172099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68102231803689800352229465 51076673852767350264172099)
          ·
            refine ⟨76615010779151025396258149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51076673852767350264172099 76615010779151025396258149)
            ·
              refine ⟨14365314521090817261798403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 76615010779151025396258149 14365314521090817261798403)
              ·
                refine ⟨21547971781636225892697605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14365314521090817261798403 21547971781636225892697605)
                ·
                  refine ⟨4040244709056792354880801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21547971781636225892697605 4040244709056792354880801)
                  ·
                    refine ⟨3030183531792594266160601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4040244709056792354880801 3030183531792594266160601)
                    ·
                      refine ⟨2272637648844445699620451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3030183531792594266160601 2272637648844445699620451)
                      ·
                        rfl

theorem cell23_4425946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 1, 4, 2, 2].length) (baseStart_4425946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4425946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4425946 prefixEnd_4425946 := by exact prefixLift 4425946
  have htrace : WordTrace (prefixWord ++ tailWord_4425946) baseStart_4425946 baseEnd_4425946 := by
    simpa [prefixWord, tailWord_4425946, baseEnd_4425946] using wordTrace_append hprefix tailTrace_4425946
  have hstable : (prefixWord ++ tailWord_4425946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4425946).length < 2 ^ (prefixWord ++ tailWord_4425946).sum := by decide
  have hdescent : baseEnd_4425946 < baseStart_4425946 := by decide
  rcases family_descends (prefixWord ++ tailWord_4425946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4426012 : List Nat := [2, 2, 3, 1, 1, 1, 1, 2, 2, 8]
def baseStart_4426012 : Nat := 118140960795 + 4426012 * 2 ^ 59
def prefixEnd_4426012 : Nat := 4983230072969 + 3 ^ 40 * 4426012 * 2
def baseEnd_4426012 : Nat := 757557179522547480465049

theorem tailTrace_4426012 : CollatzResearch.WordTrace tailWord_4426012 prefixEnd_4426012 757557179522547480465049 := by
  unfold tailWord_4426012
  simp only [CollatzResearch.WordTrace]
  refine ⟨80714959820660950757112145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107619946427547934342816193 80714959820660950757112145)
  ·
    refine ⟨60536219865495713067834109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80714959820660950757112145 60536219865495713067834109)
    ·
      refine ⟨22701082449560892400437791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60536219865495713067834109 22701082449560892400437791)
      ·
        refine ⟨34051623674341338600656687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22701082449560892400437791 34051623674341338600656687)
        ·
          refine ⟨51077435511512007900985031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34051623674341338600656687 51077435511512007900985031)
          ·
            refine ⟨76616153267268011851477547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51077435511512007900985031 76616153267268011851477547)
            ·
              refine ⟨114924229900902017777216321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76616153267268011851477547 114924229900902017777216321)
              ·
                refine ⟨86193172425676513332912241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 114924229900902017777216321 86193172425676513332912241)
                ·
                  refine ⟨64644879319257384999684181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 86193172425676513332912241 64644879319257384999684181)
                  ·
                    refine ⟨757557179522547480465049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 64644879319257384999684181 757557179522547480465049)
                    ·
                      rfl

theorem cell23_4426012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 2, 8].length) (baseStart_4426012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4426012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4426012 prefixEnd_4426012 := by exact prefixLift 4426012
  have htrace : WordTrace (prefixWord ++ tailWord_4426012) baseStart_4426012 baseEnd_4426012 := by
    simpa [prefixWord, tailWord_4426012, baseEnd_4426012] using wordTrace_append hprefix tailTrace_4426012
  have hstable : (prefixWord ++ tailWord_4426012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4426012).length < 2 ^ (prefixWord ++ tailWord_4426012).sum := by decide
  have hdescent : baseEnd_4426012 < baseStart_4426012 := by decide
  rcases family_descends (prefixWord ++ tailWord_4426012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4426032 : List Nat := [2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 4]
def baseStart_4426032 : Nat := 118140960795 + 4426032 * 2 ^ 59
def prefixEnd_4426032 : Nat := 4983230072969 + 3 ^ 40 * 4426032 * 2
def baseEnd_4426032 : Nat := 2272681808180732363145055

theorem tailTrace_4426032 : CollatzResearch.WordTrace tailWord_4426032 prefixEnd_4426032 2272681808180732363145055 := by
  unfold tailWord_4426032
  simp only [CollatzResearch.WordTrace]
  refine ⟨80715324550624722464976175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107620432734166296619968233 80715324550624722464976175)
  ·
    refine ⟨121072986825937083697464263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80715324550624722464976175 121072986825937083697464263)
    ·
      refine ⟨181609480238905625546196395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121072986825937083697464263 181609480238905625546196395)
      ·
        refine ⟨272414220358358438319294593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181609480238905625546196395 272414220358358438319294593)
        ·
          refine ⟨204310665268768828739470945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 272414220358358438319294593 204310665268768828739470945)
          ·
            refine ⟨153232998951576621554603209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 204310665268768828739470945 153232998951576621554603209)
            ·
              refine ⟨114924749213682466165952407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 153232998951576621554603209 114924749213682466165952407)
              ·
                refine ⟨172387123820523699248928611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114924749213682466165952407 172387123820523699248928611)
                ·
                  refine ⟨258580685730785548873392917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 172387123820523699248928611 258580685730785548873392917)
                  ·
                    refine ⟨12120969643630572603440293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 258580685730785548873392917 12120969643630572603440293)
                    ·
                      refine ⟨2272681808180732363145055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12120969643630572603440293 2272681808180732363145055)
                      ·
                        rfl

theorem cell23_4426032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 4].length) (baseStart_4426032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4426032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4426032 prefixEnd_4426032 := by exact prefixLift 4426032
  have htrace : WordTrace (prefixWord ++ tailWord_4426032) baseStart_4426032 baseEnd_4426032 := by
    simpa [prefixWord, tailWord_4426032, baseEnd_4426032] using wordTrace_append hprefix tailTrace_4426032
  have hstable : (prefixWord ++ tailWord_4426032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4426032).length < 2 ^ (prefixWord ++ tailWord_4426032).sum := by decide
  have hdescent : baseEnd_4426032 < baseStart_4426032 := by decide
  rcases family_descends (prefixWord ++ tailWord_4426032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4426033 : List Nat := [1, 2, 2, 3, 5, 1, 1, 1, 2, 5]
def baseStart_4426033 : Nat := 118140960795 + 4426033 * 2 ^ 59
def prefixEnd_4426033 : Nat := 4983230072969 + 3 ^ 40 * 4426033 * 2
def baseEnd_4426033 : Nat := 757560773887128953077517

theorem tailTrace_4426033 : CollatzResearch.WordTrace tailWord_4426033 prefixEnd_4426033 757560773887128953077517 := by
  unfold tailWord_4426033
  simp only [CollatzResearch.WordTrace]
  refine ⟨161430685574245822100738753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107620457049497214733825835 161430685574245822100738753)
  ·
    refine ⟨121073014180684366575554065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161430685574245822100738753 121073014180684366575554065)
    ·
      refine ⟨90804760635513274931665549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121073014180684366575554065 90804760635513274931665549)
      ·
        refine ⟨34051785238317478099374581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90804760635513274931665549 34051785238317478099374581)
        ·
          refine ⟨3192354866092263571816367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34051785238317478099374581 3192354866092263571816367)
          ·
            refine ⟨4788532299138395357724551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3192354866092263571816367 4788532299138395357724551)
            ·
              refine ⟨7182798448707593036586827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4788532299138395357724551 7182798448707593036586827)
              ·
                refine ⟨10774197673061389554880241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7182798448707593036586827 10774197673061389554880241)
                ·
                  refine ⟨8080648254796042166160181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10774197673061389554880241 8080648254796042166160181)
                  ·
                    refine ⟨757560773887128953077517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8080648254796042166160181 757560773887128953077517)
                    ·
                      rfl

theorem cell23_4426033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 1, 2, 5].length) (baseStart_4426033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4426033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4426033 prefixEnd_4426033 := by exact prefixLift 4426033
  have htrace : WordTrace (prefixWord ++ tailWord_4426033) baseStart_4426033 baseEnd_4426033 := by
    simpa [prefixWord, tailWord_4426033, baseEnd_4426033] using wordTrace_append hprefix tailTrace_4426033
  have hstable : (prefixWord ++ tailWord_4426033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4426033).length < 2 ^ (prefixWord ++ tailWord_4426033).sum := by decide
  have hdescent : baseEnd_4426033 < baseStart_4426033 := by decide
  rcases family_descends (prefixWord ++ tailWord_4426033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4426036 : List Nat := [2, 5, 1, 1, 1, 3, 1, 1, 1, 3, 4]
def baseStart_4426036 : Nat := 118140960795 + 4426036 * 2 ^ 59
def prefixEnd_4426036 : Nat := 4983230072969 + 3 ^ 40 * 4426036 * 2
def baseEnd_4426036 : Nat := 2272683862103350347495037

theorem tailTrace_4426036 : CollatzResearch.WordTrace tailWord_4426036 prefixEnd_4426036 2272683862103350347495037 := by
  unfold tailWord_4426036
  simp only [CollatzResearch.WordTrace]
  refine ⟨80715397496617476806548981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107620529995489969075398641 80715397496617476806548981)
  ·
    refine ⟨7567068515307888450613967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 80715397496617476806548981 7567068515307888450613967)
    ·
      refine ⟨11350602772961832675920951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7567068515307888450613967 11350602772961832675920951)
      ·
        refine ⟨17025904159442749013881427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11350602772961832675920951 17025904159442749013881427)
        ·
          refine ⟨25538856239164123520822141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17025904159442749013881427 25538856239164123520822141)
          ·
            refine ⟨9577071089686546320308303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25538856239164123520822141 9577071089686546320308303)
            ·
              refine ⟨14365606634529819480462455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9577071089686546320308303 14365606634529819480462455)
              ·
                refine ⟨21548409951794729220693683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14365606634529819480462455 21548409951794729220693683)
                ·
                  refine ⟨32322614927692093831040525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21548409951794729220693683 32322614927692093831040525)
                  ·
                    refine ⟨12120980597884535186640197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32322614927692093831040525 12120980597884535186640197)
                    ·
                      refine ⟨2272683862103350347495037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12120980597884535186640197 2272683862103350347495037)
                      ·
                        rfl

theorem cell23_4426036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_4426036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4426036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4426036 prefixEnd_4426036 := by exact prefixLift 4426036
  have htrace : WordTrace (prefixWord ++ tailWord_4426036) baseStart_4426036 baseEnd_4426036 := by
    simpa [prefixWord, tailWord_4426036, baseEnd_4426036] using wordTrace_append hprefix tailTrace_4426036
  have hstable : (prefixWord ++ tailWord_4426036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4426036).length < 2 ^ (prefixWord ++ tailWord_4426036).sum := by decide
  have hdescent : baseEnd_4426036 < baseStart_4426036 := by decide
  rcases family_descends (prefixWord ++ tailWord_4426036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4426072 : List Nat := [2, 1, 2, 2, 1, 1, 2, 1, 2, 9]
def baseStart_4426072 : Nat := 118140960795 + 4426072 * 2 ^ 59
def prefixEnd_4426072 : Nat := 4983230072969 + 3 ^ 40 * 4426072 * 2
def baseEnd_4426072 : Nat := 757567449135637402214957

theorem tailTrace_4426072 : CollatzResearch.WordTrace tailWord_4426072 prefixEnd_4426072 757567449135637402214957 := by
  unfold tailWord_4426072
  simp only [CollatzResearch.WordTrace]
  refine ⟨80716054010552265880704235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107621405347403021174272313 80716054010552265880704235)
  ·
    refine ⟨121074081015828398821056353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80716054010552265880704235 121074081015828398821056353)
    ·
      refine ⟨90805560761871299115792265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121074081015828398821056353 90805560761871299115792265)
      ·
        refine ⟨68104170571403474336844199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90805560761871299115792265 68104170571403474336844199)
        ·
          refine ⟨102156255857105211505266299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68104170571403474336844199 102156255857105211505266299)
          ·
            refine ⟨153234383785657817257899449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102156255857105211505266299 153234383785657817257899449)
            ·
              refine ⟨114925787839243362943424587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 153234383785657817257899449 114925787839243362943424587)
              ·
                refine ⟨172388681758865044415136881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114925787839243362943424587 172388681758865044415136881)
                ·
                  refine ⟨129291511319148783311352661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 172388681758865044415136881 129291511319148783311352661)
                  ·
                    refine ⟨757567449135637402214957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 129291511319148783311352661 757567449135637402214957)
                    ·
                      rfl

theorem cell23_4426072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 2, 9].length) (baseStart_4426072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4426072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4426072 prefixEnd_4426072 := by exact prefixLift 4426072
  have htrace : WordTrace (prefixWord ++ tailWord_4426072) baseStart_4426072 baseEnd_4426072 := by
    simpa [prefixWord, tailWord_4426072, baseEnd_4426072] using wordTrace_append hprefix tailTrace_4426072
  have hstable : (prefixWord ++ tailWord_4426072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4426072).length < 2 ^ (prefixWord ++ tailWord_4426072).sum := by decide
  have hdescent : baseEnd_4426072 < baseStart_4426072 := by decide
  rcases family_descends (prefixWord ++ tailWord_4426072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4426096 : List Nat := [2, 1, 1, 1, 4, 3, 2, 1, 1, 5, 2]
def baseStart_4426096 : Nat := 118140960795 + 4426096 * 2 ^ 59
def prefixEnd_4426096 : Nat := 4983230072969 + 3 ^ 40 * 4426096 * 2
def baseEnd_4426096 : Nat := 2272714670942620112744761

theorem tailTrace_4426096 : CollatzResearch.WordTrace tailWord_4426096 prefixEnd_4426096 2272714670942620112744761 := by
  unfold tailWord_4426096
  simp only [CollatzResearch.WordTrace]
  refine ⟨80716491686508791930141071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107621988915345055906854761 80716491686508791930141071)
  ·
    refine ⟨121074737529763187895211607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80716491686508791930141071 121074737529763187895211607)
    ·
      refine ⟨181612106294644781842817411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121074737529763187895211607 181612106294644781842817411)
      ·
        refine ⟨272418159441967172764226117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181612106294644781842817411 272418159441967172764226117)
        ·
          refine ⟨51078404895368844893292397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 272418159441967172764226117 51078404895368844893292397)
          ·
            refine ⟨19154401835763316834984649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51078404895368844893292397 19154401835763316834984649)
            ·
              refine ⟨14365801376822487626238487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19154401835763316834984649 14365801376822487626238487)
              ·
                refine ⟨21548702065233731439357731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14365801376822487626238487 21548702065233731439357731)
                ·
                  refine ⟨32323053097850597159036597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21548702065233731439357731 32323053097850597159036597)
                  ·
                    refine ⟨3030286227923493483659681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32323053097850597159036597 3030286227923493483659681)
                    ·
                      refine ⟨2272714670942620112744761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3030286227923493483659681 2272714670942620112744761)
                      ·
                        rfl

theorem cell23_4426096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 1, 1, 5, 2].length) (baseStart_4426096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4426096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4426096 prefixEnd_4426096 := by exact prefixLift 4426096
  have htrace : WordTrace (prefixWord ++ tailWord_4426096) baseStart_4426096 baseEnd_4426096 := by
    simpa [prefixWord, tailWord_4426096, baseEnd_4426096] using wordTrace_append hprefix tailTrace_4426096
  have hstable : (prefixWord ++ tailWord_4426096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4426096).length < 2 ^ (prefixWord ++ tailWord_4426096).sum := by decide
  have hdescent : baseEnd_4426096 < baseStart_4426096 := by decide
  rcases family_descends (prefixWord ++ tailWord_4426096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4426103 : List Nat := [1, 1, 3, 1, 1, 2, 2, 7, 1, 1, 3]
def baseStart_4426103 : Nat := 118140960795 + 4426103 * 2 ^ 59
def prefixEnd_4426103 : Nat := 4983230072969 + 3 ^ 40 * 4426103 * 2
def baseEnd_4426103 : Nat := 2272718265307201585357229

theorem tailTrace_4426103 : CollatzResearch.WordTrace tailWord_4426103 prefixEnd_4426103 2272718265307201585357229 := by
  unfold tailWord_4426103
  simp only [CollatzResearch.WordTrace]
  refine ⟨161433238683992224055786963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107622159122661482703857975 161433238683992224055786963)
  ·
    refine ⟨242149858025988336083680445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161433238683992224055786963 242149858025988336083680445)
    ·
      refine ⟨90806196759745626031380167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 242149858025988336083680445 90806196759745626031380167)
      ·
        refine ⟨136209295139618439047070251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90806196759745626031380167 136209295139618439047070251)
        ·
          refine ⟨204313942709427658570605377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136209295139618439047070251 204313942709427658570605377)
          ·
            refine ⟨153235457032070743927954033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 204313942709427658570605377 153235457032070743927954033)
            ·
              refine ⟨114926592774053057945965525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 153235457032070743927954033 114926592774053057945965525)
              ·
                refine ⟨2693592018141868545608567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 114926592774053057945965525 2693592018141868545608567)
                ·
                  refine ⟨4040388027212802818412851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2693592018141868545608567 4040388027212802818412851)
                  ·
                    refine ⟨6060582040819204227619277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4040388027212802818412851 6060582040819204227619277)
                    ·
                      refine ⟨2272718265307201585357229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6060582040819204227619277 2272718265307201585357229)
                      ·
                        rfl

theorem cell23_4426103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 7, 1, 1, 3].length) (baseStart_4426103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4426103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4426103 prefixEnd_4426103 := by exact prefixLift 4426103
  have htrace : WordTrace (prefixWord ++ tailWord_4426103) baseStart_4426103 baseEnd_4426103 := by
    simpa [prefixWord, tailWord_4426103, baseEnd_4426103] using wordTrace_append hprefix tailTrace_4426103
  have hstable : (prefixWord ++ tailWord_4426103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4426103).length < 2 ^ (prefixWord ++ tailWord_4426103).sum := by decide
  have hdescent : baseEnd_4426103 < baseStart_4426103 := by decide
  rcases family_descends (prefixWord ++ tailWord_4426103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4426113 : List Nat := [1, 2, 4, 3, 1, 1, 1, 1, 4, 3, 2]
def baseStart_4426113 : Nat := 118140960795 + 4426113 * 2 ^ 59
def prefixEnd_4426113 : Nat := 4983230072969 + 3 ^ 40 * 4426113 * 2
def baseEnd_4426113 : Nat := 2272723400113746546232183

theorem tailTrace_4426113 : CollatzResearch.WordTrace tailWord_4426113 prefixEnd_4426113 2272723400113746546232183 := by
  unfold tailWord_4426113
  simp only [CollatzResearch.WordTrace]
  refine ⟨161433603413955995763650993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107622402275970663842433995 161433603413955995763650993)
  ·
    refine ⟨121075202560466996822738245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161433603413955995763650993 121075202560466996822738245)
    ·
      refine ⟨22701600480087561904263421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 121075202560466996822738245 22701600480087561904263421)
      ·
        refine ⟨8513100180032835714098783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22701600480087561904263421 8513100180032835714098783)
        ·
          refine ⟨12769650270049253571148175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8513100180032835714098783 12769650270049253571148175)
          ·
            refine ⟨19154475405073880356722263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12769650270049253571148175 19154475405073880356722263)
            ·
              refine ⟨28731713107610820535083395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19154475405073880356722263 28731713107610820535083395)
              ·
                refine ⟨43097569661416230802625093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28731713107610820535083395 43097569661416230802625093)
                ·
                  refine ⟨8080794311515543275492205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43097569661416230802625093 8080794311515543275492205)
                  ·
                    refine ⟨3030297866818328728309577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8080794311515543275492205 3030297866818328728309577)
                    ·
                      refine ⟨2272723400113746546232183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3030297866818328728309577 2272723400113746546232183)
                      ·
                        rfl

theorem cell23_4426113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_4426113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4426113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4426113 prefixEnd_4426113 := by exact prefixLift 4426113
  have htrace : WordTrace (prefixWord ++ tailWord_4426113) baseStart_4426113 baseEnd_4426113 := by
    simpa [prefixWord, tailWord_4426113, baseEnd_4426113] using wordTrace_append hprefix tailTrace_4426113
  have hstable : (prefixWord ++ tailWord_4426113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4426113).length < 2 ^ (prefixWord ++ tailWord_4426113).sum := by decide
  have hdescent : baseEnd_4426113 < baseStart_4426113 := by decide
  rcases family_descends (prefixWord ++ tailWord_4426113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4426114 : List Nat := [3, 4, 2, 1, 2, 1, 3, 2, 1, 4]
def baseStart_4426114 : Nat := 118140960795 + 4426114 * 2 ^ 59
def prefixEnd_4426114 : Nat := 4983230072969 + 3 ^ 40 * 4426114 * 2
def baseEnd_4426114 : Nat := 757574637864800347439893

theorem tailTrace_4426114 : CollatzResearch.WordTrace tailWord_4426114 prefixEnd_4426114 757574637864800347439893 := by
  unfold tailWord_4426114
  simp only [CollatzResearch.WordTrace]
  refine ⟨40358409971738093233609349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107622426591301581956291597 40358409971738093233609349)
  ·
    refine ⟨7567201869700892481301753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40358409971738093233609349 7567201869700892481301753)
    ·
      refine ⟨5675401402275669360976315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7567201869700892481301753 5675401402275669360976315)
      ·
        refine ⟨8513102103413504041464473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5675401402275669360976315 8513102103413504041464473)
        ·
          refine ⟨6384826577560128031098355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8513102103413504041464473 6384826577560128031098355)
          ·
            refine ⟨9577239866340192046647533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6384826577560128031098355 9577239866340192046647533)
            ·
              refine ⟨3591464949877572017492825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9577239866340192046647533 3591464949877572017492825)
              ·
                refine ⟨2693598712408179013119619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3591464949877572017492825 2693598712408179013119619)
                ·
                  refine ⟨4040398068612268519679429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2693598712408179013119619 4040398068612268519679429)
                  ·
                    refine ⟨757574637864800347439893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4040398068612268519679429 757574637864800347439893)
                    ·
                      rfl

theorem cell23_4426114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_4426114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4426114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4426114 prefixEnd_4426114 := by exact prefixLift 4426114
  have htrace : WordTrace (prefixWord ++ tailWord_4426114) baseStart_4426114 baseEnd_4426114 := by
    simpa [prefixWord, tailWord_4426114, baseEnd_4426114] using wordTrace_append hprefix tailTrace_4426114
  have hstable : (prefixWord ++ tailWord_4426114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4426114).length < 2 ^ (prefixWord ++ tailWord_4426114).sum := by decide
  have hdescent : baseEnd_4426114 < baseStart_4426114 := by decide
  rcases family_descends (prefixWord ++ tailWord_4426114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4426143 : List Nat := [1, 1, 2, 5, 1, 1, 2, 1, 5, 2, 2]
def baseStart_4426143 : Nat := 118140960795 + 4426143 * 2 ^ 59
def prefixEnd_4426143 : Nat := 4983230072969 + 3 ^ 40 * 4426143 * 2
def baseEnd_4426143 : Nat := 2272738804533381428857045

theorem tailTrace_4426143 : CollatzResearch.WordTrace tailWord_4426143 prefixEnd_4426143 2272738804533381428857045 := by
  unfold tailWord_4426143
  simp only [CollatzResearch.WordTrace]
  refine ⟨161434697603847310887243083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107623131735898207258162055 161434697603847310887243083)
  ·
    refine ⟨242152046405770966330864625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161434697603847310887243083 242152046405770966330864625)
    ·
      refine ⟨181614034804328224748148469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 242152046405770966330864625 181614034804328224748148469)
      ·
        refine ⟨17026315762905771070138919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 181614034804328224748148469 17026315762905771070138919)
        ·
          refine ⟨25539473644358656605208379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17026315762905771070138919 25539473644358656605208379)
          ·
            refine ⟨38309210466537984907812569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25539473644358656605208379 38309210466537984907812569)
            ·
              refine ⟨28731907849903488680859427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38309210466537984907812569 28731907849903488680859427)
              ·
                refine ⟨43097861774855233021289141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28731907849903488680859427 43097861774855233021289141)
                ·
                  refine ⟨4040424541392678095745857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43097861774855233021289141 4040424541392678095745857)
                  ·
                    refine ⟨3030318406044508571809393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4040424541392678095745857 3030318406044508571809393)
                    ·
                      refine ⟨2272738804533381428857045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3030318406044508571809393 2272738804533381428857045)
                      ·
                        rfl

theorem cell23_4426143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 5, 2, 2].length) (baseStart_4426143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4426143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4426143 prefixEnd_4426143 := by exact prefixLift 4426143
  have htrace : WordTrace (prefixWord ++ tailWord_4426143) baseStart_4426143 baseEnd_4426143 := by
    simpa [prefixWord, tailWord_4426143, baseEnd_4426143] using wordTrace_append hprefix tailTrace_4426143
  have hstable : (prefixWord ++ tailWord_4426143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4426143).length < 2 ^ (prefixWord ++ tailWord_4426143).sum := by decide
  have hdescent : baseEnd_4426143 < baseStart_4426143 := by decide
  rcases family_descends (prefixWord ++ tailWord_4426143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4426209 : List Nat := [1, 2, 3, 1, 2, 2, 1, 2, 1, 8]
def baseStart_4426209 : Nat := 118140960795 + 4426209 * 2 ^ 59
def prefixEnd_4426209 : Nat := 4983230072969 + 3 ^ 40 * 4426209 * 2
def baseEnd_4426209 : Nat := 757590898085526056877247

theorem tailTrace_4426209 : CollatzResearch.WordTrace tailWord_4426209 prefixEnd_4426209 757590898085526056877247 := by
  unfold tailWord_4426209
  simp only [CollatzResearch.WordTrace]
  refine ⟨161437104821608204159145681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107624736547738802772763787 161437104821608204159145681)
  ·
    refine ⟨121077828616206153119359261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161437104821608204159145681 121077828616206153119359261)
    ·
      refine ⟨45404185731077307419759723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121077828616206153119359261 45404185731077307419759723)
      ·
        refine ⟨68106278596615961129639585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45404185731077307419759723 68106278596615961129639585)
        ·
          refine ⟨51079708947461970847229689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68106278596615961129639585 51079708947461970847229689)
          ·
            refine ⟨38309781710596478135422267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51079708947461970847229689 38309781710596478135422267)
            ·
              refine ⟨57464672565894717203133401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38309781710596478135422267 57464672565894717203133401)
              ·
                refine ⟨43098504424421037902350051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57464672565894717203133401 43098504424421037902350051)
                ·
                  refine ⟨64647756636631556853525077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43098504424421037902350051 64647756636631556853525077)
                  ·
                    refine ⟨757590898085526056877247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 64647756636631556853525077 757590898085526056877247)
                    ·
                      rfl

theorem cell23_4426209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 8].length) (baseStart_4426209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4426209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4426209 prefixEnd_4426209 := by exact prefixLift 4426209
  have htrace : WordTrace (prefixWord ++ tailWord_4426209) baseStart_4426209 baseEnd_4426209 := by
    simpa [prefixWord, tailWord_4426209, baseEnd_4426209] using wordTrace_append hprefix tailTrace_4426209
  have hstable : (prefixWord ++ tailWord_4426209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4426209).length < 2 ^ (prefixWord ++ tailWord_4426209).sum := by decide
  have hdescent : baseEnd_4426209 < baseStart_4426209 := by decide
  rcases family_descends (prefixWord ++ tailWord_4426209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4426219 : List Nat := [1, 1, 1, 1, 2, 3, 4, 1, 1, 3, 5]
def baseStart_4426219 : Nat := 118140960795 + 4426219 * 2 ^ 59
def prefixEnd_4426219 : Nat := 4983230072969 + 3 ^ 40 * 4426219 * 2
def baseEnd_4426219 : Nat := 2272777829063123131506695

theorem tailTrace_4426219 : CollatzResearch.WordTrace tailWord_4426219 prefixEnd_4426219 2272777829063123131506695 := by
  unfold tailWord_4426219
  simp only [CollatzResearch.WordTrace]
  refine ⟨161437469551571975867009711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107624979701047983911339807 161437469551571975867009711)
  ·
    refine ⟨242156204327357963800514567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161437469551571975867009711 242156204327357963800514567)
    ·
      refine ⟨363234306491036945700771851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242156204327357963800514567 363234306491036945700771851)
      ·
        refine ⟨544851459736555418551157777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 363234306491036945700771851 544851459736555418551157777)
        ·
          refine ⟨408638594802416563913368333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 544851459736555418551157777 408638594802416563913368333)
          ·
            refine ⟨153239473050906211467513125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 408638594802416563913368333 153239473050906211467513125)
            ·
              refine ⟨28732401197044914650158711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 153239473050906211467513125 28732401197044914650158711)
              ·
                refine ⟨43098601795567371975238067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28732401197044914650158711 43098601795567371975238067)
                ·
                  refine ⟨64647902693351057962857101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43098601795567371975238067 64647902693351057962857101)
                  ·
                    refine ⟨24242963510006646736071413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 64647902693351057962857101 24242963510006646736071413)
                    ·
                      refine ⟨2272777829063123131506695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24242963510006646736071413 2272777829063123131506695)
                      ·
                        rfl

theorem cell23_4426219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 3, 5].length) (baseStart_4426219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4426219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4426219 prefixEnd_4426219 := by exact prefixLift 4426219
  have htrace : WordTrace (prefixWord ++ tailWord_4426219) baseStart_4426219 baseEnd_4426219 := by
    simpa [prefixWord, tailWord_4426219, baseEnd_4426219] using wordTrace_append hprefix tailTrace_4426219
  have hstable : (prefixWord ++ tailWord_4426219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4426219).length < 2 ^ (prefixWord ++ tailWord_4426219).sum := by decide
  have hdescent : baseEnd_4426219 < baseStart_4426219 := by decide
  rcases family_descends (prefixWord ++ tailWord_4426219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4426266 : List Nat := [3, 1, 1, 3, 1, 1, 2, 2, 1, 5, 3]
def baseStart_4426266 : Nat := 118140960795 + 4426266 * 2 ^ 59
def prefixEnd_4426266 : Nat := 4983230072969 + 3 ^ 40 * 4426266 * 2
def baseEnd_4426266 : Nat := 2272801962653884447618979

theorem tailTrace_4426266 : CollatzResearch.WordTrace tailWord_4426266 prefixEnd_4426266 2272801962653884447618979 := by
  unfold tailWord_4426266
  simp only [CollatzResearch.WordTrace]
  refine ⟨40359795945600425723492663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107626122521601135262647101 40359795945600425723492663)
  ·
    refine ⟨60539693918400638585238995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40359795945600425723492663 60539693918400638585238995)
    ·
      refine ⟨90809540877600957877858493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60539693918400638585238995 90809540877600957877858493)
      ·
        refine ⟨34053577829100359204196935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90809540877600957877858493 34053577829100359204196935)
        ·
          refine ⟨51080366743650538806295403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34053577829100359204196935 51080366743650538806295403)
          ·
            refine ⟨76620550115475808209443105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51080366743650538806295403 76620550115475808209443105)
            ·
              refine ⟨57465412586606856157082329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76620550115475808209443105 57465412586606856157082329)
              ·
                refine ⟨43099059439955142117811747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57465412586606856157082329 43099059439955142117811747)
                ·
                  refine ⟨64648589159932713176717621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43099059439955142117811747 64648589159932713176717621)
                  ·
                    refine ⟨6060805233743691860317277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 64648589159932713176717621 6060805233743691860317277)
                    ·
                      refine ⟨2272801962653884447618979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6060805233743691860317277 2272801962653884447618979)
                      ·
                        rfl

theorem cell23_4426266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 1, 5, 3].length) (baseStart_4426266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4426266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4426266 prefixEnd_4426266 := by exact prefixLift 4426266
  have htrace : WordTrace (prefixWord ++ tailWord_4426266) baseStart_4426266 baseEnd_4426266 := by
    simpa [prefixWord, tailWord_4426266, baseEnd_4426266] using wordTrace_append hprefix tailTrace_4426266
  have hstable : (prefixWord ++ tailWord_4426266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4426266).length < 2 ^ (prefixWord ++ tailWord_4426266).sum := by decide
  have hdescent : baseEnd_4426266 < baseStart_4426266 := by decide
  rcases family_descends (prefixWord ++ tailWord_4426266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4426293 : List Nat := [1, 3, 3, 1, 1, 2, 2, 1, 2, 5, 2]
def baseStart_4426293 : Nat := 118140960795 + 4426293 * 2 ^ 59
def prefixEnd_4426293 : Nat := 4983230072969 + 3 ^ 40 * 4426293 * 2
def baseEnd_4426293 : Nat := 2272815826631555841981355

theorem tailTrace_4426293 : CollatzResearch.WordTrace tailWord_4426293 prefixEnd_4426293 2272815826631555841981355 := by
  unfold tailWord_4426293
  simp only [CollatzResearch.WordTrace]
  refine ⟨161440168553303886505203533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107626779035535924336802355 161440168553303886505203533)
  ·
    refine ⟨60540063207488957439451325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 161440168553303886505203533 60540063207488957439451325)
    ·
      refine ⟨22702523702808359039794247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60540063207488957439451325 22702523702808359039794247)
      ·
        refine ⟨34053785554212538559691371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22702523702808359039794247 34053785554212538559691371)
        ·
          refine ⟨51080678331318807839537057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34053785554212538559691371 51080678331318807839537057)
          ·
            refine ⟨38310508748489105879652793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51080678331318807839537057 38310508748489105879652793)
            ·
              refine ⟨28732881561366829409739595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38310508748489105879652793 28732881561366829409739595)
              ·
                refine ⟨43099322342050244114609393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28732881561366829409739595 43099322342050244114609393)
                ·
                  refine ⟨32324491756537683085957045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43099322342050244114609393 32324491756537683085957045)
                  ·
                    refine ⟨3030421102175407789308473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32324491756537683085957045 3030421102175407789308473)
                    ·
                      refine ⟨2272815826631555841981355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3030421102175407789308473 2272815826631555841981355)
                      ·
                        rfl

theorem cell23_4426293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 2, 5, 2].length) (baseStart_4426293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4426293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4426293 prefixEnd_4426293 := by exact prefixLift 4426293
  have htrace : WordTrace (prefixWord ++ tailWord_4426293) baseStart_4426293 baseEnd_4426293 := by
    simpa [prefixWord, tailWord_4426293, baseEnd_4426293] using wordTrace_append hprefix tailTrace_4426293
  have hstable : (prefixWord ++ tailWord_4426293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4426293).length < 2 ^ (prefixWord ++ tailWord_4426293).sum := by decide
  have hdescent : baseEnd_4426293 < baseStart_4426293 := by decide
  rcases family_descends (prefixWord ++ tailWord_4426293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4426296 : List Nat := [2, 1, 2, 1, 4, 1, 3, 1, 1, 2, 5]
def baseStart_4426296 : Nat := 118140960795 + 4426296 * 2 ^ 59
def prefixEnd_4426296 : Nat := 4983230072969 + 3 ^ 40 * 4426296 * 2
def baseEnd_4426296 : Nat := 2272817367073519330243841

theorem tailTrace_4426296 : CollatzResearch.WordTrace tailWord_4426296 prefixEnd_4426296 2272817367073519330243841 := by
  unfold tailWord_4426296
  simp only [CollatzResearch.WordTrace]
  refine ⟨80720138986146509008781371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107626851981528678678375161 80720138986146509008781371)
  ·
    refine ⟨121080208479219763513172057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80720138986146509008781371 121080208479219763513172057)
    ·
      refine ⟨90810156359414822634879043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121080208479219763513172057 90810156359414822634879043)
      ·
        refine ⟨136215234539122233952318565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90810156359414822634879043 136215234539122233952318565)
        ·
          refine ⟨25540356476085418866059731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 136215234539122233952318565 25540356476085418866059731)
          ·
            refine ⟨38310534714128128299089597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25540356476085418866059731 38310534714128128299089597)
            ·
              refine ⟨14366450517798048112158599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38310534714128128299089597 14366450517798048112158599)
              ·
                refine ⟨21549675776697072168237899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14366450517798048112158599 21549675776697072168237899)
                ·
                  refine ⟨32324513665045608252356849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21549675776697072168237899 32324513665045608252356849)
                  ·
                    refine ⟨24243385248784206189267637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32324513665045608252356849 24243385248784206189267637)
                    ·
                      refine ⟨2272817367073519330243841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24243385248784206189267637 2272817367073519330243841)
                      ·
                        rfl

theorem cell23_4426296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 1, 1, 2, 5].length) (baseStart_4426296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4426296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4426296 prefixEnd_4426296 := by exact prefixLift 4426296
  have htrace : WordTrace (prefixWord ++ tailWord_4426296) baseStart_4426296 baseEnd_4426296 := by
    simpa [prefixWord, tailWord_4426296, baseEnd_4426296] using wordTrace_append hprefix tailTrace_4426296
  have hstable : (prefixWord ++ tailWord_4426296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4426296).length < 2 ^ (prefixWord ++ tailWord_4426296).sum := by decide
  have hdescent : baseEnd_4426296 < baseStart_4426296 := by decide
  rcases family_descends (prefixWord ++ tailWord_4426296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4426299 : List Nat := [1, 1, 1, 1, 1, 2, 1, 2, 3, 10]
def baseStart_4426299 : Nat := 118140960795 + 4426299 * 2 ^ 59
def prefixEnd_4426299 : Nat := 4983230072969 + 3 ^ 40 * 4426299 * 2
def baseEnd_4426299 : Nat := 757606302505160939502109

theorem tailTrace_4426299 : CollatzResearch.WordTrace tailWord_4426299 prefixEnd_4426299 757606302505160939502109 := by
  unfold tailWord_4426299
  simp only [CollatzResearch.WordTrace]
  refine ⟨161440387391282149529921951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107626924927521433019947967 161440387391282149529921951)
  ·
    refine ⟨242160581086923224294882927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161440387391282149529921951 242160581086923224294882927)
    ·
      refine ⟨363240871630384836442324391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242160581086923224294882927 363240871630384836442324391)
      ·
        refine ⟨544861307445577254663486587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 363240871630384836442324391 544861307445577254663486587)
        ·
          refine ⟨817291961168365881995229881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 544861307445577254663486587 817291961168365881995229881)
          ·
            refine ⟨612968970876274411496422411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 817291961168365881995229881 612968970876274411496422411)
            ·
              refine ⟨919453456314411617244633617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 612968970876274411496422411 919453456314411617244633617)
              ·
                refine ⟨689590092235808712933475213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 919453456314411617244633617 689590092235808712933475213)
                ·
                  refine ⟨258596284588428267350053205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 689590092235808712933475213 258596284588428267350053205)
                  ·
                    refine ⟨757606302505160939502109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 258596284588428267350053205 757606302505160939502109)
                    ·
                      rfl

theorem cell23_4426299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 10].length) (baseStart_4426299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4426299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4426299 prefixEnd_4426299 := by exact prefixLift 4426299
  have htrace : WordTrace (prefixWord ++ tailWord_4426299) baseStart_4426299 baseEnd_4426299 := by
    simpa [prefixWord, tailWord_4426299, baseEnd_4426299] using wordTrace_append hprefix tailTrace_4426299
  have hstable : (prefixWord ++ tailWord_4426299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4426299).length < 2 ^ (prefixWord ++ tailWord_4426299).sum := by decide
  have hdescent : baseEnd_4426299 < baseStart_4426299 := by decide
  rcases family_descends (prefixWord ++ tailWord_4426299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4426357 : List Nat := [1, 3, 4, 2, 2, 1, 1, 1, 2, 4, 2]
def baseStart_4426357 : Nat := 118140960795 + 4426357 * 2 ^ 59
def prefixEnd_4426357 : Nat := 4983230072969 + 3 ^ 40 * 4426357 * 2
def baseEnd_4426357 : Nat := 2272848689393443591581061

theorem tailTrace_4426357 : CollatzResearch.WordTrace tailWord_4426357 prefixEnd_4426357 2272848689393443591581061 := by
  unfold tailWord_4426357
  simp only [CollatzResearch.WordTrace]
  refine ⟨161442502825072025435533325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107628335216714683623688883 161442502825072025435533325)
  ·
    refine ⟨60540938559402009538324997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 161442502825072025435533325 60540938559402009538324997)
    ·
      refine ⟨11351425979887876788435937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60540938559402009538324997 11351425979887876788435937)
      ·
        refine ⟨8513569484915907591326953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11351425979887876788435937 8513569484915907591326953)
        ·
          refine ⟨6385177113686930693495215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8513569484915907591326953 6385177113686930693495215)
          ·
            refine ⟨9577765670530396040242823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6385177113686930693495215 9577765670530396040242823)
            ·
              refine ⟨14366648505795594060364235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9577765670530396040242823 14366648505795594060364235)
              ·
                refine ⟨21549972758693391090546353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14366648505795594060364235 21549972758693391090546353)
                ·
                  refine ⟨16162479569020043317909765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21549972758693391090546353 16162479569020043317909765)
                  ·
                    refine ⟨3030464919191258122108081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16162479569020043317909765 3030464919191258122108081)
                    ·
                      refine ⟨2272848689393443591581061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3030464919191258122108081 2272848689393443591581061)
                      ·
                        rfl

theorem cell23_4426357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_4426357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4426357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4426357 prefixEnd_4426357 := by exact prefixLift 4426357
  have htrace : WordTrace (prefixWord ++ tailWord_4426357) baseStart_4426357 baseEnd_4426357 := by
    simpa [prefixWord, tailWord_4426357, baseEnd_4426357] using wordTrace_append hprefix tailTrace_4426357
  have hstable : (prefixWord ++ tailWord_4426357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4426357).length < 2 ^ (prefixWord ++ tailWord_4426357).sum := by decide
  have hdescent : baseEnd_4426357 < baseStart_4426357 := by decide
  rcases family_descends (prefixWord ++ tailWord_4426357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4426383 : List Nat := [1, 1, 2, 1, 1, 1, 1, 7, 1, 5, 2]
def baseStart_4426383 : Nat := 118140960795 + 4426383 * 2 ^ 59
def prefixEnd_4426383 : Nat := 4983230072969 + 3 ^ 40 * 4426383 * 2
def baseEnd_4426383 : Nat := 2272862039890460489855941

theorem tailTrace_4426383 : CollatzResearch.WordTrace tailWord_4426383 prefixEnd_4426383 2272862039890460489855941 := by
  unfold tailWord_4426383
  simp only [CollatzResearch.WordTrace]
  refine ⟨161443451122977831875979803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107628967415318554583986535 161443451122977831875979803)
  ·
    refine ⟨242165176684466747813969705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161443451122977831875979803 242165176684466747813969705)
    ·
      refine ⟨181623882513350060860477279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 242165176684466747813969705 181623882513350060860477279)
      ·
        refine ⟨272435823770025091290715919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181623882513350060860477279 272435823770025091290715919)
        ·
          refine ⟨408653735655037636936073879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 272435823770025091290715919 408653735655037636936073879)
          ·
            refine ⟨612980603482556455404110819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 408653735655037636936073879 612980603482556455404110819)
            ·
              refine ⟨919470905223834683106166229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 612980603482556455404110819 919470905223834683106166229)
              ·
                refine ⟨21550099341183625385300771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 919470905223834683106166229 21550099341183625385300771)
                ·
                  refine ⟨32325149011775438077951157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21550099341183625385300771 32325149011775438077951157)
                  ·
                    refine ⟨3030482719853947319807921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32325149011775438077951157 3030482719853947319807921)
                    ·
                      refine ⟨2272862039890460489855941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3030482719853947319807921 2272862039890460489855941)
                      ·
                        rfl

theorem cell23_4426383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 7, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 7, 1, 5, 2].length) (baseStart_4426383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4426383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4426383 prefixEnd_4426383 := by exact prefixLift 4426383
  have htrace : WordTrace (prefixWord ++ tailWord_4426383) baseStart_4426383 baseEnd_4426383 := by
    simpa [prefixWord, tailWord_4426383, baseEnd_4426383] using wordTrace_append hprefix tailTrace_4426383
  have hstable : (prefixWord ++ tailWord_4426383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4426383).length < 2 ^ (prefixWord ++ tailWord_4426383).sum := by decide
  have hdescent : baseEnd_4426383 < baseStart_4426383 := by decide
  rcases family_descends (prefixWord ++ tailWord_4426383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4426393 : List Nat := [1, 2, 1, 2, 1, 2, 5, 3, 1, 5]
def baseStart_4426393 : Nat := 118140960795 + 4426393 * 2 ^ 59
def prefixEnd_4426393 : Nat := 4983230072969 + 3 ^ 40 * 4426393 * 2
def baseEnd_4426393 : Nat := 757622391565668483576965

theorem tailTrace_4426393 : CollatzResearch.WordTrace tailWord_4426393 prefixEnd_4426393 757622391565668483576965 := by
  unfold tailWord_4426393
  simp only [CollatzResearch.WordTrace]
  refine ⟨161443815852941603583843833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107629210568627735722562555 161443815852941603583843833)
  ·
    refine ⟨121082861889706202687882875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161443815852941603583843833 121082861889706202687882875)
    ·
      refine ⟨181624292834559304031824313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121082861889706202687882875 181624292834559304031824313)
      ·
        refine ⟨136218219625919478023868235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 181624292834559304031824313 136218219625919478023868235)
        ·
          refine ⟨204327329438879217035802353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136218219625919478023868235 204327329438879217035802353)
          ·
            refine ⟨153245497079159412776851765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 204327329438879217035802353 153245497079159412776851765)
            ·
              refine ⟨14366765351171194947829853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 153245497079159412776851765 14366765351171194947829853)
              ·
                refine ⟨5387537006689198105436195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14366765351171194947829853 5387537006689198105436195)
                ·
                  refine ⟨8081305510033797158154293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5387537006689198105436195 8081305510033797158154293)
                  ·
                    refine ⟨757622391565668483576965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8081305510033797158154293 757622391565668483576965)
                    ·
                      rfl

theorem cell23_4426393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 3, 1, 5].length) (baseStart_4426393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4426393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4426393 prefixEnd_4426393 := by exact prefixLift 4426393
  have htrace : WordTrace (prefixWord ++ tailWord_4426393) baseStart_4426393 baseEnd_4426393 := by
    simpa [prefixWord, tailWord_4426393, baseEnd_4426393] using wordTrace_append hprefix tailTrace_4426393
  have hstable : (prefixWord ++ tailWord_4426393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4426393).length < 2 ^ (prefixWord ++ tailWord_4426393).sum := by decide
  have hdescent : baseEnd_4426393 < baseStart_4426393 := by decide
  rcases family_descends (prefixWord ++ tailWord_4426393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4426430 : List Nat := [4, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2]
def baseStart_4426430 : Nat := 118140960795 + 4426430 * 2 ^ 59
def prefixEnd_4426430 : Nat := 4983230072969 + 3 ^ 40 * 4426430 * 2
def baseEnd_4426430 : Nat := 2272886173481221805968225

theorem tailTrace_4426430 : CollatzResearch.WordTrace tailWord_4426430 prefixEnd_4426430 2272886173481221805968225 := by
  unfold tailWord_4426430
  simp only [CollatzResearch.WordTrace]
  refine ⟨20180645669225944862867593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107630110235871705935293829 20180645669225944862867593)
  ·
    refine ⟨15135484251919458647150695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20180645669225944862867593 15135484251919458647150695)
    ·
      refine ⟨22703226377879187970726043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15135484251919458647150695 22703226377879187970726043)
      ·
        refine ⟨34054839566818781956089065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22703226377879187970726043 34054839566818781956089065)
        ·
          refine ⟨25541129675114086467066799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34054839566818781956089065 25541129675114086467066799)
          ·
            refine ⟨38311694512671129700600199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25541129675114086467066799 38311694512671129700600199)
            ·
              refine ⟨57467541769006694550900299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38311694512671129700600199 57467541769006694550900299)
              ·
                refine ⟨86201312653510041826350449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57467541769006694550900299 86201312653510041826350449)
                ·
                  refine ⟨64650984490132531369762837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 86201312653510041826350449 64650984490132531369762837)
                  ·
                    refine ⟨3030514897974962407957633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 64650984490132531369762837 3030514897974962407957633)
                    ·
                      refine ⟨2272886173481221805968225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3030514897974962407957633 2272886173481221805968225)
                      ·
                        rfl

theorem cell23_4426430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2].length) (baseStart_4426430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4426430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4426430 prefixEnd_4426430 := by exact prefixLift 4426430
  have htrace : WordTrace (prefixWord ++ tailWord_4426430) baseStart_4426430 baseEnd_4426430 := by
    simpa [prefixWord, tailWord_4426430, baseEnd_4426430] using wordTrace_append hprefix tailTrace_4426430
  have hstable : (prefixWord ++ tailWord_4426430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4426430).length < 2 ^ (prefixWord ++ tailWord_4426430).sum := by decide
  have hdescent : baseEnd_4426430 < baseStart_4426430 := by decide
  rcases family_descends (prefixWord ++ tailWord_4426430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4426460 : List Nat := [2, 2, 5, 1, 1, 1, 1, 2, 1, 1, 6]
def baseStart_4426460 : Nat := 118140960795 + 4426460 * 2 ^ 59
def prefixEnd_4426460 : Nat := 4983230072969 + 3 ^ 40 * 4426460 * 2
def baseEnd_4426460 : Nat := 2272901577900856688593087

theorem tailTrace_4426460 : CollatzResearch.WordTrace tailWord_4426460 prefixEnd_4426460 2272901577900856688593087 := by
  unfold tailWord_4426460
  simp only [CollatzResearch.WordTrace]
  refine ⟨80723129771849437013266417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107630839695799249351021889 80723129771849437013266417)
  ·
    refine ⟨60542347328887077759949813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80723129771849437013266417 60542347328887077759949813)
    ·
      refine ⟨5675845062083163539995295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 60542347328887077759949813 5675845062083163539995295)
      ·
        refine ⟨8513767593124745309992943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5675845062083163539995295 8513767593124745309992943)
        ·
          refine ⟨12770651389687117964989415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8513767593124745309992943 12770651389687117964989415)
          ·
            refine ⟨19155977084530676947484123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12770651389687117964989415 19155977084530676947484123)
            ·
              refine ⟨28733965626796015421226185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19155977084530676947484123 28733965626796015421226185)
              ·
                refine ⟨21550474220097011565919639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28733965626796015421226185 21550474220097011565919639)
                ·
                  refine ⟨32325711330145517348879459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21550474220097011565919639 32325711330145517348879459)
                  ·
                    refine ⟨48488566995218276023319189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32325711330145517348879459 48488566995218276023319189)
                    ·
                      refine ⟨2272901577900856688593087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48488566995218276023319189 2272901577900856688593087)
                      ·
                        rfl

theorem cell23_4426460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_4426460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4426460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4426460 prefixEnd_4426460 := by exact prefixLift 4426460
  have htrace : WordTrace (prefixWord ++ tailWord_4426460) baseStart_4426460 baseEnd_4426460 := by
    simpa [prefixWord, tailWord_4426460, baseEnd_4426460] using wordTrace_append hprefix tailTrace_4426460
  have hstable : (prefixWord ++ tailWord_4426460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4426460).length < 2 ^ (prefixWord ++ tailWord_4426460).sum := by decide
  have hdescent : baseEnd_4426460 < baseStart_4426460 := by decide
  rcases family_descends (prefixWord ++ tailWord_4426460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4426520 : List Nat := [2, 1, 2, 3, 1, 1, 1, 1, 5, 4, 2]
def baseStart_4426520 : Nat := 118140960795 + 4426520 * 2 ^ 59
def prefixEnd_4426520 : Nat := 4983230072969 + 3 ^ 40 * 4426520 * 2
def baseEnd_4426520 : Nat := 2272932386740126453842811

theorem tailTrace_4426520 : CollatzResearch.WordTrace tailWord_4426520 prefixEnd_4426520 2272932386740126453842811 := by
  unfold tailWord_4426520
  simp only [CollatzResearch.WordTrace]
  refine ⟨80724223961740752136858507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107632298615654336182478009 80724223961740752136858507)
  ·
    refine ⟨121086335942611128205287761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80724223961740752136858507 121086335942611128205287761)
    ·
      refine ⟨90814751956958346153965821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121086335942611128205287761 90814751956958346153965821)
      ·
        refine ⟨34055531983859379807737183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90814751956958346153965821 34055531983859379807737183)
        ·
          refine ⟨51083297975789069711605775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34055531983859379807737183 51083297975789069711605775)
          ·
            refine ⟨76624946963683604567408663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51083297975789069711605775 76624946963683604567408663)
            ·
              refine ⟨114937420445525406851112995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76624946963683604567408663 114937420445525406851112995)
              ·
                refine ⟨172406130668288110276669493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114937420445525406851112995 172406130668288110276669493)
                ·
                  refine ⟨16163074750152010338437765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 172406130668288110276669493 16163074750152010338437765)
                  ·
                    refine ⟨3030576515653501938457081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16163074750152010338437765 3030576515653501938457081)
                    ·
                      refine ⟨2272932386740126453842811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3030576515653501938457081 2272932386740126453842811)
                      ·
                        rfl

theorem cell23_4426520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 5, 4, 2].length) (baseStart_4426520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4426520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4426520 prefixEnd_4426520 := by exact prefixLift 4426520
  have htrace : WordTrace (prefixWord ++ tailWord_4426520) baseStart_4426520 baseEnd_4426520 := by
    simpa [prefixWord, tailWord_4426520, baseEnd_4426520] using wordTrace_append hprefix tailTrace_4426520
  have hstable : (prefixWord ++ tailWord_4426520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4426520).length < 2 ^ (prefixWord ++ tailWord_4426520).sum := by decide
  have hdescent : baseEnd_4426520 < baseStart_4426520 := by decide
  rcases family_descends (prefixWord ++ tailWord_4426520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4426530 : List Nat := [3, 3, 1, 1, 2, 3, 1, 1, 2, 6]
def baseStart_4426530 : Nat := 118140960795 + 4426530 * 2 ^ 59
def prefixEnd_4426530 : Nat := 4983230072969 + 3 ^ 40 * 4426530 * 2
def baseEnd_4426530 : Nat := 757645840515557138239255

theorem tailTrace_4426530 : CollatzResearch.WordTrace tailWord_4426530 prefixEnd_4426530 757645840515557138239255 := by
  unfold tailWord_4426530
  simp only [CollatzResearch.WordTrace]
  refine ⟨40362203163361318995395261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107632541768963517321054029 40362203163361318995395261)
  ·
    refine ⟨15135826186260494623273223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40362203163361318995395261 15135826186260494623273223)
    ·
      refine ⟨22703739279390741934909835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15135826186260494623273223 22703739279390741934909835)
      ·
        refine ⟨34055608919086112902364753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22703739279390741934909835 34055608919086112902364753)
        ·
          refine ⟨25541706689314584676773565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34055608919086112902364753 25541706689314584676773565)
          ·
            refine ⟨9578140008492969253790087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25541706689314584676773565 9578140008492969253790087)
            ·
              refine ⟨14367210012739453880685131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9578140008492969253790087 14367210012739453880685131)
              ·
                refine ⟨21550815019109180821027697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14367210012739453880685131 21550815019109180821027697)
                ·
                  refine ⟨16163111264331885615770773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21550815019109180821027697 16163111264331885615770773)
                  ·
                    refine ⟨757645840515557138239255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16163111264331885615770773 757645840515557138239255)
                    ·
                      rfl

theorem cell23_4426530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 1, 2, 6].length) (baseStart_4426530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4426530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4426530 prefixEnd_4426530 := by exact prefixLift 4426530
  have htrace : WordTrace (prefixWord ++ tailWord_4426530) baseStart_4426530 baseEnd_4426530 := by
    simpa [prefixWord, tailWord_4426530, baseEnd_4426530] using wordTrace_append hprefix tailTrace_4426530
  have hstable : (prefixWord ++ tailWord_4426530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4426530).length < 2 ^ (prefixWord ++ tailWord_4426530).sum := by decide
  have hdescent : baseEnd_4426530 < baseStart_4426530 := by decide
  rcases family_descends (prefixWord ++ tailWord_4426530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4426558 : List Nat := [4, 2, 1, 2, 3, 2, 2, 1, 1, 3, 2]
def baseStart_4426558 : Nat := 118140960795 + 4426558 * 2 ^ 59
def prefixEnd_4426558 : Nat := 4983230072969 + 3 ^ 40 * 4426558 * 2
def baseEnd_4426558 : Nat := 2272951899004997305167637

theorem tailTrace_4426558 : CollatzResearch.WordTrace tailWord_4426558 prefixEnd_4426558 2272951899004997305167637 := by
  unfold tailWord_4426558
  simp only [CollatzResearch.WordTrace]
  refine ⟨20181229237167979595450041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107633222598229224509066885 20181229237167979595450041)
  ·
    refine ⟨15135921927875984696587531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20181229237167979595450041 15135921927875984696587531)
    ·
      refine ⟨22703882891813977044881297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15135921927875984696587531 22703882891813977044881297)
      ·
        refine ⟨17027912168860482783660973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22703882891813977044881297 17027912168860482783660973)
        ·
          refine ⟨6385467063322681043872865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17027912168860482783660973 6385467063322681043872865)
          ·
            refine ⟨4789100297492010782904649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6385467063322681043872865 4789100297492010782904649)
            ·
              refine ⟨3591825223119008087178487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4789100297492010782904649 3591825223119008087178487)
              ·
                refine ⟨5387737834678512130767731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3591825223119008087178487 5387737834678512130767731)
                ·
                  refine ⟨8081606752017768196151597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5387737834678512130767731 8081606752017768196151597)
                  ·
                    refine ⟨3030602532006663073556849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8081606752017768196151597 3030602532006663073556849)
                    ·
                      refine ⟨2272951899004997305167637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3030602532006663073556849 2272951899004997305167637)
                      ·
                        rfl

theorem cell23_4426558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 2, 1, 1, 3, 2].length) (baseStart_4426558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4426558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4426558 prefixEnd_4426558 := by exact prefixLift 4426558
  have htrace : WordTrace (prefixWord ++ tailWord_4426558) baseStart_4426558 baseEnd_4426558 := by
    simpa [prefixWord, tailWord_4426558, baseEnd_4426558] using wordTrace_append hprefix tailTrace_4426558
  have hstable : (prefixWord ++ tailWord_4426558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4426558).length < 2 ^ (prefixWord ++ tailWord_4426558).sum := by decide
  have hdescent : baseEnd_4426558 < baseStart_4426558 := by decide
  rcases family_descends (prefixWord ++ tailWord_4426558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4426588 : List Nat := [2, 2, 4, 2, 1, 2, 3, 1, 2, 2, 2]
def baseStart_4426588 : Nat := 118140960795 + 4426588 * 2 ^ 59
def prefixEnd_4426588 : Nat := 4983230072969 + 3 ^ 40 * 4426588 * 2
def baseEnd_4426588 : Nat := 2272967303424632187792499

theorem tailTrace_4426588 : CollatzResearch.WordTrace tailWord_4426588 prefixEnd_4426588 2272967303424632187792499 := by
  unfold tailWord_4426588
  simp only [CollatzResearch.WordTrace]
  refine ⟨80725464043617575943596209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107633952058156767924794945 80725464043617575943596209)
  ·
    refine ⟨60544098032713181957697157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80725464043617575943596209 60544098032713181957697157)
    ·
      refine ⟨11352018381133721617068217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60544098032713181957697157 11352018381133721617068217)
      ·
        refine ⟨8514013785850291212801163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11352018381133721617068217 8514013785850291212801163)
        ·
          refine ⟨12771020678775436819201745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8514013785850291212801163 12771020678775436819201745)
          ·
            refine ⟨9578265509081577614401309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12771020678775436819201745 9578265509081577614401309)
            ·
              refine ⟨3591849565905591605400491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9578265509081577614401309 3591849565905591605400491)
              ·
                refine ⟨5387774348858387408100737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3591849565905591605400491 5387774348858387408100737)
                ·
                  refine ⟨4040830761643790556075553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5387774348858387408100737 4040830761643790556075553)
                  ·
                    refine ⟨3030623071232842917056665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4040830761643790556075553 3030623071232842917056665)
                    ·
                      refine ⟨2272967303424632187792499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3030623071232842917056665 2272967303424632187792499)
                      ·
                        rfl

theorem cell23_4426588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_4426588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4426588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4426588 prefixEnd_4426588 := by exact prefixLift 4426588
  have htrace : WordTrace (prefixWord ++ tailWord_4426588) baseStart_4426588 baseEnd_4426588 := by
    simpa [prefixWord, tailWord_4426588, baseEnd_4426588] using wordTrace_append hprefix tailTrace_4426588
  have hstable : (prefixWord ++ tailWord_4426588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4426588).length < 2 ^ (prefixWord ++ tailWord_4426588).sum := by decide
  have hdescent : baseEnd_4426588 < baseStart_4426588 := by decide
  rcases family_descends (prefixWord ++ tailWord_4426588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4426610 : List Nat := [3, 2, 1, 2, 1, 1, 4, 1, 1, 3, 4]
def baseStart_4426610 : Nat := 118140960795 + 4426610 * 2 ^ 59
def prefixEnd_4426610 : Nat := 4983230072969 + 3 ^ 40 * 4426610 * 2
def baseEnd_4426610 : Nat := 2272978599999031101717397

theorem tailTrace_4426610 : CollatzResearch.WordTrace tailWord_4426610 prefixEnd_4426610 2272978599999031101717397 := by
  unfold tailWord_4426610
  simp only [CollatzResearch.WordTrace]
  refine ⟨40362932623288862411123321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107634486995436966429662189 40362932623288862411123321)
  ·
    refine ⟨30272199467466646808342491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40362932623288862411123321 30272199467466646808342491)
    ·
      refine ⟨45408299201199970212513737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30272199467466646808342491 45408299201199970212513737)
      ·
        refine ⟨34056224400899977659385303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45408299201199970212513737 34056224400899977659385303)
        ·
          refine ⟨51084336601349966489077955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34056224400899977659385303 51084336601349966489077955)
          ·
            refine ⟨76626504902024949733616933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51084336601349966489077955 76626504902024949733616933)
            ·
              refine ⟨14367469669129678075053175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 76626504902024949733616933 14367469669129678075053175)
              ·
                refine ⟨21551204503694517112579763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14367469669129678075053175 21551204503694517112579763)
                ·
                  refine ⟨32326806755541775668869645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21551204503694517112579763 32326806755541775668869645)
                  ·
                    refine ⟨12122552533328165875826117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32326806755541775668869645 12122552533328165875826117)
                    ·
                      refine ⟨2272978599999031101717397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12122552533328165875826117 2272978599999031101717397)
                      ·
                        rfl

theorem cell23_4426610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_4426610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4426610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4426610 prefixEnd_4426610 := by exact prefixLift 4426610
  have htrace : WordTrace (prefixWord ++ tailWord_4426610) baseStart_4426610 baseEnd_4426610 := by
    simpa [prefixWord, tailWord_4426610, baseEnd_4426610] using wordTrace_append hprefix tailTrace_4426610
  have hstable : (prefixWord ++ tailWord_4426610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4426610).length < 2 ^ (prefixWord ++ tailWord_4426610).sum := by decide
  have hdescent : baseEnd_4426610 < baseStart_4426610 := by decide
  rcases family_descends (prefixWord ++ tailWord_4426610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4426620 : List Nat := [2, 2, 2, 1, 1, 1, 1, 4, 5, 4]
def baseStart_4426620 : Nat := 118140960795 + 4426620 * 2 ^ 59
def prefixEnd_4426620 : Nat := 4983230072969 + 3 ^ 40 * 4426620 * 2
def baseEnd_4426620 : Nat := 757661244935192020864117

theorem tailTrace_4426620 : CollatzResearch.WordTrace tailWord_4426620 prefixEnd_4426620 757661244935192020864117 := by
  unfold tailWord_4426620
  simp only [CollatzResearch.WordTrace]
  refine ⟨80726047611559610676178657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107634730148746147568238209 80726047611559610676178657)
  ·
    refine ⟨60544535708669708007133993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80726047611559610676178657 60544535708669708007133993)
    ·
      refine ⟨45408401781502281005350495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60544535708669708007133993 45408401781502281005350495)
      ·
        refine ⟨68112602672253421508025743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45408401781502281005350495 68112602672253421508025743)
        ·
          refine ⟨102168904008380132262038615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68112602672253421508025743 102168904008380132262038615)
          ·
            refine ⟨153253356012570198393057923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102168904008380132262038615 153253356012570198393057923)
            ·
              refine ⟨229880034018855297589586885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 153253356012570198393057923 229880034018855297589586885)
              ·
                refine ⟨43102506378535368298047541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 229880034018855297589586885 43102506378535368298047541)
                ·
                  refine ⟨4040859972987690777941957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43102506378535368298047541 4040859972987690777941957)
                  ·
                    refine ⟨757661244935192020864117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4040859972987690777941957 757661244935192020864117)
                    ·
                      rfl

theorem cell23_4426620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 5, 4].length) (baseStart_4426620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4426620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4426620 prefixEnd_4426620 := by exact prefixLift 4426620
  have htrace : WordTrace (prefixWord ++ tailWord_4426620) baseStart_4426620 baseEnd_4426620 := by
    simpa [prefixWord, tailWord_4426620, baseEnd_4426620] using wordTrace_append hprefix tailTrace_4426620
  have hstable : (prefixWord ++ tailWord_4426620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4426620).length < 2 ^ (prefixWord ++ tailWord_4426620).sum := by decide
  have hdescent : baseEnd_4426620 < baseStart_4426620 := by decide
  rcases family_descends (prefixWord ++ tailWord_4426620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4426623 : List Nat := [1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 6]
def baseStart_4426623 : Nat := 118140960795 + 4426623 * 2 ^ 59
def prefixEnd_4426623 : Nat := 4983230072969 + 3 ^ 40 * 4426623 * 2
def baseEnd_4426623 : Nat := 2272985275247539550854837

theorem tailTrace_4426623 : CollatzResearch.WordTrace tailWord_4426623 prefixEnd_4426623 2272985275247539550854837 := by
  unfold tailWord_4426623
  simp only [CollatzResearch.WordTrace]
  refine ⟨161452204642108352864716523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107634803094738901909811015 161452204642108352864716523)
  ·
    refine ⟨242178306963162529297074785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161452204642108352864716523 242178306963162529297074785)
    ·
      refine ⟨181633730222371896972806089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 242178306963162529297074785 181633730222371896972806089)
      ·
        refine ⟨136225297666778922729604567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 181633730222371896972806089 136225297666778922729604567)
        ·
          refine ⟨204337946500168384094406851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136225297666778922729604567 204337946500168384094406851)
          ·
            refine ⟨306506919750252576141610277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 204337946500168384094406851 306506919750252576141610277)
            ·
              refine ⟨57470047453172358026551927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 306506919750252576141610277 57470047453172358026551927)
              ·
                refine ⟨86205071179758537039827891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57470047453172358026551927 86205071179758537039827891)
                ·
                  refine ⟨129307606769637805559741837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 86205071179758537039827891 129307606769637805559741837)
                  ·
                    refine ⟨48490352538614177084903189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 129307606769637805559741837 48490352538614177084903189)
                    ·
                      refine ⟨2272985275247539550854837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48490352538614177084903189 2272985275247539550854837)
                      ·
                        rfl

theorem cell23_4426623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 6].length) (baseStart_4426623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4426623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4426623 prefixEnd_4426623 := by exact prefixLift 4426623
  have htrace : WordTrace (prefixWord ++ tailWord_4426623) baseStart_4426623 baseEnd_4426623 := by
    simpa [prefixWord, tailWord_4426623, baseEnd_4426623] using wordTrace_append hprefix tailTrace_4426623
  have hstable : (prefixWord ++ tailWord_4426623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4426623).length < 2 ^ (prefixWord ++ tailWord_4426623).sum := by decide
  have hdescent : baseEnd_4426623 < baseStart_4426623 := by decide
  rcases family_descends (prefixWord ++ tailWord_4426623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4426687 : List Nat := [1, 1, 2, 2, 2, 1, 2, 3, 4, 3, 2]
def baseStart_4426687 : Nat := 118140960795 + 4426687 * 2 ^ 59
def prefixEnd_4426687 : Nat := 4983230072969 + 3 ^ 40 * 4426687 * 2
def baseEnd_4426687 : Nat := 2273018138009427300454543

theorem tailTrace_4426687 : CollatzResearch.WordTrace tailWord_4426687 prefixEnd_4426687 2273018138009427300454543 := by
  unfold tailWord_4426687
  simp only [CollatzResearch.WordTrace]
  refine ⟨161454538913876491795046315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107636359275917661196697543 161454538913876491795046315)
  ·
    refine ⟨242181808370814737692569473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161454538913876491795046315 242181808370814737692569473)
    ·
      refine ⟨181636356278111053269427105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 242181808370814737692569473 181636356278111053269427105)
      ·
        refine ⟨136227267208583289952070329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 181636356278111053269427105 136227267208583289952070329)
        ·
          refine ⟨102170450406437467464052747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136227267208583289952070329 102170450406437467464052747)
          ·
            refine ⟨153255675609656201196079121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102170450406437467464052747 153255675609656201196079121)
            ·
              refine ⟨114941756707242150897059341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 153255675609656201196079121 114941756707242150897059341)
              ·
                refine ⟨43103158765215806586397253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 114941756707242150897059341 43103158765215806586397253)
                ·
                  refine ⟨8081842268477963734949485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43103158765215806586397253 8081842268477963734949485)
                  ·
                    refine ⟨3030690850679236400606057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8081842268477963734949485 3030690850679236400606057)
                    ·
                      refine ⟨2273018138009427300454543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3030690850679236400606057 2273018138009427300454543)
                      ·
                        rfl

theorem cell23_4426687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 4, 3, 2].length) (baseStart_4426687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4426687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4426687 prefixEnd_4426687 := by exact prefixLift 4426687
  have htrace : WordTrace (prefixWord ++ tailWord_4426687) baseStart_4426687 baseEnd_4426687 := by
    simpa [prefixWord, tailWord_4426687, baseEnd_4426687] using wordTrace_append hprefix tailTrace_4426687
  have hstable : (prefixWord ++ tailWord_4426687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4426687).length < 2 ^ (prefixWord ++ tailWord_4426687).sum := by decide
  have hdescent : baseEnd_4426687 < baseStart_4426687 := by decide
  rcases family_descends (prefixWord ++ tailWord_4426687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4426727 : List Nat := [1, 1, 5, 2, 2, 1, 2, 2, 1, 6]
def baseStart_4426727 : Nat := 118140960795 + 4426727 * 2 ^ 59
def prefixEnd_4426727 : Nat := 4983230072969 + 3 ^ 40 * 4426727 * 2
def baseEnd_4426727 : Nat := 757679559078535714651453

theorem tailTrace_4426727 : CollatzResearch.WordTrace tailWord_4426727 prefixEnd_4426727 757679559078535714651453 := by
  unfold tailWord_4426727
  simp only [CollatzResearch.WordTrace]
  refine ⟨161455997833731578626502435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107637331889154385751001623 161455997833731578626502435)
  ·
    refine ⟨242183996750597367939753653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161455997833731578626502435 242183996750597367939753653)
    ·
      refine ⟨22704749695368503244351905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 242183996750597367939753653 22704749695368503244351905)
      ·
        refine ⟨17028562271526377433263929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22704749695368503244351905 17028562271526377433263929)
        ·
          refine ⟨12771421703644783074947947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17028562271526377433263929 12771421703644783074947947)
          ·
            refine ⟨19157132555467174612421921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12771421703644783074947947 19157132555467174612421921)
            ·
              refine ⟨14367849416600380959316441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19157132555467174612421921 14367849416600380959316441)
              ·
                refine ⟨10775887062450285719487331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14367849416600380959316441 10775887062450285719487331)
                ·
                  refine ⟨16163830593675428579230997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10775887062450285719487331 16163830593675428579230997)
                  ·
                    refine ⟨757679559078535714651453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16163830593675428579230997 757679559078535714651453)
                    ·
                      rfl

theorem cell23_4426727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 2, 1, 6].length) (baseStart_4426727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4426727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4426727 prefixEnd_4426727 := by exact prefixLift 4426727
  have htrace : WordTrace (prefixWord ++ tailWord_4426727) baseStart_4426727 baseEnd_4426727 := by
    simpa [prefixWord, tailWord_4426727, baseEnd_4426727] using wordTrace_append hprefix tailTrace_4426727
  have hstable : (prefixWord ++ tailWord_4426727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4426727).length < 2 ^ (prefixWord ++ tailWord_4426727).sum := by decide
  have hdescent : baseEnd_4426727 < baseStart_4426727 := by decide
  rcases family_descends (prefixWord ++ tailWord_4426727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4426764 : List Nat := [2, 2, 1, 2, 3, 4, 1, 1, 1, 2, 4]
def baseStart_4426764 : Nat := 118140960795 + 4426764 * 2 ^ 59
def prefixEnd_4426764 : Nat := 4983230072969 + 3 ^ 40 * 4426764 * 2
def baseEnd_4426764 : Nat := 2273057676019823499191689

theorem tailTrace_4426764 : CollatzResearch.WordTrace tailWord_4426764 prefixEnd_4426764 2273057676019823499191689 := by
  unfold tailWord_4426764
  simp only [CollatzResearch.WordTrace]
  refine ⟨80728673667298766972799673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107638231556398355963732897 80728673667298766972799673)
  ·
    refine ⟨60546505250474075229599755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80728673667298766972799673 60546505250474075229599755)
    ·
      refine ⟨90819757875711112844399633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60546505250474075229599755 90819757875711112844399633)
      ·
        refine ⟨68114818406783334633299725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90819757875711112844399633 68114818406783334633299725)
        ·
          refine ⟨25543056902543750487487397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68114818406783334633299725 25543056902543750487487397)
          ·
            refine ⟨4789323169226953216403887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25543056902543750487487397 4789323169226953216403887)
            ·
              refine ⟨7183984753840429824605831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4789323169226953216403887 7183984753840429824605831)
              ·
                refine ⟨10775977130760644736908747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7183984753840429824605831 10775977130760644736908747)
                ·
                  refine ⟨16163965696140967105363121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10775977130760644736908747 16163965696140967105363121)
                  ·
                    refine ⟨12122974272105725329022341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16163965696140967105363121 12122974272105725329022341)
                    ·
                      refine ⟨2273057676019823499191689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12122974272105725329022341 2273057676019823499191689)
                      ·
                        rfl

theorem cell23_4426764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 1, 1, 2, 4].length) (baseStart_4426764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4426764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4426764 prefixEnd_4426764 := by exact prefixLift 4426764
  have htrace : WordTrace (prefixWord ++ tailWord_4426764) baseStart_4426764 baseEnd_4426764 := by
    simpa [prefixWord, tailWord_4426764, baseEnd_4426764] using wordTrace_append hprefix tailTrace_4426764
  have hstable : (prefixWord ++ tailWord_4426764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4426764).length < 2 ^ (prefixWord ++ tailWord_4426764).sum := by decide
  have hdescent : baseEnd_4426764 < baseStart_4426764 := by decide
  rcases family_descends (prefixWord ++ tailWord_4426764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4426785 : List Nat := [1, 2, 3, 2, 3, 3, 1, 3, 1, 2, 2]
def baseStart_4426785 : Nat := 118140960795 + 4426785 * 2 ^ 59
def prefixEnd_4426785 : Nat := 4983230072969 + 3 ^ 40 * 4426785 * 2
def baseEnd_4426785 : Nat := 2273068459113567917029093

theorem tailTrace_4426785 : CollatzResearch.WordTrace tailWord_4426785 prefixEnd_4426785 2273068459113567917029093 := by
  unfold tailWord_4426785
  simp only [CollatzResearch.WordTrace]
  refine ⟨161458113267521454532113809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107638742178347636354742539 161458113267521454532113809)
  ·
    refine ⟨121093584950641090899085357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161458113267521454532113809 121093584950641090899085357)
    ·
      refine ⟨45410094356490409087157009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121093584950641090899085357 45410094356490409087157009)
      ·
        refine ⟨34057570767367806815367757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45410094356490409087157009 34057570767367806815367757)
        ·
          refine ⟨12771589037762927555762909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34057570767367806815367757 12771589037762927555762909)
          ·
            refine ⟨4789345889161097833411091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12771589037762927555762909 4789345889161097833411091)
            ·
              refine ⟨7184018833741646750116637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4789345889161097833411091 7184018833741646750116637)
              ·
                refine ⟨2694007062653117531293739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7184018833741646750116637 2694007062653117531293739)
                ·
                  refine ⟨4041010593979676296940609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2694007062653117531293739 4041010593979676296940609)
                  ·
                    refine ⟨3030757945484757222705457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4041010593979676296940609 3030757945484757222705457)
                    ·
                      refine ⟨2273068459113567917029093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3030757945484757222705457 2273068459113567917029093)
                      ·
                        rfl

theorem cell23_4426785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 3, 1, 2, 2].length) (baseStart_4426785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4426785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4426785 prefixEnd_4426785 := by exact prefixLift 4426785
  have htrace : WordTrace (prefixWord ++ tailWord_4426785) baseStart_4426785 baseEnd_4426785 := by
    simpa [prefixWord, tailWord_4426785, baseEnd_4426785] using wordTrace_append hprefix tailTrace_4426785
  have hstable : (prefixWord ++ tailWord_4426785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4426785).length < 2 ^ (prefixWord ++ tailWord_4426785).sum := by decide
  have hdescent : baseEnd_4426785 < baseStart_4426785 := by decide
  rcases family_descends (prefixWord ++ tailWord_4426785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4426824 : List Nat := [2, 1, 3, 1, 1, 1, 4, 3, 1, 4, 2]
def baseStart_4426824 : Nat := 118140960795 + 4426824 * 2 ^ 59
def prefixEnd_4426824 : Nat := 4983230072969 + 3 ^ 40 * 4426824 * 2
def baseEnd_4426824 : Nat := 2273088484859093264441413

theorem tailTrace_4426824 : CollatzResearch.WordTrace tailWord_4426824 prefixEnd_4426824 2273088484859093264441413 := by
  unfold tailWord_4426824
  simp only [CollatzResearch.WordTrace]
  refine ⟨80729767857190082096391763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107639690476253442795189017 80729767857190082096391763)
  ·
    refine ⟨121094651785785123144587645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80729767857190082096391763 121094651785785123144587645)
    ·
      refine ⟨45410494419669421179220367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121094651785785123144587645 45410494419669421179220367)
      ·
        refine ⟨68115741629504131768830551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45410494419669421179220367 68115741629504131768830551)
        ·
          refine ⟨102173612444256197653245827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68115741629504131768830551 102173612444256197653245827)
          ·
            refine ⟨153260418666384296479868741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102173612444256197653245827 153260418666384296479868741)
            ·
              refine ⟨28736328499947055589975389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 153260418666384296479868741 28736328499947055589975389)
              ·
                refine ⟨10776123187480145846240771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28736328499947055589975389 10776123187480145846240771)
                ·
                  refine ⟨16164184781220218769361157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10776123187480145846240771 16164184781220218769361157)
                  ·
                    refine ⟨3030784646478791019255217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16164184781220218769361157 3030784646478791019255217)
                    ·
                      refine ⟨2273088484859093264441413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3030784646478791019255217 2273088484859093264441413)
                      ·
                        rfl

theorem cell23_4426824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 3, 1, 4, 2].length) (baseStart_4426824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4426824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4426824 prefixEnd_4426824 := by exact prefixLift 4426824
  have htrace : WordTrace (prefixWord ++ tailWord_4426824) baseStart_4426824 baseEnd_4426824 := by
    simpa [prefixWord, tailWord_4426824, baseEnd_4426824] using wordTrace_append hprefix tailTrace_4426824
  have hstable : (prefixWord ++ tailWord_4426824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4426824).length < 2 ^ (prefixWord ++ tailWord_4426824).sum := by decide
  have hdescent : baseEnd_4426824 < baseStart_4426824 := by decide
  rcases family_descends (prefixWord ++ tailWord_4426824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4426858 : List Nat := [3, 1, 3, 2, 2, 1, 1, 4, 2, 2, 2]
def baseStart_4426858 : Nat := 118140960795 + 4426858 * 2 ^ 59
def prefixEnd_4426858 : Nat := 4983230072969 + 3 ^ 40 * 4426858 * 2
def baseEnd_4426858 : Nat := 2273105943201346131416257

theorem tailTrace_4426858 : CollatzResearch.WordTrace tailWord_4426858 prefixEnd_4426858 2273105943201346131416257 := by
  unfold tailWord_4426858
  simp only [CollatzResearch.WordTrace]
  refine ⟨40365193949064246999880307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107640517197504658666347485 40365193949064246999880307)
  ·
    refine ⟨60547790923596370499820461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40365193949064246999880307 60547790923596370499820461)
    ·
      refine ⟨22705421596348638937432673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60547790923596370499820461 22705421596348638937432673)
      ·
        refine ⟨17029066197261479203074505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22705421596348638937432673 17029066197261479203074505)
        ·
          refine ⟨12771799647946109402305879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17029066197261479203074505 12771799647946109402305879)
          ·
            refine ⟨19157699471919164103458819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12771799647946109402305879 19157699471919164103458819)
            ·
              refine ⟨28736549207878746155188229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19157699471919164103458819 28736549207878746155188229)
              ·
                refine ⟨5388102976477264904097793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28736549207878746155188229 5388102976477264904097793)
                ·
                  refine ⟨4041077232357948678073345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5388102976477264904097793 4041077232357948678073345)
                  ·
                    refine ⟨3030807924268461508555009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4041077232357948678073345 3030807924268461508555009)
                    ·
                      refine ⟨2273105943201346131416257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3030807924268461508555009 2273105943201346131416257)
                      ·
                        rfl

theorem cell23_4426858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 4, 2, 2, 2].length) (baseStart_4426858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4426858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4426858 prefixEnd_4426858 := by exact prefixLift 4426858
  have htrace : WordTrace (prefixWord ++ tailWord_4426858) baseStart_4426858 baseEnd_4426858 := by
    simpa [prefixWord, tailWord_4426858, baseEnd_4426858] using wordTrace_append hprefix tailTrace_4426858
  have hstable : (prefixWord ++ tailWord_4426858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4426858).length < 2 ^ (prefixWord ++ tailWord_4426858).sum := by decide
  have hdescent : baseEnd_4426858 < baseStart_4426858 := by decide
  rcases family_descends (prefixWord ++ tailWord_4426858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4426864 : List Nat := [2, 1, 1, 1, 5, 1, 3, 4, 5]
def baseStart_4426864 : Nat := 118140960795 + 4426864 * 2 ^ 59
def prefixEnd_4426864 : Nat := 4983230072969 + 3 ^ 40 * 4426864 * 2
def baseEnd_4426864 : Nat := 252567669342808123104581

theorem tailTrace_4426864 : CollatzResearch.WordTrace tailWord_4426864 prefixEnd_4426864 252567669342808123104581 := by
  unfold tailWord_4426864
  simp only [CollatzResearch.WordTrace]
  refine ⟨80730497317117625512119823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107640663089490167349493097 80730497317117625512119823)
  ·
    refine ⟨121095745975676438268179735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80730497317117625512119823 121095745975676438268179735)
    ·
      refine ⟨181643618963514657402269603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121095745975676438268179735 181643618963514657402269603)
      ·
        refine ⟨272465428445271986103404405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181643618963514657402269603 272465428445271986103404405)
        ·
          refine ⟨25543633916744248697194163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 272465428445271986103404405 25543633916744248697194163)
          ·
            refine ⟨38315450875116373045791245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25543633916744248697194163 38315450875116373045791245)
            ·
              refine ⟨14368294078168639892171717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38315450875116373045791245 14368294078168639892171717)
              ·
                refine ⟨2694055139656619979782197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14368294078168639892171717 2694055139656619979782197)
                ·
                  refine ⟨252567669342808123104581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2694055139656619979782197 252567669342808123104581)
                  ·
                    rfl

theorem cell23_4426864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 4, 5].length) (baseStart_4426864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4426864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4426864 prefixEnd_4426864 := by exact prefixLift 4426864
  have htrace : WordTrace (prefixWord ++ tailWord_4426864) baseStart_4426864 baseEnd_4426864 := by
    simpa [prefixWord, tailWord_4426864, baseEnd_4426864] using wordTrace_append hprefix tailTrace_4426864
  have hstable : (prefixWord ++ tailWord_4426864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4426864).length < 2 ^ (prefixWord ++ tailWord_4426864).sum := by decide
  have hdescent : baseEnd_4426864 < baseStart_4426864 := by decide
  rcases family_descends (prefixWord ++ tailWord_4426864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4426877 : List Nat := [1, 4, 1, 1, 3, 1, 2, 2, 1, 7]
def baseStart_4426877 : Nat := 118140960795 + 4426877 * 2 ^ 59
def prefixEnd_4426877 : Nat := 4983230072969 + 3 ^ 40 * 4426877 * 2
def baseEnd_4426877 : Nat := 757705233111260519026223

theorem tailTrace_4426877 : CollatzResearch.WordTrace tailWord_4426877 prefixEnd_4426877 757705233111260519026223 := by
  unfold tailWord_4426877
  simp only [CollatzResearch.WordTrace]
  refine ⟨161461468783188154244462885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107640979188792102829641923 161461468783188154244462885)
  ·
    refine ⟨30274025396847778920836791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 161461468783188154244462885 30274025396847778920836791)
    ·
      refine ⟨45411038095271668381255187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30274025396847778920836791 45411038095271668381255187)
      ·
        refine ⟨68116557142907502571882781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45411038095271668381255187 68116557142907502571882781)
        ·
          refine ⟨25543708928590313464456043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68116557142907502571882781 25543708928590313464456043)
          ·
            refine ⟨38315563392885470196684065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25543708928590313464456043 38315563392885470196684065)
            ·
              refine ⟨28736672544664102647513049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38315563392885470196684065 28736672544664102647513049)
              ·
                refine ⟨21552504408498076985634787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28736672544664102647513049 21552504408498076985634787)
                ·
                  refine ⟨32328756612747115478452181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21552504408498076985634787 32328756612747115478452181)
                  ·
                    refine ⟨757705233111260519026223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32328756612747115478452181 757705233111260519026223)
                    ·
                      rfl

theorem cell23_4426877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 2, 1, 7].length) (baseStart_4426877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4426877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4426877 prefixEnd_4426877 := by exact prefixLift 4426877
  have htrace : WordTrace (prefixWord ++ tailWord_4426877) baseStart_4426877 baseEnd_4426877 := by
    simpa [prefixWord, tailWord_4426877, baseEnd_4426877] using wordTrace_append hprefix tailTrace_4426877
  have hstable : (prefixWord ++ tailWord_4426877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4426877).length < 2 ^ (prefixWord ++ tailWord_4426877).sum := by decide
  have hdescent : baseEnd_4426877 < baseStart_4426877 := by decide
  rcases family_descends (prefixWord ++ tailWord_4426877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4426894 : List Nat := [4, 1, 1, 3, 2, 2, 1, 1, 1, 7]
def baseStart_4426894 : Nat := 118140960795 + 4426894 * 2 ^ 59
def prefixEnd_4426894 : Nat := 4983230072969 + 3 ^ 40 * 4426894 * 2
def baseEnd_4426894 : Nat := 757708142834969330188697

theorem tailTrace_4426894 : CollatzResearch.WordTrace tailWord_4426894 prefixEnd_4426894 757708142834969330188697 := by
  unfold tailWord_4426894
  simp only [CollatzResearch.WordTrace]
  refine ⟨20182761103015820768478967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107641392549417710765221157 20182761103015820768478967)
  ·
    refine ⟨30274141654523731152718451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20182761103015820768478967 30274141654523731152718451)
    ·
      refine ⟨45411212481785596729077677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30274141654523731152718451 45411212481785596729077677)
      ·
        refine ⟨17029204680669598773404129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45411212481785596729077677 17029204680669598773404129)
        ·
          refine ⟨12771903510502199080053097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17029204680669598773404129 12771903510502199080053097)
          ·
            refine ⟨9578927632876649310039823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12771903510502199080053097 9578927632876649310039823)
            ·
              refine ⟨14368391449314973965059735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9578927632876649310039823 14368391449314973965059735)
              ·
                refine ⟨21552587173972460947589603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14368391449314973965059735 21552587173972460947589603)
                ·
                  refine ⟨32328880760958691421384405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21552587173972460947589603 32328880760958691421384405)
                  ·
                    refine ⟨757708142834969330188697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32328880760958691421384405 757708142834969330188697)
                    ·
                      rfl

theorem cell23_4426894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 1, 1, 7].length) (baseStart_4426894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4426894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4426894 prefixEnd_4426894 := by exact prefixLift 4426894
  have htrace : WordTrace (prefixWord ++ tailWord_4426894) baseStart_4426894 baseEnd_4426894 := by
    simpa [prefixWord, tailWord_4426894, baseEnd_4426894] using wordTrace_append hprefix tailTrace_4426894
  have hstable : (prefixWord ++ tailWord_4426894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4426894).length < 2 ^ (prefixWord ++ tailWord_4426894).sum := by decide
  have hdescent : baseEnd_4426894 < baseStart_4426894 := by decide
  rcases family_descends (prefixWord ++ tailWord_4426894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4426984 : List Nat := [2, 1, 4, 1, 2, 1, 2, 2, 3, 5]
def baseStart_4426984 : Nat := 118140960795 + 4426984 * 2 ^ 59
def prefixEnd_4426984 : Nat := 4983230072969 + 3 ^ 40 * 4426984 * 2
def baseEnd_4426984 : Nat := 757723547254604212813559

theorem tailTrace_4426984 : CollatzResearch.WordTrace tailWord_4426984 prefixEnd_4426984 757723547254604212813559 := by
  unfold tailWord_4426984
  simp only [CollatzResearch.WordTrace]
  refine ⟨80732685696900255759304003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107643580929200341012405337 80732685696900255759304003)
  ·
    refine ⟨121099028545350383638956005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80732685696900255759304003 121099028545350383638956005)
    ·
      refine ⟨22706067852253196932304251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 121099028545350383638956005 22706067852253196932304251)
      ·
        refine ⟨34059101778379795398456377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22706067852253196932304251 34059101778379795398456377)
        ·
          refine ⟨25544326333784846548842283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34059101778379795398456377 25544326333784846548842283)
          ·
            refine ⟨38316489500677269823263425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25544326333784846548842283 38316489500677269823263425)
            ·
              refine ⟨28737367125507952367447569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38316489500677269823263425 28737367125507952367447569)
              ·
                refine ⟨21553025344130964275585677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28737367125507952367447569 21553025344130964275585677)
                ·
                  refine ⟨8082384504049111603344629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21553025344130964275585677 8082384504049111603344629)
                  ·
                    refine ⟨757723547254604212813559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8082384504049111603344629 757723547254604212813559)
                    ·
                      rfl

theorem cell23_4426984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 2, 3, 5].length) (baseStart_4426984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4426984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4426984 prefixEnd_4426984 := by exact prefixLift 4426984
  have htrace : WordTrace (prefixWord ++ tailWord_4426984) baseStart_4426984 baseEnd_4426984 := by
    simpa [prefixWord, tailWord_4426984, baseEnd_4426984] using wordTrace_append hprefix tailTrace_4426984
  have hstable : (prefixWord ++ tailWord_4426984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4426984).length < 2 ^ (prefixWord ++ tailWord_4426984).sum := by decide
  have hdescent : baseEnd_4426984 < baseStart_4426984 := by decide
  rcases family_descends (prefixWord ++ tailWord_4426984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4427026 : List Nat := [3, 2, 4, 2, 2, 1, 2, 2, 1, 4]
def baseStart_4427026 : Nat := 118140960795 + 4427026 * 2 ^ 59
def prefixEnd_4427026 : Nat := 4983230072969 + 3 ^ 40 * 4427026 * 2
def baseEnd_4427026 : Nat := 757730735983767158038495

theorem tailTrace_4427026 : CollatzResearch.WordTrace tailWord_4427026 prefixEnd_4427026 757730735983767158038495 := by
  unfold tailWord_4427026
  simp only [CollatzResearch.WordTrace]
  refine ⟨40366725814912088172909233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107644602173098901794424621 40366725814912088172909233)
  ·
    refine ⟨30275044361184066129681925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40366725814912088172909233 30275044361184066129681925)
    ·
      refine ⟨5676570817722012399315361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30275044361184066129681925 5676570817722012399315361)
      ·
        refine ⟨4257428113291509299486521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5676570817722012399315361 4257428113291509299486521)
        ·
          refine ⟨3193071084968631974614891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4257428113291509299486521 3193071084968631974614891)
          ·
            refine ⟨4789606627452947961922337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3193071084968631974614891 4789606627452947961922337)
            ·
              refine ⟨3592204970589710971441753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4789606627452947961922337 3592204970589710971441753)
              ·
                refine ⟨2694153727942283228581315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3592204970589710971441753 2694153727942283228581315)
                ·
                  refine ⟨4041230591913424842871973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2694153727942283228581315 4041230591913424842871973)
                  ·
                    refine ⟨757730735983767158038495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4041230591913424842871973 757730735983767158038495)
                    ·
                      rfl

theorem cell23_4427026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_4427026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4427026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4427026 prefixEnd_4427026 := by exact prefixLift 4427026
  have htrace : WordTrace (prefixWord ++ tailWord_4427026) baseStart_4427026 baseEnd_4427026 := by
    simpa [prefixWord, tailWord_4427026, baseEnd_4427026] using wordTrace_append hprefix tailTrace_4427026
  have hstable : (prefixWord ++ tailWord_4427026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4427026).length < 2 ^ (prefixWord ++ tailWord_4427026).sum := by decide
  have hdescent : baseEnd_4427026 < baseStart_4427026 := by decide
  rcases family_descends (prefixWord ++ tailWord_4427026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4427032 : List Nat := [2, 1, 2, 3, 1, 5, 2, 2, 1, 1, 3]
def baseStart_4427032 : Nat := 118140960795 + 4427032 * 2 ^ 59
def prefixEnd_4427032 : Nat := 4983230072969 + 3 ^ 40 * 4427032 * 2
def baseEnd_4427032 : Nat := 2273195288835228450640457

theorem tailTrace_4427032 : CollatzResearch.WordTrace tailWord_4427032 prefixEnd_4427032 2273195288835228450640457 := by
  unfold tailWord_4427032
  simp only [CollatzResearch.WordTrace]
  refine ⟨80733561048813307858177675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107644748065084410477570233 80733561048813307858177675)
  ·
    refine ⟨121100341573219961787266513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80733561048813307858177675 121100341573219961787266513)
    ·
      refine ⟨90825256179914971340449885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121100341573219961787266513 90825256179914971340449885)
      ·
        refine ⟨34059471067468114252668707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90825256179914971340449885 34059471067468114252668707)
        ·
          refine ⟨51089206601202171379003061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34059471067468114252668707 51089206601202171379003061)
          ·
            refine ⟨4789613118862703566781537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 51089206601202171379003061 4789613118862703566781537)
            ·
              refine ⟨3592209839147027675086153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4789613118862703566781537 3592209839147027675086153)
              ·
                refine ⟨2694157379360270756314615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3592209839147027675086153 2694157379360270756314615)
                ·
                  refine ⟨4041236069040406134471923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2694157379360270756314615 4041236069040406134471923)
                  ·
                    refine ⟨6061854103560609201707885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4041236069040406134471923 6061854103560609201707885)
                    ·
                      refine ⟨2273195288835228450640457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6061854103560609201707885 2273195288835228450640457)
                      ·
                        rfl

theorem cell23_4427032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 2, 2, 1, 1, 3].length) (baseStart_4427032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4427032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4427032 prefixEnd_4427032 := by exact prefixLift 4427032
  have htrace : WordTrace (prefixWord ++ tailWord_4427032) baseStart_4427032 baseEnd_4427032 := by
    simpa [prefixWord, tailWord_4427032, baseEnd_4427032] using wordTrace_append hprefix tailTrace_4427032
  have hstable : (prefixWord ++ tailWord_4427032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4427032).length < 2 ^ (prefixWord ++ tailWord_4427032).sum := by decide
  have hdescent : baseEnd_4427032 < baseStart_4427032 := by decide
  rcases family_descends (prefixWord ++ tailWord_4427032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4427048 : List Nat := [2, 1, 5, 1, 2, 1, 2, 3, 2, 4]
def baseStart_4427048 : Nat := 118140960795 + 4427048 * 2 ^ 59
def prefixEnd_4427048 : Nat := 4983230072969 + 3 ^ 40 * 4427048 * 2
def baseEnd_4427048 : Nat := 757734501508566796013461

theorem tailTrace_4427048 : CollatzResearch.WordTrace tailWord_4427048 prefixEnd_4427048 757734501508566796013461 := by
  unfold tailWord_4427048
  simp only [CollatzResearch.WordTrace]
  refine ⟨80733852832784325224468899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107645137110379100299291865 80733852832784325224468899)
  ·
    refine ⟨121100779249176487836703349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80733852832784325224468899 121100779249176487836703349)
    ·
      refine ⟨11353198054610295734690939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 121100779249176487836703349 11353198054610295734690939)
      ·
        refine ⟨17029797081915443602036409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11353198054610295734690939 17029797081915443602036409)
        ·
          refine ⟨12772347811436582701527307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17029797081915443602036409 12772347811436582701527307)
          ·
            refine ⟨19158521717154874052290961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12772347811436582701527307 19158521717154874052290961)
            ·
              refine ⟨14368891287866155539218221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19158521717154874052290961 14368891287866155539218221)
              ·
                refine ⟨5388334232949808327206833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14368891287866155539218221 5388334232949808327206833)
                ·
                  refine ⟨4041250674712356245405125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5388334232949808327206833 4041250674712356245405125)
                  ·
                    refine ⟨757734501508566796013461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4041250674712356245405125 757734501508566796013461)
                    ·
                      rfl

theorem cell23_4427048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_4427048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4427048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4427048 prefixEnd_4427048 := by exact prefixLift 4427048
  have htrace : WordTrace (prefixWord ++ tailWord_4427048) baseStart_4427048 baseEnd_4427048 := by
    simpa [prefixWord, tailWord_4427048, baseEnd_4427048] using wordTrace_append hprefix tailTrace_4427048
  have hstable : (prefixWord ++ tailWord_4427048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4427048).length < 2 ^ (prefixWord ++ tailWord_4427048).sum := by decide
  have hdescent : baseEnd_4427048 < baseStart_4427048 := by decide
  rcases family_descends (prefixWord ++ tailWord_4427048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4427061 : List Nat := [1, 3, 3, 1, 2, 3, 3, 7]
def baseStart_4427061 : Nat := 118140960795 + 4427061 * 2 ^ 59
def prefixEnd_4427061 : Nat := 4983230072969 + 3 ^ 40 * 4427061 * 2
def baseEnd_4427061 : Nat := 84192969621266993969549

theorem tailTrace_4427061 : CollatzResearch.WordTrace tailWord_4427061 prefixEnd_4427061 84192969621266993969549 := by
  unfold tailWord_4427061
  simp only [CollatzResearch.WordTrace]
  refine ⟨161468179814521553669161037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107645453209681035779440691 161468179814521553669161037)
  ·
    refine ⟨60550567430445582625935389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 161468179814521553669161037 60550567430445582625935389)
    ·
      refine ⟨22706462786417093484725771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60550567430445582625935389 22706462786417093484725771)
      ·
        refine ⟨34059694179625640227088657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22706462786417093484725771 34059694179625640227088657)
        ·
          refine ⟨25544770634719230170316493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34059694179625640227088657 25544770634719230170316493)
          ·
            refine ⟨9579288988019711313868685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25544770634719230170316493 9579288988019711313868685)
            ·
              refine ⟨3592233370507391742700757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9579288988019711313868685 3592233370507391742700757)
              ·
                refine ⟨84192969621266993969549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3592233370507391742700757 84192969621266993969549)
                ·
                  rfl

theorem cell23_4427061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 3, 7].length) (baseStart_4427061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4427061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4427061 prefixEnd_4427061 := by exact prefixLift 4427061
  have htrace : WordTrace (prefixWord ++ tailWord_4427061) baseStart_4427061 baseEnd_4427061 := by
    simpa [prefixWord, tailWord_4427061, baseEnd_4427061] using wordTrace_append hprefix tailTrace_4427061
  have hstable : (prefixWord ++ tailWord_4427061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4427061).length < 2 ^ (prefixWord ++ tailWord_4427061).sum := by decide
  have hdescent : baseEnd_4427061 < baseStart_4427061 := by decide
  rcases family_descends (prefixWord ++ tailWord_4427061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4427071 : List Nat := [1, 1, 2, 2, 4, 2, 2, 2, 1, 3, 3]
def baseStart_4427071 : Nat := 118140960795 + 4427071 * 2 ^ 59
def prefixEnd_4427071 : Nat := 4983230072969 + 3 ^ 40 * 4427071 * 2
def baseEnd_4427071 : Nat := 2273215314580753798052777

theorem tailTrace_4427071 : CollatzResearch.WordTrace tailWord_4427071 prefixEnd_4427071 2273215314580753798052777 := by
  unfold tailWord_4427071
  simp only [CollatzResearch.WordTrace]
  refine ⟨161468544544485325377025067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107645696362990216918016711 161468544544485325377025067)
  ·
    refine ⟨242202816816727988065537601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161468544544485325377025067 242202816816727988065537601)
    ·
      refine ⟨181652112612545991049153201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 242202816816727988065537601 181652112612545991049153201)
      ·
        refine ⟨136239084459409493286864901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 181652112612545991049153201 136239084459409493286864901)
        ·
          refine ⟨25544828336139279991287169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 136239084459409493286864901 25544828336139279991287169)
          ·
            refine ⟨19158621252104459993465377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25544828336139279991287169 19158621252104459993465377)
            ·
              refine ⟨14368965939078344995099033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19158621252104459993465377 14368965939078344995099033)
              ·
                refine ⟨10776724454308758746324275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14368965939078344995099033 10776724454308758746324275)
                ·
                  refine ⟨16165086681463138119486413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10776724454308758746324275 16165086681463138119486413)
                  ·
                    refine ⟨6061907505548676794807405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16165086681463138119486413 6061907505548676794807405)
                    ·
                      refine ⟨2273215314580753798052777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6061907505548676794807405 2273215314580753798052777)
                      ·
                        rfl

theorem cell23_4427071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 2, 1, 3, 3].length) (baseStart_4427071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4427071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4427071 prefixEnd_4427071 := by exact prefixLift 4427071
  have htrace : WordTrace (prefixWord ++ tailWord_4427071) baseStart_4427071 baseEnd_4427071 := by
    simpa [prefixWord, tailWord_4427071, baseEnd_4427071] using wordTrace_append hprefix tailTrace_4427071
  have hstable : (prefixWord ++ tailWord_4427071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4427071).length < 2 ^ (prefixWord ++ tailWord_4427071).sum := by decide
  have hdescent : baseEnd_4427071 < baseStart_4427071 := by decide
  rcases family_descends (prefixWord ++ tailWord_4427071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4427166 : List Nat := [4, 3, 1, 2, 3, 1, 1, 2, 1, 3, 2]
def baseStart_4427166 : Nat := 118140960795 + 4427166 * 2 ^ 59
def prefixEnd_4427166 : Nat := 4983230072969 + 3 ^ 40 * 4427166 * 2
def baseEnd_4427166 : Nat := 2273264095242930926364841

theorem tailTrace_4427166 : CollatzResearch.WordTrace tailWord_4427166 prefixEnd_4427166 2273264095242930926364841 := by
  unfold tailWord_4427166
  simp only [CollatzResearch.WordTrace]
  refine ⟨20184001184892644575216669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107648006319427437734488901 20184001184892644575216669)
  ·
    refine ⟨7569000444334741715706251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20184001184892644575216669 7569000444334741715706251)
    ·
      refine ⟨11353500666502112573559377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7569000444334741715706251 11353500666502112573559377)
      ·
        refine ⟨8515125499876584430169533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11353500666502112573559377 8515125499876584430169533)
        ·
          refine ⟨3193172062453719161313575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8515125499876584430169533 3193172062453719161313575)
          ·
            refine ⟨4789758093680578741970363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3193172062453719161313575 4789758093680578741970363)
            ·
              refine ⟨7184637140520868112955545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4789758093680578741970363 7184637140520868112955545)
              ·
                refine ⟨5388477855390651084716659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7184637140520868112955545 5388477855390651084716659)
                ·
                  refine ⟨8082716783085976627074989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5388477855390651084716659 8082716783085976627074989)
                  ·
                    refine ⟨3031018793657241235153121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8082716783085976627074989 3031018793657241235153121)
                    ·
                      refine ⟨2273264095242930926364841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3031018793657241235153121 2273264095242930926364841)
                      ·
                        rfl

theorem cell23_4427166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_4427166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4427166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4427166 prefixEnd_4427166 := by exact prefixLift 4427166
  have htrace : WordTrace (prefixWord ++ tailWord_4427166) baseStart_4427166 baseEnd_4427166 := by
    simpa [prefixWord, tailWord_4427166, baseEnd_4427166] using wordTrace_append hprefix tailTrace_4427166
  have hstable : (prefixWord ++ tailWord_4427166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4427166).length < 2 ^ (prefixWord ++ tailWord_4427166).sum := by decide
  have hdescent : baseEnd_4427166 < baseStart_4427166 := by decide
  rcases family_descends (prefixWord ++ tailWord_4427166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4427235 : List Nat := [1, 1, 1, 6, 2, 3, 1, 1, 2, 1, 4]
def baseStart_4427235 : Nat := 118140960795 + 4427235 * 2 ^ 59
def prefixEnd_4427235 : Nat := 4983230072969 + 3 ^ 40 * 4427235 * 2
def baseEnd_4427235 : Nat := 2273299525408091156402023

theorem tailTrace_4427235 : CollatzResearch.WordTrace tailWord_4427235 prefixEnd_4427235 2273299525408091156402023 := by
  unfold tailWord_4427235
  simp only [CollatzResearch.WordTrace]
  refine ⟨161474526115891181385995159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107649684077260787590663439 161474526115891181385995159)
  ·
    refine ⟨242211789173836772078992739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161474526115891181385995159 242211789173836772078992739)
    ·
      refine ⟨363317683760755158118489109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242211789173836772078992739 363317683760755158118489109)
      ·
        refine ⟨17030516426285398036804177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 363317683760755158118489109 17030516426285398036804177)
        ·
          refine ⟨12772887319714048527603133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17030516426285398036804177 12772887319714048527603133)
          ·
            refine ⟨4789832744892768197851175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12772887319714048527603133 4789832744892768197851175)
            ·
              refine ⟨7184749117339152296776763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4789832744892768197851175 7184749117339152296776763)
              ·
                refine ⟨10777123676008728445165145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7184749117339152296776763 10777123676008728445165145)
                ·
                  refine ⟨8082842757006546333873859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10777123676008728445165145 8082842757006546333873859)
                  ·
                    refine ⟨12124264135509819500810789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8082842757006546333873859 12124264135509819500810789)
                    ·
                      refine ⟨2273299525408091156402023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12124264135509819500810789 2273299525408091156402023)
                      ·
                        rfl

theorem cell23_4427235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_4427235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4427235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4427235 prefixEnd_4427235 := by exact prefixLift 4427235
  have htrace : WordTrace (prefixWord ++ tailWord_4427235) baseStart_4427235 baseEnd_4427235 := by
    simpa [prefixWord, tailWord_4427235, baseEnd_4427235] using wordTrace_append hprefix tailTrace_4427235
  have hstable : (prefixWord ++ tailWord_4427235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4427235).length < 2 ^ (prefixWord ++ tailWord_4427235).sum := by decide
  have hdescent : baseEnd_4427235 < baseStart_4427235 := by decide
  rcases family_descends (prefixWord ++ tailWord_4427235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4427261 : List Nat := [1, 4, 1, 1, 1, 4, 1, 1, 1, 2, 6]
def baseStart_4427261 : Nat := 118140960795 + 4427261 * 2 ^ 59
def prefixEnd_4427261 : Nat := 4983230072969 + 3 ^ 40 * 4427261 * 2
def baseEnd_4427261 : Nat := 2273312875905108054676903

theorem tailTrace_4427261 : CollatzResearch.WordTrace tailWord_4427261 prefixEnd_4427261 2273312875905108054676903 := by
  unfold tailWord_4427261
  simp only [CollatzResearch.WordTrace]
  refine ⟨161475474413796987826441637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107650316275864658550961091 161475474413796987826441637)
  ·
    refine ⟨30276651452586935217457807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 161475474413796987826441637 30276651452586935217457807)
    ·
      refine ⟨45414977178880402826186711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30276651452586935217457807 45414977178880402826186711)
      ·
        refine ⟨68122465768320604239280067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45414977178880402826186711 68122465768320604239280067)
        ·
          refine ⟨102183698652480906358920101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68122465768320604239280067 102183698652480906358920101)
          ·
            refine ⟨19159443497340169942297519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 102183698652480906358920101 19159443497340169942297519)
            ·
              refine ⟨28739165246010254913446279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19159443497340169942297519 28739165246010254913446279)
              ·
                refine ⟨43108747869015382370169419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28739165246010254913446279 43108747869015382370169419)
                ·
                  refine ⟨64663121803523073555254129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43108747869015382370169419 64663121803523073555254129)
                  ·
                    refine ⟨48497341352642305166440597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 64663121803523073555254129 48497341352642305166440597)
                    ·
                      refine ⟨2273312875905108054676903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48497341352642305166440597 2273312875905108054676903)
                      ·
                        rfl

theorem cell23_4427261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 2, 6].length) (baseStart_4427261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4427261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4427261 prefixEnd_4427261 := by exact prefixLift 4427261
  have htrace : WordTrace (prefixWord ++ tailWord_4427261) baseStart_4427261 baseEnd_4427261 := by
    simpa [prefixWord, tailWord_4427261, baseEnd_4427261] using wordTrace_append hprefix tailTrace_4427261
  have hstable : (prefixWord ++ tailWord_4427261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4427261).length < 2 ^ (prefixWord ++ tailWord_4427261).sum := by decide
  have hdescent : baseEnd_4427261 < baseStart_4427261 := by decide
  rcases family_descends (prefixWord ++ tailWord_4427261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4427275 : List Nat := [1, 1, 1, 1, 8, 1, 3, 1, 6]
def baseStart_4427275 : Nat := 118140960795 + 4427275 * 2 ^ 59
def prefixEnd_4427275 : Nat := 4983230072969 + 3 ^ 40 * 4427275 * 2
def baseEnd_4427275 : Nat := 252591118292696777766871

theorem tailTrace_4427275 : CollatzResearch.WordTrace tailWord_4427275 prefixEnd_4427275 252591118292696777766871 := by
  unfold tailWord_4427275
  simp only [CollatzResearch.WordTrace]
  refine ⟨161475985035746268217451279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107650656690497512144967519 161475985035746268217451279)
  ·
    refine ⟨242213977553619402326176919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161475985035746268217451279 242213977553619402326176919)
    ·
      refine ⟨363320966330429103489265379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242213977553619402326176919 363320966330429103489265379)
      ·
        refine ⟨544981449495643655233898069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 363320966330429103489265379 544981449495643655233898069)
        ·
          refine ⟨6386501361277074084772243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 544981449495643655233898069 6386501361277074084772243)
          ·
            refine ⟨9579752041915611127158365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6386501361277074084772243 9579752041915611127158365)
            ·
              refine ⟨3592407015718354172684387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9579752041915611127158365 3592407015718354172684387)
              ·
                refine ⟨5388610523577531259026581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3592407015718354172684387 5388610523577531259026581)
                ·
                  refine ⟨252591118292696777766871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5388610523577531259026581 252591118292696777766871)
                  ·
                    rfl

theorem cell23_4427275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 3, 1, 6].length) (baseStart_4427275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4427275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4427275 prefixEnd_4427275 := by exact prefixLift 4427275
  have htrace : WordTrace (prefixWord ++ tailWord_4427275) baseStart_4427275 baseEnd_4427275 := by
    simpa [prefixWord, tailWord_4427275, baseEnd_4427275] using wordTrace_append hprefix tailTrace_4427275
  have hstable : (prefixWord ++ tailWord_4427275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4427275).length < 2 ^ (prefixWord ++ tailWord_4427275).sum := by decide
  have hdescent : baseEnd_4427275 < baseStart_4427275 := by decide
  rcases family_descends (prefixWord ++ tailWord_4427275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4427285 : List Nat := [1, 3, 2, 1, 3, 2, 2, 2, 3, 1, 3]
def baseStart_4427285 : Nat := 118140960795 + 4427285 * 2 ^ 59
def prefixEnd_4427285 : Nat := 4983230072969 + 3 ^ 40 * 4427285 * 2
def baseEnd_4427285 : Nat := 2273325199440815960776793

theorem tailTrace_4427285 : CollatzResearch.WordTrace tailWord_4427285 prefixEnd_4427285 2273325199440815960776793 := by
  unfold tailWord_4427285
  simp only [CollatzResearch.WordTrace]
  refine ⟨161476349765710039925315309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107650899843806693283543539 161476349765710039925315309)
  ·
    refine ⟨60553631162141264971993241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 161476349765710039925315309 60553631162141264971993241)
    ·
      refine ⟨45415223371605948728994931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60553631162141264971993241 45415223371605948728994931)
      ·
        refine ⟨68122835057408923093492397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45415223371605948728994931 68122835057408923093492397)
        ·
          refine ⟨25546063146528346160059649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68122835057408923093492397 25546063146528346160059649)
          ·
            refine ⟨19159547359896259620044737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25546063146528346160059649 19159547359896259620044737)
            ·
              refine ⟨14369660519922194715033553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19159547359896259620044737 14369660519922194715033553)
              ·
                refine ⟨10777245389941646036275165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14369660519922194715033553 10777245389941646036275165)
                ·
                  refine ⟨4041467021228117263603187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10777245389941646036275165 4041467021228117263603187)
                  ·
                    refine ⟨6062200531842175895404781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4041467021228117263603187 6062200531842175895404781)
                    ·
                      refine ⟨2273325199440815960776793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6062200531842175895404781 2273325199440815960776793)
                      ·
                        rfl

theorem cell23_4427285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 2, 3, 1, 3].length) (baseStart_4427285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4427285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4427285 prefixEnd_4427285 := by exact prefixLift 4427285
  have htrace : WordTrace (prefixWord ++ tailWord_4427285) baseStart_4427285 baseEnd_4427285 := by
    simpa [prefixWord, tailWord_4427285, baseEnd_4427285] using wordTrace_append hprefix tailTrace_4427285
  have hstable : (prefixWord ++ tailWord_4427285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4427285).length < 2 ^ (prefixWord ++ tailWord_4427285).sum := by decide
  have hdescent : baseEnd_4427285 < baseStart_4427285 := by decide
  rcases family_descends (prefixWord ++ tailWord_4427285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4427301 : List Nat := [1, 3, 1, 2, 2, 1, 1, 3, 3, 6]
def baseStart_4427301 : Nat := 118140960795 + 4427301 * 2 ^ 59
def prefixEnd_4427301 : Nat := 4983230072969 + 3 ^ 40 * 4427301 * 2
def baseEnd_4427301 : Nat := 757777805043762632725573

theorem tailTrace_4427301 : CollatzResearch.WordTrace tailWord_4427301 prefixEnd_4427301 757777805043762632725573 := by
  unfold tailWord_4427301
  simp only [CollatzResearch.WordTrace]
  refine ⟨161476933333652074657897757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107651288889101383105265171 161476933333652074657897757)
  ·
    refine ⟨60553850000119527996711659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 161476933333652074657897757 60553850000119527996711659)
    ·
      refine ⟨90830775000179291995067489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60553850000119527996711659 90830775000179291995067489)
      ·
        refine ⟨68123081250134468996300617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90830775000179291995067489 68123081250134468996300617)
        ·
          refine ⟨51092310937600851747225463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68123081250134468996300617 51092310937600851747225463)
          ·
            refine ⟨76638466406401277620838195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51092310937600851747225463 76638466406401277620838195)
            ·
              refine ⟨114957699609601916431257293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76638466406401277620838195 114957699609601916431257293)
              ·
                refine ⟨43109137353600718661721485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 114957699609601916431257293 43109137353600718661721485)
                ·
                  refine ⟨16165926507600269498145557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43109137353600718661721485 16165926507600269498145557)
                  ·
                    refine ⟨757777805043762632725573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16165926507600269498145557 757777805043762632725573)
                    ·
                      rfl

theorem cell23_4427301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 3, 6].length) (baseStart_4427301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4427301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4427301 prefixEnd_4427301 := by exact prefixLift 4427301
  have htrace : WordTrace (prefixWord ++ tailWord_4427301) baseStart_4427301 baseEnd_4427301 := by
    simpa [prefixWord, tailWord_4427301, baseEnd_4427301] using wordTrace_append hprefix tailTrace_4427301
  have hstable : (prefixWord ++ tailWord_4427301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4427301).length < 2 ^ (prefixWord ++ tailWord_4427301).sum := by decide
  have hdescent : baseEnd_4427301 < baseStart_4427301 := by decide
  rcases family_descends (prefixWord ++ tailWord_4427301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4427319 : List Nat := [1, 1, 3, 1, 2, 5, 3, 2, 1, 1, 3]
def baseStart_4427319 : Nat := 118140960795 + 4427319 * 2 ^ 59
def prefixEnd_4427319 : Nat := 4983230072969 + 3 ^ 40 * 4427319 * 2
def baseEnd_4427319 : Nat := 2273342657783068827751637

theorem tailTrace_4427319 : CollatzResearch.WordTrace tailWord_4427319 prefixEnd_4427319 2273342657783068827751637 := by
  unfold tailWord_4427319
  simp only [CollatzResearch.WordTrace]
  refine ⟨161477589847586863732053011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107651726565057909154702007 161477589847586863732053011)
  ·
    refine ⟨242216384771380295598079517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161477589847586863732053011 242216384771380295598079517)
    ·
      refine ⟨90831144289267610849279819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 242216384771380295598079517 90831144289267610849279819)
      ·
        refine ⟨136246716433901416273919729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90831144289267610849279819 136246716433901416273919729)
        ·
          refine ⟨102185037325426062205439797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136246716433901416273919729 102185037325426062205439797)
          ·
            refine ⟨9579847249258693331759981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 102185037325426062205439797 9579847249258693331759981)
            ·
              refine ⟨3592442718472009999409993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9579847249258693331759981 3592442718472009999409993)
              ·
                refine ⟨2694332038854007499557495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3592442718472009999409993 2694332038854007499557495)
                ·
                  refine ⟨4041498058281011249336243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2694332038854007499557495 4041498058281011249336243)
                  ·
                    refine ⟨6062247087421516874004365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4041498058281011249336243 6062247087421516874004365)
                    ·
                      refine ⟨2273342657783068827751637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6062247087421516874004365 2273342657783068827751637)
                      ·
                        rfl

theorem cell23_4427319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 3, 2, 1, 1, 3].length) (baseStart_4427319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4427319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4427319 prefixEnd_4427319 := by exact prefixLift 4427319
  have htrace : WordTrace (prefixWord ++ tailWord_4427319) baseStart_4427319 baseEnd_4427319 := by
    simpa [prefixWord, tailWord_4427319, baseEnd_4427319] using wordTrace_append hprefix tailTrace_4427319
  have hstable : (prefixWord ++ tailWord_4427319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4427319).length < 2 ^ (prefixWord ++ tailWord_4427319).sum := by decide
  have hdescent : baseEnd_4427319 < baseStart_4427319 := by decide
  rcases family_descends (prefixWord ++ tailWord_4427319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4427328 : List Nat := [2, 1, 1, 2, 2, 2, 1, 4, 3, 2, 3]
def baseStart_4427328 : Nat := 118140960795 + 4427328 * 2 ^ 59
def prefixEnd_4427328 : Nat := 4983230072969 + 3 ^ 40 * 4427328 * 2
def baseEnd_4427328 : Nat := 2273347279108959292539095

theorem tailTrace_4427328 : CollatzResearch.WordTrace tailWord_4427328 prefixEnd_4427328 2273347279108959292539095 := by
  unfold tailWord_4427328
  simp only [CollatzResearch.WordTrace]
  refine ⟨80738959052277129134565319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107651945403036172179420425 80738959052277129134565319)
  ·
    refine ⟨121108438578415693701847979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80738959052277129134565319 121108438578415693701847979)
    ·
      refine ⟨181662657867623540552771969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121108438578415693701847979 181662657867623540552771969)
      ·
        refine ⟨136246993400717655414578977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 181662657867623540552771969 136246993400717655414578977)
        ·
          refine ⟨102185245050538241560934233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136246993400717655414578977 102185245050538241560934233)
          ·
            refine ⟨76638933787903681170700675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102185245050538241560934233 76638933787903681170700675)
            ·
              refine ⟨114958400681855521756051013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76638933787903681170700675 114958400681855521756051013)
              ·
                refine ⟨21554700127847910329259565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 114958400681855521756051013 21554700127847910329259565)
                ·
                  refine ⟨8083012547942966373472337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21554700127847910329259565 8083012547942966373472337)
                  ·
                    refine ⟨6062259410957224780104253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8083012547942966373472337 6062259410957224780104253)
                    ·
                      refine ⟨2273347279108959292539095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6062259410957224780104253 2273347279108959292539095)
                      ·
                        rfl

theorem cell23_4427328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 4, 3, 2, 3].length) (baseStart_4427328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4427328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4427328 prefixEnd_4427328 := by exact prefixLift 4427328
  have htrace : WordTrace (prefixWord ++ tailWord_4427328) baseStart_4427328 baseEnd_4427328 := by
    simpa [prefixWord, tailWord_4427328, baseEnd_4427328] using wordTrace_append hprefix tailTrace_4427328
  have hstable : (prefixWord ++ tailWord_4427328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4427328).length < 2 ^ (prefixWord ++ tailWord_4427328).sum := by decide
  have hdescent : baseEnd_4427328 < baseStart_4427328 := by decide
  rcases family_descends (prefixWord ++ tailWord_4427328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4427338 : List Nat := [3, 1, 2, 1, 1, 3, 2, 3, 1, 2, 4]
def baseStart_4427338 : Nat := 118140960795 + 4427338 * 2 ^ 59
def prefixEnd_4427338 : Nat := 4983230072969 + 3 ^ 40 * 4427338 * 2
def baseEnd_4427338 : Nat := 2273352413915504253414049

theorem tailTrace_4427338 : CollatzResearch.WordTrace tailWord_4427338 prefixEnd_4427338 2273352413915504253414049 := by
  unfold tailWord_4427338
  simp only [CollatzResearch.WordTrace]
  refine ⟨40369570708629507494248667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107652188556345353317996445 40369570708629507494248667)
  ·
    refine ⟨60554356062944261241373001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40369570708629507494248667 60554356062944261241373001)
    ·
      refine ⟨45415767047208195931029751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60554356062944261241373001 45415767047208195931029751)
      ·
        refine ⟨68123650570812293896544627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45415767047208195931029751 68123650570812293896544627)
        ·
          refine ⟨102185475856218440844816941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68123650570812293896544627 102185475856218440844816941)
          ·
            refine ⟨38319553446081915316806353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102185475856218440844816941 38319553446081915316806353)
            ·
              refine ⟨28739665084561436487604765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38319553446081915316806353 28739665084561436487604765)
              ·
                refine ⟨10777374406710538682851787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28739665084561436487604765 10777374406710538682851787)
                ·
                  refine ⟨16166061610065808024277681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10777374406710538682851787 16166061610065808024277681)
                  ·
                    refine ⟨12124546207549356018208261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16166061610065808024277681 12124546207549356018208261)
                    ·
                      refine ⟨2273352413915504253414049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12124546207549356018208261 2273352413915504253414049)
                      ·
                        rfl

theorem cell23_4427338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 3, 1, 2, 4].length) (baseStart_4427338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4427338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4427338 prefixEnd_4427338 := by exact prefixLift 4427338
  have htrace : WordTrace (prefixWord ++ tailWord_4427338) baseStart_4427338 baseEnd_4427338 := by
    simpa [prefixWord, tailWord_4427338, baseEnd_4427338] using wordTrace_append hprefix tailTrace_4427338
  have hstable : (prefixWord ++ tailWord_4427338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4427338).length < 2 ^ (prefixWord ++ tailWord_4427338).sum := by decide
  have hdescent : baseEnd_4427338 < baseStart_4427338 := by decide
  rcases family_descends (prefixWord ++ tailWord_4427338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4427371 : List Nat := [1, 1, 1, 1, 2, 2, 1, 2, 3, 4, 5]
def baseStart_4427371 : Nat := 118140960795 + 4427371 * 2 ^ 59
def prefixEnd_4427371 : Nat := 4983230072969 + 3 ^ 40 * 4427371 * 2
def baseEnd_4427371 : Nat := 2273369358777102624301397

theorem tailTrace_4427371 : CollatzResearch.WordTrace tailWord_4427371 prefixEnd_4427371 2273369358777102624301397 := by
  unfold tailWord_4427371
  simp only [CollatzResearch.WordTrace]
  refine ⟨161479486443398476612945967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107652990962265651075297311 161479486443398476612945967)
  ·
    refine ⟨242219229665097714919418951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161479486443398476612945967 242219229665097714919418951)
    ·
      refine ⟨363328844497646572379128427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242219229665097714919418951 363328844497646572379128427)
      ·
        refine ⟨544993266746469858568692641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 363328844497646572379128427 544993266746469858568692641)
        ·
          refine ⟨408744950059852393926519481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 544993266746469858568692641 408744950059852393926519481)
          ·
            refine ⟨306558712544889295444889611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 408744950059852393926519481 306558712544889295444889611)
            ·
              refine ⟨459838068817333943167334417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 306558712544889295444889611 459838068817333943167334417)
              ·
                refine ⟨344878551613000457375500813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 459838068817333943167334417 344878551613000457375500813)
                ·
                  refine ⟨129329456854875171515812805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 344878551613000457375500813 129329456854875171515812805)
                  ·
                    refine ⟨24249273160289094659214901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 129329456854875171515812805 24249273160289094659214901)
                    ·
                      refine ⟨2273369358777102624301397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24249273160289094659214901 2273369358777102624301397)
                      ·
                        rfl

theorem cell23_4427371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 4, 5].length) (baseStart_4427371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4427371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4427371 prefixEnd_4427371 := by exact prefixLift 4427371
  have htrace : WordTrace (prefixWord ++ tailWord_4427371) baseStart_4427371 baseEnd_4427371 := by
    simpa [prefixWord, tailWord_4427371, baseEnd_4427371] using wordTrace_append hprefix tailTrace_4427371
  have hstable : (prefixWord ++ tailWord_4427371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4427371).length < 2 ^ (prefixWord ++ tailWord_4427371).sum := by decide
  have hdescent : baseEnd_4427371 < baseStart_4427371 := by decide
  rcases family_descends (prefixWord ++ tailWord_4427371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4427376 : List Nat := [2, 1, 1, 1, 6, 1, 4, 2, 1, 2, 2]
def baseStart_4427376 : Nat := 118140960795 + 4427376 * 2 ^ 59
def prefixEnd_4427376 : Nat := 4983230072969 + 3 ^ 40 * 4427376 * 2
def baseEnd_4427376 : Nat := 2273371926180375104738875

theorem tailTrace_4427376 : CollatzResearch.WordTrace tailWord_4427376 prefixEnd_4427376 2273371926180375104738875 := by
  unfold tailWord_4427376
  simp only [CollatzResearch.WordTrace]
  refine ⟨80739834404190181233438991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107653112538920241644585321 80739834404190181233438991)
  ·
    refine ⟨121109751606285271850158487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80739834404190181233438991 121109751606285271850158487)
    ·
      refine ⟨181664627409427907775237731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121109751606285271850158487 181664627409427907775237731)
      ·
        refine ⟨272496941114141861662856597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181664627409427907775237731 272496941114141861662856597)
        ·
          refine ⟨12773294114725399765446403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 272496941114141861662856597 12773294114725399765446403)
          ·
            refine ⟨19159941172088099648169605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12773294114725399765446403 19159941172088099648169605)
            ·
              refine ⟨3592488969766518684031801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19159941172088099648169605 3592488969766518684031801)
              ·
                refine ⟨2694366727324889013023851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3592488969766518684031801 2694366727324889013023851)
                ·
                  refine ⟨4041550090987333519535777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2694366727324889013023851 4041550090987333519535777)
                  ·
                    refine ⟨3031162568240500139651833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4041550090987333519535777 3031162568240500139651833)
                    ·
                      refine ⟨2273371926180375104738875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3031162568240500139651833 2273371926180375104738875)
                      ·
                        rfl

theorem cell23_4427376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 4, 2, 1, 2, 2].length) (baseStart_4427376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4427376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4427376 prefixEnd_4427376 := by exact prefixLift 4427376
  have htrace : WordTrace (prefixWord ++ tailWord_4427376) baseStart_4427376 baseEnd_4427376 := by
    simpa [prefixWord, tailWord_4427376, baseEnd_4427376] using wordTrace_append hprefix tailTrace_4427376
  have hstable : (prefixWord ++ tailWord_4427376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4427376).length < 2 ^ (prefixWord ++ tailWord_4427376).sum := by decide
  have hdescent : baseEnd_4427376 < baseStart_4427376 := by decide
  rcases family_descends (prefixWord ++ tailWord_4427376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4427378 : List Nat := [3, 2, 1, 2, 3, 1, 1, 1, 2, 7]
def baseStart_4427378 : Nat := 118140960795 + 4427378 * 2 ^ 59
def prefixEnd_4427378 : Nat := 4983230072969 + 3 ^ 40 * 4427378 * 2
def baseEnd_4427378 : Nat := 757790984380561365637955

theorem tailTrace_4427378 : CollatzResearch.WordTrace tailWord_4427378 prefixEnd_4427378 757790984380561365637955 := by
  unfold tailWord_4427378
  simp only [CollatzResearch.WordTrace]
  refine ⟨40369935438593279202112697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107653161169582077872300525 40369935438593279202112697)
  ·
    refine ⟨30277451578944959401584523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40369935438593279202112697 30277451578944959401584523)
    ·
      refine ⟨45416177368417439102376785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30277451578944959401584523 45416177368417439102376785)
      ·
        refine ⟨34062133026313079326782589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45416177368417439102376785 34062133026313079326782589)
        ·
          refine ⟨12773299884867404747543471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34062133026313079326782589 12773299884867404747543471)
          ·
            refine ⟨19159949827301107121315207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12773299884867404747543471 19159949827301107121315207)
            ·
              refine ⟨28739924740951660681972811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19159949827301107121315207 28739924740951660681972811)
              ·
                refine ⟨43109887111427491022959217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28739924740951660681972811 43109887111427491022959217)
                ·
                  refine ⟨32332415333570618267219413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43109887111427491022959217 32332415333570618267219413)
                  ·
                    refine ⟨757790984380561365637955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32332415333570618267219413 757790984380561365637955)
                    ·
                      rfl

theorem cell23_4427378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 2, 7].length) (baseStart_4427378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4427378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4427378 prefixEnd_4427378 := by exact prefixLift 4427378
  have htrace : WordTrace (prefixWord ++ tailWord_4427378) baseStart_4427378 baseEnd_4427378 := by
    simpa [prefixWord, tailWord_4427378, baseEnd_4427378] using wordTrace_append hprefix tailTrace_4427378
  have hstable : (prefixWord ++ tailWord_4427378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4427378).length < 2 ^ (prefixWord ++ tailWord_4427378).sum := by decide
  have hdescent : baseEnd_4427378 < baseStart_4427378 := by decide
  rcases family_descends (prefixWord ++ tailWord_4427378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4427385 : List Nat := [1, 2, 1, 3, 3, 1, 1, 1, 5, 3, 2]
def baseStart_4427385 : Nat := 118140960795 + 4427385 * 2 ^ 59
def prefixEnd_4427385 : Nat := 4983230072969 + 3 ^ 40 * 4427385 * 2
def baseEnd_4427385 : Nat := 2273376547506265569526333

theorem tailTrace_4427385 : CollatzResearch.WordTrace tailWord_4427385 prefixEnd_4427385 2273376547506265569526333 := by
  unfold tailWord_4427385
  simp only [CollatzResearch.WordTrace]
  refine ⟨161479997065347757003955609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107653331376898504669303739 161479997065347757003955609)
  ·
    refine ⟨121109997799010817752966707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161479997065347757003955609 121109997799010817752966707)
    ·
      refine ⟨181664996698516226629450061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121109997799010817752966707 181664996698516226629450061)
      ·
        refine ⟨68124373761943584986043773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 181664996698516226629450061 68124373761943584986043773)
        ·
          refine ⟨25546640160728844369766415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68124373761943584986043773 25546640160728844369766415)
          ·
            refine ⟨38319960241093266554649623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25546640160728844369766415 38319960241093266554649623)
            ·
              refine ⟨57479940361639899831974435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38319960241093266554649623 57479940361639899831974435)
              ·
                refine ⟨86219910542459849747961653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57479940361639899831974435 86219910542459849747961653)
                ·
                  refine ⟨8083116613355610913871405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 86219910542459849747961653 8083116613355610913871405)
                  ·
                    refine ⟨3031168730008354092701777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8083116613355610913871405 3031168730008354092701777)
                    ·
                      refine ⟨2273376547506265569526333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3031168730008354092701777 2273376547506265569526333)
                      ·
                        rfl

theorem cell23_4427385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 5, 3, 2].length) (baseStart_4427385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4427385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4427385 prefixEnd_4427385 := by exact prefixLift 4427385
  have htrace : WordTrace (prefixWord ++ tailWord_4427385) baseStart_4427385 baseEnd_4427385 := by
    simpa [prefixWord, tailWord_4427385, baseEnd_4427385] using wordTrace_append hprefix tailTrace_4427385
  have hstable : (prefixWord ++ tailWord_4427385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4427385).length < 2 ^ (prefixWord ++ tailWord_4427385).sum := by decide
  have hdescent : baseEnd_4427385 < baseStart_4427385 := by decide
  rcases family_descends (prefixWord ++ tailWord_4427385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4427402 : List Nat := [3, 1, 2, 3, 2, 1, 2, 1, 3, 3, 2]
def baseStart_4427402 : Nat := 118140960795 + 4427402 * 2 ^ 59
def prefixEnd_4427402 : Nat := 4983230072969 + 3 ^ 40 * 4427402 * 2
def baseEnd_4427402 : Nat := 2273385276677392003013755

theorem tailTrace_4427402 : CollatzResearch.WordTrace tailWord_4427402 prefixEnd_4427402 2273385276677392003013755 := by
  unfold tailWord_4427402
  simp only [CollatzResearch.WordTrace]
  refine ⟨40370154276571542226831115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107653744737524112604882973 40370154276571542226831115)
  ·
    refine ⟨60555231414857313340246673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40370154276571542226831115 60555231414857313340246673)
    ·
      refine ⟨45416423561142985005185005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60555231414857313340246673 45416423561142985005185005)
      ·
        refine ⟨17031158835428619376944377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45416423561142985005185005 17031158835428619376944377)
        ·
          refine ⟨12773369126571464532708283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17031158835428619376944377 12773369126571464532708283)
          ·
            refine ⟨19160053689857196799062425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12773369126571464532708283 19160053689857196799062425)
            ·
              refine ⟨14370040267392897599296819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19160053689857196799062425 14370040267392897599296819)
              ·
                refine ⟨21555060401089346398945229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14370040267392897599296819 21555060401089346398945229)
                ·
                  refine ⟨8083147650408504899604461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21555060401089346398945229 8083147650408504899604461)
                  ·
                    refine ⟨3031180368903189337351673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8083147650408504899604461 3031180368903189337351673)
                    ·
                      refine ⟨2273385276677392003013755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3031180368903189337351673 2273385276677392003013755)
                      ·
                        rfl

theorem cell23_4427402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 1, 3, 3, 2].length) (baseStart_4427402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4427402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4427402 prefixEnd_4427402 := by exact prefixLift 4427402
  have htrace : WordTrace (prefixWord ++ tailWord_4427402) baseStart_4427402 baseEnd_4427402 := by
    simpa [prefixWord, tailWord_4427402, baseEnd_4427402] using wordTrace_append hprefix tailTrace_4427402
  have hstable : (prefixWord ++ tailWord_4427402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4427402).length < 2 ^ (prefixWord ++ tailWord_4427402).sum := by decide
  have hdescent : baseEnd_4427402 < baseStart_4427402 := by decide
  rcases family_descends (prefixWord ++ tailWord_4427402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4427489 : List Nat := [1, 2, 3, 1, 5, 1, 3, 2, 5]
def baseStart_4427489 : Nat := 118140960795 + 4427489 * 2 ^ 59
def prefixEnd_4427489 : Nat := 4983230072969 + 3 ^ 40 * 4427489 * 2
def baseEnd_4427489 : Nat := 252603327721592573625095

theorem tailTrace_4427489 : CollatzResearch.WordTrace tailWord_4427489 prefixEnd_4427489 252603327721592573625095 := by
  unfold tailWord_4427489
  simp only [CollatzResearch.WordTrace]
  refine ⟨161483790256970982765741521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107655860171313988510494347 161483790256970982765741521)
  ·
    refine ⟨121112842692728237074306141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161483790256970982765741521 121112842692728237074306141)
    ·
      refine ⟨45417316009773088902864803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121112842692728237074306141 45417316009773088902864803)
      ·
        refine ⟨68125974014659633354297205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45417316009773088902864803 68125974014659633354297205)
        ·
          refine ⟨6386810063874340626965363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 68125974014659633354297205 6386810063874340626965363)
          ·
            refine ⟨9580215095811510940448045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6386810063874340626965363 9580215095811510940448045)
            ·
              refine ⟨3592580660929316602668017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9580215095811510940448045 3592580660929316602668017)
              ·
                refine ⟨2694435495696987452001013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3592580660929316602668017 2694435495696987452001013)
                ·
                  refine ⟨252603327721592573625095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2694435495696987452001013 252603327721592573625095)
                  ·
                    rfl

theorem cell23_4427489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 3, 2, 5].length) (baseStart_4427489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4427489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4427489 prefixEnd_4427489 := by exact prefixLift 4427489
  have htrace : WordTrace (prefixWord ++ tailWord_4427489) baseStart_4427489 baseEnd_4427489 := by
    simpa [prefixWord, tailWord_4427489, baseEnd_4427489] using wordTrace_append hprefix tailTrace_4427489
  have hstable : (prefixWord ++ tailWord_4427489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4427489).length < 2 ^ (prefixWord ++ tailWord_4427489).sum := by decide
  have hdescent : baseEnd_4427489 < baseStart_4427489 := by decide
  rcases family_descends (prefixWord ++ tailWord_4427489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4427540 : List Nat := [2, 4, 4, 1, 1, 2, 2, 2, 5]
def baseStart_4427540 : Nat := 118140960795 + 4427540 * 2 ^ 59
def prefixEnd_4427540 : Nat := 4983230072969 + 3 ^ 40 * 4427540 * 2
def baseEnd_4427540 : Nat := 252606237445301384787569

theorem tailTrace_4427540 : CollatzResearch.WordTrace tailWord_4427540 prefixEnd_4427540 252606237445301384787569 := by
  unfold tailWord_4427540
  simp only [CollatzResearch.WordTrace]
  refine ⟨80742825189893109237924037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107657100253190812317232049 80742825189893109237924037)
  ·
    refine ⟨15139279723104957982110757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80742825189893109237924037 15139279723104957982110757)
    ·
      refine ⟨2838614948082179621645767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15139279723104957982110757 2838614948082179621645767)
      ·
        refine ⟨4257922422123269432468651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2838614948082179621645767 4257922422123269432468651)
        ·
          refine ⟨6386883633184904148702977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4257922422123269432468651 6386883633184904148702977)
          ·
            refine ⟨4790162724888678111527233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6386883633184904148702977 4790162724888678111527233)
            ·
              refine ⟨3592622043666508583645425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4790162724888678111527233 3592622043666508583645425)
              ·
                refine ⟨2694466532749881437734069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3592622043666508583645425 2694466532749881437734069)
                ·
                  refine ⟨252606237445301384787569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2694466532749881437734069 252606237445301384787569)
                  ·
                    rfl

theorem cell23_4427540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 2, 2, 5].length) (baseStart_4427540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4427540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4427540 prefixEnd_4427540 := by exact prefixLift 4427540
  have htrace : WordTrace (prefixWord ++ tailWord_4427540) baseStart_4427540 baseEnd_4427540 := by
    simpa [prefixWord, tailWord_4427540, baseEnd_4427540] using wordTrace_append hprefix tailTrace_4427540
  have hstable : (prefixWord ++ tailWord_4427540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4427540).length < 2 ^ (prefixWord ++ tailWord_4427540).sum := by decide
  have hdescent : baseEnd_4427540 < baseStart_4427540 := by decide
  rcases family_descends (prefixWord ++ tailWord_4427540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4427592 : List Nat := [2, 1, 3, 1, 1, 5, 1, 3, 1, 5]
def baseStart_4427592 : Nat := 118140960795 + 4427592 * 2 ^ 59
def prefixEnd_4427592 : Nat := 4983230072969 + 3 ^ 40 * 4427592 * 2
def baseEnd_4427592 : Nat := 757827612667248753212627

theorem tailTrace_4427592 : CollatzResearch.WordTrace tailWord_4427592 prefixEnd_4427592 757827612667248753212627 := by
  unfold tailWord_4427592
  simp only [CollatzResearch.WordTrace]
  refine ⟨80743773487798915678370515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107658364650398554237827353 80743773487798915678370515)
  ·
    refine ⟨121115660231698373517555773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80743773487798915678370515 121115660231698373517555773)
    ·
      refine ⟨45418372586886890069083415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121115660231698373517555773 45418372586886890069083415)
      ·
        refine ⟨68127558880330335103625123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45418372586886890069083415 68127558880330335103625123)
        ·
          refine ⟨102191338320495502655437685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68127558880330335103625123 102191338320495502655437685)
          ·
            refine ⟨9580437967546453373947283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 102191338320495502655437685 9580437967546453373947283)
            ·
              refine ⟨14370656951319680060920925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9580437967546453373947283 14370656951319680060920925)
              ·
                refine ⟨5388996356744880022845347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14370656951319680060920925 5388996356744880022845347)
                ·
                  refine ⟨8083494535117320034268021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5388996356744880022845347 8083494535117320034268021)
                  ·
                    refine ⟨757827612667248753212627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8083494535117320034268021 757827612667248753212627)
                    ·
                      rfl

theorem cell23_4427592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 3, 1, 5].length) (baseStart_4427592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4427592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4427592 prefixEnd_4427592 := by exact prefixLift 4427592
  have htrace : WordTrace (prefixWord ++ tailWord_4427592) baseStart_4427592 baseEnd_4427592 := by
    simpa [prefixWord, tailWord_4427592, baseEnd_4427592] using wordTrace_append hprefix tailTrace_4427592
  have hstable : (prefixWord ++ tailWord_4427592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4427592).length < 2 ^ (prefixWord ++ tailWord_4427592).sum := by decide
  have hdescent : baseEnd_4427592 < baseStart_4427592 := by decide
  rcases family_descends (prefixWord ++ tailWord_4427592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4427615 : List Nat := [1, 1, 2, 3, 1, 4, 1, 1, 3, 1, 5]
def baseStart_4427615 : Nat := 118140960795 + 4427615 * 2 ^ 59
def prefixEnd_4427615 : Nat := 4983230072969 + 3 ^ 40 * 4427615 * 2
def baseEnd_4427615 : Nat := 2273494648056799669650275

theorem tailTrace_4427615 : CollatzResearch.WordTrace tailWord_4427615 prefixEnd_4427615 2273494648056799669650275 := by
  unfold tailWord_4427615
  simp only [CollatzResearch.WordTrace]
  refine ⟨161488385854514506284828299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107658923903009670856552199 161488385854514506284828299)
  ·
    refine ⟨242232578781771759427242449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161488385854514506284828299 242232578781771759427242449)
    ·
      refine ⟨181674434086328819570431837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 242232578781771759427242449 181674434086328819570431837)
      ·
        refine ⟨68127912782373307338911939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 181674434086328819570431837 68127912782373307338911939)
        ·
          refine ⟨102191869173559961008367909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68127912782373307338911939 102191869173559961008367909)
          ·
            refine ⟨19160975470042492689068983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 102191869173559961008367909 19160975470042492689068983)
            ·
              refine ⟨28741463205063739033603475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19160975470042492689068983 28741463205063739033603475)
              ·
                refine ⟨43112194807595608550405213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28741463205063739033603475 43112194807595608550405213)
                ·
                  refine ⟨16167073052848353206401955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43112194807595608550405213 16167073052848353206401955)
                  ·
                    refine ⟨24250609579272529809602933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16167073052848353206401955 24250609579272529809602933)
                    ·
                      refine ⟨2273494648056799669650275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24250609579272529809602933 2273494648056799669650275)
                      ·
                        rfl

theorem cell23_4427615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 3, 1, 5].length) (baseStart_4427615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4427615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4427615 prefixEnd_4427615 := by exact prefixLift 4427615
  have htrace : WordTrace (prefixWord ++ tailWord_4427615) baseStart_4427615 baseEnd_4427615 := by
    simpa [prefixWord, tailWord_4427615, baseEnd_4427615] using wordTrace_append hprefix tailTrace_4427615
  have hstable : (prefixWord ++ tailWord_4427615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4427615).length < 2 ^ (prefixWord ++ tailWord_4427615).sum := by decide
  have hdescent : baseEnd_4427615 < baseStart_4427615 := by decide
  rcases family_descends (prefixWord ++ tailWord_4427615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4427626 : List Nat := [3, 1, 3, 4, 1, 1, 2, 2, 1, 5]
def baseStart_4427626 : Nat := 118140960795 + 4427626 * 2 ^ 59
def prefixEnd_4427626 : Nat := 4983230072969 + 3 ^ 40 * 4427626 * 2
def baseEnd_4427626 : Nat := 757833432114666375537575

theorem tailTrace_4427626 : CollatzResearch.WordTrace tailWord_4427626 prefixEnd_4427626 757833432114666375537575 := by
  unfold tailWord_4427626
  simp only [CollatzResearch.WordTrace]
  refine ⟨40372196764368663790869683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107659191371649770108985821 40372196764368663790869683)
  ·
    refine ⟨60558295146552995686304525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40372196764368663790869683 60558295146552995686304525)
    ·
      refine ⟨22709360679957373382364197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60558295146552995686304525 22709360679957373382364197)
      ·
        refine ⟨4258005127492007509193287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22709360679957373382364197 4258005127492007509193287)
        ·
          refine ⟨6387007691238011263789931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4258005127492007509193287 6387007691238011263789931)
          ·
            refine ⟨9580511536857016895684897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6387007691238011263789931 9580511536857016895684897)
            ·
              refine ⟨7185383652642762671763673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9580511536857016895684897 7185383652642762671763673)
              ·
                refine ⟨5389037739482072003822755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7185383652642762671763673 5389037739482072003822755)
                ·
                  refine ⟨8083556609223108005734133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5389037739482072003822755 8083556609223108005734133)
                  ·
                    refine ⟨757833432114666375537575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8083556609223108005734133 757833432114666375537575)
                    ·
                      rfl

theorem cell23_4427626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 2, 1, 5].length) (baseStart_4427626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4427626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4427626 prefixEnd_4427626 := by exact prefixLift 4427626
  have htrace : WordTrace (prefixWord ++ tailWord_4427626) baseStart_4427626 baseEnd_4427626 := by
    simpa [prefixWord, tailWord_4427626, baseEnd_4427626] using wordTrace_append hprefix tailTrace_4427626
  have hstable : (prefixWord ++ tailWord_4427626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4427626).length < 2 ^ (prefixWord ++ tailWord_4427626).sum := by decide
  have hdescent : baseEnd_4427626 < baseStart_4427626 := by decide
  rcases family_descends (prefixWord ++ tailWord_4427626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4427646 : List Nat := [4, 2, 3, 1, 1, 1, 2, 3, 1, 1, 4]
def baseStart_4427646 : Nat := 118140960795 + 4427646 * 2 ^ 59
def prefixEnd_4427646 : Nat := 4983230072969 + 3 ^ 40 * 4427646 * 2
def baseEnd_4427646 : Nat := 2273510565957089048362633

theorem tailTrace_4427646 : CollatzResearch.WordTrace tailWord_4427646 prefixEnd_4427646 2273510565957089048362633 := by
  unfold tailWord_4427646
  simp only [CollatzResearch.WordTrace]
  refine ⟨20186189564675274822400849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107659677678268132386137861 20186189564675274822400849)
  ·
    refine ⟨15139642173506456116800637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20186189564675274822400849 15139642173506456116800637)
    ·
      refine ⟨5677365815064921043800239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15139642173506456116800637 5677365815064921043800239)
      ·
        refine ⟨8516048722597381565700359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5677365815064921043800239 8516048722597381565700359)
        ·
          refine ⟨12774073083896072348550539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8516048722597381565700359 12774073083896072348550539)
          ·
            refine ⟨19161109625844108522825809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12774073083896072348550539 19161109625844108522825809)
            ·
              refine ⟨14370832219383081392119357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19161109625844108522825809 14370832219383081392119357)
              ·
                refine ⟨5389062082268655522044759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14370832219383081392119357 5389062082268655522044759)
                ·
                  refine ⟨8083593123402983283067139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5389062082268655522044759 8083593123402983283067139)
                  ·
                    refine ⟨12125389685104474924600709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8083593123402983283067139 12125389685104474924600709)
                    ·
                      refine ⟨2273510565957089048362633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12125389685104474924600709 2273510565957089048362633)
                      ·
                        rfl

theorem cell23_4427646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_4427646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4427646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4427646 prefixEnd_4427646 := by exact prefixLift 4427646
  have htrace : WordTrace (prefixWord ++ tailWord_4427646) baseStart_4427646 baseEnd_4427646 := by
    simpa [prefixWord, tailWord_4427646, baseEnd_4427646] using wordTrace_append hprefix tailTrace_4427646
  have hstable : (prefixWord ++ tailWord_4427646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4427646).length < 2 ^ (prefixWord ++ tailWord_4427646).sum := by decide
  have hdescent : baseEnd_4427646 < baseStart_4427646 := by decide
  rcases family_descends (prefixWord ++ tailWord_4427646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4427689 : List Nat := [1, 2, 1, 1, 1, 1, 4, 6, 1, 3, 2]
def baseStart_4427689 : Nat := 118140960795 + 4427689 * 2 ^ 59
def prefixEnd_4427689 : Nat := 4983230072969 + 3 ^ 40 * 4427689 * 2
def baseEnd_4427689 : Nat := 2273532645625232380124935

theorem tailTrace_4427689 : CollatzResearch.WordTrace tailWord_4427689 prefixEnd_4427689 2273532645625232380124935 := by
  unfold tailWord_4427689
  simp only [CollatzResearch.WordTrace]
  refine ⟨161491084856246416923022121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107660723237497611282014747 161491084856246416923022121)
  ·
    refine ⟨121118313642184812692266591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161491084856246416923022121 121118313642184812692266591)
    ·
      refine ⟨181677470463277219038399887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121118313642184812692266591 181677470463277219038399887)
      ·
        refine ⟨272516205694915828557599831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181677470463277219038399887 272516205694915828557599831)
        ·
          refine ⟨408774308542373742836399747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 272516205694915828557599831 408774308542373742836399747)
          ·
            refine ⟨613161462813560614254599621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 408774308542373742836399747 613161462813560614254599621)
            ·
              refine ⟨114967774277542615172737429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 613161462813560614254599621 114967774277542615172737429)
              ·
                refine ⟨5389114419259810086222067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 114967774277542615172737429 5389114419259810086222067)
                ·
                  refine ⟨8083671628889715129333101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5389114419259810086222067 8083671628889715129333101)
                  ·
                    refine ⟨3031376860833643173499913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8083671628889715129333101 3031376860833643173499913)
                    ·
                      refine ⟨2273532645625232380124935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3031376860833643173499913 2273532645625232380124935)
                      ·
                        rfl

theorem cell23_4427689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 6, 1, 3, 2].length) (baseStart_4427689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4427689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4427689 prefixEnd_4427689 := by exact prefixLift 4427689
  have htrace : WordTrace (prefixWord ++ tailWord_4427689) baseStart_4427689 baseEnd_4427689 := by
    simpa [prefixWord, tailWord_4427689, baseEnd_4427689] using wordTrace_append hprefix tailTrace_4427689
  have hstable : (prefixWord ++ tailWord_4427689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4427689).length < 2 ^ (prefixWord ++ tailWord_4427689).sum := by decide
  have hdescent : baseEnd_4427689 < baseStart_4427689 := by decide
  rcases family_descends (prefixWord ++ tailWord_4427689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4427700 : List Nat := [2, 5, 2, 1, 2, 1, 3, 1, 1, 2, 3]
def baseStart_4427700 : Nat := 118140960795 + 4427700 * 2 ^ 59
def prefixEnd_4427700 : Nat := 4983230072969 + 3 ^ 40 * 4427700 * 2
def baseEnd_4427700 : Nat := 2273538293912431837087385

theorem tailTrace_4427700 : CollatzResearch.WordTrace tailWord_4427700 prefixEnd_4427700 2273538293912431837087385 := by
  unfold tailWord_4427700
  simp only [CollatzResearch.WordTrace]
  refine ⟨80745743029603282900836277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107660990706137710534448369 80745743029603282900836277)
  ·
    refine ⟨7569913409025307771953401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 80745743029603282900836277 7569913409025307771953401)
    ·
      refine ⟨5677435056768980828965051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7569913409025307771953401 5677435056768980828965051)
      ·
        refine ⟨8516152585153471243447577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5677435056768980828965051 8516152585153471243447577)
        ·
          refine ⟨6387114438865103432585683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8516152585153471243447577 6387114438865103432585683)
          ·
            refine ⟨9580671658297655148878525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6387114438865103432585683 9580671658297655148878525)
            ·
              refine ⟨3592751871861620680829447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9580671658297655148878525 3592751871861620680829447)
              ·
                refine ⟨5389127807792431021244171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3592751871861620680829447 5389127807792431021244171)
                ·
                  refine ⟨8083691711688646531866257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5389127807792431021244171 8083691711688646531866257)
                  ·
                    refine ⟨6062768783766484898899693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8083691711688646531866257 6062768783766484898899693)
                    ·
                      refine ⟨2273538293912431837087385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6062768783766484898899693 2273538293912431837087385)
                      ·
                        rfl

theorem cell23_4427700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_4427700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4427700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4427700 prefixEnd_4427700 := by exact prefixLift 4427700
  have htrace : WordTrace (prefixWord ++ tailWord_4427700) baseStart_4427700 baseEnd_4427700 := by
    simpa [prefixWord, tailWord_4427700, baseEnd_4427700] using wordTrace_append hprefix tailTrace_4427700
  have hstable : (prefixWord ++ tailWord_4427700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4427700).length < 2 ^ (prefixWord ++ tailWord_4427700).sum := by decide
  have hdescent : baseEnd_4427700 < baseStart_4427700 := by decide
  rcases family_descends (prefixWord ++ tailWord_4427700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4427722 : List Nat := [3, 1, 2, 1, 2, 1, 3, 1, 2, 4, 3]
def baseStart_4427722 : Nat := 118140960795 + 4427722 * 2 ^ 59
def prefixEnd_4427722 : Nat := 4983230072969 + 3 ^ 40 * 4427722 * 2
def baseEnd_4427722 : Nat := 2273549590486830751012283

theorem tailTrace_4427722 : CollatzResearch.WordTrace tailWord_4427722 prefixEnd_4427722 2273549590486830751012283 := by
  unfold tailWord_4427722
  simp only [CollatzResearch.WordTrace]
  refine ⟨40373072116281715889743355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107661525643417909039315613 40373072116281715889743355)
  ·
    refine ⟨60559608174422573834615033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40373072116281715889743355 60559608174422573834615033)
    ·
      refine ⟨45419706130816930375961275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60559608174422573834615033 45419706130816930375961275)
      ·
        refine ⟨68129559196225395563941913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45419706130816930375961275 68129559196225395563941913)
        ·
          refine ⟨51097169397169046672956435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68129559196225395563941913 51097169397169046672956435)
          ·
            refine ⟨76645754095753570009434653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51097169397169046672956435 76645754095753570009434653)
            ·
              refine ⟨28742157785907588753537995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76645754095753570009434653 28742157785907588753537995)
              ·
                refine ⟨43113236678861383130306993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28742157785907588753537995 43113236678861383130306993)
                ·
                  refine ⟨32334927509146037347730245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43113236678861383130306993 32334927509146037347730245)
                  ·
                    refine ⟨6062798907964882002699421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32334927509146037347730245 6062798907964882002699421)
                    ·
                      refine ⟨2273549590486830751012283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6062798907964882002699421 2273549590486830751012283)
                      ·
                        rfl

theorem cell23_4427722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 2, 4, 3].length) (baseStart_4427722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4427722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4427722 prefixEnd_4427722 := by exact prefixLift 4427722
  have htrace : WordTrace (prefixWord ++ tailWord_4427722) baseStart_4427722 baseEnd_4427722 := by
    simpa [prefixWord, tailWord_4427722, baseEnd_4427722] using wordTrace_append hprefix tailTrace_4427722
  have hstable : (prefixWord ++ tailWord_4427722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4427722).length < 2 ^ (prefixWord ++ tailWord_4427722).sum := by decide
  have hdescent : baseEnd_4427722 < baseStart_4427722 := by decide
  rcases family_descends (prefixWord ++ tailWord_4427722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4427736 : List Nat := [2, 1, 2, 2, 2, 2, 1, 5, 2, 2, 2]
def baseStart_4427736 : Nat := 118140960795 + 4427736 * 2 ^ 59
def prefixEnd_4427736 : Nat := 4983230072969 + 3 ^ 40 * 4427736 * 2
def baseEnd_4427736 : Nat := 2273556779215993696237219

theorem tailTrace_4427736 : CollatzResearch.WordTrace tailWord_4427736 prefixEnd_4427736 2273556779215993696237219 := by
  unfold tailWord_4427736
  simp only [CollatzResearch.WordTrace]
  refine ⟨80746399543538071974991531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107661866058050762633322041 80746399543538071974991531)
  ·
    refine ⟨121119599315307107962487297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80746399543538071974991531 121119599315307107962487297)
    ·
      refine ⟨90839699486480330971865473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121119599315307107962487297 90839699486480330971865473)
      ·
        refine ⟨68129774614860248228899105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90839699486480330971865473 68129774614860248228899105)
        ·
          refine ⟨51097330961145186171674329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68129774614860248228899105 51097330961145186171674329)
          ·
            refine ⟨38322998220858889628755747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51097330961145186171674329 38322998220858889628755747)
            ·
              refine ⟨57484497331288334443133621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38322998220858889628755747 57484497331288334443133621)
              ·
                refine ⟨5389171624808281354043777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 57484497331288334443133621 5389171624808281354043777)
                ·
                  refine ⟨4041878718606211015532833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5389171624808281354043777 4041878718606211015532833)
                  ·
                    refine ⟨3031409038954658261649625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4041878718606211015532833 3031409038954658261649625)
                    ·
                      refine ⟨2273556779215993696237219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3031409038954658261649625 2273556779215993696237219)
                      ·
                        rfl

theorem cell23_4427736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 5, 2, 2, 2].length) (baseStart_4427736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4427736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4427736 prefixEnd_4427736 := by exact prefixLift 4427736
  have htrace : WordTrace (prefixWord ++ tailWord_4427736) baseStart_4427736 baseEnd_4427736 := by
    simpa [prefixWord, tailWord_4427736, baseEnd_4427736] using wordTrace_append hprefix tailTrace_4427736
  have hstable : (prefixWord ++ tailWord_4427736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4427736).length < 2 ^ (prefixWord ++ tailWord_4427736).sum := by decide
  have hdescent : baseEnd_4427736 < baseStart_4427736 := by decide
  rcases family_descends (prefixWord ++ tailWord_4427736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4427752 : List Nat := [2, 1, 4, 1, 1, 1, 1, 1, 3, 5, 3]
def baseStart_4427752 : Nat := 118140960795 + 4427752 * 2 ^ 59
def prefixEnd_4427752 : Nat := 4983230072969 + 3 ^ 40 * 4427752 * 2
def baseEnd_4427752 : Nat := 2273564994906465633637145

theorem tailTrace_4427752 : CollatzResearch.WordTrace tailWord_4427752 prefixEnd_4427752 2273564994906465633637145 := by
  unfold tailWord_4427752
  simp only [CollatzResearch.WordTrace]
  refine ⟨80746691327509089341282755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107662255103345452455043673 80746691327509089341282755)
  ·
    refine ⟨121120036991263634011924133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80746691327509089341282755 121120036991263634011924133)
    ·
      refine ⟨22710006935861931377235775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 121120036991263634011924133 22710006935861931377235775)
      ·
        refine ⟨34065010403792897065853663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22710006935861931377235775 34065010403792897065853663)
        ·
          refine ⟨51097515605689345598780495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34065010403792897065853663 51097515605689345598780495)
          ·
            refine ⟨76646273408534018398170743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51097515605689345598780495 76646273408534018398170743)
            ·
              refine ⟨114969410112801027597256115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76646273408534018398170743 114969410112801027597256115)
              ·
                refine ⟨172454115169201541395884173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114969410112801027597256115 172454115169201541395884173)
                ·
                  refine ⟨64670293188450578023456565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 172454115169201541395884173 64670293188450578023456565)
                  ·
                    refine ⟨6062839986417241689699053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 64670293188450578023456565 6062839986417241689699053)
                    ·
                      refine ⟨2273564994906465633637145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6062839986417241689699053 2273564994906465633637145)
                      ·
                        rfl

theorem cell23_4427752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 3, 5, 3].length) (baseStart_4427752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4427752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4427752 prefixEnd_4427752 := by exact prefixLift 4427752
  have htrace : WordTrace (prefixWord ++ tailWord_4427752) baseStart_4427752 baseEnd_4427752 := by
    simpa [prefixWord, tailWord_4427752, baseEnd_4427752] using wordTrace_append hprefix tailTrace_4427752
  have hstable : (prefixWord ++ tailWord_4427752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4427752).length < 2 ^ (prefixWord ++ tailWord_4427752).sum := by decide
  have hdescent : baseEnd_4427752 < baseStart_4427752 := by decide
  rcases family_descends (prefixWord ++ tailWord_4427752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4427757 : List Nat := [1, 5, 1, 4, 1, 2, 2, 1, 1, 3, 2]
def baseStart_4427757 : Nat := 118140960795 + 4427757 * 2 ^ 59
def prefixEnd_4427757 : Nat := 4983230072969 + 3 ^ 40 * 4427757 * 2
def baseEnd_4427757 : Nat := 2273567562309738114074623

theorem tailTrace_4427757 : CollatzResearch.WordTrace tailWord_4427757 prefixEnd_4427757 2273567562309738114074623 := by
  unfold tailWord_4427757
  simp only [CollatzResearch.WordTrace]
  refine ⟨161493565020000064536497525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107662376680000043024331683 161493565020000064536497525)
  ·
    refine ⟨15140021720625006050296643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 161493565020000064536497525 15140021720625006050296643)
    ·
      refine ⟨22710032580937509075444965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15140021720625006050296643 22710032580937509075444965)
      ·
        refine ⟨4258131108925782951645931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22710032580937509075444965 4258131108925782951645931)
        ·
          refine ⟨6387196663388674427468897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4258131108925782951645931 6387196663388674427468897)
          ·
            refine ⟨4790397497541505820601673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6387196663388674427468897 4790397497541505820601673)
            ·
              refine ⟨3592798123156129365451255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4790397497541505820601673 3592798123156129365451255)
              ·
                refine ⟨5389197184734194048176883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3592798123156129365451255 5389197184734194048176883)
                ·
                  refine ⟨8083795777101291072265325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5389197184734194048176883 8083795777101291072265325)
                  ·
                    refine ⟨3031423416412984152099497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8083795777101291072265325 3031423416412984152099497)
                    ·
                      refine ⟨2273567562309738114074623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3031423416412984152099497 2273567562309738114074623)
                      ·
                        rfl

theorem cell23_4427757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_4427757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4427757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4427757 prefixEnd_4427757 := by exact prefixLift 4427757
  have htrace : WordTrace (prefixWord ++ tailWord_4427757) baseStart_4427757 baseEnd_4427757 := by
    simpa [prefixWord, tailWord_4427757, baseEnd_4427757] using wordTrace_append hprefix tailTrace_4427757
  have hstable : (prefixWord ++ tailWord_4427757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4427757).length < 2 ^ (prefixWord ++ tailWord_4427757).sum := by decide
  have hdescent : baseEnd_4427757 < baseStart_4427757 := by decide
  rcases family_descends (prefixWord ++ tailWord_4427757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4427759 : List Nat := [1, 1, 2, 1, 4, 2, 4, 3, 5]
def baseStart_4427759 : Nat := 118140960795 + 4427759 * 2 ^ 59
def prefixEnd_4427759 : Nat := 4983230072969 + 3 ^ 40 * 4427759 * 2
def baseEnd_4427759 : Nat := 252618732141227456249957

theorem tailTrace_4427759 : CollatzResearch.WordTrace tailWord_4427759 prefixEnd_4427759 252618732141227456249957 := by
  unfold tailWord_4427759
  simp only [CollatzResearch.WordTrace]
  refine ⟨161493637965992818878070331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107662425310661879252046887 161493637965992818878070331)
  ·
    refine ⟨242240456948989228317105497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161493637965992818878070331 242240456948989228317105497)
    ·
      refine ⟨181680342711741921237829123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 242240456948989228317105497 181680342711741921237829123)
      ·
        refine ⟨272520514067612881856743685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181680342711741921237829123 272520514067612881856743685)
        ·
          refine ⟨51097596387677415348139441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 272520514067612881856743685 51097596387677415348139441)
          ·
            refine ⟨38323197290758061511104581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51097596387677415348139441 38323197290758061511104581)
            ·
              refine ⟨7185599492017136533332109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38323197290758061511104581 7185599492017136533332109)
              ·
                refine ⟨2694599809506426199999541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7185599492017136533332109 2694599809506426199999541)
                ·
                  refine ⟨252618732141227456249957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2694599809506426199999541 252618732141227456249957)
                  ·
                    rfl

theorem cell23_4427759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 3, 5].length) (baseStart_4427759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4427759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4427759 prefixEnd_4427759 := by exact prefixLift 4427759
  have htrace : WordTrace (prefixWord ++ tailWord_4427759) baseStart_4427759 baseEnd_4427759 := by
    simpa [prefixWord, tailWord_4427759, baseEnd_4427759] using wordTrace_append hprefix tailTrace_4427759
  have hstable : (prefixWord ++ tailWord_4427759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4427759).length < 2 ^ (prefixWord ++ tailWord_4427759).sum := by decide
  have hdescent : baseEnd_4427759 < baseStart_4427759 := by decide
  rcases family_descends (prefixWord ++ tailWord_4427759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4427772 : List Nat := [2, 2, 2, 1, 2, 2, 2, 1, 4, 5]
def baseStart_4427772 : Nat := 118140960795 + 4427772 * 2 ^ 59
def prefixEnd_4427772 : Nat := 4983230072969 + 3 ^ 40 * 4427772 * 2
def baseEnd_4427772 : Nat := 757858421506518518462351

theorem tailTrace_4427772 : CollatzResearch.WordTrace tailWord_4427772 prefixEnd_4427772 757858421506518518462351 := by
  unfold tailWord_4427772
  simp only [CollatzResearch.WordTrace]
  refine ⟨80747056057472861049146785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107662741409963814732195713 80747056057472861049146785)
  ·
    refine ⟨60560292043104645786860089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80747056057472861049146785 60560292043104645786860089)
    ·
      refine ⟨45420219032328484340145067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60560292043104645786860089 45420219032328484340145067)
      ·
        refine ⟨68130328548492726510217601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45420219032328484340145067 68130328548492726510217601)
        ·
          refine ⟨51097746411369544882663201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68130328548492726510217601 51097746411369544882663201)
          ·
            refine ⟨38323309808527158661997401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51097746411369544882663201 38323309808527158661997401)
            ·
              refine ⟨28742482356395368996498051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38323309808527158661997401 28742482356395368996498051)
              ·
                refine ⟨43113723534593053494747077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28742482356395368996498051 43113723534593053494747077)
                ·
                  refine ⟨8083823162736197530265077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43113723534593053494747077 8083823162736197530265077)
                  ·
                    refine ⟨757858421506518518462351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8083823162736197530265077 757858421506518518462351)
                    ·
                      rfl

theorem cell23_4427772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 4, 5].length) (baseStart_4427772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4427772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4427772 prefixEnd_4427772 := by exact prefixLift 4427772
  have htrace : WordTrace (prefixWord ++ tailWord_4427772) baseStart_4427772 baseEnd_4427772 := by
    simpa [prefixWord, tailWord_4427772, baseEnd_4427772] using wordTrace_append hprefix tailTrace_4427772
  have hstable : (prefixWord ++ tailWord_4427772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4427772).length < 2 ^ (prefixWord ++ tailWord_4427772).sum := by decide
  have hdescent : baseEnd_4427772 < baseStart_4427772 := by decide
  rcases family_descends (prefixWord ++ tailWord_4427772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4427792 : List Nat := [2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 4]
def baseStart_4427792 : Nat := 118140960795 + 4427792 * 2 ^ 59
def prefixEnd_4427792 : Nat := 4983230072969 + 3 ^ 40 * 4427792 * 2
def baseEnd_4427792 : Nat := 2273585534132645477136961

theorem tailTrace_4427792 : CollatzResearch.WordTrace tailWord_4427792 prefixEnd_4427792 2273585534132645477136961 := by
  unfold tailWord_4427792
  simp only [CollatzResearch.WordTrace]
  refine ⟨80747420787436632757010815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107663227716582177009347753 80747420787436632757010815)
  ·
    refine ⟨121121131181154949135516223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80747420787436632757010815 121121131181154949135516223)
    ·
      refine ⟨181681696771732423703274335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121121131181154949135516223 181681696771732423703274335)
      ·
        refine ⟨272522545157598635554911503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181681696771732423703274335 272522545157598635554911503)
        ·
          refine ⟨408783817736397953332367255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 272522545157598635554911503 408783817736397953332367255)
          ·
            refine ⟨613175726604596929998550883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 408783817736397953332367255 613175726604596929998550883)
            ·
              refine ⟨919763589906895394997826325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 613175726604596929998550883 919763589906895394997826325)
              ·
                refine ⟨43113918276885721640523109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 919763589906895394997826325 43113918276885721640523109)
                ·
                  refine ⟨8083859676916072807598083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43113918276885721640523109 8083859676916072807598083)
                  ·
                    refine ⟨12125789515374109211397125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8083859676916072807598083 12125789515374109211397125)
                    ·
                      refine ⟨2273585534132645477136961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12125789515374109211397125 2273585534132645477136961)
                      ·
                        rfl

theorem cell23_4427792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 4].length) (baseStart_4427792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4427792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4427792 prefixEnd_4427792 := by exact prefixLift 4427792
  have htrace : WordTrace (prefixWord ++ tailWord_4427792) baseStart_4427792 baseEnd_4427792 := by
    simpa [prefixWord, tailWord_4427792, baseEnd_4427792] using wordTrace_append hprefix tailTrace_4427792
  have hstable : (prefixWord ++ tailWord_4427792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4427792).length < 2 ^ (prefixWord ++ tailWord_4427792).sum := by decide
  have hdescent : baseEnd_4427792 < baseStart_4427792 := by decide
  rcases family_descends (prefixWord ++ tailWord_4427792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4427829 : List Nat := [1, 3, 3, 1, 1, 1, 3, 1, 4, 2, 3]
def baseStart_4427829 : Nat := 118140960795 + 4427829 * 2 ^ 59
def prefixEnd_4427829 : Nat := 4983230072969 + 3 ^ 40 * 4427829 * 2
def baseEnd_4427829 : Nat := 2273604532916861832374291

theorem tailTrace_4427829 : CollatzResearch.WordTrace tailWord_4427829 prefixEnd_4427829 2273604532916861832374291 := by
  unfold tailWord_4427829
  simp only [CollatzResearch.WordTrace]
  refine ⟨161496191075739220833118541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107664127383826147222079027 161496191075739220833118541)
  ·
    refine ⟨60561071653402207812419453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 161496191075739220833118541 60561071653402207812419453)
    ·
      refine ⟨22710401870025827929657295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60561071653402207812419453 22710401870025827929657295)
      ·
        refine ⟨34065602805038741894485943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22710401870025827929657295 34065602805038741894485943)
        ·
          refine ⟨51098404207558112841728915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34065602805038741894485943 51098404207558112841728915)
          ·
            refine ⟨76647606311337169262593373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51098404207558112841728915 76647606311337169262593373)
            ·
              refine ⟨28742852366751438473472515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76647606311337169262593373 28742852366751438473472515)
              ·
                refine ⟨43114278550127157710208773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28742852366751438473472515 43114278550127157710208773)
                ·
                  refine ⟨8083927228148842070664145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43114278550127157710208773 8083927228148842070664145)
                  ·
                    refine ⟨6062945421111631552998109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8083927228148842070664145 6062945421111631552998109)
                    ·
                      refine ⟨2273604532916861832374291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6062945421111631552998109 2273604532916861832374291)
                      ·
                        rfl

theorem cell23_4427829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 4, 2, 3].length) (baseStart_4427829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4427829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4427829 prefixEnd_4427829 := by exact prefixLift 4427829
  have htrace : WordTrace (prefixWord ++ tailWord_4427829) baseStart_4427829 baseEnd_4427829 := by
    simpa [prefixWord, tailWord_4427829, baseEnd_4427829] using wordTrace_append hprefix tailTrace_4427829
  have hstable : (prefixWord ++ tailWord_4427829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4427829).length < 2 ^ (prefixWord ++ tailWord_4427829).sum := by decide
  have hdescent : baseEnd_4427829 < baseStart_4427829 := by decide
  rcases family_descends (prefixWord ++ tailWord_4427829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4427852 : List Nat := [2, 2, 1, 3, 1, 1, 2, 2, 1, 2, 6]
def baseStart_4427852 : Nat := 118140960795 + 4427852 * 2 ^ 59
def prefixEnd_4427852 : Nat := 4983230072969 + 3 ^ 40 * 4427852 * 2
def baseEnd_4427852 : Nat := 2273616342971915242386685

theorem tailTrace_4427852 : CollatzResearch.WordTrace tailWord_4427852 prefixEnd_4427852 2273616342971915242386685 := by
  unfold tailWord_4427852
  simp only [CollatzResearch.WordTrace]
  refine ⟨80748514977327947880602905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107664686636437263840803873 80748514977327947880602905)
  ·
    refine ⟨60561386232995960910452179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80748514977327947880602905 60561386232995960910452179)
    ·
      refine ⟨90842079349493941365678269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60561386232995960910452179 90842079349493941365678269)
      ·
        refine ⟨34065779756060228012129351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90842079349493941365678269 34065779756060228012129351)
        ·
          refine ⟨51098669634090342018194027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34065779756060228012129351 51098669634090342018194027)
          ·
            refine ⟨76648004451135513027291041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51098669634090342018194027 76648004451135513027291041)
            ·
              refine ⟨57486003338351634770468281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76648004451135513027291041 57486003338351634770468281)
              ·
                refine ⟨43114502503763726077851211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57486003338351634770468281 43114502503763726077851211)
                ·
                  refine ⟨64671753755645589116776817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43114502503763726077851211 64671753755645589116776817)
                  ·
                    refine ⟨48503815316734191837582613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 64671753755645589116776817 48503815316734191837582613)
                    ·
                      refine ⟨2273616342971915242386685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48503815316734191837582613 2273616342971915242386685)
                      ·
                        rfl

theorem cell23_4427852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_4427852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4427852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4427852 prefixEnd_4427852 := by exact prefixLift 4427852
  have htrace : WordTrace (prefixWord ++ tailWord_4427852) baseStart_4427852 baseEnd_4427852 := by
    simpa [prefixWord, tailWord_4427852, baseEnd_4427852] using wordTrace_append hprefix tailTrace_4427852
  have hstable : (prefixWord ++ tailWord_4427852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4427852).length < 2 ^ (prefixWord ++ tailWord_4427852).sum := by decide
  have hdescent : baseEnd_4427852 < baseStart_4427852 := by decide
  rcases family_descends (prefixWord ++ tailWord_4427852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4427899 : List Nat := [1, 1, 1, 1, 1, 4, 1, 1, 4, 6, 2]
def baseStart_4427899 : Nat := 118140960795 + 4427899 * 2 ^ 59
def prefixEnd_4427899 : Nat := 4983230072969 + 3 ^ 40 * 4427899 * 2
def baseEnd_4427899 : Nat := 2273640476562676558498969

theorem tailTrace_4427899 : CollatzResearch.WordTrace tailWord_4427899 prefixEnd_4427899 2273640476562676558498969 := by
  unfold tailWord_4427899
  simp only [CollatzResearch.WordTrace]
  refine ⟨161498744185485622788166751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107665829456990415192111167 161498744185485622788166751)
  ·
    refine ⟨242248116278228434182250127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161498744185485622788166751 242248116278228434182250127)
    ·
      refine ⟨363372174417342651273375191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242248116278228434182250127 363372174417342651273375191)
      ·
        refine ⟨545058261626013976910062787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 363372174417342651273375191 545058261626013976910062787)
        ·
          refine ⟨817587392439020965365094181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 545058261626013976910062787 817587392439020965365094181)
          ·
            refine ⟨153297636082316431005955159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 817587392439020965365094181 153297636082316431005955159)
            ·
              refine ⟨229946454123474646508932739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 153297636082316431005955159 229946454123474646508932739)
              ·
                refine ⟨344919681185211969763399109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 229946454123474646508932739 344919681185211969763399109)
                ·
                  refine ⟨64672440222227244330637333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 344919681185211969763399109 64672440222227244330637333)
                  ·
                    refine ⟨3031520635416902077998625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 64672440222227244330637333 3031520635416902077998625)
                    ·
                      refine ⟨2273640476562676558498969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3031520635416902077998625 2273640476562676558498969)
                      ·
                        rfl

theorem cell23_4427899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 6, 2].length) (baseStart_4427899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4427899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4427899 prefixEnd_4427899 := by exact prefixLift 4427899
  have htrace : WordTrace (prefixWord ++ tailWord_4427899) baseStart_4427899 baseEnd_4427899 := by
    simpa [prefixWord, tailWord_4427899, baseEnd_4427899] using wordTrace_append hprefix tailTrace_4427899
  have hstable : (prefixWord ++ tailWord_4427899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4427899).length < 2 ^ (prefixWord ++ tailWord_4427899).sum := by decide
  have hdescent : baseEnd_4427899 < baseStart_4427899 := by decide
  rcases family_descends (prefixWord ++ tailWord_4427899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4427909 : List Nat := [1, 3, 1, 1, 5, 1, 1, 3, 1, 6]
def baseStart_4427909 : Nat := 118140960795 + 4427909 * 2 ^ 59
def prefixEnd_4427909 : Nat := 4983230072969 + 3 ^ 40 * 4427909 * 2
def baseEnd_4427909 : Nat := 757881870456407173124641

theorem tailTrace_4427909 : CollatzResearch.WordTrace tailWord_4427909 prefixEnd_4427909 757881870456407173124641 := by
  unfold tailWord_4427909
  simp only [CollatzResearch.WordTrace]
  refine ⟨161499108915449394496030781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107666072610299596330687187 161499108915449394496030781)
  ·
    refine ⟨60562165843293522936011543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 161499108915449394496030781 60562165843293522936011543)
    ·
      refine ⟨90843248764940284404017315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60562165843293522936011543 90843248764940284404017315)
      ·
        refine ⟨136264873147410426606025973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90843248764940284404017315 136264873147410426606025973)
        ·
          refine ⟨12774831857569727494314935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 136264873147410426606025973 12774831857569727494314935)
          ·
            refine ⟨19162247786354591241472403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12774831857569727494314935 19162247786354591241472403)
            ·
              refine ⟨28743371679531886862208605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19162247786354591241472403 28743371679531886862208605)
              ·
                refine ⟨10778764379824457573328227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28743371679531886862208605 10778764379824457573328227)
                ·
                  refine ⟨16168146569736686359992341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10778764379824457573328227 16168146569736686359992341)
                  ·
                    refine ⟨757881870456407173124641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16168146569736686359992341 757881870456407173124641)
                    ·
                      rfl

theorem cell23_4427909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 3, 1, 6].length) (baseStart_4427909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4427909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4427909 prefixEnd_4427909 := by exact prefixLift 4427909
  have htrace : WordTrace (prefixWord ++ tailWord_4427909) baseStart_4427909 baseEnd_4427909 := by
    simpa [prefixWord, tailWord_4427909, baseEnd_4427909] using wordTrace_append hprefix tailTrace_4427909
  have hstable : (prefixWord ++ tailWord_4427909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4427909).length < 2 ^ (prefixWord ++ tailWord_4427909).sum := by decide
  have hdescent : baseEnd_4427909 < baseStart_4427909 := by decide
  rcases family_descends (prefixWord ++ tailWord_4427909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4427930 : List Nat := [3, 1, 1, 5, 2, 2, 2, 1, 1, 5]
def baseStart_4427930 : Nat := 118140960795 + 4427930 * 2 ^ 59
def prefixEnd_4427930 : Nat := 4983230072969 + 3 ^ 40 * 4427930 * 2
def baseEnd_4427930 : Nat := 757885464820988645737109

theorem tailTrace_4427930 : CollatzResearch.WordTrace tailWord_4427930 prefixEnd_4427930 757885464820988645737109 := by
  unfold tailWord_4427930
  simp only [CollatzResearch.WordTrace]
  refine ⟨40374968712093328770636311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107666583232248876721696829 40374968712093328770636311)
  ·
    refine ⟨60562453068139993155954467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40374968712093328770636311 60562453068139993155954467)
    ·
      refine ⟨90843679602209989733931701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60562453068139993155954467 90843679602209989733931701)
      ·
        refine ⟨8516594962707186537556097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 90843679602209989733931701 8516594962707186537556097)
        ·
          refine ⟨6387446222030389903167073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8516594962707186537556097 6387446222030389903167073)
          ·
            refine ⟨4790584666522792427375305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6387446222030389903167073 4790584666522792427375305)
            ·
              refine ⟨3592938499892094320531479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4790584666522792427375305 3592938499892094320531479)
              ·
                refine ⟨5389407749838141480797219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3592938499892094320531479 5389407749838141480797219)
                ·
                  refine ⟨8084111624757212221195829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5389407749838141480797219 8084111624757212221195829)
                  ·
                    refine ⟨757885464820988645737109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8084111624757212221195829 757885464820988645737109)
                    ·
                      rfl

theorem cell23_4427930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 2, 1, 1, 5].length) (baseStart_4427930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4427930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4427930 prefixEnd_4427930 := by exact prefixLift 4427930
  have htrace : WordTrace (prefixWord ++ tailWord_4427930) baseStart_4427930 baseEnd_4427930 := by
    simpa [prefixWord, tailWord_4427930, baseEnd_4427930] using wordTrace_append hprefix tailTrace_4427930
  have hstable : (prefixWord ++ tailWord_4427930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4427930).length < 2 ^ (prefixWord ++ tailWord_4427930).sum := by decide
  have hdescent : baseEnd_4427930 < baseStart_4427930 := by decide
  rcases family_descends (prefixWord ++ tailWord_4427930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4427933 : List Nat := [1, 4, 2, 1, 1, 3, 4, 1, 1, 1, 4]
def baseStart_4427933 : Nat := 118140960795 + 4427933 * 2 ^ 59
def prefixEnd_4427933 : Nat := 4983230072969 + 3 ^ 40 * 4427933 * 2
def baseEnd_4427933 : Nat := 2273657934904929425473813

theorem tailTrace_4427933 : CollatzResearch.WordTrace tailWord_4427933 prefixEnd_4427933 2273657934904929425473813 := by
  unfold tailWord_4427933
  simp only [CollatzResearch.WordTrace]
  refine ⟨161499984267362446594904453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107666656178241631063269635 161499984267362446594904453)
  ·
    refine ⟨30281247050130458736544585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 161499984267362446594904453 30281247050130458736544585)
    ·
      refine ⟨22710935287597844052408439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30281247050130458736544585 22710935287597844052408439)
      ·
        refine ⟨34066402931396766078612659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22710935287597844052408439 34066402931396766078612659)
        ·
          refine ⟨51099604397095149117918989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34066402931396766078612659 51099604397095149117918989)
          ·
            refine ⟨19162351648910680919219621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51099604397095149117918989 19162351648910680919219621)
            ·
              refine ⟨3592940934170752672353679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19162351648910680919219621 3592940934170752672353679)
              ·
                refine ⟨5389411401256129008530519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3592940934170752672353679 5389411401256129008530519)
                ·
                  refine ⟨8084117101884193512795779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5389411401256129008530519 8084117101884193512795779)
                  ·
                    refine ⟨12126175652826290269193669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8084117101884193512795779 12126175652826290269193669)
                    ·
                      refine ⟨2273657934904929425473813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12126175652826290269193669 2273657934904929425473813)
                      ·
                        rfl

theorem cell23_4427933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 4, 1, 1, 1, 4].length) (baseStart_4427933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4427933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4427933 prefixEnd_4427933 := by exact prefixLift 4427933
  have htrace : WordTrace (prefixWord ++ tailWord_4427933) baseStart_4427933 baseEnd_4427933 := by
    simpa [prefixWord, tailWord_4427933, baseEnd_4427933] using wordTrace_append hprefix tailTrace_4427933
  have hstable : (prefixWord ++ tailWord_4427933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4427933).length < 2 ^ (prefixWord ++ tailWord_4427933).sum := by decide
  have hdescent : baseEnd_4427933 < baseStart_4427933 := by decide
  rcases family_descends (prefixWord ++ tailWord_4427933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4427943 : List Nat := [1, 1, 6, 2, 2, 1, 1, 1, 4, 4]
def baseStart_4427943 : Nat := 118140960795 + 4427943 * 2 ^ 59
def prefixEnd_4427943 : Nat := 4983230072969 + 3 ^ 40 * 4427943 * 2
def baseEnd_4427943 : Nat := 757887689903824795449589

theorem tailTrace_4427943 : CollatzResearch.WordTrace tailWord_4427943 prefixEnd_4427943 757887689903824795449589 := by
  unfold tailWord_4427943
  simp only [CollatzResearch.WordTrace]
  refine ⟨161500348997326218302768483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107666899331550812201845655 161500348997326218302768483)
  ·
    refine ⟨242250523495989327454152725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161500348997326218302768483 242250523495989327454152725)
    ·
      refine ⟨11355493288874499724413409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 242250523495989327454152725 11355493288874499724413409)
      ·
        refine ⟨8516619966655874793310057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11355493288874499724413409 8516619966655874793310057)
        ·
          refine ⟨6387464974991906094982543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8516619966655874793310057 6387464974991906094982543)
          ·
            refine ⟨9581197462487859142473815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6387464974991906094982543 9581197462487859142473815)
            ·
              refine ⟨14371796193731788713710723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9581197462487859142473815 14371796193731788713710723)
              ·
                refine ⟨21557694290597683070566085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14371796193731788713710723 21557694290597683070566085)
                ·
                  refine ⟨4042067679487065575731141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21557694290597683070566085 4042067679487065575731141)
                  ·
                    refine ⟨757887689903824795449589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4042067679487065575731141 757887689903824795449589)
                    ·
                      rfl

theorem cell23_4427943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_4427943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4427943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4427943 prefixEnd_4427943 := by exact prefixLift 4427943
  have htrace : WordTrace (prefixWord ++ tailWord_4427943) baseStart_4427943 baseEnd_4427943 := by
    simpa [prefixWord, tailWord_4427943, baseEnd_4427943] using wordTrace_append hprefix tailTrace_4427943
  have hstable : (prefixWord ++ tailWord_4427943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4427943).length < 2 ^ (prefixWord ++ tailWord_4427943).sum := by decide
  have hdescent : baseEnd_4427943 < baseStart_4427943 := by decide
  rcases family_descends (prefixWord ++ tailWord_4427943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4427993 : List Nat := [1, 2, 1, 2, 3, 1, 4, 3, 1, 3, 2]
def baseStart_4427993 : Nat := 118140960795 + 4427993 * 2 ^ 59
def prefixEnd_4427993 : Nat := 4983230072969 + 3 ^ 40 * 4427993 * 2
def baseEnd_4427993 : Nat := 2273688743744199190723537

theorem tailTrace_4427993 : CollatzResearch.WordTrace tailWord_4427993 prefixEnd_4427993 2273688743744199190723537 := by
  unfold tailWord_4427993
  simp only [CollatzResearch.WordTrace]
  refine ⟨161502172647145076842088633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107668115098096717894725755 161502172647145076842088633)
  ·
    refine ⟨121126629485358807631566475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161502172647145076842088633 121126629485358807631566475)
    ·
      refine ⟨181689944228038211447349713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121126629485358807631566475 181689944228038211447349713)
      ·
        refine ⟨136267458171028658585512285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 181689944228038211447349713 136267458171028658585512285)
        ·
          refine ⟨51100296814135746969567107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 136267458171028658585512285 51100296814135746969567107)
          ·
            refine ⟨76650445221203620454350661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51100296814135746969567107 76650445221203620454350661)
            ·
              refine ⟨14371958478975678835190749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 76650445221203620454350661 14371958478975678835190749)
              ·
                refine ⟨5389484429615879563196531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14371958478975678835190749 5389484429615879563196531)
                ·
                  refine ⟨8084226644423819344794797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5389484429615879563196531 8084226644423819344794797)
                  ·
                    refine ⟨3031584991658932254298049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8084226644423819344794797 3031584991658932254298049)
                    ·
                      refine ⟨2273688743744199190723537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3031584991658932254298049 2273688743744199190723537)
                      ·
                        rfl

theorem cell23_4427993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 3, 1, 3, 2].length) (baseStart_4427993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4427993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4427993 prefixEnd_4427993 := by exact prefixLift 4427993
  have htrace : WordTrace (prefixWord ++ tailWord_4427993) baseStart_4427993 baseEnd_4427993 := by
    simpa [prefixWord, tailWord_4427993, baseEnd_4427993] using wordTrace_append hprefix tailTrace_4427993
  have hstable : (prefixWord ++ tailWord_4427993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4427993).length < 2 ^ (prefixWord ++ tailWord_4427993).sum := by decide
  have hdescent : baseEnd_4427993 < baseStart_4427993 := by decide
  rcases family_descends (prefixWord ++ tailWord_4427993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4428009 : List Nat := [1, 2, 1, 1, 1, 2, 2, 3, 1, 6, 3]
def baseStart_4428009 : Nat := 118140960795 + 4428009 * 2 ^ 59
def prefixEnd_4428009 : Nat := 4983230072969 + 3 ^ 40 * 4428009 * 2
def baseEnd_4428009 : Nat := 2273696959434671128123463

theorem tailTrace_4428009 : CollatzResearch.WordTrace tailWord_4428009 prefixEnd_4428009 2273696959434671128123463 := by
  unfold tailWord_4428009
  simp only [CollatzResearch.WordTrace]
  refine ⟨161502756215087111574671081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107668504143391407716447387 161502756215087111574671081)
  ·
    refine ⟨121127067161315333681003311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161502756215087111574671081 121127067161315333681003311)
    ·
      refine ⟨181690600741973000521504967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121127067161315333681003311 181690600741973000521504967)
      ·
        refine ⟨272535901112959500782257451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181690600741973000521504967 272535901112959500782257451)
        ·
          refine ⟨408803851669439251173386177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 272535901112959500782257451 408803851669439251173386177)
          ·
            refine ⟨306602888752079438380039633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 408803851669439251173386177 306602888752079438380039633)
            ·
              refine ⟨229952166564059578785029725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 306602888752079438380039633 229952166564059578785029725)
              ·
                refine ⟨86232062461522342044386147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 229952166564059578785029725 86232062461522342044386147)
                ·
                  refine ⟨129348093692283513066579221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 86232062461522342044386147 129348093692283513066579221)
                  ·
                    refine ⟨6063191891825789674995901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 129348093692283513066579221 6063191891825789674995901)
                    ·
                      refine ⟨2273696959434671128123463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6063191891825789674995901 2273696959434671128123463)
                      ·
                        rfl

theorem cell23_4428009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 6, 3].length) (baseStart_4428009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4428009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4428009 prefixEnd_4428009 := by exact prefixLift 4428009
  have htrace : WordTrace (prefixWord ++ tailWord_4428009) baseStart_4428009 baseEnd_4428009 := by
    simpa [prefixWord, tailWord_4428009, baseEnd_4428009] using wordTrace_append hprefix tailTrace_4428009
  have hstable : (prefixWord ++ tailWord_4428009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4428009).length < 2 ^ (prefixWord ++ tailWord_4428009).sum := by decide
  have hdescent : baseEnd_4428009 < baseStart_4428009 := by decide
  rcases family_descends (prefixWord ++ tailWord_4428009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4428019 : List Nat := [1, 1, 1, 2, 2, 4, 2, 1, 1, 4, 4]
def baseStart_4428019 : Nat := 118140960795 + 4428019 * 2 ^ 59
def prefixEnd_4428019 : Nat := 4983230072969 + 3 ^ 40 * 4428019 * 2
def baseEnd_4428019 : Nat := 2273702094241216088998417

theorem tailTrace_4428019 : CollatzResearch.WordTrace tailWord_4428019 prefixEnd_4428019 2273702094241216088998417 := by
  unfold tailWord_4428019
  simp only [CollatzResearch.WordTrace]
  refine ⟨161503120945050883282535111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107668747296700588855023407 161503120945050883282535111)
  ·
    refine ⟨242254681417576324923802667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161503120945050883282535111 242254681417576324923802667)
    ·
      refine ⟨363382022126364487385704001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242254681417576324923802667 363382022126364487385704001)
      ·
        refine ⟨272536516594773365539278001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 363382022126364487385704001 272536516594773365539278001)
        ·
          refine ⟨204402387446080024154458501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 272536516594773365539278001 204402387446080024154458501)
          ·
            refine ⟨38325447646140004528960969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 204402387446080024154458501 38325447646140004528960969)
            ·
              refine ⟨28744085734605003396720727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38325447646140004528960969 28744085734605003396720727)
              ·
                refine ⟨43116128601907505095081091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28744085734605003396720727 43116128601907505095081091)
                ·
                  refine ⟨64674192902861257642621637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43116128601907505095081091 64674192902861257642621637)
                  ·
                    refine ⟨12126411169286485807991557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 64674192902861257642621637 12126411169286485807991557)
                    ·
                      refine ⟨2273702094241216088998417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12126411169286485807991557 2273702094241216088998417)
                      ·
                        rfl

theorem cell23_4428019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 4, 4].length) (baseStart_4428019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4428019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4428019 prefixEnd_4428019 := by exact prefixLift 4428019
  have htrace : WordTrace (prefixWord ++ tailWord_4428019) baseStart_4428019 baseEnd_4428019 := by
    simpa [prefixWord, tailWord_4428019, baseEnd_4428019] using wordTrace_append hprefix tailTrace_4428019
  have hstable : (prefixWord ++ tailWord_4428019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4428019).length < 2 ^ (prefixWord ++ tailWord_4428019).sum := by decide
  have hdescent : baseEnd_4428019 < baseStart_4428019 := by decide
  rcases family_descends (prefixWord ++ tailWord_4428019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4428029 : List Nat := [1, 4, 1, 1, 1, 1, 1, 6, 7]
def baseStart_4428029 : Nat := 118140960795 + 4428029 * 2 ^ 59
def prefixEnd_4428029 : Nat := 4983230072969 + 3 ^ 40 * 4428029 * 2
def baseEnd_4428029 : Nat := 252634136560862338874819

theorem tailTrace_4428029 : CollatzResearch.WordTrace tailWord_4428029 prefixEnd_4428029 252634136560862338874819 := by
  unfold tailWord_4428029
  simp only [CollatzResearch.WordTrace]
  refine ⟨161503485675014654990399141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107668990450009769993599427 161503485675014654990399141)
  ·
    refine ⟨30281903564065247810699839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 161503485675014654990399141 30281903564065247810699839)
    ·
      refine ⟨45422855346097871716049759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30281903564065247810699839 45422855346097871716049759)
      ·
        refine ⟨68134283019146807574074639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45422855346097871716049759 68134283019146807574074639)
        ·
          refine ⟨102201424528720211361111959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68134283019146807574074639 102201424528720211361111959)
          ·
            refine ⟨153302136793080317041667939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102201424528720211361111959 153302136793080317041667939)
            ·
              refine ⟨229953205189620475562501909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 153302136793080317041667939 229953205189620475562501909)
              ·
                refine ⟨10779056493263459791992277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 229953205189620475562501909 10779056493263459791992277)
                ·
                  refine ⟨252634136560862338874819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10779056493263459791992277 252634136560862338874819)
                  ·
                    rfl

theorem cell23_4428029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 6, 7].length) (baseStart_4428029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4428029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4428029 prefixEnd_4428029 := by exact prefixLift 4428029
  have htrace : WordTrace (prefixWord ++ tailWord_4428029) baseStart_4428029 baseEnd_4428029 := by
    simpa [prefixWord, tailWord_4428029, baseEnd_4428029] using wordTrace_append hprefix tailTrace_4428029
  have hstable : (prefixWord ++ tailWord_4428029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4428029).length < 2 ^ (prefixWord ++ tailWord_4428029).sum := by decide
  have hdescent : baseEnd_4428029 < baseStart_4428029 := by decide
  rcases family_descends (prefixWord ++ tailWord_4428029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4428056 : List Nat := [2, 1, 2, 3, 1, 2, 2, 2, 2, 3, 3]
def baseStart_4428056 : Nat := 118140960795 + 4428056 * 2 ^ 59
def prefixEnd_4428056 : Nat := 4983230072969 + 3 ^ 40 * 4428056 * 2
def baseEnd_4428056 : Nat := 2273721093025432444235747

theorem tailTrace_4428056 : CollatzResearch.WordTrace tailWord_4428056 prefixEnd_4428056 2273721093025432444235747 := by
  unfold tailWord_4428056
  simp only [CollatzResearch.WordTrace]
  refine ⟨80752235222958419300816011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107669646963944559067754681 80752235222958419300816011)
  ·
    refine ⟨121128352834437628951224017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80752235222958419300816011 121128352834437628951224017)
    ·
      refine ⟨90846264625828221713418013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121128352834437628951224017 90846264625828221713418013)
      ·
        refine ⟨34067349234685583142531755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90846264625828221713418013 34067349234685583142531755)
        ·
          refine ⟨51101023852028374713797633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34067349234685583142531755 51101023852028374713797633)
          ·
            refine ⟨38325767889021281035348225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51101023852028374713797633 38325767889021281035348225)
            ·
              refine ⟨28744325916765960776511169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38325767889021281035348225 28744325916765960776511169)
              ·
                refine ⟨21558244437574470582383377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28744325916765960776511169 21558244437574470582383377)
                ·
                  refine ⟨16168683328180852936787533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21558244437574470582383377 16168683328180852936787533)
                  ·
                    refine ⟨6063256248067819851295325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16168683328180852936787533 6063256248067819851295325)
                    ·
                      refine ⟨2273721093025432444235747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6063256248067819851295325 2273721093025432444235747)
                      ·
                        rfl

theorem cell23_4428056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 2, 2, 3, 3].length) (baseStart_4428056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4428056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4428056 prefixEnd_4428056 := by exact prefixLift 4428056
  have htrace : WordTrace (prefixWord ++ tailWord_4428056) baseStart_4428056 baseEnd_4428056 := by
    simpa [prefixWord, tailWord_4428056, baseEnd_4428056] using wordTrace_append hprefix tailTrace_4428056
  have hstable : (prefixWord ++ tailWord_4428056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4428056).length < 2 ^ (prefixWord ++ tailWord_4428056).sum := by decide
  have hdescent : baseEnd_4428056 < baseStart_4428056 := by decide
  rcases family_descends (prefixWord ++ tailWord_4428056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4428063 : List Nat := [1, 1, 2, 4, 3, 2, 1, 4, 5]
def baseStart_4428063 : Nat := 118140960795 + 4428063 * 2 ^ 59
def prefixEnd_4428063 : Nat := 4983230072969 + 3 ^ 40 * 4428063 * 2
def baseEnd_4428063 : Nat := 252636076376668212983135

theorem tailTrace_4428063 : CollatzResearch.WordTrace tailWord_4428063 prefixEnd_4428063 252636076376668212983135 := by
  unfold tailWord_4428063
  simp only [CollatzResearch.WordTrace]
  refine ⟨161504725756891478797136843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107669817171260985864757895 161504725756891478797136843)
  ·
    refine ⟨242257088635337218195705265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161504725756891478797136843 242257088635337218195705265)
    ·
      refine ⟨181692816476502913646778949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 242257088635337218195705265 181692816476502913646778949)
      ·
        refine ⟨34067403089344296308771053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 181692816476502913646778949 34067403089344296308771053)
        ·
          refine ⟨12775276158504111115789145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34067403089344296308771053 12775276158504111115789145)
          ·
            refine ⟨9581457118878083336841859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12775276158504111115789145 9581457118878083336841859)
            ·
              refine ⟨14372185678317125005262789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9581457118878083336841859 14372185678317125005262789)
              ·
                refine ⟨2694784814684460938486773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14372185678317125005262789 2694784814684460938486773)
                ·
                  refine ⟨252636076376668212983135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2694784814684460938486773 252636076376668212983135)
                  ·
                    rfl

theorem cell23_4428063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 4, 5].length) (baseStart_4428063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4428063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4428063 prefixEnd_4428063 := by exact prefixLift 4428063
  have htrace : WordTrace (prefixWord ++ tailWord_4428063) baseStart_4428063 baseEnd_4428063 := by
    simpa [prefixWord, tailWord_4428063, baseEnd_4428063] using wordTrace_append hprefix tailTrace_4428063
  have hstable : (prefixWord ++ tailWord_4428063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4428063).length < 2 ^ (prefixWord ++ tailWord_4428063).sum := by decide
  have hdescent : baseEnd_4428063 < baseStart_4428063 := by decide
  rcases family_descends (prefixWord ++ tailWord_4428063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4428096 : List Nat := [2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 4]
def baseStart_4428096 : Nat := 118140960795 + 4428096 * 2 ^ 59
def prefixEnd_4428096 : Nat := 4983230072969 + 3 ^ 40 * 4428096 * 2
def baseEnd_4428096 : Nat := 2273741632251612287735563

theorem tailTrace_4428096 : CollatzResearch.WordTrace tailWord_4428096 prefixEnd_4428096 2273741632251612287735563 := by
  unfold tailWord_4428096
  simp only [CollatzResearch.WordTrace]
  refine ⟨80752964682885962716544071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107670619577181283622058761 80752964682885962716544071)
  ·
    refine ⟨121129447024328944074816107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80752964682885962716544071 121129447024328944074816107)
    ·
      refine ⟨181694170536493416112224161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121129447024328944074816107 181694170536493416112224161)
      ·
        refine ⟨136270627902370062084168121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 181694170536493416112224161 136270627902370062084168121)
        ·
          refine ⟨102202970926777546563126091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136270627902370062084168121 102202970926777546563126091)
          ·
            refine ⟨153304456390166319844689137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102202970926777546563126091 153304456390166319844689137)
            ·
              refine ⟨114978342292624739883516853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 153304456390166319844689137 114978342292624739883516853)
              ·
                refine ⟨10779219589933569364079705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 114978342292624739883516853 10779219589933569364079705)
                ·
                  refine ⟨8084414692450177023059779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10779219589933569364079705 8084414692450177023059779)
                  ·
                    refine ⟨12126622038675265534589669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8084414692450177023059779 12126622038675265534589669)
                    ·
                      refine ⟨2273741632251612287735563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12126622038675265534589669 2273741632251612287735563)
                      ·
                        rfl

theorem cell23_4428096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 4].length) (baseStart_4428096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4428096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4428096 prefixEnd_4428096 := by exact prefixLift 4428096
  have htrace : WordTrace (prefixWord ++ tailWord_4428096) baseStart_4428096 baseEnd_4428096 := by
    simpa [prefixWord, tailWord_4428096, baseEnd_4428096] using wordTrace_append hprefix tailTrace_4428096
  have hstable : (prefixWord ++ tailWord_4428096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4428096).length < 2 ^ (prefixWord ++ tailWord_4428096).sum := by decide
  have hdescent : baseEnd_4428096 < baseStart_4428096 := by decide
  rcases family_descends (prefixWord ++ tailWord_4428096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4428113 : List Nat := [1, 2, 2, 1, 4, 2, 1, 2, 2, 4, 2]
def baseStart_4428113 : Nat := 118140960795 + 4428113 * 2 ^ 59
def prefixEnd_4428113 : Nat := 4983230072969 + 3 ^ 40 * 4428113 * 2
def baseEnd_4428113 : Nat := 2273750361422738721222985

theorem tailTrace_4428113 : CollatzResearch.WordTrace tailWord_4428113 prefixEnd_4428113 2273750361422738721222985 := by
  unfold tailWord_4428113
  simp only [CollatzResearch.WordTrace]
  refine ⟨161506549406710337336456993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107671032937806891557637995 161506549406710337336456993)
  ·
    refine ⟨121129912055032753002342745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161506549406710337336456993 121129912055032753002342745)
    ·
      refine ⟨90847434041274564751757059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121129912055032753002342745 90847434041274564751757059)
      ·
        refine ⟨136271151061911847127635589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90847434041274564751757059 136271151061911847127635589)
        ·
          refine ⟨25550840824108471336431673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 136271151061911847127635589 25550840824108471336431673)
          ·
            refine ⟨19163130618081353502323755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25550840824108471336431673 19163130618081353502323755)
            ·
              refine ⟨28744695927122030253485633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19163130618081353502323755 28744695927122030253485633)
              ·
                refine ⟨21558521945341522690114225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28744695927122030253485633 21558521945341522690114225)
                ·
                  refine ⟨16168891459006142017585669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21558521945341522690114225 16168891459006142017585669)
                  ·
                    refine ⟨3031667148563651628297313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16168891459006142017585669 3031667148563651628297313)
                    ·
                      refine ⟨2273750361422738721222985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3031667148563651628297313 2273750361422738721222985)
                      ·
                        rfl

theorem cell23_4428113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 2, 2, 4, 2].length) (baseStart_4428113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4428113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4428113 prefixEnd_4428113 := by exact prefixLift 4428113
  have htrace : WordTrace (prefixWord ++ tailWord_4428113) baseStart_4428113 baseEnd_4428113 := by
    simpa [prefixWord, tailWord_4428113, baseEnd_4428113] using wordTrace_append hprefix tailTrace_4428113
  have hstable : (prefixWord ++ tailWord_4428113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4428113).length < 2 ^ (prefixWord ++ tailWord_4428113).sum := by decide
  have hdescent : baseEnd_4428113 < baseStart_4428113 := by decide
  rcases family_descends (prefixWord ++ tailWord_4428113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4428130 : List Nat := [3, 3, 2, 1, 1, 2, 2, 1, 2, 4, 2]
def baseStart_4428130 : Nat := 118140960795 + 4428130 * 2 ^ 59
def prefixEnd_4428130 : Nat := 4983230072969 + 3 ^ 40 * 4428130 * 2
def baseEnd_4428130 : Nat := 2273759090593865154710407

theorem tailTrace_4428130 : CollatzResearch.WordTrace tailWord_4428130 prefixEnd_4428130 2273759090593865154710407 := by
  unfold tailWord_4428130
  simp only [CollatzResearch.WordTrace]
  refine ⟨40376792361912187309956461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107671446298432499493217229 40376792361912187309956461)
  ·
    refine ⟨15141297135717070241233673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40376792361912187309956461 15141297135717070241233673)
    ·
      refine ⟨11355972851787802680925255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15141297135717070241233673 11355972851787802680925255)
      ·
        refine ⟨17033959277681704021387883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11355972851787802680925255 17033959277681704021387883)
        ·
          refine ⟨25550938916522556032081825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17033959277681704021387883 25550938916522556032081825)
          ·
            refine ⟨19163204187391917024061369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25550938916522556032081825 19163204187391917024061369)
            ·
              refine ⟨14372403140543937768046027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19163204187391917024061369 14372403140543937768046027)
              ·
                refine ⟨21558604710815906652069041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14372403140543937768046027 21558604710815906652069041)
                ·
                  refine ⟨16168953533111929989051781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21558604710815906652069041 16168953533111929989051781)
                  ·
                    refine ⟨3031678787458486872947209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16168953533111929989051781 3031678787458486872947209)
                    ·
                      refine ⟨2273759090593865154710407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3031678787458486872947209 2273759090593865154710407)
                      ·
                        rfl

theorem cell23_4428130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 1, 2, 4, 2].length) (baseStart_4428130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4428130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4428130 prefixEnd_4428130 := by exact prefixLift 4428130
  have htrace : WordTrace (prefixWord ++ tailWord_4428130) baseStart_4428130 baseEnd_4428130 := by
    simpa [prefixWord, tailWord_4428130, baseEnd_4428130] using wordTrace_append hprefix tailTrace_4428130
  have hstable : (prefixWord ++ tailWord_4428130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4428130).length < 2 ^ (prefixWord ++ tailWord_4428130).sum := by decide
  have hdescent : baseEnd_4428130 < baseStart_4428130 := by decide
  rcases family_descends (prefixWord ++ tailWord_4428130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4428157 : List Nat := [1, 4, 1, 1, 2, 5, 1, 3, 1, 4]
def baseStart_4428157 : Nat := 118140960795 + 4428157 * 2 ^ 59
def prefixEnd_4428157 : Nat := 4983230072969 + 3 ^ 40 * 4428157 * 2
def baseEnd_4428157 : Nat := 757924318190512183024261

theorem tailTrace_4428157 : CollatzResearch.WordTrace tailWord_4428157 prefixEnd_4428157 757924318190512183024261 := by
  unfold tailWord_4428157
  simp only [CollatzResearch.WordTrace]
  refine ⟨161508154218550932851058725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107672102812367288567372483 161508154218550932851058725)
  ·
    refine ⟨30282778915978299909573511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 161508154218550932851058725 30282778915978299909573511)
    ·
      refine ⟨45424168373967449864360267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30282778915978299909573511 45424168373967449864360267)
      ·
        refine ⟨68136252560951174796540401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45424168373967449864360267 68136252560951174796540401)
        ·
          refine ⟨51102189420713381097405301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68136252560951174796540401 51102189420713381097405301)
          ·
            refine ⟨4790830258191879477881747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 51102189420713381097405301 4790830258191879477881747)
            ·
              refine ⟨7186245387287819216822621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4790830258191879477881747 7186245387287819216822621)
              ·
                refine ⟨2694842020232932206308483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7186245387287819216822621 2694842020232932206308483)
                ·
                  refine ⟨4042263030349398309462725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2694842020232932206308483 4042263030349398309462725)
                  ·
                    refine ⟨757924318190512183024261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4042263030349398309462725 757924318190512183024261)
                    ·
                      rfl

theorem cell23_4428157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 3, 1, 4].length) (baseStart_4428157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4428157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4428157 prefixEnd_4428157 := by exact prefixLift 4428157
  have htrace : WordTrace (prefixWord ++ tailWord_4428157) baseStart_4428157 baseEnd_4428157 := by
    simpa [prefixWord, tailWord_4428157, baseEnd_4428157] using wordTrace_append hprefix tailTrace_4428157
  have hstable : (prefixWord ++ tailWord_4428157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4428157).length < 2 ^ (prefixWord ++ tailWord_4428157).sum := by decide
  have hdescent : baseEnd_4428157 < baseStart_4428157 := by decide
  rcases family_descends (prefixWord ++ tailWord_4428157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4428174 : List Nat := [4, 1, 1, 4, 1, 2, 3, 2, 1, 4]
def baseStart_4428174 : Nat := 118140960795 + 4428174 * 2 ^ 59
def prefixEnd_4428174 : Nat := 4983230072969 + 3 ^ 40 * 4428174 * 2
def baseEnd_4428174 : Nat := 757927227914220994186735

theorem tailTrace_4428174 : CollatzResearch.WordTrace tailWord_4428174 prefixEnd_4428174 757927227914220994186735 := by
  unfold tailWord_4428174
  simp only [CollatzResearch.WordTrace]
  refine ⟨20188596782436168094303447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107672516172992896502951717 20188596782436168094303447)
  ·
    refine ⟨30282895173654252141455171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20188596782436168094303447 30282895173654252141455171)
    ·
      refine ⟨45424342760481378212182757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30282895173654252141455171 45424342760481378212182757)
      ·
        refine ⟨8517064267590258414784267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45424342760481378212182757 8517064267590258414784267)
        ·
          refine ⟨12775596401385387622176401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8517064267590258414784267 12775596401385387622176401)
          ·
            refine ⟨9581697301039040716632301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12775596401385387622176401 9581697301039040716632301)
            ·
              refine ⟨3593136487889640268737113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9581697301039040716632301 3593136487889640268737113)
              ·
                refine ⟨2694852365917230201552835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3593136487889640268737113 2694852365917230201552835)
                ·
                  refine ⟨4042278548875845302329253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2694852365917230201552835 4042278548875845302329253)
                  ·
                    refine ⟨757927227914220994186735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4042278548875845302329253 757927227914220994186735)
                    ·
                      rfl

theorem cell23_4428174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 3, 2, 1, 4].length) (baseStart_4428174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4428174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4428174 prefixEnd_4428174 := by exact prefixLift 4428174
  have htrace : WordTrace (prefixWord ++ tailWord_4428174) baseStart_4428174 baseEnd_4428174 := by
    simpa [prefixWord, tailWord_4428174, baseEnd_4428174] using wordTrace_append hprefix tailTrace_4428174
  have hstable : (prefixWord ++ tailWord_4428174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4428174).length < 2 ^ (prefixWord ++ tailWord_4428174).sum := by decide
  have hdescent : baseEnd_4428174 < baseStart_4428174 := by decide
  rcases family_descends (prefixWord ++ tailWord_4428174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4428200 : List Nat := [2, 1, 6, 1, 1, 2, 1, 1, 3, 5]
def baseStart_4428200 : Nat := 118140960795 + 4428200 * 2 ^ 59
def prefixEnd_4428200 : Nat := 4983230072969 + 3 ^ 40 * 4428200 * 2
def baseEnd_4428200 : Nat := 757931678079893293611695

theorem tailTrace_4428200 : CollatzResearch.WordTrace tailWord_4428200 prefixEnd_4428200 757931678079893293611695 := by
  unfold tailWord_4428200
  simp only [CollatzResearch.WordTrace]
  refine ⟨80754861278697575597437027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107673148371596767463249369 80754861278697575597437027)
  ·
    refine ⟨121132291918046363396155541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80754861278697575597437027 121132291918046363396155541)
    ·
      refine ⟨5678076183658423284194791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 121132291918046363396155541 5678076183658423284194791)
      ·
        refine ⟨8517114275487634926292187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5678076183658423284194791 8517114275487634926292187)
        ·
          refine ⟨12775671413231452389438281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8517114275487634926292187 12775671413231452389438281)
          ·
            refine ⟨9581753559923589292078711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12775671413231452389438281 9581753559923589292078711)
            ·
              refine ⟨14372630339885383938118067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9581753559923589292078711 14372630339885383938118067)
              ·
                refine ⟨21558945509828075907177101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14372630339885383938118067 21558945509828075907177101)
                ·
                  refine ⟨8084604566185528465191413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21558945509828075907177101 8084604566185528465191413)
                  ·
                    refine ⟨757931678079893293611695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8084604566185528465191413 757931678079893293611695)
                    ·
                      rfl

theorem cell23_4428200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_4428200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4428200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4428200 prefixEnd_4428200 := by exact prefixLift 4428200
  have htrace : WordTrace (prefixWord ++ tailWord_4428200) baseStart_4428200 baseEnd_4428200 := by
    simpa [prefixWord, tailWord_4428200, baseEnd_4428200] using wordTrace_append hprefix tailTrace_4428200
  have hstable : (prefixWord ++ tailWord_4428200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4428200).length < 2 ^ (prefixWord ++ tailWord_4428200).sum := by decide
  have hdescent : baseEnd_4428200 < baseStart_4428200 := by decide
  rcases family_descends (prefixWord ++ tailWord_4428200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4428225 : List Nat := [1, 2, 7, 1, 2, 1, 2, 2, 1, 4]
def baseStart_4428225 : Nat := 118140960795 + 4428225 * 2 ^ 59
def prefixEnd_4428225 : Nat := 4983230072969 + 3 ^ 40 * 4428225 * 2
def baseEnd_4428225 : Nat := 757935957085347427674157

theorem tailTrace_4428225 : CollatzResearch.WordTrace tailWord_4428225 prefixEnd_4428225 757935957085347427674157 := by
  unfold tailWord_4428225
  simp only [CollatzResearch.WordTrace]
  refine ⟨161510634382304580464534129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107673756254869720309689419 161510634382304580464534129)
  ·
    refine ⟨121132975786728435348400597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161510634382304580464534129 121132975786728435348400597)
    ·
      refine ⟨2839054120001447703478139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 121132975786728435348400597 2839054120001447703478139)
      ·
        refine ⟨4258581180002171555217209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2839054120001447703478139 4258581180002171555217209)
        ·
          refine ⟨3193935885001628666412907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4258581180002171555217209 3193935885001628666412907)
          ·
            refine ⟨4790903827502442999619361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3193935885001628666412907 4790903827502442999619361)
            ·
              refine ⟨3593177870626832249714521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4790903827502442999619361 3593177870626832249714521)
              ·
                refine ⟨2694883402970124187285891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3593177870626832249714521 2694883402970124187285891)
                ·
                  refine ⟨4042325104455186280928837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2694883402970124187285891 4042325104455186280928837)
                  ·
                    refine ⟨757935957085347427674157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4042325104455186280928837 757935957085347427674157)
                    ·
                      rfl

theorem cell23_4428225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_4428225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4428225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4428225 prefixEnd_4428225 := by exact prefixLift 4428225
  have htrace : WordTrace (prefixWord ++ tailWord_4428225) baseStart_4428225 baseEnd_4428225 := by
    simpa [prefixWord, tailWord_4428225, baseEnd_4428225] using wordTrace_append hprefix tailTrace_4428225
  have hstable : (prefixWord ++ tailWord_4428225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4428225).length < 2 ^ (prefixWord ++ tailWord_4428225).sum := by decide
  have hdescent : baseEnd_4428225 < baseStart_4428225 := by decide
  rcases family_descends (prefixWord ++ tailWord_4428225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4428256 : List Nat := [2, 1, 1, 3, 1, 1, 3, 2, 2, 7]
def baseStart_4428256 : Nat := 118140960795 + 4428256 * 2 ^ 59
def prefixEnd_4428256 : Nat := 4983230072969 + 3 ^ 40 * 4428256 * 2
def baseEnd_4428256 : Nat := 757941263052110553911609

theorem tailTrace_4428256 : CollatzResearch.WordTrace tailWord_4428256 prefixEnd_4428256 757941263052110553911609 := by
  unfold tailWord_4428256
  simp only [CollatzResearch.WordTrace]
  refine ⟨80755882522596136379456311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107674510030128181839275081 80755882522596136379456311)
  ·
    refine ⟨121133823783894204569184467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80755882522596136379456311 121133823783894204569184467)
    ·
      refine ⟨181700735675841306853776701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121133823783894204569184467 181700735675841306853776701)
      ·
        refine ⟨68137775878440490070166263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 181700735675841306853776701 68137775878440490070166263)
        ·
          refine ⟨102206663817660735105249395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68137775878440490070166263 102206663817660735105249395)
          ·
            refine ⟨153309995726491102657874093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102206663817660735105249395 153309995726491102657874093)
            ·
              refine ⟨57491248397434163496702785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 153309995726491102657874093 57491248397434163496702785)
              ·
                refine ⟨43118436298075622622527089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57491248397434163496702785 43118436298075622622527089)
                ·
                  refine ⟨32338827223556716966895317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43118436298075622622527089 32338827223556716966895317)
                  ·
                    refine ⟨757941263052110553911609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32338827223556716966895317 757941263052110553911609)
                    ·
                      rfl

theorem cell23_4428256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 2, 7].length) (baseStart_4428256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4428256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4428256 prefixEnd_4428256 := by exact prefixLift 4428256
  have htrace : WordTrace (prefixWord ++ tailWord_4428256) baseStart_4428256 baseEnd_4428256 := by
    simpa [prefixWord, tailWord_4428256, baseEnd_4428256] using wordTrace_append hprefix tailTrace_4428256
  have hstable : (prefixWord ++ tailWord_4428256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4428256).length < 2 ^ (prefixWord ++ tailWord_4428256).sum := by decide
  have hdescent : baseEnd_4428256 < baseStart_4428256 := by decide
  rcases family_descends (prefixWord ++ tailWord_4428256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4428258 : List Nat := [3, 3, 3, 2, 2, 1, 1, 1, 2, 3, 2]
def baseStart_4428258 : Nat := 118140960795 + 4428258 * 2 ^ 59
def prefixEnd_4428258 : Nat := 4983230072969 + 3 ^ 40 * 4428258 * 2
def baseEnd_4428258 : Nat := 2273824816117640653909819

theorem tailTrace_4428258 : CollatzResearch.WordTrace tailWord_4428258 prefixEnd_4428258 2273824816117640653909819 := by
  unfold tailWord_4428258
  simp only [CollatzResearch.WordTrace]
  refine ⟨40377959497796256775121357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107674558660790018066990285 40377959497796256775121357)
  ·
    refine ⟨15141734811673596290670509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40377959497796256775121357 15141734811673596290670509)
    ·
      refine ⟨5678150554377598609001441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15141734811673596290670509 5678150554377598609001441)
      ·
        refine ⟨4258612915783198956751081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5678150554377598609001441 4258612915783198956751081)
        ·
          refine ⟨3193959686837399217563311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4258612915783198956751081 3193959686837399217563311)
          ·
            refine ⟨4790939530256098826344967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3193959686837399217563311 4790939530256098826344967)
            ·
              refine ⟨7186409295384148239517451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4790939530256098826344967 7186409295384148239517451)
              ·
                refine ⟨10779613943076222359276177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7186409295384148239517451 10779613943076222359276177)
                ·
                  refine ⟨8084710457307166769457133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10779613943076222359276177 8084710457307166769457133)
                  ·
                    refine ⟨3031766421490187538546425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8084710457307166769457133 3031766421490187538546425)
                    ·
                      refine ⟨2273824816117640653909819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3031766421490187538546425 2273824816117640653909819)
                      ·
                        rfl

theorem cell23_4428258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_4428258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4428258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4428258 prefixEnd_4428258 := by exact prefixLift 4428258
  have htrace : WordTrace (prefixWord ++ tailWord_4428258) baseStart_4428258 baseEnd_4428258 := by
    simpa [prefixWord, tailWord_4428258, baseEnd_4428258] using wordTrace_append hprefix tailTrace_4428258
  have hstable : (prefixWord ++ tailWord_4428258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4428258).length < 2 ^ (prefixWord ++ tailWord_4428258).sum := by decide
  have hdescent : baseEnd_4428258 < baseStart_4428258 := by decide
  rcases family_descends (prefixWord ++ tailWord_4428258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4428270 : List Nat := [4, 1, 2, 1, 2, 2, 2, 2, 1, 3, 3]
def baseStart_4428270 : Nat := 118140960795 + 4428270 * 2 ^ 59
def prefixEnd_4428270 : Nat := 4983230072969 + 3 ^ 40 * 4428270 * 2
def baseEnd_4428270 : Nat := 2273830977885494606959763

theorem tailTrace_4428270 : CollatzResearch.WordTrace tailWord_4428270 prefixEnd_4428270 2273830977885494606959763 := by
  unfold tailWord_4428270
  simp only [CollatzResearch.WordTrace]
  refine ⟨20189034458392694143740283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107674850444761035433281509 20189034458392694143740283)
  ·
    refine ⟨30283551687589041215610425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20189034458392694143740283 30283551687589041215610425)
    ·
      refine ⟨22712663765691780911707819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30283551687589041215610425 22712663765691780911707819)
      ·
        refine ⟨34068995648537671367561729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22712663765691780911707819 34068995648537671367561729)
        ·
          refine ⟨25551746736403253525671297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34068995648537671367561729 25551746736403253525671297)
          ·
            refine ⟨19163810052302440144253473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25551746736403253525671297 19163810052302440144253473)
            ·
              refine ⟨14372857539226830108190105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19163810052302440144253473 14372857539226830108190105)
              ·
                refine ⟨10779643154420122581142579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14372857539226830108190105 10779643154420122581142579)
                ·
                  refine ⟨16169464731630183871713869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10779643154420122581142579 16169464731630183871713869)
                  ·
                    refine ⟨6063549274361318951892701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16169464731630183871713869 6063549274361318951892701)
                    ·
                      refine ⟨2273830977885494606959763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6063549274361318951892701 2273830977885494606959763)
                      ·
                        rfl

theorem cell23_4428270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 2, 1, 3, 3].length) (baseStart_4428270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4428270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4428270 prefixEnd_4428270 := by exact prefixLift 4428270
  have htrace : WordTrace (prefixWord ++ tailWord_4428270) baseStart_4428270 baseEnd_4428270 := by
    simpa [prefixWord, tailWord_4428270, baseEnd_4428270] using wordTrace_append hprefix tailTrace_4428270
  have hstable : (prefixWord ++ tailWord_4428270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4428270).length < 2 ^ (prefixWord ++ tailWord_4428270).sum := by decide
  have hdescent : baseEnd_4428270 < baseStart_4428270 := by decide
  rcases family_descends (prefixWord ++ tailWord_4428270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4428330 : List Nat := [3, 1, 4, 1, 1, 3, 1, 1, 2, 1, 5]
def baseStart_4428330 : Nat := 118140960795 + 4428330 * 2 ^ 59
def prefixEnd_4428330 : Nat := 4983230072969 + 3 ^ 40 * 4428330 * 2
def baseEnd_4428330 : Nat := 2273861786724764372209487

theorem tailTrace_4428330 : CollatzResearch.WordTrace tailWord_4428330 prefixEnd_4428330 2273861786724764372209487 := by
  unfold tailWord_4428330
  simp only [CollatzResearch.WordTrace]
  refine ⟨40378616011731045849276611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107676309364616122264737629 40378616011731045849276611)
  ·
    refine ⟨60567924017596568773914917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40378616011731045849276611 60567924017596568773914917)
    ·
      refine ⟨11356485753299356645109047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60567924017596568773914917 11356485753299356645109047)
      ·
        refine ⟨17034728629949034967663571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11356485753299356645109047 17034728629949034967663571)
        ·
          refine ⟨25552092944923552451495357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17034728629949034967663571 25552092944923552451495357)
          ·
            refine ⟨9582034854346332169310759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25552092944923552451495357 9582034854346332169310759)
            ·
              refine ⟨14373052281519498253966139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9582034854346332169310759 14373052281519498253966139)
              ·
                refine ⟨21559578422279247380949209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14373052281519498253966139 21559578422279247380949209)
                ·
                  refine ⟨16169683816709435535711907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21559578422279247380949209 16169683816709435535711907)
                  ·
                    refine ⟨24254525725064153303567861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16169683816709435535711907 24254525725064153303567861)
                    ·
                      refine ⟨2273861786724764372209487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24254525725064153303567861 2273861786724764372209487)
                      ·
                        rfl

theorem cell23_4428330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_4428330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4428330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4428330 prefixEnd_4428330 := by exact prefixLift 4428330
  have htrace : WordTrace (prefixWord ++ tailWord_4428330) baseStart_4428330 baseEnd_4428330 := by
    simpa [prefixWord, tailWord_4428330, baseEnd_4428330] using wordTrace_append hprefix tailTrace_4428330
  have hstable : (prefixWord ++ tailWord_4428330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4428330).length < 2 ^ (prefixWord ++ tailWord_4428330).sum := by decide
  have hdescent : baseEnd_4428330 < baseStart_4428330 := by decide
  rcases family_descends (prefixWord ++ tailWord_4428330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4428383 : List Nat := [1, 1, 2, 3, 1, 1, 1, 5, 1, 3, 4]
def baseStart_4428383 : Nat := 118140960795 + 4428383 * 2 ^ 59
def prefixEnd_4428383 : Nat := 4983230072969 + 3 ^ 40 * 4428383 * 2
def baseEnd_4428383 : Nat := 2273889001199452664846743

theorem tailTrace_4428383 : CollatzResearch.WordTrace tailWord_4428383 prefixEnd_4428383 2273889001199452664846743 := by
  unfold tailWord_4428383
  simp only [CollatzResearch.WordTrace]
  refine ⟨161516397115732173448785803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107677598077154782299190535 161516397115732173448785803)
  ·
    refine ⟨242274595673598260173178705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161516397115732173448785803 242274595673598260173178705)
    ·
      refine ⟨181705946755198695129884029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 242274595673598260173178705 181705946755198695129884029)
      ·
        refine ⟨68139730033199510673706511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 181705946755198695129884029 68139730033199510673706511)
        ·
          refine ⟨102209595049799266010559767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68139730033199510673706511 102209595049799266010559767)
          ·
            refine ⟨153314392574698899015839651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102209595049799266010559767 153314392574698899015839651)
            ·
              refine ⟨229971588862048348523759477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 153314392574698899015839651 229971588862048348523759477)
              ·
                refine ⟨21559836455817032674102451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 229971588862048348523759477 21559836455817032674102451)
                ·
                  refine ⟨32339754683725549011153677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21559836455817032674102451 32339754683725549011153677)
                  ·
                    refine ⟨12127408006397080879182629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32339754683725549011153677 12127408006397080879182629)
                    ·
                      refine ⟨2273889001199452664846743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12127408006397080879182629 2273889001199452664846743)
                      ·
                        rfl

theorem cell23_4428383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 5, 1, 3, 4].length) (baseStart_4428383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4428383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4428383 prefixEnd_4428383 := by exact prefixLift 4428383
  have htrace : WordTrace (prefixWord ++ tailWord_4428383) baseStart_4428383 baseEnd_4428383 := by
    simpa [prefixWord, tailWord_4428383, baseEnd_4428383] using wordTrace_append hprefix tailTrace_4428383
  have hstable : (prefixWord ++ tailWord_4428383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4428383).length < 2 ^ (prefixWord ++ tailWord_4428383).sum := by decide
  have hdescent : baseEnd_4428383 < baseStart_4428383 := by decide
  rcases family_descends (prefixWord ++ tailWord_4428383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4428417 : List Nat := [1, 2, 4, 2, 1, 1, 3, 1, 2, 4, 2]
def baseStart_4428417 : Nat := 118140960795 + 4428417 * 2 ^ 59
def prefixEnd_4428417 : Nat := 4983230072969 + 3 ^ 40 * 4428417 * 2
def baseEnd_4428417 : Nat := 2273906459541705531821587

theorem tailTrace_4428417 : CollatzResearch.WordTrace tailWord_4428417 prefixEnd_4428417 2273906459541705531821587 := by
  unfold tailWord_4428417
  simp only [CollatzResearch.WordTrace]
  refine ⟨161517637197608997255523505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107678424798405998170349003 161517637197608997255523505)
  ·
    refine ⟨121138227898206747941642629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161517637197608997255523505 121138227898206747941642629)
    ·
      refine ⟨22713417730913765239057993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 121138227898206747941642629 22713417730913765239057993)
      ·
        refine ⟨17035063298185323929293495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22713417730913765239057993 17035063298185323929293495)
        ·
          refine ⟨25552594947277985893940243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17035063298185323929293495 25552594947277985893940243)
          ·
            refine ⟨38328892420916978840910365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25552594947277985893940243 38328892420916978840910365)
            ·
              refine ⟨14373334657843867065341387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38328892420916978840910365 14373334657843867065341387)
              ·
                refine ⟨21560001986765800598012081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14373334657843867065341387 21560001986765800598012081)
                ·
                  refine ⟨16170001490074350448509061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21560001986765800598012081 16170001490074350448509061)
                  ·
                    refine ⟨3031875279388940709095449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16170001490074350448509061 3031875279388940709095449)
                    ·
                      refine ⟨2273906459541705531821587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3031875279388940709095449 2273906459541705531821587)
                      ·
                        rfl

theorem cell23_4428417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 1, 2, 4, 2].length) (baseStart_4428417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4428417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4428417 prefixEnd_4428417 := by exact prefixLift 4428417
  have htrace : WordTrace (prefixWord ++ tailWord_4428417) baseStart_4428417 baseEnd_4428417 := by
    simpa [prefixWord, tailWord_4428417, baseEnd_4428417] using wordTrace_append hprefix tailTrace_4428417
  have hstable : (prefixWord ++ tailWord_4428417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4428417).length < 2 ^ (prefixWord ++ tailWord_4428417).sum := by decide
  have hdescent : baseEnd_4428417 < baseStart_4428417 := by decide
  rcases family_descends (prefixWord ++ tailWord_4428417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4428434 : List Nat := [3, 2, 3, 1, 2, 3, 1, 1, 2, 1, 4]
def baseStart_4428434 : Nat := 118140960795 + 4428434 * 2 ^ 59
def prefixEnd_4428434 : Nat := 4983230072969 + 3 ^ 40 * 4428434 * 2
def baseEnd_4428434 : Nat := 2273915188712831965309009

theorem tailTrace_4428434 : CollatzResearch.WordTrace tailWord_4428434 prefixEnd_4428434 2273915188712831965309009 := by
  unfold tailWord_4428434
  simp only [CollatzResearch.WordTrace]
  refine ⟨40379564309636852289723089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107678838159031606105928237 40379564309636852289723089)
  ·
    refine ⟨30284673232227639217292317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40379564309636852289723089 30284673232227639217292317)
    ·
      refine ⟨11356752462085364706484619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30284673232227639217292317 11356752462085364706484619)
      ·
        refine ⟨17035128693128047059726929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11356752462085364706484619 17035128693128047059726929)
        ·
          refine ⟨12776346519846035294795197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17035128693128047059726929 12776346519846035294795197)
          ·
            refine ⟨4791129944942263235548199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12776346519846035294795197 4791129944942263235548199)
            ·
              refine ⟨7186694917413394853322299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4791129944942263235548199 7186694917413394853322299)
              ·
                refine ⟨10780042376120092279983449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7186694917413394853322299 10780042376120092279983449)
                ·
                  refine ⟨8085031782090069209987587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10780042376120092279983449 8085031782090069209987587)
                  ·
                    refine ⟨12127547673135103814981381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8085031782090069209987587 12127547673135103814981381)
                    ·
                      refine ⟨2273915188712831965309009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12127547673135103814981381 2273915188712831965309009)
                      ·
                        rfl

theorem cell23_4428434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_4428434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4428434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4428434 prefixEnd_4428434 := by exact prefixLift 4428434
  have htrace : WordTrace (prefixWord ++ tailWord_4428434) baseStart_4428434 baseEnd_4428434 := by
    simpa [prefixWord, tailWord_4428434, baseEnd_4428434] using wordTrace_append hprefix tailTrace_4428434
  have hstable : (prefixWord ++ tailWord_4428434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4428434).length < 2 ^ (prefixWord ++ tailWord_4428434).sum := by decide
  have hdescent : baseEnd_4428434 < baseStart_4428434 := by decide
  rcases family_descends (prefixWord ++ tailWord_4428434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4428444 : List Nat := [2, 2, 3, 2, 2, 1, 1, 5, 1, 4]
def baseStart_4428444 : Nat := 118140960795 + 4428444 * 2 ^ 59
def prefixEnd_4428444 : Nat := 4983230072969 + 3 ^ 40 * 4428444 * 2
def baseEnd_4428444 : Nat := 757973441173125642061321

theorem tailTrace_4428444 : CollatzResearch.WordTrace tailWord_4428444 prefixEnd_4428444 757973441173125642061321 := by
  unfold tailWord_4428444
  simp only [CollatzResearch.WordTrace]
  refine ⟨80759310984255590433378193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107679081312340787244504257 80759310984255590433378193)
  ·
    refine ⟨60569483238191692825033645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80759310984255590433378193 60569483238191692825033645)
    ·
      refine ⟨22713556214321884809387617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60569483238191692825033645 22713556214321884809387617)
      ·
        refine ⟨17035167160741413607040713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22713556214321884809387617 17035167160741413607040713)
        ·
          refine ⟨12776375370556060205280535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17035167160741413607040713 12776375370556060205280535)
          ·
            refine ⟨19164563055834090307920803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12776375370556060205280535 19164563055834090307920803)
            ·
              refine ⟨28746844583751135461881205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19164563055834090307920803 28746844583751135461881205)
              ·
                refine ⟨2695016679726668949551363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28746844583751135461881205 2695016679726668949551363)
                ·
                  refine ⟨4042525019590003424327045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2695016679726668949551363 4042525019590003424327045)
                  ·
                    refine ⟨757973441173125642061321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4042525019590003424327045 757973441173125642061321)
                    ·
                      rfl

theorem cell23_4428444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 5, 1, 4].length) (baseStart_4428444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4428444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4428444 prefixEnd_4428444 := by exact prefixLift 4428444
  have htrace : WordTrace (prefixWord ++ tailWord_4428444) baseStart_4428444 baseEnd_4428444 := by
    simpa [prefixWord, tailWord_4428444, baseEnd_4428444] using wordTrace_append hprefix tailTrace_4428444
  have hstable : (prefixWord ++ tailWord_4428444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4428444).length < 2 ^ (prefixWord ++ tailWord_4428444).sum := by decide
  have hdescent : baseEnd_4428444 < baseStart_4428444 := by decide
  rcases family_descends (prefixWord ++ tailWord_4428444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4428467 : List Nat := [1, 1, 1, 2, 3, 4, 1, 3, 3, 1, 3]
def baseStart_4428467 : Nat := 118140960795 + 4428467 * 2 ^ 59
def prefixEnd_4428467 : Nat := 4983230072969 + 3 ^ 40 * 4428467 * 2
def baseEnd_4428467 : Nat := 2273932133574430336196357

theorem tailTrace_4428467 : CollatzResearch.WordTrace tailWord_4428467 prefixEnd_4428467 2273932133574430336196357 := by
  unfold tailWord_4428467
  simp only [CollatzResearch.WordTrace]
  refine ⟨161519460847427855794843655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107679640564951903863229103 161519460847427855794843655)
  ·
    refine ⟨242279191271141783692265483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161519460847427855794843655 242279191271141783692265483)
    ·
      refine ⟨363418786906712675538398225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242279191271141783692265483 363418786906712675538398225)
      ·
        refine ⟨272564090180034506653798669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 363418786906712675538398225 272564090180034506653798669)
        ·
          refine ⟨102211533817512939995174501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 272564090180034506653798669 102211533817512939995174501)
          ·
            refine ⟨19164662590783676249095219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 102211533817512939995174501 19164662590783676249095219)
            ·
              refine ⟨28746993886175514373642829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19164662590783676249095219 28746993886175514373642829)
              ·
                refine ⟨10780122707315817890116061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28746993886175514373642829 10780122707315817890116061)
                ·
                  refine ⟨4042546015243431708793523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10780122707315817890116061 4042546015243431708793523)
                  ·
                    refine ⟨6063819022865147563190285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4042546015243431708793523 6063819022865147563190285)
                    ·
                      refine ⟨2273932133574430336196357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6063819022865147563190285 2273932133574430336196357)
                      ·
                        rfl

theorem cell23_4428467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 3, 3, 1, 3].length) (baseStart_4428467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4428467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4428467 prefixEnd_4428467 := by exact prefixLift 4428467
  have htrace : WordTrace (prefixWord ++ tailWord_4428467) baseStart_4428467 baseEnd_4428467 := by
    simpa [prefixWord, tailWord_4428467, baseEnd_4428467] using wordTrace_append hprefix tailTrace_4428467
  have hstable : (prefixWord ++ tailWord_4428467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4428467).length < 2 ^ (prefixWord ++ tailWord_4428467).sum := by decide
  have hdescent : baseEnd_4428467 < baseStart_4428467 := by decide
  rcases family_descends (prefixWord ++ tailWord_4428467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4428477 : List Nat := [1, 4, 1, 2, 1, 3, 1, 2, 1, 5, 2]
def baseStart_4428477 : Nat := 118140960795 + 4428477 * 2 ^ 59
def prefixEnd_4428477 : Nat := 4983230072969 + 3 ^ 40 * 4428477 * 2
def baseEnd_4428477 : Nat := 2273937268380975297071311

theorem tailTrace_4428477 : CollatzResearch.WordTrace tailWord_4428477 prefixEnd_4428477 2273937268380975297071311 := by
  unfold tailWord_4428477
  simp only [CollatzResearch.WordTrace]
  refine ⟨161519825577391627502707685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107679883718261085001805123 161519825577391627502707685)
  ·
    refine ⟨30284967295760930156757691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 161519825577391627502707685 30284967295760930156757691)
    ·
      refine ⟨45427450943641395235136537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30284967295760930156757691 45427450943641395235136537)
      ·
        refine ⟨34070588207731046426352403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45427450943641395235136537 34070588207731046426352403)
        ·
          refine ⟨51105882311596569639528605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34070588207731046426352403 51105882311596569639528605)
          ·
            refine ⟨19164705866848713614823227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51105882311596569639528605 19164705866848713614823227)
            ·
              refine ⟨28747058800273070422234841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19164705866848713614823227 28747058800273070422234841)
              ·
                refine ⟨21560294100204802816676131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28747058800273070422234841 21560294100204802816676131)
                ·
                  refine ⟨32340441150307204225014197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21560294100204802816676131 32340441150307204225014197)
                  ·
                    refine ⟨3031916357841300396095081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32340441150307204225014197 3031916357841300396095081)
                    ·
                      refine ⟨2273937268380975297071311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3031916357841300396095081 2273937268380975297071311)
                      ·
                        rfl

theorem cell23_4428477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 2, 1, 5, 2].length) (baseStart_4428477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4428477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4428477 prefixEnd_4428477 := by exact prefixLift 4428477
  have htrace : WordTrace (prefixWord ++ tailWord_4428477) baseStart_4428477 baseEnd_4428477 := by
    simpa [prefixWord, tailWord_4428477, baseEnd_4428477] using wordTrace_append hprefix tailTrace_4428477
  have hstable : (prefixWord ++ tailWord_4428477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4428477).length < 2 ^ (prefixWord ++ tailWord_4428477).sum := by decide
  have hdescent : baseEnd_4428477 < baseStart_4428477 := by decide
  rcases family_descends (prefixWord ++ tailWord_4428477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4428484 : List Nat := [2, 3, 3, 1, 1, 2, 2, 2, 3, 1, 3]
def baseStart_4428484 : Nat := 118140960795 + 4428484 * 2 ^ 59
def prefixEnd_4428484 : Nat := 4983230072969 + 3 ^ 40 * 4428484 * 2
def baseEnd_4428484 : Nat := 2273940862745556769683779

theorem tailTrace_4428484 : CollatzResearch.WordTrace tailWord_4428484 prefixEnd_4428484 2273940862745556769683779 := by
  unfold tailWord_4428484
  simp only [CollatzResearch.WordTrace]
  refine ⟨80760040444183133849106253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107680053925577511798808337 80760040444183133849106253)
  ·
    refine ⟨30285015166568675193414845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80760040444183133849106253 30285015166568675193414845)
    ·
      refine ⟨11356880687463253197530567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30285015166568675193414845 11356880687463253197530567)
      ·
        refine ⟨17035321031194879796295851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11356880687463253197530567 17035321031194879796295851)
        ·
          refine ⟨25552981546792319694443777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17035321031194879796295851 25552981546792319694443777)
          ·
            refine ⟨19164736160094239770832833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25552981546792319694443777 19164736160094239770832833)
            ·
              refine ⟨14373552120070679828124625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19164736160094239770832833 14373552120070679828124625)
              ·
                refine ⟨10780164090053009871093469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14373552120070679828124625 10780164090053009871093469)
                ·
                  refine ⟨4042561533769878701660051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10780164090053009871093469 4042561533769878701660051)
                  ·
                    refine ⟨6063842300654818052490077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4042561533769878701660051 6063842300654818052490077)
                    ·
                      refine ⟨2273940862745556769683779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6063842300654818052490077 2273940862745556769683779)
                      ·
                        rfl

theorem cell23_4428484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_4428484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4428484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4428484 prefixEnd_4428484 := by exact prefixLift 4428484
  have htrace : WordTrace (prefixWord ++ tailWord_4428484) baseStart_4428484 baseEnd_4428484 := by
    simpa [prefixWord, tailWord_4428484, baseEnd_4428484] using wordTrace_append hprefix tailTrace_4428484
  have hstable : (prefixWord ++ tailWord_4428484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4428484).length < 2 ^ (prefixWord ++ tailWord_4428484).sum := by decide
  have hdescent : baseEnd_4428484 < baseStart_4428484 := by decide
  rcases family_descends (prefixWord ++ tailWord_4428484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4428517 : List Nat := [1, 3, 1, 4, 1, 2, 2, 1, 4, 4]
def baseStart_4428517 : Nat := 118140960795 + 4428517 * 2 ^ 59
def prefixEnd_4428517 : Nat := 4983230072969 + 3 ^ 40 * 4428517 * 2
def baseEnd_4428517 : Nat := 757985935869051713523709

theorem tailTrace_4428517 : CollatzResearch.WordTrace tailWord_4428517 prefixEnd_4428517 757985935869051713523709 := by
  unfold tailWord_4428517
  simp only [CollatzResearch.WordTrace]
  refine ⟨161521284497246714334163805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107680856331497809556109203 161521284497246714334163805)
  ·
    refine ⟨60570481686467517875311427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 161521284497246714334163805 60570481686467517875311427)
    ·
      refine ⟨90855722529701276812967141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60570481686467517875311427 90855722529701276812967141)
      ·
        refine ⟨17035447974318989402431339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 90855722529701276812967141 17035447974318989402431339)
        ·
          refine ⟨25553171961478484103647009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17035447974318989402431339 25553171961478484103647009)
          ·
            refine ⟨19164878971108863077735257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25553171961478484103647009 19164878971108863077735257)
            ·
              refine ⟨14373659228331647308301443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19164878971108863077735257 14373659228331647308301443)
              ·
                refine ⟨21560488842497470962452165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14373659228331647308301443 21560488842497470962452165)
                ·
                  refine ⟨4042591657968275805459781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21560488842497470962452165 4042591657968275805459781)
                  ·
                    refine ⟨757985935869051713523709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4042591657968275805459781 757985935869051713523709)
                    ·
                      rfl

theorem cell23_4428517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 1, 4, 4].length) (baseStart_4428517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4428517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4428517 prefixEnd_4428517 := by exact prefixLift 4428517
  have htrace : WordTrace (prefixWord ++ tailWord_4428517) baseStart_4428517 baseEnd_4428517 := by
    simpa [prefixWord, tailWord_4428517, baseEnd_4428517] using wordTrace_append hprefix tailTrace_4428517
  have hstable : (prefixWord ++ tailWord_4428517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4428517).length < 2 ^ (prefixWord ++ tailWord_4428517).sum := by decide
  have hdescent : baseEnd_4428517 < baseStart_4428517 := by decide
  rcases family_descends (prefixWord ++ tailWord_4428517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4428530 : List Nat := [3, 2, 1, 3, 1, 2, 1, 10]
def baseStart_4428530 : Nat := 118140960795 + 4428530 * 2 ^ 59
def prefixEnd_4428530 : Nat := 4983230072969 + 3 ^ 40 * 4428530 * 2
def baseEnd_4428530 : Nat := 84220906772431984804021

theorem tailTrace_4428530 : CollatzResearch.WordTrace tailWord_4428530 prefixEnd_4428530 84220906772431984804021 := by
  unfold tailWord_4428530
  simp only [CollatzResearch.WordTrace]
  refine ⟨40380439661549904388596761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107681172430799745036258029 40380439661549904388596761)
  ·
    refine ⟨30285329746162428291447571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40380439661549904388596761 30285329746162428291447571)
    ·
      refine ⟨45427994619243642437171357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30285329746162428291447571 45427994619243642437171357)
      ·
        refine ⟨17035497982216365913939259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45427994619243642437171357 17035497982216365913939259)
        ·
          refine ⟨25553246973324548870908889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17035497982216365913939259 25553246973324548870908889)
          ·
            refine ⟨19164935229993411653181667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25553246973324548870908889 19164935229993411653181667)
            ·
              refine ⟨28747402844990117479772501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19164935229993411653181667 28747402844990117479772501)
              ·
                refine ⟨84220906772431984804021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 28747402844990117479772501 84220906772431984804021)
                ·
                  rfl

theorem cell23_4428530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 10].length) (baseStart_4428530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4428530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4428530 prefixEnd_4428530 := by exact prefixLift 4428530
  have htrace : WordTrace (prefixWord ++ tailWord_4428530) baseStart_4428530 baseEnd_4428530 := by
    simpa [prefixWord, tailWord_4428530, baseEnd_4428530] using wordTrace_append hprefix tailTrace_4428530
  have hstable : (prefixWord ++ tailWord_4428530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4428530).length < 2 ^ (prefixWord ++ tailWord_4428530).sum := by decide
  have hdescent : baseEnd_4428530 < baseStart_4428530 := by decide
  rcases family_descends (prefixWord ++ tailWord_4428530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4428534 : List Nat := [5, 1, 1, 1, 1, 2, 3, 3, 2, 4]
def baseStart_4428534 : Nat := 118140960795 + 4428534 * 2 ^ 59
def prefixEnd_4428534 : Nat := 4983230072969 + 3 ^ 40 * 4428534 * 2
def baseEnd_4428534 : Nat := 757988845592760524686183

theorem tailTrace_4428534 : CollatzResearch.WordTrace tailWord_4428534 prefixEnd_4428534 757988845592760524686183 := by
  unfold tailWord_4428534
  simp only [CollatzResearch.WordTrace]
  refine ⟨10095119033636570389845791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 107681269692123417491688437 10095119033636570389845791)
  ·
    refine ⟨15142678550454855584768687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10095119033636570389845791 15142678550454855584768687)
    ·
      refine ⟨22714017825682283377153031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15142678550454855584768687 22714017825682283377153031)
      ·
        refine ⟨34071026738523425065729547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22714017825682283377153031 34071026738523425065729547)
        ·
          refine ⟨51106540107785137598594321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34071026738523425065729547 51106540107785137598594321)
          ·
            refine ⟨38329905080838853198945741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51106540107785137598594321 38329905080838853198945741)
            ·
              refine ⟨14373714405314569949604653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38329905080838853198945741 14373714405314569949604653)
              ·
                refine ⟨5390142901992963731101745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14373714405314569949604653 5390142901992963731101745)
                ·
                  refine ⟨4042607176494722798326309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5390142901992963731101745 4042607176494722798326309)
                  ·
                    refine ⟨757988845592760524686183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4042607176494722798326309 757988845592760524686183)
                    ·
                      rfl

theorem cell23_4428534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 3, 2, 4].length) (baseStart_4428534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4428534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4428534 prefixEnd_4428534 := by exact prefixLift 4428534
  have htrace : WordTrace (prefixWord ++ tailWord_4428534) baseStart_4428534 baseEnd_4428534 := by
    simpa [prefixWord, tailWord_4428534, baseEnd_4428534] using wordTrace_append hprefix tailTrace_4428534
  have hstable : (prefixWord ++ tailWord_4428534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4428534).length < 2 ^ (prefixWord ++ tailWord_4428534).sum := by decide
  have hdescent : baseEnd_4428534 < baseStart_4428534 := by decide
  rcases family_descends (prefixWord ++ tailWord_4428534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4428575 : List Nat := [1, 1, 2, 4, 2, 4, 2, 2, 1, 2, 2]
def baseStart_4428575 : Nat := 118140960795 + 4428575 * 2 ^ 59
def prefixEnd_4428575 : Nat := 4983230072969 + 3 ^ 40 * 4428575 * 2
def baseEnd_4428575 : Nat := 2273987589485115913645861

theorem tailTrace_4428575 : CollatzResearch.WordTrace tailWord_4428575 prefixEnd_4428575 2273987589485115913645861 := by
  unfold tailWord_4428575
  simp only [CollatzResearch.WordTrace]
  refine ⟨161523399931036590239775179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107682266620691060159850119 161523399931036590239775179)
  ·
    refine ⟨242285099896554885359662769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161523399931036590239775179 242285099896554885359662769)
    ·
      refine ⟨181713824922416164019747077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 242285099896554885359662769 181713824922416164019747077)
      ·
        refine ⟨34071342172953030753702577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 181713824922416164019747077 34071342172953030753702577)
        ·
          refine ⟨25553506629714773065276933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34071342172953030753702577 25553506629714773065276933)
          ·
            refine ⟨4791282493071519949739425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25553506629714773065276933 4791282493071519949739425)
            ·
              refine ⟨3593461869803639962304569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4791282493071519949739425 3593461869803639962304569)
              ·
                refine ⟨2695096402352729971728427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3593461869803639962304569 2695096402352729971728427)
                ·
                  refine ⟨4042644603529094957592641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2695096402352729971728427 4042644603529094957592641)
                  ·
                    refine ⟨3031983452646821218194481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4042644603529094957592641 3031983452646821218194481)
                    ·
                      refine ⟨2273987589485115913645861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3031983452646821218194481 2273987589485115913645861)
                      ·
                        rfl

theorem cell23_4428575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 2, 2, 1, 2, 2].length) (baseStart_4428575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4428575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4428575 prefixEnd_4428575 := by exact prefixLift 4428575
  have htrace : WordTrace (prefixWord ++ tailWord_4428575) baseStart_4428575 baseEnd_4428575 := by
    simpa [prefixWord, tailWord_4428575, baseEnd_4428575] using wordTrace_append hprefix tailTrace_4428575
  have hstable : (prefixWord ++ tailWord_4428575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4428575).length < 2 ^ (prefixWord ++ tailWord_4428575).sum := by decide
  have hdescent : baseEnd_4428575 < baseStart_4428575 := by decide
  rcases family_descends (prefixWord ++ tailWord_4428575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4428584 : List Nat := [2, 1, 5, 1, 1, 1, 1, 1, 5, 3, 2]
def baseStart_4428584 : Nat := 118140960795 + 4428584 * 2 ^ 59
def prefixEnd_4428584 : Nat := 4983230072969 + 3 ^ 40 * 4428584 * 2
def baseEnd_4428584 : Nat := 2273992210811006378433319

theorem tailTrace_4428584 : CollatzResearch.WordTrace tailWord_4428584 prefixEnd_4428584 2273992210811006378433319 := by
  unfold tailWord_4428584
  simp only [CollatzResearch.WordTrace]
  refine ⟨80761864094001992388426403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107682485458669323184568537 80761864094001992388426403)
  ·
    refine ⟨121142796141002988582639605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80761864094001992388426403 121142796141002988582639605)
    ·
      refine ⟨11357137138219030179622463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 121142796141002988582639605 11357137138219030179622463)
      ·
        refine ⟨17035705707328545269433695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11357137138219030179622463 17035705707328545269433695)
        ·
          refine ⟨25553558560992817904150543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17035705707328545269433695 25553558560992817904150543)
          ·
            refine ⟨38330337841489226856225815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25553558560992817904150543 38330337841489226856225815)
            ·
              refine ⟨57495506762233840284338723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38330337841489226856225815 57495506762233840284338723)
              ·
                refine ⟨86243260143350760426508085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57495506762233840284338723 86243260143350760426508085)
                ·
                  refine ⟨8085305638439133789985133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 86243260143350760426508085 8085305638439133789985133)
                  ·
                    refine ⟨3031989614414675171244425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8085305638439133789985133 3031989614414675171244425)
                    ·
                      refine ⟨2273992210811006378433319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3031989614414675171244425 2273992210811006378433319)
                      ·
                        rfl

theorem cell23_4428584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 5, 3, 2].length) (baseStart_4428584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4428584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4428584 prefixEnd_4428584 := by exact prefixLift 4428584
  have htrace : WordTrace (prefixWord ++ tailWord_4428584) baseStart_4428584 baseEnd_4428584 := by
    simpa [prefixWord, tailWord_4428584, baseEnd_4428584] using wordTrace_append hprefix tailTrace_4428584
  have hstable : (prefixWord ++ tailWord_4428584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4428584).length < 2 ^ (prefixWord ++ tailWord_4428584).sum := by decide
  have hdescent : baseEnd_4428584 < baseStart_4428584 := by decide
  rcases family_descends (prefixWord ++ tailWord_4428584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4428612 : List Nat := [2, 3, 4, 2, 2, 1, 2, 1, 1, 2, 3]
def baseStart_4428612 : Nat := 118140960795 + 4428612 * 2 ^ 59
def prefixEnd_4428612 : Nat := 4983230072969 + 3 ^ 40 * 4428612 * 2
def baseEnd_4428612 : Nat := 2274006588269332268883191

theorem tailTrace_4428612 : CollatzResearch.WordTrace tailWord_4428612 prefixEnd_4428612 2274006588269332268883191 := by
  unfold tailWord_4428612
  simp only [CollatzResearch.WordTrace]
  refine ⟨80762374715951272779436045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107683166287935030372581393 80762374715951272779436045)
  ·
    refine ⟨30285890518481727292288517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80762374715951272779436045 30285890518481727292288517)
    ·
      refine ⟨5678604472215323867304097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30285890518481727292288517 5678604472215323867304097)
      ·
        refine ⟨4258953354161492900478073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5678604472215323867304097 4258953354161492900478073)
        ·
          refine ⟨3194215015621119675358555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4258953354161492900478073 3194215015621119675358555)
          ·
            refine ⟨4791322523431679513037833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3194215015621119675358555 4791322523431679513037833)
            ·
              refine ⟨3593491892573759634778375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4791322523431679513037833 3593491892573759634778375)
              ·
                refine ⟨5390237838860639452167563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3593491892573759634778375 5390237838860639452167563)
                ·
                  refine ⟨8085356758290959178251345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5390237838860639452167563 8085356758290959178251345)
                  ·
                    refine ⟨6064017568718219383688509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8085356758290959178251345 6064017568718219383688509)
                    ·
                      refine ⟨2274006588269332268883191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6064017568718219383688509 2274006588269332268883191)
                      ·
                        rfl

theorem cell23_4428612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_4428612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4428612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4428612 prefixEnd_4428612 := by exact prefixLift 4428612
  have htrace : WordTrace (prefixWord ++ tailWord_4428612) baseStart_4428612 baseEnd_4428612 := by
    simpa [prefixWord, tailWord_4428612, baseEnd_4428612] using wordTrace_append hprefix tailTrace_4428612
  have hstable : (prefixWord ++ tailWord_4428612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4428612).length < 2 ^ (prefixWord ++ tailWord_4428612).sum := by decide
  have hdescent : baseEnd_4428612 < baseStart_4428612 := by decide
  rcases family_descends (prefixWord ++ tailWord_4428612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4428631 : List Nat := [1, 1, 3, 2, 4, 2, 1, 1, 4, 2, 2]
def baseStart_4428631 : Nat := 118140960795 + 4428631 * 2 ^ 59
def prefixEnd_4428631 : Nat := 4983230072969 + 3 ^ 40 * 4428631 * 2
def baseEnd_4428631 : Nat := 2274016344401767694545603

theorem tailTrace_4428631 : CollatzResearch.WordTrace tailWord_4428631 prefixEnd_4428631 2274016344401767694545603 := by
  unfold tailWord_4428631
  simp only [CollatzResearch.WordTrace]
  refine ⟨161525442418833711803813747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107683628279222474535875831 161525442418833711803813747)
  ·
    refine ⟨242288163628250567705720621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161525442418833711803813747 242288163628250567705720621)
    ·
      refine ⟨90858061360593962889645233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 242288163628250567705720621 90858061360593962889645233)
      ·
        refine ⟨68143546020445472167233925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90858061360593962889645233 68143546020445472167233925)
        ·
          refine ⟨12776914878833526031356361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68143546020445472167233925 12776914878833526031356361)
          ·
            refine ⟨9582686159125144523517271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12776914878833526031356361 9582686159125144523517271)
            ·
              refine ⟨14374029238687716785275907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9582686159125144523517271 14374029238687716785275907)
              ·
                refine ⟨21561043858031575177913861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14374029238687716785275907 21561043858031575177913861)
                ·
                  refine ⟨4042695723380920345858849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21561043858031575177913861 4042695723380920345858849)
                  ·
                    refine ⟨3032021792535690259394137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4042695723380920345858849 3032021792535690259394137)
                    ·
                      refine ⟨2274016344401767694545603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3032021792535690259394137 2274016344401767694545603)
                      ·
                        rfl

theorem cell23_4428631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 1, 4, 2, 2].length) (baseStart_4428631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4428631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4428631 prefixEnd_4428631 := by exact prefixLift 4428631
  have htrace : WordTrace (prefixWord ++ tailWord_4428631) baseStart_4428631 baseEnd_4428631 := by
    simpa [prefixWord, tailWord_4428631, baseEnd_4428631] using wordTrace_append hprefix tailTrace_4428631
  have hstable : (prefixWord ++ tailWord_4428631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4428631).length < 2 ^ (prefixWord ++ tailWord_4428631).sum := by decide
  have hdescent : baseEnd_4428631 < baseStart_4428631 := by decide
  rcases family_descends (prefixWord ++ tailWord_4428631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4428704 : List Nat := [2, 1, 1, 4, 1, 1, 2, 3, 2, 4, 2]
def baseStart_4428704 : Nat := 118140960795 + 4428704 * 2 ^ 59
def prefixEnd_4428704 : Nat := 4983230072969 + 3 ^ 40 * 4428704 * 2
def baseEnd_4428704 : Nat := 2274053828489545908932767

theorem tailTrace_4428704 : CollatzResearch.WordTrace tailWord_4428704 prefixEnd_4428704 2274053828489545908932767 := by
  unfold tailWord_4428704
  simp only [CollatzResearch.WordTrace]
  refine ⟨80764052473784622635610583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107685403298379496847480777 80764052473784622635610583)
  ·
    refine ⟨121146078710676933953415875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80764052473784622635610583 121146078710676933953415875)
    ·
      refine ⟨181719118066015400930123813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121146078710676933953415875 181719118066015400930123813)
      ·
        refine ⟨34072334637377887674398215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 181719118066015400930123813 34072334637377887674398215)
        ·
          refine ⟨51108501956066831511597323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34072334637377887674398215 51108501956066831511597323)
          ·
            refine ⟨76662752934100247267395985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51108501956066831511597323 76662752934100247267395985)
            ·
              refine ⟨57497064700575185450546989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76662752934100247267395985 57497064700575185450546989)
              ·
                refine ⟨21561399262715694543955121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57497064700575185450546989 21561399262715694543955121)
                ·
                  refine ⟨16171049447036770907966341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21561399262715694543955121 16171049447036770907966341)
                  ·
                    refine ⟨3032071771319394545243689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16171049447036770907966341 3032071771319394545243689)
                    ·
                      refine ⟨2274053828489545908932767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3032071771319394545243689 2274053828489545908932767)
                      ·
                        rfl

theorem cell23_4428704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 3, 2, 4, 2].length) (baseStart_4428704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4428704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4428704 prefixEnd_4428704 := by exact prefixLift 4428704
  have htrace : WordTrace (prefixWord ++ tailWord_4428704) baseStart_4428704 baseEnd_4428704 := by
    simpa [prefixWord, tailWord_4428704, baseEnd_4428704] using wordTrace_append hprefix tailTrace_4428704
  have hstable : (prefixWord ++ tailWord_4428704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4428704).length < 2 ^ (prefixWord ++ tailWord_4428704).sum := by decide
  have hdescent : baseEnd_4428704 < baseStart_4428704 := by decide
  rcases family_descends (prefixWord ++ tailWord_4428704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4428707 : List Nat := [1, 1, 1, 4, 1, 2, 2, 1, 3, 4, 3]
def baseStart_4428707 : Nat := 118140960795 + 4428707 * 2 ^ 59
def prefixEnd_4428707 : Nat := 4983230072969 + 3 ^ 40 * 4428707 * 2
def baseEnd_4428707 : Nat := 2274055368931509397195253

theorem tailTrace_4428707 : CollatzResearch.WordTrace tailWord_4428707 prefixEnd_4428707 2274055368931509397195253 := by
  unfold tailWord_4428707
  simp only [CollatzResearch.WordTrace]
  refine ⟨161528214366558376783580375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107685476244372251189053583 161528214366558376783580375)
  ·
    refine ⟨242292321549837565175370563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161528214366558376783580375 242292321549837565175370563)
    ·
      refine ⟨363438482324756347763055845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242292321549837565175370563 363438482324756347763055845)
      ·
        refine ⟨68144715435891815205572971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 363438482324756347763055845 68144715435891815205572971)
        ·
          refine ⟨102217073153837722808359457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68144715435891815205572971 102217073153837722808359457)
          ·
            refine ⟨76662804865378292106269593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102217073153837722808359457 76662804865378292106269593)
            ·
              refine ⟨57497103649033719079702195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76662804865378292106269593 57497103649033719079702195)
              ·
                refine ⟨86245655473550578619553293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57497103649033719079702195 86245655473550578619553293)
                ·
                  refine ⟨32342120802581466982332485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 86245655473550578619553293 32342120802581466982332485)
                  ·
                    refine ⟨6064147650484025059187341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32342120802581466982332485 6064147650484025059187341)
                    ·
                      refine ⟨2274055368931509397195253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6064147650484025059187341 2274055368931509397195253)
                      ·
                        rfl

theorem cell23_4428707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 3, 4, 3].length) (baseStart_4428707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4428707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4428707 prefixEnd_4428707 := by exact prefixLift 4428707
  have htrace : WordTrace (prefixWord ++ tailWord_4428707) baseStart_4428707 baseEnd_4428707 := by
    simpa [prefixWord, tailWord_4428707, baseEnd_4428707] using wordTrace_append hprefix tailTrace_4428707
  have hstable : (prefixWord ++ tailWord_4428707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4428707).length < 2 ^ (prefixWord ++ tailWord_4428707).sum := by decide
  have hdescent : baseEnd_4428707 < baseStart_4428707 := by decide
  rcases family_descends (prefixWord ++ tailWord_4428707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4428721 : List Nat := [1, 2, 2, 4, 3, 1, 2, 1, 2, 1, 4]
def baseStart_4428721 : Nat := 118140960795 + 4428721 * 2 ^ 59
def prefixEnd_4428721 : Nat := 4983230072969 + 3 ^ 40 * 4428721 * 2
def baseEnd_4428721 : Nat := 2274062557660672342420189

theorem tailTrace_4428721 : CollatzResearch.WordTrace tailWord_4428721 prefixEnd_4428721 2274062557660672342420189 := by
  unfold tailWord_4428721
  simp only [CollatzResearch.WordTrace]
  refine ⟨161528724988507657174590017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107685816659005104783060011 161528724988507657174590017)
  ·
    refine ⟨121146543741380742880942513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161528724988507657174590017 121146543741380742880942513)
    ·
      refine ⟨90859907806035557160706885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121146543741380742880942513 90859907806035557160706885)
      ·
        refine ⟨17036232713631666967632541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 90859907806035557160706885 17036232713631666967632541)
        ·
          refine ⟨6388587267611875112862203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17036232713631666967632541 6388587267611875112862203)
          ·
            refine ⟨9582880901417812669293305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6388587267611875112862203 9582880901417812669293305)
            ·
              refine ⟨7187160676063359501969979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9582880901417812669293305 7187160676063359501969979)
              ·
                refine ⟨10780741014095039252954969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7187160676063359501969979 10780741014095039252954969)
                ·
                  refine ⟨8085555760571279439716227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10780741014095039252954969 8085555760571279439716227)
                  ·
                    refine ⟨12128333640856919159574341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8085555760571279439716227 12128333640856919159574341)
                    ·
                      refine ⟨2274062557660672342420189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12128333640856919159574341 2274062557660672342420189)
                      ·
                        rfl

theorem cell23_4428721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_4428721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4428721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4428721 prefixEnd_4428721 := by exact prefixLift 4428721
  have htrace : WordTrace (prefixWord ++ tailWord_4428721) baseStart_4428721 baseEnd_4428721 := by
    simpa [prefixWord, tailWord_4428721, baseEnd_4428721] using wordTrace_append hprefix tailTrace_4428721
  have hstable : (prefixWord ++ tailWord_4428721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4428721).length < 2 ^ (prefixWord ++ tailWord_4428721).sum := by decide
  have hdescent : baseEnd_4428721 < baseStart_4428721 := by decide
  rcases family_descends (prefixWord ++ tailWord_4428721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4428771 : List Nat := [1, 1, 1, 6, 1, 1, 3, 2, 3, 1, 3]
def baseStart_4428771 : Nat := 118140960795 + 4428771 * 2 ^ 59
def prefixEnd_4428771 : Nat := 4983230072969 + 3 ^ 40 * 4428771 * 2
def baseEnd_4428771 : Nat := 2274088231693397146794959

theorem tailTrace_4428771 : CollatzResearch.WordTrace tailWord_4428771 prefixEnd_4428771 2274088231693397146794959 := by
  unfold tailWord_4428771
  simp only [CollatzResearch.WordTrace]
  refine ⟨161530548638326515713910167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107687032425551010475940111 161530548638326515713910167)
  ·
    refine ⟨242295822957489773570865251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161530548638326515713910167 242295822957489773570865251)
    ·
      refine ⟨363443734436234660356297877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242295822957489773570865251 363443734436234660356297877)
      ·
        refine ⟨17036425051698499704201463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 363443734436234660356297877 17036425051698499704201463)
        ·
          refine ⟨25554637577547749556302195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17036425051698499704201463 25554637577547749556302195)
          ·
            refine ⟨38331956366321624334453293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25554637577547749556302195 38331956366321624334453293)
            ·
              refine ⟨14374483637370609125419985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38331956366321624334453293 14374483637370609125419985)
              ·
                refine ⟨10780862728027956844064989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14374483637370609125419985 10780862728027956844064989)
                ·
                  refine ⟨4042823523010483816524371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10780862728027956844064989 4042823523010483816524371)
                  ·
                    refine ⟨6064235284515725724786557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4042823523010483816524371 6064235284515725724786557)
                    ·
                      refine ⟨2274088231693397146794959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6064235284515725724786557 2274088231693397146794959)
                      ·
                        rfl

theorem cell23_4428771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_4428771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4428771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4428771 prefixEnd_4428771 := by exact prefixLift 4428771
  have htrace : WordTrace (prefixWord ++ tailWord_4428771) baseStart_4428771 baseEnd_4428771 := by
    simpa [prefixWord, tailWord_4428771, baseEnd_4428771] using wordTrace_append hprefix tailTrace_4428771
  have hstable : (prefixWord ++ tailWord_4428771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4428771).length < 2 ^ (prefixWord ++ tailWord_4428771).sum := by decide
  have hdescent : baseEnd_4428771 < baseStart_4428771 := by decide
  rcases family_descends (prefixWord ++ tailWord_4428771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4428794 : List Nat := [3, 1, 1, 1, 1, 2, 1, 2, 1, 8, 2]
def baseStart_4428794 : Nat := 118140960795 + 4428794 * 2 ^ 59
def prefixEnd_4428794 : Nat := 4983230072969 + 3 ^ 40 * 4428794 * 2
def baseEnd_4428794 : Nat := 2274100041748450556807353

theorem tailTrace_4428794 : CollatzResearch.WordTrace tailWord_4428794 prefixEnd_4428794 2274100041748450556807353 := by
  unfold tailWord_4428794
  simp only [CollatzResearch.WordTrace]
  refine ⟨40382846879310797660499359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107687591678162127094664957 40382846879310797660499359)
  ·
    refine ⟨60574270318966196490749039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40382846879310797660499359 60574270318966196490749039)
    ·
      refine ⟨90861405478449294736123559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60574270318966196490749039 90861405478449294736123559)
      ·
        refine ⟨136292108217673942104185339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90861405478449294736123559 136292108217673942104185339)
        ·
          refine ⟨204438162326510913156278009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136292108217673942104185339 204438162326510913156278009)
          ·
            refine ⟨153328621744883184867208507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 204438162326510913156278009 153328621744883184867208507)
            ·
              refine ⟨229992932617324777300812761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 153328621744883184867208507 229992932617324777300812761)
              ·
                refine ⟨172494699462993582975609571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 229992932617324777300812761 172494699462993582975609571)
                ·
                  refine ⟨258742049194490374463414357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 172494699462993582975609571 258742049194490374463414357)
                  ·
                    refine ⟨3032133388997934075743137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 258742049194490374463414357 3032133388997934075743137)
                    ·
                      refine ⟨2274100041748450556807353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3032133388997934075743137 2274100041748450556807353)
                      ·
                        rfl

theorem cell23_4428794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 1, 8, 2].length) (baseStart_4428794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4428794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4428794 prefixEnd_4428794 := by exact prefixLift 4428794
  have htrace : WordTrace (prefixWord ++ tailWord_4428794) baseStart_4428794 baseEnd_4428794 := by
    simpa [prefixWord, tailWord_4428794, baseEnd_4428794] using wordTrace_append hprefix tailTrace_4428794
  have hstable : (prefixWord ++ tailWord_4428794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4428794).length < 2 ^ (prefixWord ++ tailWord_4428794).sum := by decide
  have hdescent : baseEnd_4428794 < baseStart_4428794 := by decide
  rcases family_descends (prefixWord ++ tailWord_4428794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4428814 : List Nat := [4, 1, 1, 2, 2, 2, 1, 1, 3, 1, 5]
def baseStart_4428814 : Nat := 118140960795 + 4428814 * 2 ^ 59
def prefixEnd_4428814 : Nat := 4983230072969 + 3 ^ 40 * 4428814 * 2
def baseEnd_4428814 : Nat := 2274110311361540478557261

theorem tailTrace_4428814 : CollatzResearch.WordTrace tailWord_4428814 prefixEnd_4428814 2274110311361540478557261 := by
  unfold tailWord_4428814
  simp only [CollatzResearch.WordTrace]
  refine ⟨20191514622146341757215687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107688077984780489371816997 20191514622146341757215687)
  ·
    refine ⟨30287271933219512635823531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20191514622146341757215687 30287271933219512635823531)
    ·
      refine ⟨45430907899829268953735297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30287271933219512635823531 45430907899829268953735297)
      ·
        refine ⟨34073180924871951715301473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45430907899829268953735297 34073180924871951715301473)
        ·
          refine ⟨25554885693653963786476105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34073180924871951715301473 25554885693653963786476105)
          ·
            refine ⟨19166164270240472839857079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25554885693653963786476105 19166164270240472839857079)
            ·
              refine ⟨28749246405360709259785619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19166164270240472839857079 28749246405360709259785619)
              ·
                refine ⟨43123869608041063889678429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28749246405360709259785619 43123869608041063889678429)
                ·
                  refine ⟨16171451103015398958629411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43123869608041063889678429 16171451103015398958629411)
                  ·
                    refine ⟨24257176654523098437944117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16171451103015398958629411 24257176654523098437944117)
                    ·
                      refine ⟨2274110311361540478557261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24257176654523098437944117 2274110311361540478557261)
                      ·
                        rfl

theorem cell23_4428814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_4428814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4428814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4428814 prefixEnd_4428814 := by exact prefixLift 4428814
  have htrace : WordTrace (prefixWord ++ tailWord_4428814) baseStart_4428814 baseEnd_4428814 := by
    simpa [prefixWord, tailWord_4428814, baseEnd_4428814] using wordTrace_append hprefix tailTrace_4428814
  have hstable : (prefixWord ++ tailWord_4428814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4428814).length < 2 ^ (prefixWord ++ tailWord_4428814).sum := by decide
  have hdescent : baseEnd_4428814 < baseStart_4428814 := by decide
  rcases family_descends (prefixWord ++ tailWord_4428814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4428821 : List Nat := [1, 3, 2, 1, 4, 3, 1, 1, 1, 6]
def baseStart_4428821 : Nat := 118140960795 + 4428821 * 2 ^ 59
def prefixEnd_4428821 : Nat := 4983230072969 + 3 ^ 40 * 4428821 * 2
def baseEnd_4428821 : Nat := 758037968575373983723243

theorem tailTrace_4428821 : CollatzResearch.WordTrace tailWord_4428821 prefixEnd_4428821 758037968575373983723243 := by
  unfold tailWord_4428821
  simp only [CollatzResearch.WordTrace]
  refine ⟨161532372288145374253230317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107688248192096916168820211 161532372288145374253230317)
  ·
    refine ⟨60574639608054515344961369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 161532372288145374253230317 60574639608054515344961369)
    ·
      refine ⟨45430979706040886508721027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60574639608054515344961369 45430979706040886508721027)
      ·
        refine ⟨68146469559061329763081541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45430979706040886508721027 68146469559061329763081541)
        ·
          refine ⟨12777463042323999330577789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68146469559061329763081541 12777463042323999330577789)
          ·
            refine ⟨4791548640871499748966671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12777463042323999330577789 4791548640871499748966671)
            ·
              refine ⟨7187322961307249623450007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4791548640871499748966671 7187322961307249623450007)
              ·
                refine ⟨10780984441960874435175011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7187322961307249623450007 10780984441960874435175011)
                ·
                  refine ⟨16171476662941311652762517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10780984441960874435175011 16171476662941311652762517)
                  ·
                    refine ⟨758037968575373983723243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16171476662941311652762517 758037968575373983723243)
                    ·
                      rfl

theorem cell23_4428821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 1, 1, 6].length) (baseStart_4428821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4428821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4428821 prefixEnd_4428821 := by exact prefixLift 4428821
  have htrace : WordTrace (prefixWord ++ tailWord_4428821) baseStart_4428821 baseEnd_4428821 := by
    simpa [prefixWord, tailWord_4428821, baseEnd_4428821] using wordTrace_append hprefix tailTrace_4428821
  have hstable : (prefixWord ++ tailWord_4428821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4428821).length < 2 ^ (prefixWord ++ tailWord_4428821).sum := by decide
  have hdescent : baseEnd_4428821 < baseStart_4428821 := by decide
  rcases family_descends (prefixWord ++ tailWord_4428821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4428824 : List Nat := [2, 1, 2, 3, 2, 3, 1, 1, 1, 1, 6]
def baseStart_4428824 : Nat := 118140960795 + 4428824 * 2 ^ 59
def prefixEnd_4428824 : Nat := 4983230072969 + 3 ^ 40 * 4428824 * 2
def baseEnd_4428824 : Nat := 2274115446168085439432215

theorem tailTrace_4428824 : CollatzResearch.WordTrace tailWord_4428824 prefixEnd_4428824 2274115446168085439432215 := by
  unfold tailWord_4428824
  simp only [CollatzResearch.WordTrace]
  refine ⟨80766240853567252882794763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107688321138089670510393017 80766240853567252882794763)
  ·
    refine ⟨121149361280350879324192145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80766240853567252882794763 121149361280350879324192145)
    ·
      refine ⟨90862020960263159493144109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121149361280350879324192145 90862020960263159493144109)
      ·
        refine ⟨34073257860098684809929041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90862020960263159493144109 34073257860098684809929041)
        ·
          refine ⟨25554943395074013607446781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34073257860098684809929041 25554943395074013607446781)
          ·
            refine ⟨9583103773152755102792543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25554943395074013607446781 9583103773152755102792543)
            ·
              refine ⟨14374655659729132654188815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9583103773152755102792543 14374655659729132654188815)
              ·
                refine ⟨21561983489593698981283223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14374655659729132654188815 21561983489593698981283223)
                ·
                  refine ⟨32342975234390548471924835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21561983489593698981283223 32342975234390548471924835)
                  ·
                    refine ⟨48514462851585822707887253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32342975234390548471924835 48514462851585822707887253)
                    ·
                      refine ⟨2274115446168085439432215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48514462851585822707887253 2274115446168085439432215)
                      ·
                        rfl

theorem cell23_4428824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_4428824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4428824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4428824 prefixEnd_4428824 := by exact prefixLift 4428824
  have htrace : WordTrace (prefixWord ++ tailWord_4428824) baseStart_4428824 baseEnd_4428824 := by
    simpa [prefixWord, tailWord_4428824, baseEnd_4428824] using wordTrace_append hprefix tailTrace_4428824
  have hstable : (prefixWord ++ tailWord_4428824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4428824).length < 2 ^ (prefixWord ++ tailWord_4428824).sum := by decide
  have hdescent : baseEnd_4428824 < baseStart_4428824 := by decide
  rcases family_descends (prefixWord ++ tailWord_4428824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4428828 : List Nat := [2, 2, 3, 1, 4, 1, 2, 2, 1, 1, 4]
def baseStart_4428828 : Nat := 118140960795 + 4428828 * 2 ^ 59
def prefixEnd_4428828 : Nat := 4983230072969 + 3 ^ 40 * 4428828 * 2
def baseEnd_4428828 : Nat := 2274117500090703423782197

theorem tailTrace_4428828 : CollatzResearch.WordTrace tailWord_4428828 prefixEnd_4428828 2274117500090703423782197 := by
  unfold tailWord_4428828
  simp only [CollatzResearch.WordTrace]
  refine ⟨80766313799560007224367569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107688418399413342965823425 80766313799560007224367569)
  ·
    refine ⟨60574735349670005418275677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80766313799560007224367569 60574735349670005418275677)
    ·
      refine ⟨22715525756126252031853379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60574735349670005418275677 22715525756126252031853379)
      ·
        refine ⟨34073288634189378047780069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22715525756126252031853379 34073288634189378047780069)
        ·
          refine ⟨6388741618910508383958763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34073288634189378047780069 6388741618910508383958763)
          ·
            refine ⟨9583112428365762575938145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6388741618910508383958763 9583112428365762575938145)
            ·
              refine ⟨7187334321274321931953609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9583112428365762575938145 7187334321274321931953609)
              ·
                refine ⟨5390500740955741448965207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7187334321274321931953609 5390500740955741448965207)
                ·
                  refine ⟨8085751111433612173447811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5390500740955741448965207 8085751111433612173447811)
                  ·
                    refine ⟨12128626667150418260171717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8085751111433612173447811 12128626667150418260171717)
                    ·
                      refine ⟨2274117500090703423782197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12128626667150418260171717 2274117500090703423782197)
                      ·
                        rfl

theorem cell23_4428828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 2, 1, 1, 4].length) (baseStart_4428828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4428828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4428828 prefixEnd_4428828 := by exact prefixLift 4428828
  have htrace : WordTrace (prefixWord ++ tailWord_4428828) baseStart_4428828 baseEnd_4428828 := by
    simpa [prefixWord, tailWord_4428828, baseEnd_4428828] using wordTrace_append hprefix tailTrace_4428828
  have hstable : (prefixWord ++ tailWord_4428828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4428828).length < 2 ^ (prefixWord ++ tailWord_4428828).sum := by decide
  have hdescent : baseEnd_4428828 < baseStart_4428828 := by decide
  rcases family_descends (prefixWord ++ tailWord_4428828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4428831 : List Nat := [1, 1, 2, 4, 1, 3, 1, 4, 1, 2, 3]
def baseStart_4428831 : Nat := 118140960795 + 4428831 * 2 ^ 59
def prefixEnd_4428831 : Nat := 4983230072969 + 3 ^ 40 * 4428831 * 2
def baseEnd_4428831 : Nat := 2274119040532666912044683

theorem tailTrace_4428831 : CollatzResearch.WordTrace tailWord_4428831 prefixEnd_4428831 2274119040532666912044683 := by
  unfold tailWord_4428831
  simp only [CollatzResearch.WordTrace]
  refine ⟨161532737018109145961094347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107688491345406097307396231 161532737018109145961094347)
  ·
    refine ⟨242299105527163718941641521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161532737018109145961094347 242299105527163718941641521)
    ·
      refine ⟨181724329145372789206231141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 242299105527163718941641521 181724329145372789206231141)
      ·
        refine ⟨34073311714757397976168339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 181724329145372789206231141 34073311714757397976168339)
        ·
          refine ⟨51109967572136096964252509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34073311714757397976168339 51109967572136096964252509)
          ·
            refine ⟨19166237839551036361594691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51109967572136096964252509 19166237839551036361594691)
            ·
              refine ⟨28749356759326554542392037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19166237839551036361594691 28749356759326554542392037)
              ·
                refine ⟨5390504392373728976698507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28749356759326554542392037 5390504392373728976698507)
                ·
                  refine ⟨8085756588560593465047761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5390504392373728976698507 8085756588560593465047761)
                  ·
                    refine ⟨6064317441420445098785821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8085756588560593465047761 6064317441420445098785821)
                    ·
                      refine ⟨2274119040532666912044683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6064317441420445098785821 2274119040532666912044683)
                      ·
                        rfl

theorem cell23_4428831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 4, 1, 2, 3].length) (baseStart_4428831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4428831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4428831 prefixEnd_4428831 := by exact prefixLift 4428831
  have htrace : WordTrace (prefixWord ++ tailWord_4428831) baseStart_4428831 baseEnd_4428831 := by
    simpa [prefixWord, tailWord_4428831, baseEnd_4428831] using wordTrace_append hprefix tailTrace_4428831
  have hstable : (prefixWord ++ tailWord_4428831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4428831).length < 2 ^ (prefixWord ++ tailWord_4428831).sum := by decide
  have hdescent : baseEnd_4428831 < baseStart_4428831 := by decide
  rcases family_descends (prefixWord ++ tailWord_4428831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4428834 : List Nat := [3, 3, 1, 1, 1, 4, 1, 9]
def baseStart_4428834 : Nat := 118140960795 + 4428834 * 2 ^ 59
def prefixEnd_4428834 : Nat := 4983230072969 + 3 ^ 40 * 4428834 * 2
def baseEnd_4428834 : Nat := 84226688184245570381747

theorem tailTrace_4428834 : CollatzResearch.WordTrace tailWord_4428834 prefixEnd_4428834 84226688184245570381747 := by
  unfold tailWord_4428834
  simp only [CollatzResearch.WordTrace]
  refine ⟨40383211609274569368363389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107688564291398851648969037 40383211609274569368363389)
  ·
    refine ⟨15143704353477963513136271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40383211609274569368363389 15143704353477963513136271)
    ·
      refine ⟨22715556530216945269704407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15143704353477963513136271 22715556530216945269704407)
      ·
        refine ⟨34073334795325417904556611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22715556530216945269704407 34073334795325417904556611)
        ·
          refine ⟨51110002192988126856834917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34073334795325417904556611 51110002192988126856834917)
          ·
            refine ⟨9583125411185273785656547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51110002192988126856834917 9583125411185273785656547)
            ·
              refine ⟨14374688116777910678484821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9583125411185273785656547 14374688116777910678484821)
              ·
                refine ⟨84226688184245570381747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14374688116777910678484821 84226688184245570381747)
                ·
                  rfl

theorem cell23_4428834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 9].length) (baseStart_4428834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4428834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4428834 prefixEnd_4428834 := by exact prefixLift 4428834
  have htrace : WordTrace (prefixWord ++ tailWord_4428834) baseStart_4428834 baseEnd_4428834 := by
    simpa [prefixWord, tailWord_4428834, baseEnd_4428834] using wordTrace_append hprefix tailTrace_4428834
  have hstable : (prefixWord ++ tailWord_4428834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4428834).length < 2 ^ (prefixWord ++ tailWord_4428834).sum := by decide
  have hdescent : baseEnd_4428834 < baseStart_4428834 := by decide
  rcases family_descends (prefixWord ++ tailWord_4428834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4428844 : List Nat := [2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 3]
def baseStart_4428844 : Nat := 118140960795 + 4428844 * 2 ^ 59
def prefixEnd_4428844 : Nat := 4983230072969 + 3 ^ 40 * 4428844 * 2
def baseEnd_4428844 : Nat := 2274125715781175361182123

theorem tailTrace_4428844 : CollatzResearch.WordTrace tailWord_4428844 prefixEnd_4428844 2274125715781175361182123 := by
  unfold tailWord_4428844
  simp only [CollatzResearch.WordTrace]
  refine ⟨80766605583531024590658793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107688807444708032787545057 80766605583531024590658793)
  ·
    refine ⟨60574954187648268442994095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80766605583531024590658793 60574954187648268442994095)
    ·
      refine ⟨90862431281472402664491143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60574954187648268442994095 90862431281472402664491143)
      ·
        refine ⟨136293646922208603996736715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90862431281472402664491143 136293646922208603996736715)
        ·
          refine ⟨204440470383312905995105073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136293646922208603996736715 204440470383312905995105073)
          ·
            refine ⟨153330352787484679496328805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 204440470383312905995105073 153330352787484679496328805)
            ·
              refine ⟨28749441147653377405561651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 153330352787484679496328805 28749441147653377405561651)
              ·
                refine ⟨43124161721480066108342477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28749441147653377405561651 43124161721480066108342477)
                ·
                  refine ⟨16171560645555024790628429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43124161721480066108342477 16171560645555024790628429)
                  ·
                    refine ⟨6064335242083134296485661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16171560645555024790628429 6064335242083134296485661)
                    ·
                      refine ⟨2274125715781175361182123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6064335242083134296485661 2274125715781175361182123)
                      ·
                        rfl

theorem cell23_4428844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 3].length) (baseStart_4428844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4428844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4428844 prefixEnd_4428844 := by exact prefixLift 4428844
  have htrace : WordTrace (prefixWord ++ tailWord_4428844) baseStart_4428844 baseEnd_4428844 := by
    simpa [prefixWord, tailWord_4428844, baseEnd_4428844] using wordTrace_append hprefix tailTrace_4428844
  have hstable : (prefixWord ++ tailWord_4428844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4428844).length < 2 ^ (prefixWord ++ tailWord_4428844).sum := by decide
  have hdescent : baseEnd_4428844 < baseStart_4428844 := by decide
  rcases family_descends (prefixWord ++ tailWord_4428844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4428862 : List Nat := [4, 2, 1, 3, 1, 3, 1, 1, 3, 2, 2]
def baseStart_4428862 : Nat := 118140960795 + 4428862 * 2 ^ 59
def prefixEnd_4428862 : Nat := 4983230072969 + 3 ^ 40 * 4428862 * 2
def baseEnd_4428862 : Nat := 2274134958432956290757041

theorem tailTrace_4428862 : CollatzResearch.WordTrace tailWord_4428862 prefixEnd_4428862 2274134958432956290757041 := by
  unfold tailWord_4428862
  simp only [CollatzResearch.WordTrace]
  refine ⟨20191733460124604781934105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107689245120664558836981893 20191733460124604781934105)
  ·
    refine ⟨15143800095093453586450579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20191733460124604781934105 15143800095093453586450579)
    ·
      refine ⟨22715700142640180379675869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15143800095093453586450579 22715700142640180379675869)
      ·
        refine ⟨8518387553490067642378451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22715700142640180379675869 8518387553490067642378451)
        ·
          refine ⟨12777581330235101463567677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8518387553490067642378451 12777581330235101463567677)
          ·
            refine ⟨4791592998838163048837879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12777581330235101463567677 4791592998838163048837879)
            ·
              refine ⟨7187389498257244573256819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4791592998838163048837879 7187389498257244573256819)
              ·
                refine ⟨10781084247385866859885229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7187389498257244573256819 10781084247385866859885229)
                ·
                  refine ⟨4042906592769700072456961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10781084247385866859885229 4042906592769700072456961)
                  ·
                    refine ⟨3032179944577275054342721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4042906592769700072456961 3032179944577275054342721)
                    ·
                      refine ⟨2274134958432956290757041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3032179944577275054342721 2274134958432956290757041)
                      ·
                        rfl

theorem cell23_4428862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_4428862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4428862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4428862 prefixEnd_4428862 := by exact prefixLift 4428862
  have htrace : WordTrace (prefixWord ++ tailWord_4428862) baseStart_4428862 baseEnd_4428862 := by
    simpa [prefixWord, tailWord_4428862, baseEnd_4428862] using wordTrace_append hprefix tailTrace_4428862
  have hstable : (prefixWord ++ tailWord_4428862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4428862).length < 2 ^ (prefixWord ++ tailWord_4428862).sum := by decide
  have hdescent : baseEnd_4428862 < baseStart_4428862 := by decide
  rcases family_descends (prefixWord ++ tailWord_4428862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4428878 : List Nat := [4, 1, 1, 1, 1, 3, 3, 3, 2, 1, 3]
def baseStart_4428878 : Nat := 118140960795 + 4428878 * 2 ^ 59
def prefixEnd_4428878 : Nat := 4983230072969 + 3 ^ 40 * 4428878 * 2
def baseEnd_4428878 : Nat := 2274143174123428228156967

theorem tailTrace_4428878 : CollatzResearch.WordTrace tailWord_4428878 prefixEnd_4428878 2274143174123428228156967 := by
  unfold tailWord_4428878
  simp only [CollatzResearch.WordTrace]
  refine ⟨20191806406117359123506911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107689634165959248658703525 20191806406117359123506911)
  ·
    refine ⟨30287709609176038685260367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20191806406117359123506911 30287709609176038685260367)
    ·
      refine ⟨45431564413764058027890551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30287709609176038685260367 45431564413764058027890551)
      ·
        refine ⟨68147346620646087041835827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45431564413764058027890551 68147346620646087041835827)
        ·
          refine ⟨102221019930969130562753741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68147346620646087041835827 102221019930969130562753741)
          ·
            refine ⟨38332882474113423961032653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102221019930969130562753741 38332882474113423961032653)
            ·
              refine ⟨14374830927792533985387245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38332882474113423961032653 14374830927792533985387245)
              ·
                refine ⟨5390561597922200244520217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14374830927792533985387245 5390561597922200244520217)
                ·
                  refine ⟨4042921198441650183390163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5390561597922200244520217 4042921198441650183390163)
                  ·
                    refine ⟨6064381797662475275085245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4042921198441650183390163 6064381797662475275085245)
                    ·
                      refine ⟨2274143174123428228156967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6064381797662475275085245 2274143174123428228156967)
                      ·
                        rfl

theorem cell23_4428878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 3, 2, 1, 3].length) (baseStart_4428878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4428878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4428878 prefixEnd_4428878 := by exact prefixLift 4428878
  have htrace : WordTrace (prefixWord ++ tailWord_4428878) baseStart_4428878 baseEnd_4428878 := by
    simpa [prefixWord, tailWord_4428878, baseEnd_4428878] using wordTrace_append hprefix tailTrace_4428878
  have hstable : (prefixWord ++ tailWord_4428878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4428878).length < 2 ^ (prefixWord ++ tailWord_4428878).sum := by decide
  have hdescent : baseEnd_4428878 < baseStart_4428878 := by decide
  rcases family_descends (prefixWord ++ tailWord_4428878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4428905 : List Nat := [1, 2, 1, 1, 1, 7, 3, 1, 1, 3, 2]
def baseStart_4428905 : Nat := 118140960795 + 4428905 * 2 ^ 59
def prefixEnd_4428905 : Nat := 4983230072969 + 3 ^ 40 * 4428905 * 2
def baseEnd_4428905 : Nat := 2274157038101099622519343

theorem tailTrace_4428905 : CollatzResearch.WordTrace tailWord_4428905 prefixEnd_4428905 2274157038101099622519343 := by
  unfold tailWord_4428905
  simp only [CollatzResearch.WordTrace]
  refine ⟨161535436019841056599288169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107690290679894037732858779 161535436019841056599288169)
  ·
    refine ⟨121151577014880792449466127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161535436019841056599288169 121151577014880792449466127)
    ·
      refine ⟨181727365522321188674199191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121151577014880792449466127 181727365522321188674199191)
      ·
        refine ⟨272591048283481783011298787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181727365522321188674199191 272591048283481783011298787)
        ·
          refine ⟨408886572425222674516948181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 272591048283481783011298787 408886572425222674516948181)
          ·
            refine ⟨9583279041216156433990973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 408886572425222674516948181 9583279041216156433990973)
            ·
              refine ⟨3593729640456058662746615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9583279041216156433990973 3593729640456058662746615)
              ·
                refine ⟨5390594460684087994119923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3593729640456058662746615 5390594460684087994119923)
                ·
                  refine ⟨8085891691026131991179885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5390594460684087994119923 8085891691026131991179885)
                  ·
                    refine ⟨3032209384134799496692457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8085891691026131991179885 3032209384134799496692457)
                    ·
                      refine ⟨2274157038101099622519343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3032209384134799496692457 2274157038101099622519343)
                      ·
                        rfl

theorem cell23_4428905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 3, 1, 1, 3, 2].length) (baseStart_4428905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4428905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4428905 prefixEnd_4428905 := by exact prefixLift 4428905
  have htrace : WordTrace (prefixWord ++ tailWord_4428905) baseStart_4428905 baseEnd_4428905 := by
    simpa [prefixWord, tailWord_4428905, baseEnd_4428905] using wordTrace_append hprefix tailTrace_4428905
  have hstable : (prefixWord ++ tailWord_4428905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4428905).length < 2 ^ (prefixWord ++ tailWord_4428905).sum := by decide
  have hdescent : baseEnd_4428905 < baseStart_4428905 := by decide
  rcases family_descends (prefixWord ++ tailWord_4428905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4428918 : List Nat := [5, 1, 1, 2, 1, 1, 1, 2, 3, 4, 2]
def baseStart_4428918 : Nat := 118140960795 + 4428918 * 2 ^ 59
def prefixEnd_4428918 : Nat := 4983230072969 + 3 ^ 40 * 4428918 * 2
def baseEnd_4428918 : Nat := 2274163713349608071656783

theorem tailTrace_4428918 : CollatzResearch.WordTrace tailWord_4428918 prefixEnd_4428918 2274163713349608071656783 := by
  unfold tailWord_4428918
  simp only [CollatzResearch.WordTrace]
  refine ⟨10095994385549622488719463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 107690606779195973213007605 10095994385549622488719463)
  ·
    refine ⟨15143991578324433733079195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10095994385549622488719463 15143991578324433733079195)
    ·
      refine ⟨22715987367486650599618793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15143991578324433733079195 22715987367486650599618793)
      ·
        refine ⟨17036990525614987949714095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22715987367486650599618793 17036990525614987949714095)
        ·
          refine ⟨25555485788422481924571143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17036990525614987949714095 25555485788422481924571143)
          ·
            refine ⟨38333228682633722886856715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25555485788422481924571143 38333228682633722886856715)
            ·
              refine ⟨57499843023950584330285073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38333228682633722886856715 57499843023950584330285073)
              ·
                refine ⟨43124882267962938247713805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57499843023950584330285073 43124882267962938247713805)
                ·
                  refine ⟨16171830850486101842892677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43124882267962938247713805 16171830850486101842892677)
                  ·
                    refine ⟨3032218284466144095542377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16171830850486101842892677 3032218284466144095542377)
                    ·
                      refine ⟨2274163713349608071656783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3032218284466144095542377 2274163713349608071656783)
                      ·
                        rfl

theorem cell23_4428918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 3, 4, 2].length) (baseStart_4428918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4428918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4428918 prefixEnd_4428918 := by exact prefixLift 4428918
  have htrace : WordTrace (prefixWord ++ tailWord_4428918) baseStart_4428918 baseEnd_4428918 := by
    simpa [prefixWord, tailWord_4428918, baseEnd_4428918] using wordTrace_append hprefix tailTrace_4428918
  have hstable : (prefixWord ++ tailWord_4428918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4428918).length < 2 ^ (prefixWord ++ tailWord_4428918).sum := by decide
  have hdescent : baseEnd_4428918 < baseStart_4428918 := by decide
  rcases family_descends (prefixWord ++ tailWord_4428918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4428924 : List Nat := [2, 2, 2, 1, 1, 3, 2, 3, 7]
def baseStart_4428924 : Nat := 118140960795 + 4428924 * 2 ^ 59
def prefixEnd_4428924 : Nat := 4983230072969 + 3 ^ 40 * 4428924 * 2
def baseEnd_4428924 : Nat := 252685199359281672020195

theorem tailTrace_4428924 : CollatzResearch.WordTrace tailWord_4428924 prefixEnd_4428924 252685199359281672020195 := by
  unfold tailWord_4428924
  simp only [CollatzResearch.WordTrace]
  refine ⟨80768064503386111422114913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107690752671181481896153217 80768064503386111422114913)
  ·
    refine ⟨60576048377539583566586185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80768064503386111422114913 60576048377539583566586185)
    ·
      refine ⟨45432036283154687674939639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60576048377539583566586185 45432036283154687674939639)
      ·
        refine ⟨68148054424732031512409459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45432036283154687674939639 68148054424732031512409459)
        ·
          refine ⟨102222081637098047268614189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68148054424732031512409459 102222081637098047268614189)
          ·
            refine ⟨38333280613911767725730321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102222081637098047268614189 38333280613911767725730321)
            ·
              refine ⟨28749960460433825794297741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38333280613911767725730321 28749960460433825794297741)
              ·
                refine ⟨10781235172662684672861653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28749960460433825794297741 10781235172662684672861653)
                ·
                  refine ⟨252685199359281672020195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10781235172662684672861653 252685199359281672020195)
                  ·
                    rfl

theorem cell23_4428924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 3, 7].length) (baseStart_4428924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4428924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4428924 prefixEnd_4428924 := by exact prefixLift 4428924
  have htrace : WordTrace (prefixWord ++ tailWord_4428924) baseStart_4428924 baseEnd_4428924 := by
    simpa [prefixWord, tailWord_4428924, baseEnd_4428924] using wordTrace_append hprefix tailTrace_4428924
  have hstable : (prefixWord ++ tailWord_4428924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4428924).length < 2 ^ (prefixWord ++ tailWord_4428924).sum := by decide
  have hdescent : baseEnd_4428924 < baseStart_4428924 := by decide
  rcases family_descends (prefixWord ++ tailWord_4428924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4429061 : List Nat := [1, 3, 1, 1, 2, 1, 5, 1, 3, 5]
def baseStart_4429061 : Nat := 118140960795 + 4429061 * 2 ^ 59
def prefixEnd_4429061 : Nat := 4983230072969 + 3 ^ 40 * 4429061 * 2
def baseEnd_4429061 : Nat := 758079047027733670722875

theorem tailTrace_4429061 : CollatzResearch.WordTrace tailWord_4429061 prefixEnd_4429061 758079047027733670722875 := by
  unfold tailWord_4429061
  simp only [CollatzResearch.WordTrace]
  refine ⟨161541125807275895241967037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107694083871517263494644691 161541125807275895241967037)
  ·
    refine ⟨60577922177728460715737639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 161541125807275895241967037 60577922177728460715737639)
    ·
      refine ⟨90866883266592691073606459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60577922177728460715737639 90866883266592691073606459)
      ·
        refine ⟨136300324899889036610409689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90866883266592691073606459 136300324899889036610409689)
        ·
          refine ⟨102225243674916777457807267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136300324899889036610409689 102225243674916777457807267)
          ·
            refine ⟨153337865512375166186710901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102225243674916777457807267 153337865512375166186710901)
            ·
              refine ⟨14375424891785171830004147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 153337865512375166186710901 14375424891785171830004147)
              ·
                refine ⟨21563137337677757745006221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14375424891785171830004147 21563137337677757745006221)
                ·
                  refine ⟨8086176501629159154377333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21563137337677757745006221 8086176501629159154377333)
                  ·
                    refine ⟨758079047027733670722875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8086176501629159154377333 758079047027733670722875)
                    ·
                      rfl

theorem cell23_4429061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 1, 3, 5].length) (baseStart_4429061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4429061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4429061 prefixEnd_4429061 := by exact prefixLift 4429061
  have htrace : WordTrace (prefixWord ++ tailWord_4429061) baseStart_4429061 baseEnd_4429061 := by
    simpa [prefixWord, tailWord_4429061, baseEnd_4429061] using wordTrace_append hprefix tailTrace_4429061
  have hstable : (prefixWord ++ tailWord_4429061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4429061).length < 2 ^ (prefixWord ++ tailWord_4429061).sum := by decide
  have hdescent : baseEnd_4429061 < baseStart_4429061 := by decide
  rcases family_descends (prefixWord ++ tailWord_4429061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4429092 : List Nat := [2, 3, 1, 3, 1, 1, 3, 4, 1, 1, 3]
def baseStart_4429092 : Nat := 118140960795 + 4429092 * 2 ^ 59
def prefixEnd_4429092 : Nat := 4983230072969 + 3 ^ 40 * 4429092 * 2
def baseEnd_4429092 : Nat := 2274253058983490390880983

theorem tailTrace_4429092 : CollatzResearch.WordTrace tailWord_4429092 prefixEnd_4429092 2274253058983490390880983 := by
  unfold tailWord_4429092
  simp only [CollatzResearch.WordTrace]
  refine ⟨80771128235081793768172765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107694837646775725024230353 80771128235081793768172765)
  ·
    refine ⟨30289173088155672663064787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80771128235081793768172765 30289173088155672663064787)
    ·
      refine ⟨45433759632233508994597181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30289173088155672663064787 45433759632233508994597181)
      ·
        refine ⟨17037659862087565872973943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45433759632233508994597181 17037659862087565872973943)
        ·
          refine ⟨25556489793131348809460915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17037659862087565872973943 25556489793131348809460915)
          ·
            refine ⟨38334734689697023214191373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25556489793131348809460915 38334734689697023214191373)
            ·
              refine ⟨14375525508636383705321765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38334734689697023214191373 14375525508636383705321765)
              ·
                refine ⟨2695411032869321944747831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14375525508636383705321765 2695411032869321944747831)
                ·
                  refine ⟨4043116549303982917121747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2695411032869321944747831 4043116549303982917121747)
                  ·
                    refine ⟨6064674823955974375682621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4043116549303982917121747 6064674823955974375682621)
                    ·
                      refine ⟨2274253058983490390880983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6064674823955974375682621 2274253058983490390880983)
                      ·
                        rfl

theorem cell23_4429092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 4, 1, 1, 3].length) (baseStart_4429092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4429092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4429092 prefixEnd_4429092 := by exact prefixLift 4429092
  have htrace : WordTrace (prefixWord ++ tailWord_4429092) baseStart_4429092 baseEnd_4429092 := by
    simpa [prefixWord, tailWord_4429092, baseEnd_4429092] using wordTrace_append hprefix tailTrace_4429092
  have hstable : (prefixWord ++ tailWord_4429092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4429092).length < 2 ^ (prefixWord ++ tailWord_4429092).sum := by decide
  have hdescent : baseEnd_4429092 < baseStart_4429092 := by decide
  rcases family_descends (prefixWord ++ tailWord_4429092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4429131 : List Nat := [1, 1, 1, 1, 3, 1, 1, 2, 2, 7, 3]
def baseStart_4429131 : Nat := 118140960795 + 4429131 * 2 ^ 59
def prefixEnd_4429131 : Nat := 4983230072969 + 3 ^ 40 * 4429131 * 2
def baseEnd_4429131 : Nat := 2274273084729015738293303

theorem tailTrace_4429131 : CollatzResearch.WordTrace tailWord_4429131 prefixEnd_4429131 2274273084729015738293303 := by
  unfold tailWord_4429131
  simp only [CollatzResearch.WordTrace]
  refine ⟨161543678917022297197015247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107695785944681531464676831 161543678917022297197015247)
  ·
    refine ⟨242315518375533445795522871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161543678917022297197015247 242315518375533445795522871)
    ·
      refine ⟨363473277563300168693284307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242315518375533445795522871 363473277563300168693284307)
      ·
        refine ⟨545209916344950253039926461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 363473277563300168693284307 545209916344950253039926461)
        ·
          refine ⟨204453718629356344889972423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 545209916344950253039926461 204453718629356344889972423)
          ·
            refine ⟨306680577944034517334958635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 204453718629356344889972423 306680577944034517334958635)
            ·
              refine ⟨460020866916051776002437953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 306680577944034517334958635 460020866916051776002437953)
              ·
                refine ⟨345015650187038832001828465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 460020866916051776002437953 345015650187038832001828465)
                ·
                  refine ⟨258761737640279124001371349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 345015650187038832001828465 258761737640279124001371349)
                  ·
                    refine ⟨6064728225944041968782141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 258761737640279124001371349 6064728225944041968782141)
                    ·
                      refine ⟨2274273084729015738293303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6064728225944041968782141 2274273084729015738293303)
                      ·
                        rfl

theorem cell23_4429131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 7, 3].length) (baseStart_4429131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4429131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4429131 prefixEnd_4429131 := by exact prefixLift 4429131
  have htrace : WordTrace (prefixWord ++ tailWord_4429131) baseStart_4429131 baseEnd_4429131 := by
    simpa [prefixWord, tailWord_4429131, baseEnd_4429131] using wordTrace_append hprefix tailTrace_4429131
  have hstable : (prefixWord ++ tailWord_4429131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4429131).length < 2 ^ (prefixWord ++ tailWord_4429131).sum := by decide
  have hdescent : baseEnd_4429131 < baseStart_4429131 := by decide
  rcases family_descends (prefixWord ++ tailWord_4429131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4429132 : List Nat := [2, 2, 1, 3, 2, 4, 2, 1, 1, 1, 4]
def baseStart_4429132 : Nat := 118140960795 + 4429132 * 2 ^ 59
def prefixEnd_4429132 : Nat := 4983230072969 + 3 ^ 40 * 4429132 * 2
def baseEnd_4429132 : Nat := 2274273598209670234380799

theorem tailTrace_4429132 : CollatzResearch.WordTrace tailWord_4429132 prefixEnd_4429132 2274273598209670234380799 := by
  unfold tailWord_4429132
  simp only [CollatzResearch.WordTrace]
  refine ⟨80771857695009337183900825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107695810260012449578534433 80771857695009337183900825)
  ·
    refine ⟨60578893271257002887925619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80771857695009337183900825 60578893271257002887925619)
    ·
      refine ⟨90868339906885504331888429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60578893271257002887925619 90868339906885504331888429)
      ·
        refine ⟨34075627465082064124458161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90868339906885504331888429 34075627465082064124458161)
        ·
          refine ⟨25556720598811548093343621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34075627465082064124458161 25556720598811548093343621)
          ·
            refine ⟨4791885112277165267501929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25556720598811548093343621 4791885112277165267501929)
            ·
              refine ⟨3593913834207873950626447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4791885112277165267501929 3593913834207873950626447)
              ·
                refine ⟨5390870751311810925939671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3593913834207873950626447 5390870751311810925939671)
                ·
                  refine ⟨8086306126967716388909507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5390870751311810925939671 8086306126967716388909507)
                  ·
                    refine ⟨12129459190451574583364261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8086306126967716388909507 12129459190451574583364261)
                    ·
                      refine ⟨2274273598209670234380799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12129459190451574583364261 2274273598209670234380799)
                      ·
                        rfl

theorem cell23_4429132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 2, 1, 1, 1, 4].length) (baseStart_4429132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4429132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4429132 prefixEnd_4429132 := by exact prefixLift 4429132
  have htrace : WordTrace (prefixWord ++ tailWord_4429132) baseStart_4429132 baseEnd_4429132 := by
    simpa [prefixWord, tailWord_4429132, baseEnd_4429132] using wordTrace_append hprefix tailTrace_4429132
  have hstable : (prefixWord ++ tailWord_4429132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4429132).length < 2 ^ (prefixWord ++ tailWord_4429132).sum := by decide
  have hdescent : baseEnd_4429132 < baseStart_4429132 := by decide
  rcases family_descends (prefixWord ++ tailWord_4429132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4429162 : List Nat := [3, 1, 3, 3, 2, 2, 1, 1, 1, 2, 4]
def baseStart_4429162 : Nat := 118140960795 + 4429162 * 2 ^ 59
def prefixEnd_4429162 : Nat := 4983230072969 + 3 ^ 40 * 4429162 * 2
def baseEnd_4429162 : Nat := 2274289002629305117005661

theorem tailTrace_4429162 : CollatzResearch.WordTrace tailWord_4429162 prefixEnd_4429162 2274289002629305117005661 := by
  unfold tailWord_4429162
  simp only [CollatzResearch.WordTrace]
  refine ⟨40386202394977497372848435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107696539719939992994262493 40386202394977497372848435)
  ·
    refine ⟨60579303592466246059272653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40386202394977497372848435 60579303592466246059272653)
    ·
      refine ⟨22717238847174842272227245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60579303592466246059272653 22717238847174842272227245)
      ·
        refine ⟨8518964567690565852085217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22717238847174842272227245 8518964567690565852085217)
        ·
          refine ⟨6389223425767924389063913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8518964567690565852085217 6389223425767924389063913)
          ·
            refine ⟨4791917569325943291797935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6389223425767924389063913 4791917569325943291797935)
            ·
              refine ⟨7187876353988914937696903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4791917569325943291797935 7187876353988914937696903)
              ·
                refine ⟨10781814530983372406545355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7187876353988914937696903 10781814530983372406545355)
                ·
                  refine ⟨16172721796475058609818033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10781814530983372406545355 16172721796475058609818033)
                  ·
                    refine ⟨12129541347356293957363525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16172721796475058609818033 12129541347356293957363525)
                    ·
                      refine ⟨2274289002629305117005661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12129541347356293957363525 2274289002629305117005661)
                      ·
                        rfl

theorem cell23_4429162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_4429162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4429162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4429162 prefixEnd_4429162 := by exact prefixLift 4429162
  have htrace : WordTrace (prefixWord ++ tailWord_4429162) baseStart_4429162 baseEnd_4429162 := by
    simpa [prefixWord, tailWord_4429162, baseEnd_4429162] using wordTrace_append hprefix tailTrace_4429162
  have hstable : (prefixWord ++ tailWord_4429162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4429162).length < 2 ^ (prefixWord ++ tailWord_4429162).sum := by decide
  have hdescent : baseEnd_4429162 < baseStart_4429162 := by decide
  rcases family_descends (prefixWord ++ tailWord_4429162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4429165 : List Nat := [1, 5, 1, 1, 1, 3, 3, 1, 1, 3, 3]
def baseStart_4429165 : Nat := 118140960795 + 4429165 * 2 ^ 59
def prefixEnd_4429165 : Nat := 4983230072969 + 3 ^ 40 * 4429165 * 2
def baseEnd_4429165 : Nat := 2274290543071268605268147

theorem tailTrace_4429165 : CollatzResearch.WordTrace tailWord_4429165 prefixEnd_4429165 2274290543071268605268147 := by
  unfold tailWord_4429165
  simp only [CollatzResearch.WordTrace]
  refine ⟨161544918998899121003752949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107696612665932747335835299 161544918998899121003752949)
  ·
    refine ⟨15144836156146792594101839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 161544918998899121003752949 15144836156146792594101839)
    ·
      refine ⟨22717254234220188891152759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15144836156146792594101839 22717254234220188891152759)
      ·
        refine ⟨34075881351330283336729139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22717254234220188891152759 34075881351330283336729139)
        ·
          refine ⟨51113822026995425005093709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34075881351330283336729139 51113822026995425005093709)
          ·
            refine ⟨19167683260123284376910141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51113822026995425005093709 19167683260123284376910141)
            ·
              refine ⟨7187881222546231641341303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19167683260123284376910141 7187881222546231641341303)
              ·
                refine ⟨10781821833819347462011955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7187881222546231641341303 10781821833819347462011955)
                ·
                  refine ⟨16172732750729021193017933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10781821833819347462011955 16172732750729021193017933)
                  ·
                    refine ⟨6064774781523382947381725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16172732750729021193017933 6064774781523382947381725)
                    ·
                      refine ⟨2274290543071268605268147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6064774781523382947381725 2274290543071268605268147)
                      ·
                        rfl

theorem cell23_4429165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 1, 1, 3, 3].length) (baseStart_4429165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4429165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4429165 prefixEnd_4429165 := by exact prefixLift 4429165
  have htrace : WordTrace (prefixWord ++ tailWord_4429165) baseStart_4429165 baseEnd_4429165 := by
    simpa [prefixWord, tailWord_4429165, baseEnd_4429165] using wordTrace_append hprefix tailTrace_4429165
  have hstable : (prefixWord ++ tailWord_4429165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4429165).length < 2 ^ (prefixWord ++ tailWord_4429165).sum := by decide
  have hdescent : baseEnd_4429165 < baseStart_4429165 := by decide
  rcases family_descends (prefixWord ++ tailWord_4429165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4429192 : List Nat := [2, 1, 3, 3, 1, 2, 2, 3, 1, 3, 2]
def baseStart_4429192 : Nat := 118140960795 + 4429192 * 2 ^ 59
def prefixEnd_4429192 : Nat := 4983230072969 + 3 ^ 40 * 4429192 * 2
def baseEnd_4429192 : Nat := 2274304407048939999630523

theorem tailTrace_4429192 : CollatzResearch.WordTrace tailWord_4429192 prefixEnd_4429192 2274304407048939999630523 := by
  unfold tailWord_4429192
  simp only [CollatzResearch.WordTrace]
  refine ⟨80772951884900652307492915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107697269179867536409990553 80772951884900652307492915)
  ·
    refine ⟨121159427827350978461239373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80772951884900652307492915 121159427827350978461239373)
    ·
      refine ⟨45434785435256616922964765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121159427827350978461239373 45434785435256616922964765)
      ·
        refine ⟨17038044538221231346111787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45434785435256616922964765 17038044538221231346111787)
        ·
          refine ⟨25557066807331847019167681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17038044538221231346111787 25557066807331847019167681)
          ·
            refine ⟨19167800105498885264375761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25557066807331847019167681 19167800105498885264375761)
            ·
              refine ⟨14375850079124163948281821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19167800105498885264375761 14375850079124163948281821)
              ·
                refine ⟨5390943779671561480605683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14375850079124163948281821 5390943779671561480605683)
                ·
                  refine ⟨8086415669507342220908525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5390943779671561480605683 8086415669507342220908525)
                  ·
                    refine ⟨3032405876065253332840697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8086415669507342220908525 3032405876065253332840697)
                    ·
                      refine ⟨2274304407048939999630523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3032405876065253332840697 2274304407048939999630523)
                      ·
                        rfl

theorem cell23_4429192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 3, 1, 3, 2].length) (baseStart_4429192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4429192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4429192 prefixEnd_4429192 := by exact prefixLift 4429192
  have htrace : WordTrace (prefixWord ++ tailWord_4429192) baseStart_4429192 baseEnd_4429192 := by
    simpa [prefixWord, tailWord_4429192, baseEnd_4429192] using wordTrace_append hprefix tailTrace_4429192
  have hstable : (prefixWord ++ tailWord_4429192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4429192).length < 2 ^ (prefixWord ++ tailWord_4429192).sum := by decide
  have hdescent : baseEnd_4429192 < baseStart_4429192 := by decide
  rcases family_descends (prefixWord ++ tailWord_4429192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4429231 : List Nat := [1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 8]
def baseStart_4429231 : Nat := 118140960795 + 4429231 * 2 ^ 59
def prefixEnd_4429231 : Nat := 4983230072969 + 3 ^ 40 * 4429231 * 2
def baseEnd_4429231 : Nat := 2274324432794465347042843

theorem tailTrace_4429231 : CollatzResearch.WordTrace tailWord_4429231 prefixEnd_4429231 2274324432794465347042843 := by
  unfold tailWord_4429231
  simp only [CollatzResearch.WordTrace]
  refine ⟨161547326216660014275655547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107698217477773342850437031 161547326216660014275655547)
  ·
    refine ⟨242320989324990021413483321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161547326216660014275655547 242320989324990021413483321)
    ·
      refine ⟨181740741993742516060112491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 242320989324990021413483321 181740741993742516060112491)
      ·
        refine ⟨272611112990613774090168737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181740741993742516060112491 272611112990613774090168737)
        ·
          refine ⟨204458334742960330567626553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 272611112990613774090168737 204458334742960330567626553)
          ·
            refine ⟨153343751057220247925719915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 204458334742960330567626553 153343751057220247925719915)
            ·
              refine ⟨230015626585830371888579873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 153343751057220247925719915 230015626585830371888579873)
              ·
                refine ⟨172511719939372778916434905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 230015626585830371888579873 172511719939372778916434905)
                ·
                  refine ⟨129383789954529584187326179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 172511719939372778916434905 129383789954529584187326179)
                  ·
                    refine ⟨194075684931794376280989269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 129383789954529584187326179 194075684931794376280989269)
                    ·
                      refine ⟨2274324432794465347042843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 194075684931794376280989269 2274324432794465347042843)
                      ·
                        rfl

theorem cell23_4429231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 8].length) (baseStart_4429231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4429231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4429231 prefixEnd_4429231 := by exact prefixLift 4429231
  have htrace : WordTrace (prefixWord ++ tailWord_4429231) baseStart_4429231 baseEnd_4429231 := by
    simpa [prefixWord, tailWord_4429231, baseEnd_4429231] using wordTrace_append hprefix tailTrace_4429231
  have hstable : (prefixWord ++ tailWord_4429231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4429231).length < 2 ^ (prefixWord ++ tailWord_4429231).sum := by decide
  have hdescent : baseEnd_4429231 < baseStart_4429231 := by decide
  rcases family_descends (prefixWord ++ tailWord_4429231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4429245 : List Nat := [1, 4, 1, 2, 2, 1, 2, 5, 5]
def baseStart_4429245 : Nat := 118140960795 + 4429245 * 2 ^ 59
def prefixEnd_4429245 : Nat := 4983230072969 + 3 ^ 40 * 4429245 * 2
def baseEnd_4429245 : Nat := 252703513502625365807531

theorem tailTrace_4429245 : CollatzResearch.WordTrace tailWord_4429245 prefixEnd_4429245 252703513502625365807531 := by
  unfold tailWord_4429245
  simp only [CollatzResearch.WordTrace]
  refine ⟨161547836838609294666665189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107698557892406196444443459 161547836838609294666665189)
  ·
    refine ⟨30290219407239242749999723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 161547836838609294666665189 30290219407239242749999723)
    ·
      refine ⟨45435329110858864124999585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30290219407239242749999723 45435329110858864124999585)
      ·
        refine ⟨34076496833144148093749689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45435329110858864124999585 34076496833144148093749689)
        ·
          refine ⟨25557372624858111070312267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34076496833144148093749689 25557372624858111070312267)
          ·
            refine ⟨38336058937287166605468401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25557372624858111070312267 38336058937287166605468401)
            ·
              refine ⟨28752044202965374954101301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38336058937287166605468401 28752044202965374954101301)
              ·
                refine ⟨2695504144028003901946997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28752044202965374954101301 2695504144028003901946997)
                ·
                  refine ⟨252703513502625365807531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2695504144028003901946997 252703513502625365807531)
                  ·
                    rfl

theorem cell23_4429245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 5, 5].length) (baseStart_4429245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4429245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4429245 prefixEnd_4429245 := by exact prefixLift 4429245
  have htrace : WordTrace (prefixWord ++ tailWord_4429245) baseStart_4429245 baseEnd_4429245 := by
    simpa [prefixWord, tailWord_4429245, baseEnd_4429245] using wordTrace_append hprefix tailTrace_4429245
  have hstable : (prefixWord ++ tailWord_4429245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4429245).length < 2 ^ (prefixWord ++ tailWord_4429245).sum := by decide
  have hdescent : baseEnd_4429245 < baseStart_4429245 := by decide
  rcases family_descends (prefixWord ++ tailWord_4429245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4429250 : List Nat := [3, 5, 2, 1, 1, 1, 2, 2, 2, 1, 3]
def baseStart_4429250 : Nat := 118140960795 + 4429250 * 2 ^ 59
def prefixEnd_4429250 : Nat := 4983230072969 + 3 ^ 40 * 4429250 * 2
def baseEnd_4429250 : Nat := 2274334188926900772705257

theorem tailTrace_4429250 : CollatzResearch.WordTrace tailWord_4429250 prefixEnd_4429250 2274334188926900772705257 := by
  unfold tailWord_4429250
  simp only [CollatzResearch.WordTrace]
  refine ⟨40387004800897795130149301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107698679469060787013731469 40387004800897795130149301)
  ·
    refine ⟨3786281700084168293451497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40387004800897795130149301 3786281700084168293451497)
    ·
      refine ⟨2839711275063126220088623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3786281700084168293451497 2839711275063126220088623)
      ·
        refine ⟨4259566912594689330132935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2839711275063126220088623 4259566912594689330132935)
        ·
          refine ⟨6389350368892033995199403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4259566912594689330132935 6389350368892033995199403)
          ·
            refine ⟨9584025553338050992799105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6389350368892033995199403 9584025553338050992799105)
            ·
              refine ⟨7188019165003538244599329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9584025553338050992799105 7188019165003538244599329)
              ·
                refine ⟨5391014373752653683449497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7188019165003538244599329 5391014373752653683449497)
                ·
                  refine ⟨4043260780314490262587123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5391014373752653683449497 4043260780314490262587123)
                  ·
                    refine ⟨6064891170471735393880685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4043260780314490262587123 6064891170471735393880685)
                    ·
                      refine ⟨2274334188926900772705257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6064891170471735393880685 2274334188926900772705257)
                      ·
                        rfl

theorem cell23_4429250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_4429250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4429250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4429250 prefixEnd_4429250 := by exact prefixLift 4429250
  have htrace : WordTrace (prefixWord ++ tailWord_4429250) baseStart_4429250 baseEnd_4429250 := by
    simpa [prefixWord, tailWord_4429250, baseEnd_4429250] using wordTrace_append hprefix tailTrace_4429250
  have hstable : (prefixWord ++ tailWord_4429250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4429250).length < 2 ^ (prefixWord ++ tailWord_4429250).sum := by decide
  have hdescent : baseEnd_4429250 < baseStart_4429250 := by decide
  rcases family_descends (prefixWord ++ tailWord_4429250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4429262 : List Nat := [4, 1, 1, 1, 2, 1, 6, 2, 5]
def baseStart_4429262 : Nat := 118140960795 + 4429262 * 2 ^ 59
def prefixEnd_4429262 : Nat := 4983230072969 + 3 ^ 40 * 4429262 * 2
def baseEnd_4429262 : Nat := 252704483410528302861689

theorem tailTrace_4429262 : CollatzResearch.WordTrace tailWord_4429262 prefixEnd_4429262 252704483410528302861689 := by
  unfold tailWord_4429262
  simp only [CollatzResearch.WordTrace]
  refine ⟨20193557109943463321254255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107698971253031804380022693 20193557109943463321254255)
  ·
    refine ⟨30290335664915194981881383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20193557109943463321254255 30290335664915194981881383)
    ·
      refine ⟨45435503497372792472822075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30290335664915194981881383 45435503497372792472822075)
      ·
        refine ⟨68153255246059188709233113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45435503497372792472822075 68153255246059188709233113)
        ·
          refine ⟨51114941434544391531924835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68153255246059188709233113 51114941434544391531924835)
          ·
            refine ⟨76672412151816587297887253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51114941434544391531924835 76672412151816587297887253)
            ·
              refine ⟨3594019319616402529588465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 76672412151816587297887253 3594019319616402529588465)
              ·
                refine ⟨2695514489712301897191349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3594019319616402529588465 2695514489712301897191349)
                ·
                  refine ⟨252704483410528302861689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2695514489712301897191349 252704483410528302861689)
                  ·
                    rfl

theorem cell23_4429262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 6, 2, 5].length) (baseStart_4429262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4429262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4429262 prefixEnd_4429262 := by exact prefixLift 4429262
  have htrace : WordTrace (prefixWord ++ tailWord_4429262) baseStart_4429262 baseEnd_4429262 := by
    simpa [prefixWord, tailWord_4429262, baseEnd_4429262] using wordTrace_append hprefix tailTrace_4429262
  have hstable : (prefixWord ++ tailWord_4429262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4429262).length < 2 ^ (prefixWord ++ tailWord_4429262).sum := by decide
  have hdescent : baseEnd_4429262 < baseStart_4429262 := by decide
  rcases family_descends (prefixWord ++ tailWord_4429262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4429295 : List Nat := [1, 1, 2, 1, 4, 1, 5, 1, 2, 1, 4]
def baseStart_4429295 : Nat := 118140960795 + 4429295 * 2 ^ 59
def prefixEnd_4429295 : Nat := 4983230072969 + 3 ^ 40 * 4429295 * 2
def baseEnd_4429295 : Nat := 2274357295556353096642549

theorem tailTrace_4429295 : CollatzResearch.WordTrace tailWord_4429295 prefixEnd_4429295 2274357295556353096642549 := by
  unfold tailWord_4429295
  simp only [CollatzResearch.WordTrace]
  refine ⟨161549660488428153205985339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107699773658952102137323559 161549660488428153205985339)
  ·
    refine ⟨242324490732642229808978009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161549660488428153205985339 242324490732642229808978009)
    ·
      refine ⟨181743368049481672356733507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 242324490732642229808978009 181743368049481672356733507)
      ·
        refine ⟨272615052074222508535100261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181743368049481672356733507 272615052074222508535100261)
        ·
          refine ⟨51115322263916720350331299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 272615052074222508535100261 51115322263916720350331299)
          ·
            refine ⟨76672983395875080525496949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51115322263916720350331299 76672983395875080525496949)
            ·
              refine ⟨7188092193363288799265339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 76672983395875080525496949 7188092193363288799265339)
              ·
                refine ⟨10782138290044933198898009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7188092193363288799265339 10782138290044933198898009)
                ·
                  refine ⟨8086603717533699899173507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10782138290044933198898009 8086603717533699899173507)
                  ·
                    refine ⟨12129905576300549848760261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8086603717533699899173507 12129905576300549848760261)
                    ·
                      refine ⟨2274357295556353096642549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12129905576300549848760261 2274357295556353096642549)
                      ·
                        rfl

theorem cell23_4429295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 1, 2, 1, 4].length) (baseStart_4429295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4429295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4429295 prefixEnd_4429295 := by exact prefixLift 4429295
  have htrace : WordTrace (prefixWord ++ tailWord_4429295) baseStart_4429295 baseEnd_4429295 := by
    simpa [prefixWord, tailWord_4429295, baseEnd_4429295] using wordTrace_append hprefix tailTrace_4429295
  have hstable : (prefixWord ++ tailWord_4429295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4429295).length < 2 ^ (prefixWord ++ tailWord_4429295).sum := by decide
  have hdescent : baseEnd_4429295 < baseStart_4429295 := by decide
  rcases family_descends (prefixWord ++ tailWord_4429295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4429308 : List Nat := [2, 2, 2, 1, 2, 1, 3, 1, 2, 1, 6]
def baseStart_4429308 : Nat := 118140960795 + 4429308 * 2 ^ 59
def prefixEnd_4429308 : Nat := 4983230072969 + 3 ^ 40 * 4429308 * 2
def baseEnd_4429308 : Nat := 2274363970804861545779989

theorem tailTrace_4429308 : CollatzResearch.WordTrace tailWord_4429308 prefixEnd_4429308 2274363970804861545779989 := by
  unfold tailWord_4429308
  simp only [CollatzResearch.WordTrace]
  refine ⟨80775067318690528213104289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107700089758254037617472385 80775067318690528213104289)
  ·
    refine ⟨60581300489017896159828217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80775067318690528213104289 60581300489017896159828217)
    ·
      refine ⟨45435975366763422119871163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60581300489017896159828217 45435975366763422119871163)
      ·
        refine ⟨68153963050145133179806745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45435975366763422119871163 68153963050145133179806745)
        ·
          refine ⟨51115472287608849884855059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68153963050145133179806745 51115472287608849884855059)
          ·
            refine ⟨76673208431413274827282589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51115472287608849884855059 76673208431413274827282589)
            ·
              refine ⟨28752453161779978060230971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76673208431413274827282589 28752453161779978060230971)
              ·
                refine ⟨43128679742669967090346457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28752453161779978060230971 43128679742669967090346457)
                ·
                  refine ⟨32346509807002475317759843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43128679742669967090346457 32346509807002475317759843)
                  ·
                    refine ⟨48519764710503712976639765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32346509807002475317759843 48519764710503712976639765)
                    ·
                      refine ⟨2274363970804861545779989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48519764710503712976639765 2274363970804861545779989)
                      ·
                        rfl

theorem cell23_4429308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 2, 1, 6].length) (baseStart_4429308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4429308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4429308 prefixEnd_4429308 := by exact prefixLift 4429308
  have htrace : WordTrace (prefixWord ++ tailWord_4429308) baseStart_4429308 baseEnd_4429308 := by
    simpa [prefixWord, tailWord_4429308, baseEnd_4429308] using wordTrace_append hprefix tailTrace_4429308
  have hstable : (prefixWord ++ tailWord_4429308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4429308).length < 2 ^ (prefixWord ++ tailWord_4429308).sum := by decide
  have hdescent : baseEnd_4429308 < baseStart_4429308 := by decide
  rcases family_descends (prefixWord ++ tailWord_4429308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4429322 : List Nat := [3, 1, 2, 2, 2, 3, 2, 1, 3, 4]
def baseStart_4429322 : Nat := 118140960795 + 4429322 * 2 ^ 59
def prefixEnd_4429322 : Nat := 4983230072969 + 3 ^ 40 * 4429322 * 2
def baseEnd_4429322 : Nat := 758123719844674830334975

theorem tailTrace_4429322 : CollatzResearch.WordTrace tailWord_4429322 prefixEnd_4429322 758123719844674830334975 := by
  unfold tailWord_4429322
  simp only [CollatzResearch.WordTrace]
  refine ⟨40387661314832584204304555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107700430172886891211478813 40387661314832584204304555)
  ·
    refine ⟨60581491972248876306456833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40387661314832584204304555 60581491972248876306456833)
    ·
      refine ⟨45436118979186657229842625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60581491972248876306456833 45436118979186657229842625)
      ·
        refine ⟨34077089234389992922381969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45436118979186657229842625 34077089234389992922381969)
        ·
          refine ⟨25557816925792494691786477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34077089234389992922381969 25557816925792494691786477)
          ·
            refine ⟨9584181347172185509419929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25557816925792494691786477 9584181347172185509419929)
            ·
              refine ⟨7188136010379139132064947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9584181347172185509419929 7188136010379139132064947)
              ·
                refine ⟨10782204015568708698097421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7188136010379139132064947 10782204015568708698097421)
                ·
                  refine ⟨4043326505838265761786533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10782204015568708698097421 4043326505838265761786533)
                  ·
                    refine ⟨758123719844674830334975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4043326505838265761786533 758123719844674830334975)
                    ·
                      rfl

theorem cell23_4429322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 1, 3, 4].length) (baseStart_4429322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4429322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4429322 prefixEnd_4429322 := by exact prefixLift 4429322
  have htrace : WordTrace (prefixWord ++ tailWord_4429322) baseStart_4429322 baseEnd_4429322 := by
    simpa [prefixWord, tailWord_4429322, baseEnd_4429322] using wordTrace_append hprefix tailTrace_4429322
  have hstable : (prefixWord ++ tailWord_4429322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4429322).length < 2 ^ (prefixWord ++ tailWord_4429322).sum := by decide
  have hdescent : baseEnd_4429322 < baseStart_4429322 := by decide
  rcases family_descends (prefixWord ++ tailWord_4429322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4429338 : List Nat := [3, 1, 1, 3, 1, 1, 1, 1, 3, 2, 6]
def baseStart_4429338 : Nat := 118140960795 + 4429338 * 2 ^ 59
def prefixEnd_4429338 : Nat := 4983230072969 + 3 ^ 40 * 4429338 * 2
def baseEnd_4429338 : Nat := 2274379375224496428404851

theorem tailTrace_4429338 : CollatzResearch.WordTrace tailWord_4429338 prefixEnd_4429338 2274379375224496428404851 := by
  unfold tailWord_4429338
  simp only [CollatzResearch.WordTrace]
  refine ⟨40387807206818092887450167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107700819218181581033200445 40387807206818092887450167)
  ·
    refine ⟨60581710810227139331175251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40387807206818092887450167 60581710810227139331175251)
    ·
      refine ⟨90872566215340708996762877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60581710810227139331175251 90872566215340708996762877)
      ·
        refine ⟨34077212330752765873786079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90872566215340708996762877 34077212330752765873786079)
        ·
          refine ⟨51115818496129148810679119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34077212330752765873786079 51115818496129148810679119)
          ·
            refine ⟨76673727744193723216018679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51115818496129148810679119 76673727744193723216018679)
            ·
              refine ⟨115010591616290584824028019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76673727744193723216018679 115010591616290584824028019)
              ·
                refine ⟨172515887424435877236042029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 115010591616290584824028019 172515887424435877236042029)
                ·
                  refine ⟨64693457784163453963515761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 172515887424435877236042029 64693457784163453963515761)
                  ·
                    refine ⟨48520093338122590472636821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 64693457784163453963515761 48520093338122590472636821)
                    ·
                      refine ⟨2274379375224496428404851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48520093338122590472636821 2274379375224496428404851)
                      ·
                        rfl

theorem cell23_4429338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_4429338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4429338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4429338 prefixEnd_4429338 := by exact prefixLift 4429338
  have htrace : WordTrace (prefixWord ++ tailWord_4429338) baseStart_4429338 baseEnd_4429338 := by
    simpa [prefixWord, tailWord_4429338, baseEnd_4429338] using wordTrace_append hprefix tailTrace_4429338
  have hstable : (prefixWord ++ tailWord_4429338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4429338).length < 2 ^ (prefixWord ++ tailWord_4429338).sum := by decide
  have hdescent : baseEnd_4429338 < baseStart_4429338 := by decide
  rcases family_descends (prefixWord ++ tailWord_4429338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4429415 : List Nat := [1, 1, 5, 1, 1, 1, 3, 1, 3, 2, 4]
def baseStart_4429415 : Nat := 118140960795 + 4429415 * 2 ^ 59
def prefixEnd_4429415 : Nat := 4983230072969 + 3 ^ 40 * 4429415 * 2
def baseEnd_4429415 : Nat := 2274418913234892627141997

theorem tailTrace_4429415 : CollatzResearch.WordTrace tailWord_4429415 prefixEnd_4429415 2274418913234892627141997 := by
  unfold tailWord_4429415
  simp only [CollatzResearch.WordTrace]
  refine ⟨161554037247993413700353699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107702691498662275800235799 161554037247993413700353699)
  ·
    refine ⟨242331055871990120550530549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161554037247993413700353699 242331055871990120550530549)
    ·
      refine ⟨22718536487999073801612239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 242331055871990120550530549 22718536487999073801612239)
      ·
        refine ⟨34077804731998610702418359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22718536487999073801612239 34077804731998610702418359)
        ·
          refine ⟨51116707097997916053627539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34077804731998610702418359 51116707097997916053627539)
          ·
            refine ⟨76675060646996874080441309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51116707097997916053627539 76675060646996874080441309)
            ·
              refine ⟨28753147742623827780165491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76675060646996874080441309 28753147742623827780165491)
              ·
                refine ⟨43129721613935741670248237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28753147742623827780165491 43129721613935741670248237)
                ·
                  refine ⟨16173645605225903126343089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43129721613935741670248237 16173645605225903126343089)
                  ·
                    refine ⟨12130234203919427344757317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16173645605225903126343089 12130234203919427344757317)
                    ·
                      refine ⟨2274418913234892627141997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12130234203919427344757317 2274418913234892627141997)
                      ·
                        rfl

theorem cell23_4429415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_4429415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4429415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4429415 prefixEnd_4429415 := by exact prefixLift 4429415
  have htrace : WordTrace (prefixWord ++ tailWord_4429415) baseStart_4429415 baseEnd_4429415 := by
    simpa [prefixWord, tailWord_4429415, baseEnd_4429415] using wordTrace_append hprefix tailTrace_4429415
  have hstable : (prefixWord ++ tailWord_4429415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4429415).length < 2 ^ (prefixWord ++ tailWord_4429415).sum := by decide
  have hdescent : baseEnd_4429415 < baseStart_4429415 := by decide
  rcases family_descends (prefixWord ++ tailWord_4429415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4429429 : List Nat := [1, 3, 4, 2, 1, 1, 1, 4, 2, 4]
def baseStart_4429429 : Nat := 118140960795 + 4429429 * 2 ^ 59
def prefixEnd_4429429 : Nat := 4983230072969 + 3 ^ 40 * 4429429 * 2
def baseEnd_4429429 : Nat := 758142033988018524122311

theorem tailTrace_4429429 : CollatzResearch.WordTrace tailWord_4429429 prefixEnd_4429429 758142033988018524122311 := by
  unfold tailWord_4429429
  simp only [CollatzResearch.WordTrace]
  refine ⟨161554547869942694091363341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107703031913295129394242227 161554547869942694091363341)
  ·
    refine ⟨60582955451228510284261253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 161554547869942694091363341 60582955451228510284261253)
    ·
      refine ⟨11359304147105345678298985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60582955451228510284261253 11359304147105345678298985)
      ·
        refine ⟨8519478110329009258724239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11359304147105345678298985 8519478110329009258724239)
        ·
          refine ⟨12779217165493513888086359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8519478110329009258724239 12779217165493513888086359)
          ·
            refine ⟨19168825748240270832129539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12779217165493513888086359 19168825748240270832129539)
            ·
              refine ⟨28753238622360406248194309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19168825748240270832129539 28753238622360406248194309)
              ·
                refine ⟨5391232241692576171536433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28753238622360406248194309 5391232241692576171536433)
                ·
                  refine ⟨4043424181269432128652325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5391232241692576171536433 4043424181269432128652325)
                  ·
                    refine ⟨758142033988018524122311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4043424181269432128652325 758142033988018524122311)
                    ·
                      rfl

theorem cell23_4429429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_4429429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4429429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4429429 prefixEnd_4429429 := by exact prefixLift 4429429
  have htrace : WordTrace (prefixWord ++ tailWord_4429429) baseStart_4429429 baseEnd_4429429 := by
    simpa [prefixWord, tailWord_4429429, baseEnd_4429429] using wordTrace_append hprefix tailTrace_4429429
  have hstable : (prefixWord ++ tailWord_4429429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4429429).length < 2 ^ (prefixWord ++ tailWord_4429429).sum := by decide
  have hdescent : baseEnd_4429429 < baseStart_4429429 := by decide
  rcases family_descends (prefixWord ++ tailWord_4429429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4429430 : List Nat := [5, 1, 1, 2, 2, 3, 2, 2, 1, 1, 3]
def baseStart_4429430 : Nat := 118140960795 + 4429430 * 2 ^ 59
def prefixEnd_4429430 : Nat := 4983230072969 + 3 ^ 40 * 4429430 * 2
def baseEnd_4429430 : Nat := 2274426615444710068454429

theorem tailTrace_4429430 : CollatzResearch.WordTrace tailWord_4429430 prefixEnd_4429430 2274426615444710068454429 := by
  unfold tailWord_4429430
  simp only [CollatzResearch.WordTrace]
  refine ⟨10097161521433691953884359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 107703056228626047508099829 10097161521433691953884359)
  ·
    refine ⟨15145742282150537930826539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10097161521433691953884359 15145742282150537930826539)
    ·
      refine ⟨22718613423225806896239809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15145742282150537930826539 22718613423225806896239809)
      ·
        refine ⟨17038960067419355172179857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22718613423225806896239809 17038960067419355172179857)
        ·
          refine ⟨12779220050564516379134893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17038960067419355172179857 12779220050564516379134893)
          ·
            refine ⟨4792207518961693642175585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12779220050564516379134893 4792207518961693642175585)
            ·
              refine ⟨3594155639221270231631689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4792207518961693642175585 3594155639221270231631689)
              ·
                refine ⟨2695616729415952673723767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3594155639221270231631689 2695616729415952673723767)
                ·
                  refine ⟨4043425094123929010585651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2695616729415952673723767 4043425094123929010585651)
                  ·
                    refine ⟨6065137641185893515878477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4043425094123929010585651 6065137641185893515878477)
                    ·
                      refine ⟨2274426615444710068454429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6065137641185893515878477 2274426615444710068454429)
                      ·
                        rfl

theorem cell23_4429430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 2, 2, 1, 1, 3].length) (baseStart_4429430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4429430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4429430 prefixEnd_4429430 := by exact prefixLift 4429430
  have htrace : WordTrace (prefixWord ++ tailWord_4429430) baseStart_4429430 baseEnd_4429430 := by
    simpa [prefixWord, tailWord_4429430, baseEnd_4429430] using wordTrace_append hprefix tailTrace_4429430
  have hstable : (prefixWord ++ tailWord_4429430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4429430).length < 2 ^ (prefixWord ++ tailWord_4429430).sum := by decide
  have hdescent : baseEnd_4429430 < baseStart_4429430 := by decide
  rcases family_descends (prefixWord ++ tailWord_4429430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4429435 : List Nat := [1, 1, 1, 1, 1, 4, 3, 2, 3, 3, 3]
def baseStart_4429435 : Nat := 118140960795 + 4429435 * 2 ^ 59
def prefixEnd_4429435 : Nat := 4983230072969 + 3 ^ 40 * 4429435 * 2
def baseEnd_4429435 : Nat := 2274429182847982548891905

theorem tailTrace_4429435 : CollatzResearch.WordTrace tailWord_4429435 prefixEnd_4429435 2274429182847982548891905 := by
  unfold tailWord_4429435
  simp only [CollatzResearch.WordTrace]
  refine ⟨161554766707920957116081759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107703177805280638077387839 161554766707920957116081759)
  ·
    refine ⟨242332150061881435674122639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161554766707920957116081759 242332150061881435674122639)
    ·
      refine ⟨363498225092822153511183959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242332150061881435674122639 363498225092822153511183959)
      ·
        refine ⟨545247337639233230266775939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 363498225092822153511183959 545247337639233230266775939)
        ·
          refine ⟨817871006458849845400163909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 545247337639233230266775939 817871006458849845400163909)
          ·
            refine ⟨153350813711034346012530733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 817871006458849845400163909 153350813711034346012530733)
            ·
              refine ⟨57506555141637879754699025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 153350813711034346012530733 57506555141637879754699025)
              ·
                refine ⟨43129916356228409816024269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57506555141637879754699025 43129916356228409816024269)
                ·
                  refine ⟨16173718633585653681009101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43129916356228409816024269 16173718633585653681009101)
                  ·
                    refine ⟨6065144487594620130378413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16173718633585653681009101 6065144487594620130378413)
                    ·
                      refine ⟨2274429182847982548891905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6065144487594620130378413 2274429182847982548891905)
                      ·
                        rfl

theorem cell23_4429435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 3, 3, 3].length) (baseStart_4429435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4429435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4429435 prefixEnd_4429435 := by exact prefixLift 4429435
  have htrace : WordTrace (prefixWord ++ tailWord_4429435) baseStart_4429435 baseEnd_4429435 := by
    simpa [prefixWord, tailWord_4429435, baseEnd_4429435] using wordTrace_append hprefix tailTrace_4429435
  have hstable : (prefixWord ++ tailWord_4429435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4429435).length < 2 ^ (prefixWord ++ tailWord_4429435).sum := by decide
  have hdescent : baseEnd_4429435 < baseStart_4429435 := by decide
  rcases family_descends (prefixWord ++ tailWord_4429435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4429452 : List Nat := [2, 2, 1, 2, 1, 1, 6, 1, 1, 3, 3]
def baseStart_4429452 : Nat := 118140960795 + 4429452 * 2 ^ 59
def prefixEnd_4429452 : Nat := 4983230072969 + 3 ^ 40 * 4429452 * 2
def baseEnd_4429452 : Nat := 2274437912019108982379327

theorem tailTrace_4429452 : CollatzResearch.WordTrace tailWord_4429452 prefixEnd_4429452 2274437912019108982379327 := by
  unfold tailWord_4429452
  simp only [CollatzResearch.WordTrace]
  refine ⟨80777693374429684509725305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107703591165906246012967073 80777693374429684509725305)
  ·
    refine ⟨60583270030822263382293979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80777693374429684509725305 60583270030822263382293979)
    ·
      refine ⟨90874905046233395073440969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60583270030822263382293979 90874905046233395073440969)
      ·
        refine ⟨68156178784675046305080727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90874905046233395073440969 68156178784675046305080727)
        ·
          refine ⟨102234268177012569457621091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68156178784675046305080727 102234268177012569457621091)
          ·
            refine ⟨153351402265518854186431637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102234268177012569457621091 153351402265518854186431637)
            ·
              refine ⟨7188346981196196289988983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 153351402265518854186431637 7188346981196196289988983)
              ·
                refine ⟨10782520471794294434983475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7188346981196196289988983 10782520471794294434983475)
                ·
                  refine ⟨16173780707691441652475213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10782520471794294434983475 16173780707691441652475213)
                  ·
                    refine ⟨6065167765384290619678205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16173780707691441652475213 6065167765384290619678205)
                    ·
                      refine ⟨2274437912019108982379327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6065167765384290619678205 2274437912019108982379327)
                      ·
                        rfl

theorem cell23_4429452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 1, 1, 3, 3].length) (baseStart_4429452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4429452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4429452 prefixEnd_4429452 := by exact prefixLift 4429452
  have htrace : WordTrace (prefixWord ++ tailWord_4429452) baseStart_4429452 baseEnd_4429452 := by
    simpa [prefixWord, tailWord_4429452, baseEnd_4429452] using wordTrace_append hprefix tailTrace_4429452
  have hstable : (prefixWord ++ tailWord_4429452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4429452).length < 2 ^ (prefixWord ++ tailWord_4429452).sum := by decide
  have hdescent : baseEnd_4429452 < baseStart_4429452 := by decide
  rcases family_descends (prefixWord ++ tailWord_4429452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4429470 : List Nat := [4, 3, 1, 1, 1, 3, 2, 3, 1, 2, 2]
def baseStart_4429470 : Nat := 118140960795 + 4429470 * 2 ^ 59
def prefixEnd_4429470 : Nat := 4983230072969 + 3 ^ 40 * 4429470 * 2
def baseEnd_4429470 : Nat := 2274447154670889911954245

theorem tailTrace_4429470 : CollatzResearch.WordTrace tailWord_4429470 prefixEnd_4429470 2274447154670889911954245 := by
  unfold tailWord_4429470
  simp only [CollatzResearch.WordTrace]
  refine ⟨20194505407849269761700733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107704028841862772062403909 20194505407849269761700733)
  ·
    refine ⟨7572939527943476160637775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20194505407849269761700733 7572939527943476160637775)
    ·
      refine ⟨11359409291915214240956663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7572939527943476160637775 11359409291915214240956663)
      ·
        refine ⟨17039113937872821361434995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11359409291915214240956663 17039113937872821361434995)
        ·
          refine ⟨25558670906809232042152493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17039113937872821361434995 25558670906809232042152493)
          ·
            refine ⟨9584501590053462015807185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25558670906809232042152493 9584501590053462015807185)
            ·
              refine ⟨7188376192540096511855389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9584501590053462015807185 7188376192540096511855389)
              ·
                refine ⟨2695641072202536191945771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7188376192540096511855389 2695641072202536191945771)
                ·
                  refine ⟨4043461608303804287918657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2695641072202536191945771 4043461608303804287918657)
                  ·
                    refine ⟨3032596206227853215938993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4043461608303804287918657 3032596206227853215938993)
                    ·
                      refine ⟨2274447154670889911954245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3032596206227853215938993 2274447154670889911954245)
                      ·
                        rfl

theorem cell23_4429470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 3, 1, 2, 2].length) (baseStart_4429470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4429470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4429470 prefixEnd_4429470 := by exact prefixLift 4429470
  have htrace : WordTrace (prefixWord ++ tailWord_4429470) baseStart_4429470 baseEnd_4429470 := by
    simpa [prefixWord, tailWord_4429470, baseEnd_4429470] using wordTrace_append hprefix tailTrace_4429470
  have hstable : (prefixWord ++ tailWord_4429470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4429470).length < 2 ^ (prefixWord ++ tailWord_4429470).sum := by decide
  have hdescent : baseEnd_4429470 < baseStart_4429470 := by decide
  rcases family_descends (prefixWord ++ tailWord_4429470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4429480 : List Nat := [2, 1, 7, 1, 1, 2, 1, 2, 2, 4]
def baseStart_4429480 : Nat := 118140960795 + 4429480 * 2 ^ 59
def prefixEnd_4429480 : Nat := 4983230072969 + 3 ^ 40 * 4429480 * 2
def baseEnd_4429480 : Nat := 758150763159144957609733

theorem tailTrace_4429480 : CollatzResearch.WordTrace tailWord_4429480 prefixEnd_4429480 758150763159144957609733 := by
  unfold tailWord_4429480
  simp only [CollatzResearch.WordTrace]
  refine ⟨80778203996378964900734947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107704271995171953200979929 80778203996378964900734947)
  ·
    refine ⟨121167305994568447351102421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80778203996378964900734947 121167305994568447351102421)
    ·
      refine ⟨2839858734247697984791463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 121167305994568447351102421 2839858734247697984791463)
      ·
        refine ⟨4259788101371546977187195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2839858734247697984791463 4259788101371546977187195)
        ·
          refine ⟨6389682152057320465780793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4259788101371546977187195 6389682152057320465780793)
          ·
            refine ⟨4792261614042990349335595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6389682152057320465780793 4792261614042990349335595)
            ·
              refine ⟨7188392421064485524003393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4792261614042990349335595 7188392421064485524003393)
              ·
                refine ⟨5391294315798364143002545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7188392421064485524003393 5391294315798364143002545)
                ·
                  refine ⟨4043470736848773107251909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5391294315798364143002545 4043470736848773107251909)
                  ·
                    refine ⟨758150763159144957609733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4043470736848773107251909 758150763159144957609733)
                    ·
                      rfl

theorem cell23_4429480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_4429480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4429480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4429480 prefixEnd_4429480 := by exact prefixLift 4429480
  have htrace : WordTrace (prefixWord ++ tailWord_4429480) baseStart_4429480 baseEnd_4429480 := by
    simpa [prefixWord, tailWord_4429480, baseEnd_4429480] using wordTrace_append hprefix tailTrace_4429480
  have hstable : (prefixWord ++ tailWord_4429480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4429480).length < 2 ^ (prefixWord ++ tailWord_4429480).sum := by decide
  have hdescent : baseEnd_4429480 < baseStart_4429480 := by decide
  rcases family_descends (prefixWord ++ tailWord_4429480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4429502 : List Nat := [4, 2, 1, 1, 2, 2, 2, 1, 2, 6]
def baseStart_4429502 : Nat := 118140960795 + 4429502 * 2 ^ 59
def prefixEnd_4429502 : Nat := 4983230072969 + 3 ^ 40 * 4429502 * 2
def baseEnd_4429502 : Nat := 758154528683944595584699

theorem tailTrace_4429502 : CollatzResearch.WordTrace tailWord_4429502 prefixEnd_4429502 758154528683944595584699 := by
  unfold tailWord_4429502
  simp only [CollatzResearch.WordTrace]
  refine ⟨20194651299834778444846345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107704806932452151705847173 20194651299834778444846345)
  ·
    refine ⟨15145988474876083833634759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20194651299834778444846345 15145988474876083833634759)
    ·
      refine ⟨22718982712314125750452139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15145988474876083833634759 22718982712314125750452139)
      ·
        refine ⟨34078474068471188625678209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22718982712314125750452139 34078474068471188625678209)
        ·
          refine ⟨25558855551353391469258657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34078474068471188625678209 25558855551353391469258657)
          ·
            refine ⟨19169141663515043601943993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25558855551353391469258657 19169141663515043601943993)
            ·
              refine ⟨14376856247636282701457995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19169141663515043601943993 14376856247636282701457995)
              ·
                refine ⟨21565284371454424052186993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14376856247636282701457995 21565284371454424052186993)
                ·
                  refine ⟨16173963278590818039140245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21565284371454424052186993 16173963278590818039140245)
                  ·
                    refine ⟨758154528683944595584699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16173963278590818039140245 758154528683944595584699)
                    ·
                      rfl

theorem cell23_4429502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 1, 2, 6].length) (baseStart_4429502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4429502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4429502 prefixEnd_4429502 := by exact prefixLift 4429502
  have htrace : WordTrace (prefixWord ++ tailWord_4429502) baseStart_4429502 baseEnd_4429502 := by
    simpa [prefixWord, tailWord_4429502, baseEnd_4429502] using wordTrace_append hprefix tailTrace_4429502
  have hstable : (prefixWord ++ tailWord_4429502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4429502).length < 2 ^ (prefixWord ++ tailWord_4429502).sum := by decide
  have hdescent : baseEnd_4429502 < baseStart_4429502 := by decide
  rcases family_descends (prefixWord ++ tailWord_4429502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4429549 : List Nat := [1, 5, 1, 2, 1, 4, 1, 1, 7]
def baseStart_4429549 : Nat := 118140960795 + 4429549 * 2 ^ 59
def prefixEnd_4429549 : Nat := 4983230072969 + 3 ^ 40 * 4429549 * 2
def baseEnd_4429549 : Nat := 252720857738066122540709

theorem tailTrace_4429549 : CollatzResearch.WordTrace tailWord_4429549 prefixEnd_4429549 252720857738066122540709 := by
  unfold tailWord_4429549
  simp only [CollatzResearch.WordTrace]
  refine ⟨161558924629507954585731701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107705949753005303057154467 161558924629507954585731701)
  ·
    refine ⟨15146149184016370742412347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 161558924629507954585731701 15146149184016370742412347)
    ·
      refine ⟨22719223776024556113618521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15146149184016370742412347 22719223776024556113618521)
      ·
        refine ⟨17039417832018417085213891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22719223776024556113618521 17039417832018417085213891)
        ·
          refine ⟨25559126748027625627820837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17039417832018417085213891 25559126748027625627820837)
          ·
            refine ⟨4792336265255179805216407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25559126748027625627820837 4792336265255179805216407)
            ·
              refine ⟨7188504397882769707824611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4792336265255179805216407 7188504397882769707824611)
              ·
                refine ⟨10782756596824154561736917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7188504397882769707824611 10782756596824154561736917)
                ·
                  refine ⟨252720857738066122540709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10782756596824154561736917 252720857738066122540709)
                  ·
                    rfl

theorem cell23_4429549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 1, 7].length) (baseStart_4429549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4429549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4429549 prefixEnd_4429549 := by exact prefixLift 4429549
  have htrace : WordTrace (prefixWord ++ tailWord_4429549) baseStart_4429549 baseEnd_4429549 := by
    simpa [prefixWord, tailWord_4429549, baseEnd_4429549] using wordTrace_append hprefix tailTrace_4429549
  have hstable : (prefixWord ++ tailWord_4429549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4429549).length < 2 ^ (prefixWord ++ tailWord_4429549).sum := by decide
  have hdescent : baseEnd_4429549 < baseStart_4429549 := by decide
  rcases family_descends (prefixWord ++ tailWord_4429549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4429555 : List Nat := [1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 7]
def baseStart_4429555 : Nat := 118140960795 + 4429555 * 2 ^ 59
def prefixEnd_4429555 : Nat := 4983230072969 + 3 ^ 40 * 4429555 * 2
def baseEnd_4429555 : Nat := 2274490800526522079391353

theorem tailTrace_4429555 : CollatzResearch.WordTrace tailWord_4429555 prefixEnd_4429555 2274490800526522079391353 := by
  unfold tailWord_4429555
  simp only [CollatzResearch.WordTrace]
  refine ⟨161559143467486217610450119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107706095644990811740300079 161559143467486217610450119)
  ·
    refine ⟨242338715201229326415675179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161559143467486217610450119 242338715201229326415675179)
    ·
      refine ⟨363508072801843989623512769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242338715201229326415675179 363508072801843989623512769)
      ·
        refine ⟨272631054601382992217634577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 363508072801843989623512769 272631054601382992217634577)
        ·
          refine ⟨204473290951037244163225933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 272631054601382992217634577 204473290951037244163225933)
          ·
            refine ⟨76677484106638966561209725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 204473290951037244163225933 76677484106638966561209725)
            ·
              refine ⟨28754056539989612460453647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76677484106638966561209725 28754056539989612460453647)
              ·
                refine ⟨43131084809984418690680471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28754056539989612460453647 43131084809984418690680471)
                ·
                  refine ⟨64696627214976628036020707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43131084809984418690680471 64696627214976628036020707)
                  ·
                    refine ⟨97044940822464942054031061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 64696627214976628036020707 97044940822464942054031061)
                    ·
                      refine ⟨2274490800526522079391353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 97044940822464942054031061 2274490800526522079391353)
                      ·
                        rfl

theorem cell23_4429555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 7].length) (baseStart_4429555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4429555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4429555 prefixEnd_4429555 := by exact prefixLift 4429555
  have htrace : WordTrace (prefixWord ++ tailWord_4429555) baseStart_4429555 baseEnd_4429555 := by
    simpa [prefixWord, tailWord_4429555, baseEnd_4429555] using wordTrace_append hprefix tailTrace_4429555
  have hstable : (prefixWord ++ tailWord_4429555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4429555).length < 2 ^ (prefixWord ++ tailWord_4429555).sum := by decide
  have hdescent : baseEnd_4429555 < baseStart_4429555 := by decide
  rcases family_descends (prefixWord ++ tailWord_4429555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
